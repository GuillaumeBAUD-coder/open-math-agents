import OMAStatements.S_oeis_a269729

namespace OMA.S_oeis_a269729




/-! ### Fibonacci-type sequences on ℤ -/

/-- G satisfies the Fibonacci recurrence on all of ℤ. -/
def IsFib (G : ℤ → ℤ) : Prop := ∀ k : ℤ, G (k + 2) = G (k + 1) + G k

lemma IsFib.shift {G : ℤ → ℤ} (hG : IsFib G) (s : ℤ) : IsFib (fun k => G (k + s)) := by
  intro k
  have := hG (k + s)
  simp only
  rw [show k + 2 + s = k + s + 2 by ring, show k + 1 + s = k + s + 1 by ring]
  exact this

lemma IsFib.neg {G : ℤ → ℤ} (hG : IsFib G) : IsFib (fun k => -G k) := by
  intro k
  simp only
  rw [hG k]
  ring

lemma IsFib.mul {G : ℤ → ℤ} (hG : IsFib G) (e : ℤ) : IsFib (fun k => e * G k) := by
  intro k
  simp only
  rw [hG k]
  ring

lemma IsFib.pred {G : ℤ → ℤ} (hG : IsFib G) (k : ℤ) : G (k + 1) = G k + G (k - 1) := by
  have := hG (k - 1)
  rw [show k - 1 + 2 = k + 1 by ring, show k - 1 + 1 = k by ring] at this
  exact this

lemma fib_ext {G H : ℤ → ℤ} (hG : IsFib G) (hH : IsFib H) (h1 : G (-1) = H (-1))
    (h0 : G 0 = H 0) : ∀ k, G k = H k := by
  have up : ∀ m : ℕ, G ((m : ℤ) - 1) = H ((m : ℤ) - 1) ∧ G m = H m := by
    intro m
    induction m with
    | zero => exact ⟨by simpa using h1, by simpa using h0⟩
    | succ m ih =>
      refine ⟨by push_cast; rw [show (m : ℤ) + 1 - 1 = m by ring]; exact ih.2, ?_⟩
      push_cast
      rw [hG.pred, hH.pred, ih.1, ih.2]
  have down : ∀ m : ℕ, G (-(m : ℤ)) = H (-(m : ℤ)) ∧ G (-(m : ℤ) - 1) = H (-(m : ℤ) - 1) := by
    intro m
    induction m with
    | zero => exact ⟨by simpa using h0, by simpa using h1⟩
    | succ m ih =>
      refine ⟨by push_cast; rw [show -((m : ℤ) + 1) = -(m : ℤ) - 1 by ring]; exact ih.2, ?_⟩
      have eG := hG (-(m : ℤ) - 2)
      have eH := hH (-(m : ℤ) - 2)
      rw [show -(m : ℤ) - 2 + 2 = -(m : ℤ) by ring,
        show -(m : ℤ) - 2 + 1 = -(m : ℤ) - 1 by ring] at eG eH
      push_cast
      rw [show -((m : ℤ) + 1) - 1 = -(m : ℤ) - 2 by ring]
      linarith [ih.1, ih.2]
  intro k
  rcases Int.eq_nat_or_neg k with ⟨m, rfl | rfl⟩
  · exact (up m).2
  · exact (down m).1

/-! ### Signs -/

lemma negpow_add (a b : ℤ) :
    (-1 : ℤ) ^ (a + b).natAbs = (-1) ^ a.natAbs * (-1) ^ b.natAbs := by
  rcases Int.even_or_odd a with ha | ha <;> rcases Int.even_or_odd b with hb | hb
  · rw [(Int.natAbs_even.mpr (ha.add hb)).neg_one_pow, (Int.natAbs_even.mpr ha).neg_one_pow,
      (Int.natAbs_even.mpr hb).neg_one_pow]
    norm_num
  · rw [(Int.natAbs_odd.mpr (ha.add_odd hb)).neg_one_pow, (Int.natAbs_even.mpr ha).neg_one_pow,
      (Int.natAbs_odd.mpr hb).neg_one_pow]
    norm_num
  · rw [(Int.natAbs_odd.mpr (ha.add_even hb)).neg_one_pow, (Int.natAbs_odd.mpr ha).neg_one_pow,
      (Int.natAbs_even.mpr hb).neg_one_pow]
    norm_num
  · rw [(Int.natAbs_even.mpr (ha.add_odd hb)).neg_one_pow, (Int.natAbs_odd.mpr ha).neg_one_pow,
      (Int.natAbs_odd.mpr hb).neg_one_pow]
    norm_num

lemma negpow_sq (a : ℤ) : (-1 : ℤ) ^ a.natAbs * (-1) ^ a.natAbs = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]
  norm_num

lemma negpow_one : (-1 : ℤ) ^ (1 : ℤ).natAbs = -1 := by norm_num

lemma negpow_two : (-1 : ℤ) ^ (2 : ℤ).natAbs = 1 := by norm_num

lemma negpow_cases (a : ℤ) : (-1 : ℤ) ^ a.natAbs = 1 ∨ (-1 : ℤ) ^ a.natAbs = -1 := by
  rcases Int.even_or_odd a with ha | ha
  · left
    exact (Int.natAbs_even.mpr ha).neg_one_pow
  · right
    exact (Int.natAbs_odd.mpr ha).neg_one_pow

/-! ### The rows and their reversals -/

/-- floor((r+1) phi) -/
noncomputable def A (r : ℕ) : ℤ := ⌊((r : ℝ) + 1) * Real.goldenRatio⌋

lemma isFib_W (r : ℕ) : IsFib (W r) := by
  intro k
  unfold W
  rw [show k + 2 + 1 = (k + 1) + 2 by ring, Int.fib_add_two (k + 1), Int.fib_add_two k,
    show k + 1 + 1 = k + 2 by ring, Int.fib_add_two k]
  ring

lemma W_neg_one (r : ℕ) : W r (-1) = r := by
  simp [W]

lemma W_zero (r : ℕ) : W r 0 = A r := by
  simp [W, A]

lemma isFib_rev (n : ℕ) : IsFib (rev n) := by
  intro k
  unfold rev
  have e := isFib_W n (-k - 2)
  rw [show -k - 2 + 2 = -k by ring, show -k - 2 + 1 = -(k + 1) by ring] at e
  rw [show -(k + 2) = -k - 2 by ring, negpow_add k 2, negpow_add k 1, negpow_one, negpow_two]
  linear_combination (-(-1 : ℤ) ^ k.natAbs) * e

lemma A_pos (r : ℕ) : 1 ≤ A r := by
  unfold A
  rw [Int.le_floor]
  have h1 := Real.one_lt_goldenRatio
  have h2 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  push_cast
  nlinarith

lemma W_pos (r : ℕ) : ∀ k : ℤ, 0 ≤ k → 1 ≤ W r k := by
  have h : ∀ m : ℕ, 1 ≤ W r m ∧ 1 ≤ W r (m + 1) := by
    intro m
    induction m with
    | zero =>
      refine ⟨by simpa [W_zero] using A_pos r, ?_⟩
      have := (isFib_W r).pred 0
      simp only [zero_add] at this
      simp only [Nat.cast_zero, zero_add]
      rw [this, W_zero, show (0 : ℤ) - 1 = -1 by norm_num, W_neg_one]
      have := A_pos r
      omega
    | succ m ih =>
      refine ⟨by push_cast; exact ih.2, ?_⟩
      push_cast
      have := isFib_W r m
      rw [show (m : ℤ) + 1 + 1 = m + 2 by ring, this]
      omega
  intro k hk
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
  exact (h m).1

/-- Once two consecutive terms are nonpositive and negative, the sequence stays negative. -/
lemma neg_forever {G : ℤ → ℤ} (hG : IsFib G) {t : ℤ} (h1 : G (t - 1) ≤ 0) (h2 : G t < 0) :
    ∀ m : ℕ, G (t + m) < 0 := by
  have h : ∀ m : ℕ, G (t + m) < 0 ∧ G (t + m + 1) < 0 := by
    intro m
    induction m with
    | zero =>
      refine ⟨by simpa using h2, ?_⟩
      simp only [Nat.cast_zero, add_zero]
      rw [hG.pred]
      omega
    | succ m ih =>
      refine ⟨by push_cast; rw [← add_assoc]; exact ih.2, ?_⟩
      push_cast
      have := hG (t + m)
      rw [show t + (m + 1) + 1 = t + m + 2 by ring, this]
      omega
  exact fun m => (h m).1

/-! ### The golden ratio window -/

lemma inv_gold : Real.goldenRatio⁻¹ = Real.goldenRatio - 1 := by
  rw [Real.inv_goldenRatio, ← Real.one_sub_goldenConj]
  ring

/-- delta(k) = G(k) - G(k-1) phi. -/
noncomputable def dlt (G : ℤ → ℤ) (k : ℤ) : ℝ := (G k : ℝ) - (G (k - 1) : ℝ) * Real.goldenRatio

/-- The window (1/phi, phi]. -/
def InW (x : ℝ) : Prop := Real.goldenRatio⁻¹ < x ∧ x ≤ Real.goldenRatio

lemma dlt_succ {G : ℤ → ℤ} (hG : IsFib G) (k : ℤ) :
    dlt G (k + 1) = -dlt G k / Real.goldenRatio := by
  unfold dlt
  rw [show k + 1 - 1 = k by ring, hG.pred k]
  have hφ := Real.goldenRatio_pos.ne'
  have hsq := Real.goldenRatio_sq
  rw [eq_div_iff hφ]
  push_cast
  linear_combination (-(G k : ℝ)) * hsq

lemma abs_dlt_succ {G : ℤ → ℤ} (hG : IsFib G) (k : ℤ) :
    |dlt G (k + 1)| = |dlt G k| / Real.goldenRatio := by
  rw [dlt_succ hG, abs_div, abs_neg, abs_of_pos Real.goldenRatio_pos]

lemma abs_dlt_add {G : ℤ → ℤ} (hG : IsFib G) (k : ℤ) (m : ℕ) :
    |dlt G (k + m)| = |dlt G k| / Real.goldenRatio ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    push_cast
    rw [← add_assoc, abs_dlt_succ hG, ih, pow_succ, div_div]

lemma abs_dlt_sub {G : ℤ → ℤ} (hG : IsFib G) (k : ℤ) (m : ℕ) :
    |dlt G (k - m)| = |dlt G k| * Real.goldenRatio ^ m := by
  have h := abs_dlt_add hG (k - m) m
  rw [show k - (m : ℤ) + m = k by ring] at h
  have hp : (0 : ℝ) < Real.goldenRatio ^ m := pow_pos Real.goldenRatio_pos m
  rw [h, div_mul_cancel₀ _ hp.ne']

lemma window_unique {G : ℤ → ℤ} (hG : IsFib G) {k k' : ℤ} (hk : InW (dlt G k))
    (hk' : InW (dlt G k')) : k = k' := by
  have hφ := Real.one_lt_goldenRatio
  have hφ0 := Real.goldenRatio_pos
  have hinv : (0 : ℝ) < Real.goldenRatio⁻¹ := inv_pos.mpr hφ0
  -- one step later the sign flips, two or more steps later delta has size at most 1/phi
  have key : ∀ {j j' : ℤ}, InW (dlt G j) → InW (dlt G j') → j < j' → False := by
    intro j j' hj hj' hlt
    obtain ⟨m, hm⟩ : ∃ m : ℕ, j' = j + (m + 1 : ℕ) := ⟨(j' - j - 1).toNat, by omega⟩
    subst hm
    rcases m with _ | m
    · have h := dlt_succ hG j
      simp only [Nat.cast_one, zero_add] at hj'
      rw [h] at hj'
      have : -dlt G j / Real.goldenRatio < 0 := div_neg_of_neg_of_pos (by linarith [hj.1]) hφ0
      linarith [hj'.1]
    · have h := abs_dlt_add hG j (m + 2)
      have hle : |dlt G j| ≤ Real.goldenRatio := by
        rw [abs_of_pos (by linarith [hj.1])]
        exact hj.2
      have hpow : Real.goldenRatio ^ 2 ≤ Real.goldenRatio ^ (m + 2) :=
        pow_le_pow_right₀ hφ.le (by omega)
      have hbound : |dlt G (j + ((m + 2 : ℕ) : ℤ))| ≤ Real.goldenRatio⁻¹ := by
        rw [h, div_le_iff₀ (pow_pos hφ0 _)]
        calc |dlt G j| ≤ Real.goldenRatio := hle
          _ = Real.goldenRatio⁻¹ * Real.goldenRatio ^ 2 := by
            field_simp
          _ ≤ Real.goldenRatio⁻¹ * Real.goldenRatio ^ (m + 2) :=
            mul_le_mul_of_nonneg_left hpow hinv.le
      have hj'' := hj'.1
      have : dlt G (j + ((m + 1 + 1 : ℕ) : ℤ)) ≤ |dlt G (j + ((m + 2 : ℕ) : ℤ))| := le_abs_self _
      linarith
  rcases lt_trichotomy k k' with h | h | h
  · exact (key hk hk' h).elim
  · exact h
  · exact (key hk' hk h).elim

lemma dlt_zero_ne {G : ℤ → ℤ} (h : ¬ (G (-1) = 0 ∧ G 0 = 0)) : dlt G 0 ≠ 0 := by
  unfold dlt
  intro h0
  simp only [zero_sub] at h0
  by_cases h1 : G (-1) = 0
  · rw [h1] at h0
    simp only [Int.cast_zero, zero_mul, sub_zero, Int.cast_eq_zero] at h0
    exact h ⟨h1, h0⟩
  · have hirr := Real.goldenRatio_irrational.intCast_mul h1
    exact hirr.ne_int (G 0) (by linarith)

lemma window_exists {G : ℤ → ℤ} (hG : IsFib G) (h0 : dlt G 0 ≠ 0) : ∃ k, InW (dlt G k) := by
  classical
  have hφ := Real.one_lt_goldenRatio
  have hφ0 := Real.goldenRatio_pos
  set c := |dlt G 0| with hc
  have hcpos : 0 < c := abs_pos.mpr h0
  -- find k with 1 < |delta(k)| <= phi
  have hk : ∃ k, 1 < |dlt G k| ∧ |dlt G k| ≤ Real.goldenRatio := by
    by_cases hc1 : c ≤ 1
    · have hex : ∃ m : ℕ, 1 < c * Real.goldenRatio ^ m := by
        obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (1 / c) hφ
        exact ⟨m, by rw [div_lt_iff₀ hcpos] at hm; linarith⟩
      let m := Nat.find hex
      have hm : 1 < c * Real.goldenRatio ^ m := Nat.find_spec hex
      have hm0 : m ≠ 0 := by
        intro h
        rw [h, pow_zero, mul_one] at hm
        linarith
      obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hprev : ¬ 1 < c * Real.goldenRatio ^ m' := Nat.find_min hex (by omega)
      refine ⟨0 - m, ?_, ?_⟩
      · rw [abs_dlt_sub hG]
        exact hm
      · rw [abs_dlt_sub hG, hm', pow_succ, ← mul_assoc]
        push_neg at hprev
        nlinarith
    · push_neg at hc1
      have hex : ∃ m : ℕ, c / Real.goldenRatio ^ m ≤ 1 := by
        obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt c hφ
        exact ⟨m, by rw [div_le_iff₀ (pow_pos hφ0 _)]; linarith⟩
      let m := Nat.find hex
      have hm : c / Real.goldenRatio ^ m ≤ 1 := Nat.find_spec hex
      have hm0 : m ≠ 0 := by
        intro h
        rw [h, pow_zero, div_one] at hm
        linarith
      obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hprev : ¬ c / Real.goldenRatio ^ m' ≤ 1 := Nat.find_min hex (by omega)
      push_neg at hprev
      refine ⟨0 + m', ?_, ?_⟩
      · rw [abs_dlt_add hG]
        exact hprev
      · rw [abs_dlt_add hG]
        rw [hm', pow_succ, ← div_div] at hm
        have hp : (0 : ℝ) < Real.goldenRatio ^ m' := pow_pos hφ0 _
        rw [div_le_iff₀ hφ0, one_mul] at hm
        exact hm
  obtain ⟨k, hk1, hk2⟩ := hk
  rcases lt_or_gt_of_ne (show dlt G k ≠ 0 by intro h; rw [h] at hk1; simp at hk1; linarith)
    with hneg | hpos
  · refine ⟨k + 1, ?_, ?_⟩
    · rw [dlt_succ hG, abs_of_neg hneg] at *
      rw [lt_div_iff₀ hφ0, inv_mul_cancel₀ hφ0.ne']
      linarith
    · rw [dlt_succ hG, div_le_iff₀ hφ0]
      rw [abs_of_neg hneg] at hk1 hk2
      nlinarith
  · refine ⟨k, ?_, ?_⟩
    · rw [abs_of_pos hpos] at hk1
      have : Real.goldenRatio⁻¹ < 1 := inv_lt_one_of_one_lt₀ hφ
      linarith
    · rw [abs_of_pos hpos] at hk2
      exact hk2

/-- y = floor((x+1) phi) exactly when y - x phi lies in the window. -/
lemma floor_iff (x y : ℤ) :
    ⌊((x : ℝ) + 1) * Real.goldenRatio⌋ = y ↔ InW ((y : ℝ) - x * Real.goldenRatio) := by
  rw [Int.floor_eq_iff, InW, inv_gold]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor <;> linarith

lemma W_window (r : ℕ) : InW (dlt (W r) 0) := by
  unfold dlt
  rw [show (0 : ℤ) - 1 = -1 by norm_num, W_zero, W_neg_one]
  have := (floor_iff (r : ℤ) (A r)).mp (by simp [A])
  simpa using this

/-! ### Existence, uniqueness and symmetry of the row -/

/-- Row r contains the sequence G up to shift and sign. -/
def Contains (r : ℕ) (G : ℤ → ℤ) : Prop :=
  ∃ s : ℤ, (∀ k : ℤ, W r k = G (k + s)) ∨ (∀ k : ℤ, W r k = -G (k + s))

lemma contains_sign {r : ℕ} {G : ℤ → ℤ} (h : Contains r G) :
    ∃ s e : ℤ, (e = 1 ∨ e = -1) ∧ ∀ k, W r k = e * G (k + s) := by
  obtain ⟨s, h | h⟩ := h
  · exact ⟨s, 1, Or.inl rfl, fun k => by rw [h k]; ring⟩
  · exact ⟨s, -1, Or.inr rfl, fun k => by rw [h k]; ring⟩

lemma contains_of_sign {r : ℕ} {G : ℤ → ℤ} (s e : ℤ) (he : e = 1 ∨ e = -1)
    (h : ∀ k, W r k = e * G (k + s)) : Contains r G := by
  rcases he with rfl | rfl
  · exact ⟨s, Or.inl fun k => by rw [h k]; ring⟩
  · exact ⟨s, Or.inr fun k => by rw [h k]; ring⟩

/-- A Fibonacci-type sequence whose window pair has a nonnegative first term is a row. -/
lemma contains_of_window {G : ℤ → ℤ} (hG : IsFib G) {j : ℤ} (hj : InW (dlt G j))
    (hx : 0 ≤ G (j - 1)) : ∀ k, W (G (j - 1)).toNat k = G (k + j) := by
  have hr : ((G (j - 1)).toNat : ℤ) = G (j - 1) := Int.toNat_of_nonneg hx
  have hrR : ((G (j - 1)).toNat : ℝ) = ((G (j - 1) : ℤ) : ℝ) := by exact_mod_cast hr
  apply fib_ext (isFib_W _) (hG.shift j)
  · rw [W_neg_one, hr]
    show G (j - 1) = G (-1 + j)
    rw [show -1 + j = j - 1 by ring]
  · rw [W_zero]
    show A _ = G (0 + j)
    rw [zero_add]
    unfold A
    have hfl := (floor_iff (G (j - 1)) (G j)).mpr hj
    rw [hrR]
    exact hfl

lemma rows_exist (n : ℕ) : ∃ r, Contains r (rev n) := by
  have hG := isFib_rev n
  have hG0 : rev n 0 = A n := by simp [rev, W_zero]
  have hne : dlt (rev n) 0 ≠ 0 := by
    apply dlt_zero_ne
    rintro ⟨-, h⟩
    have := A_pos n
    omega
  obtain ⟨j, hj⟩ := window_exists hG hne
  by_cases hx : 0 ≤ rev n (j - 1)
  · exact ⟨_, ⟨j, Or.inl (contains_of_window hG hj hx)⟩⟩
  · push_neg at hx
    have hG' := hG.neg
    have hne' : dlt (fun k => -rev n k) 0 ≠ 0 := by
      have : dlt (fun k => -rev n k) 0 = -dlt (rev n) 0 := by
        unfold dlt
        push_cast
        ring
      rw [this]
      exact neg_ne_zero.mpr hne
    obtain ⟨j', hj'⟩ := window_exists hG' hne'
    by_cases hx' : 0 ≤ -rev n (j' - 1)
    · refine ⟨(-rev n (j' - 1)).toNat, ⟨j', Or.inr fun k => ?_⟩⟩
      exact contains_of_window hG' hj' hx' k
    · push_neg at hx'
      exfalso
      -- rev n is negative from j + 1 on, and positive from j' + 1 on
      have hy : rev n j ≤ 0 := by
        have hfl := (floor_iff (rev n (j - 1)) (rev n j)).mpr hj
        rw [← hfl]
        apply Int.floor_nonpos
        have : ((rev n (j - 1) : ℤ) : ℝ) + 1 ≤ 0 := by
          have : rev n (j - 1) + 1 ≤ 0 := by omega
          exact_mod_cast this
        nlinarith [Real.goldenRatio_pos]
      have hy' : -rev n j' ≤ 0 := by
        have hfl := (floor_iff (-rev n (j' - 1)) (-rev n j')).mpr hj'
        rw [← hfl]
        apply Int.floor_nonpos
        have : ((-rev n (j' - 1) : ℤ) : ℝ) + 1 ≤ 0 := by
          have : -rev n (j' - 1) + 1 ≤ 0 := by omega
          exact_mod_cast this
        nlinarith [Real.goldenRatio_pos]
      have n1 := neg_forever hG (t := j + 1) (by simpa using hy)
        (by rw [hG.pred]; omega)
      have n2 := neg_forever hG' (t := j' + 1) (by simpa using hy')
        (by show -rev n (j' + 1) < 0; rw [hG.pred]; omega)
      set N := max j j' with hN
      have a1 := n1 (N - j).toNat
      have a2 := n2 (N - j').toNat
      rw [Int.toNat_of_nonneg (by omega)] at a1 a2
      rw [show j + 1 + (N - j) = N + 1 by ring] at a1
      rw [show j' + 1 + (N - j') = N + 1 by ring] at a2
      omega

lemma rows_unique {n r r' : ℕ} (h : Contains r (rev n)) (h' : Contains r' (rev n)) : r = r' := by
  obtain ⟨s, e, he, hW⟩ := contains_sign h
  obtain ⟨s', e', he', hW'⟩ := contains_sign h'
  have hee : e * e = 1 := by rcases he with rfl | rfl <;> norm_num
  -- rev n j = e W r (j - s)
  have hrev : ∀ j, rev n j = e * W r (j - s) := by
    intro j
    rw [hW (j - s), show j - s + s = j by ring, ← mul_assoc, hee, one_mul]
  have hrel : ∀ k, W r' k = (e' * e) * W r (k + (s' - s)) := by
    intro k
    rw [hW' k, hrev, mul_assoc, show k + s' - s = k + (s' - s) by ring]
  set t := s' - s
  have hη : e' * e = 1 ∨ e' * e = -1 := by
    rcases he with rfl | rfl <;> rcases he' with rfl | rfl <;> norm_num
  have hwin := W_window r'
  have hdl : dlt (W r') 0 = ((e' * e : ℤ) : ℝ) * dlt (W r) t := by
    unfold dlt
    rw [hrel 0, hrel (0 - 1), show (0 : ℤ) + t = t by ring, show (0 : ℤ) - 1 + t = t - 1 by ring]
    push_cast
    ring
  rcases hη with hη | hη
  · rw [hdl, hη] at hwin
    simp only [Int.cast_one, one_mul] at hwin
    have ht : t = 0 := window_unique (isFib_W r) hwin (W_window r)
    have := hrel (-1)
    rw [hη, ht, one_mul, add_zero, W_neg_one, W_neg_one] at this
    exact_mod_cast this.symm
  · exfalso
    have h1 := hrel (-1)
    have h0 := hrel 0
    rw [hη, W_neg_one] at h1
    rw [hη, W_zero, zero_add] at h0
    have hA := A_pos r'
    have hneg := neg_forever (isFib_W r) (t := t) (by rw [show -1 + t = t - 1 by ring] at h1; omega)
      (by omega)
    have := hneg t.natAbs
    have hp := W_pos r (t + t.natAbs) (by omega)
    omega

lemma rows_symm {n r : ℕ} (h : Contains r (rev n)) : Contains n (rev r) := by
  obtain ⟨s, e, he, hW⟩ := contains_sign h
  have hee : e * e = 1 := by rcases he with rfl | rfl <;> norm_num
  have hs2 := negpow_sq s
  refine contains_of_sign s (e * (-1) ^ s.natAbs) ?_ fun k => ?_
  · rcases he with rfl | rfl <;> rcases negpow_cases s with h | h <;> rw [h] <;> norm_num
  · -- rev r (k + s) = e (-1)^s W n k
    have hr : rev r (k + s) = e * (-1) ^ s.natAbs * W n k := by
      unfold rev
      rw [hW (-(k + s)), show -(k + s) + s = -k by ring]
      unfold rev
      rw [neg_neg, show k + s = s + k by ring, negpow_add s k, show (-k).natAbs = k.natAbs from
        Int.natAbs_neg k]
      have := negpow_sq k
      linear_combination (e * (-1) ^ s.natAbs * W n k) * this
    rw [hr]
    calc W n k = (e * e) * ((-1) ^ s.natAbs * (-1) ^ s.natAbs) * W n k := by
          rw [hee, hs2]; ring
      _ = e * (-1) ^ s.natAbs * (e * (-1) ^ s.natAbs * W n k) := by ring

/-- Mathar's conjecture: A269729 is its own inverse. -/
theorem conjecture : ∀ n : ℕ, a (a n) = n := by
  intro n
  have hset : ∀ m : ℕ, {r : ℕ | ∃ s : ℤ, (∀ k : ℤ, W r k = rev m (k + s)) ∨
      (∀ k : ℤ, W r k = -rev m (k + s))}.Nonempty := fun m => rows_exist m
  have h1 : Contains (a n) (rev n) := Nat.sInf_mem (hset n)
  have h2 : Contains n (rev (a n)) := rows_symm h1
  have h3 : Contains (a (a n)) (rev (a n)) := Nat.sInf_mem (hset (a n))
  exact (rows_unique h2 h3).symm

/-! ### Controls from the entry -/

lemma a_eq {n r : ℕ} (h : Contains r (rev n)) : a n = r := by
  have hne : {r : ℕ | ∃ s : ℤ, (∀ k : ℤ, W r k = rev n (k + s)) ∨
      (∀ k : ℤ, W r k = -rev n (k + s))}.Nonempty := ⟨r, h⟩
  have hmem : Contains (a n) (rev n) := Nat.sInf_mem hne
  exact rows_unique hmem h

lemma sqrt5_bounds : (2 : ℝ) ≤ Real.sqrt 5 ∧ Real.sqrt 5 < 9 / 4 := by
  constructor
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  · rw [Real.sqrt_lt' (by norm_num)]
    norm_num

lemma W_eq (r : ℕ) (k : ℤ) : W r k = Int.fib (k + 1) * A r + r * Int.fib k := rfl

lemma A_val (r : ℕ) (v : ℤ) (h1 : (v : ℝ) ≤ ((r : ℝ) + 1) * ((1 + Real.sqrt 5) / 2))
    (h2 : ((r : ℝ) + 1) * ((1 + Real.sqrt 5) / 2) < v + 1) : A r = v := by
  unfold A
  rw [Int.floor_eq_iff]
  exact ⟨h1, h2⟩

lemma A_zero : A 0 = 1 := by
  obtain ⟨h1, h2⟩ := sqrt5_bounds
  apply A_val <;> push_cast <;> linarith

lemma A_five : A 5 = 9 := by
  obtain ⟨h1, h2⟩ := sqrt5_bounds
  apply A_val <;> push_cast <;> linarith

lemma A_seven : A 7 = 12 := by
  obtain ⟨h1, h2⟩ := sqrt5_bounds
  apply A_val <;> push_cast <;> linarith

/-- a(0) = 0: row 0 (the Fibonacci numbers) read backwards with signs is row 0 again. -/
lemma a_zero : a 0 = 0 := by
  apply a_eq
  refine ⟨2, Or.inl (fib_ext (isFib_W 0) ((isFib_rev 0).shift 2) ?_ ?_)⟩
  · show W 0 (-1) = rev 0 (-1 + 2)
    simp only [rev, W_eq, A_zero]
    decide
  · show W 0 0 = rev 0 (0 + 2)
    simp only [rev, W_eq, A_zero]
    decide

/-- a(5) = 7, the example of the entry: row 5 read backwards is row 7. -/
lemma a_five : a 5 = 7 := by
  apply a_eq
  refine ⟨8, Or.inl (fib_ext (isFib_W 7) ((isFib_rev 5).shift 8) ?_ ?_)⟩
  · show W 7 (-1) = rev 5 (-1 + 8)
    simp only [rev, W_eq, A_five, A_seven]
    decide
  · show W 7 0 = rev 5 (0 + 8)
    simp only [rev, W_eq, A_five, A_seven]
    decide

end OMA.S_oeis_a269729

theorem OMA.solution : type_of% @OMA.S_oeis_a269729.main :=
  OMA.S_oeis_a269729.conjecture
