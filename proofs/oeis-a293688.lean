import OMAStatements.S_oeis_a293688

namespace OMA.S_oeis_a293688

open Real

/-! ### The golden ratio -/

lemma g_inv1 : (goldenRatio - 1) * goldenRatio = 1 := by
  have := goldenRatio_sq
  nlinarith

lemma g_inv2 : (2 - goldenRatio) * goldenRatio ^ 2 = 1 := by
  have := goldenRatio_sq
  rw [this]
  nlinarith

lemma upperW_eq (k : ℕ) : upperW k = lowerW k + k := by
  unfold upperW lowerW
  rw [goldenRatio_sq, mul_add, mul_one]
  exact Nat.floor_add_natCast (by positivity) k

lemma lowerW_succ (k : ℕ) : lowerW k + 1 ≤ lowerW (k + 1) := by
  unfold lowerW
  rw [← Nat.floor_add_one (by positivity)]
  apply Nat.floor_le_floor
  push_cast
  nlinarith [one_lt_goldenRatio]

lemma lowerW_strictMono : StrictMono lowerW :=
  strictMono_nat_of_lt_succ fun k => by have := lowerW_succ k; omega

lemma upperW_strictMono : StrictMono upperW :=
  strictMono_nat_of_lt_succ fun k => by rw [upperW_eq, upperW_eq]; have := lowerW_succ k; omega

lemma lowerW_pos (k : ℕ) (hk : 1 ≤ k) : 1 ≤ lowerW k := by
  unfold lowerW
  rw [Nat.one_le_floor_iff]
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith [one_lt_goldenRatio]

/-! ### The counting functions -/

/-- c(n): the number of k >= 1 with L(k) <= n. -/
noncomputable def cL (n : ℕ) : ℕ := ⌊((n : ℝ) + 1) * (goldenRatio - 1)⌋₊

/-- d(n): the number of k >= 1 with U(k) <= n. -/
noncomputable def cU (n : ℕ) : ℕ := ⌊((n : ℝ) + 1) * (2 - goldenRatio)⌋₊

lemma irr1 (n : ℕ) : Irrational (((n : ℝ) + 1) * (goldenRatio - 1)) := by
  have h : ((n : ℝ) + 1) * (goldenRatio - 1) =
      ((n + 1 : ℕ) : ℝ) * goldenRatio - ((n + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [h]
  exact (goldenRatio_irrational.natCast_mul (by omega)).sub_natCast _

lemma irr2 (n : ℕ) : Irrational (((n : ℝ) + 1) * (2 - goldenRatio)) := by
  have h : ((n : ℝ) + 1) * (2 - goldenRatio) =
      ((2 * (n + 1) : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ) * goldenRatio := by push_cast; ring
  rw [h]
  exact (goldenRatio_irrational.natCast_mul (by omega)).natCast_sub _

lemma pos1 : 0 < goldenRatio - 1 := by linarith [one_lt_goldenRatio]

lemma pos2 : 0 < 2 - goldenRatio := by linarith [goldenRatio_lt_two]

lemma lower_le_iff (k n : ℕ) : lowerW k ≤ n ↔ k ≤ cL n := by
  have hy : (0 : ℝ) ≤ ((n : ℝ) + 1) * (goldenRatio - 1) := mul_nonneg (by positivity) pos1.le
  have hne : (k : ℝ) ≠ ((n : ℝ) + 1) * (goldenRatio - 1) := fun h => (irr1 n).ne_nat k h.symm
  have e : ((n : ℝ) + 1) * (goldenRatio - 1) * goldenRatio = (n : ℝ) + 1 := by
    rw [mul_assoc, g_inv1, mul_one]
  unfold lowerW cL
  rw [← Nat.lt_succ_iff, Nat.floor_lt (by positivity), Nat.le_floor_iff hy]
  push_cast
  constructor
  · intro h
    by_contra hc
    rw [not_le] at hc
    have := mul_lt_mul_of_pos_right hc goldenRatio_pos
    rw [e] at this
    linarith
  · intro h
    have hlt := lt_of_le_of_ne h hne
    have := mul_lt_mul_of_pos_right hlt goldenRatio_pos
    rw [e] at this
    linarith

lemma upper_le_iff (k n : ℕ) : upperW k ≤ n ↔ k ≤ cU n := by
  have hy : (0 : ℝ) ≤ ((n : ℝ) + 1) * (2 - goldenRatio) := mul_nonneg (by positivity) pos2.le
  have hne : (k : ℝ) ≠ ((n : ℝ) + 1) * (2 - goldenRatio) := fun h => (irr2 n).ne_nat k h.symm
  have e : ((n : ℝ) + 1) * (2 - goldenRatio) * goldenRatio ^ 2 = (n : ℝ) + 1 := by
    rw [mul_assoc, g_inv2, mul_one]
  have hg2 : 0 < goldenRatio ^ 2 := by positivity
  unfold upperW cU
  rw [← Nat.lt_succ_iff, Nat.floor_lt (by positivity), Nat.le_floor_iff hy]
  push_cast
  constructor
  · intro h
    by_contra hc
    rw [not_le] at hc
    have := mul_lt_mul_of_pos_right hc hg2
    rw [e] at this
    linarith
  · intro h
    have hlt := lt_of_le_of_ne h hne
    have := mul_lt_mul_of_pos_right hlt hg2
    rw [e] at this
    linarith

lemma cL_add_cU (n : ℕ) : cL n + cU n = n := by
  unfold cL cU
  set x := ((n : ℝ) + 1) * (goldenRatio - 1) with hx
  set y := ((n : ℝ) + 1) * (2 - goldenRatio) with hy
  have hxy : x + y = (n : ℝ) + 1 := by rw [hx, hy]; ring
  have hx0 : 0 ≤ x := mul_nonneg (by positivity) pos1.le
  have hy0 : 0 ≤ y := mul_nonneg (by positivity) pos2.le
  have h1 : (⌊x⌋₊ : ℝ) < x := lt_of_le_of_ne (Nat.floor_le hx0) fun h => (irr1 n).ne_nat _ h.symm
  have h2 : (⌊y⌋₊ : ℝ) < y := lt_of_le_of_ne (Nat.floor_le hy0) fun h => (irr2 n).ne_nat _ h.symm
  have h3 := Nat.lt_floor_add_one x
  have h4 := Nat.lt_floor_add_one y
  have a1 : ⌊x⌋₊ + ⌊y⌋₊ < n + 1 := by
    have : ((⌊x⌋₊ + ⌊y⌋₊ : ℕ) : ℝ) < ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have a2 : n < ⌊x⌋₊ + ⌊y⌋₊ + 1 := by
    have : ((n : ℕ) : ℝ) < ((⌊x⌋₊ + ⌊y⌋₊ + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  omega

lemma cL_le (n : ℕ) : cL n ≤ n := by have := cL_add_cU n; omega

lemma cL_mono (n : ℕ) : cL n ≤ cL (n + 1) := by
  unfold cL
  apply Nat.floor_le_floor
  push_cast
  nlinarith [pos1]

lemma cU_mono (n : ℕ) : cU n ≤ cU (n + 1) := by
  unfold cU
  apply Nat.floor_le_floor
  push_cast
  nlinarith [pos2]

lemma cL_zero : cL 0 = 0 := by
  unfold cL
  rw [Nat.floor_eq_zero]
  push_cast
  linarith [goldenRatio_lt_two]

/-- U(k) = L(L(k)) + 1 for k >= 1. -/
lemma upper_eq_lower_lower (k : ℕ) (hk : 1 ≤ k) : upperW k = lowerW (lowerW k) + 1 := by
  rw [upperW_eq]
  set m := lowerW k with hm
  have hkφ : 0 ≤ (k : ℝ) * goldenRatio := by positivity
  have hθ1 : (m : ℝ) < (k : ℝ) * goldenRatio := lt_of_le_of_ne (Nat.floor_le hkφ)
    fun h => (goldenRatio_irrational.natCast_mul (by omega : k ≠ 0)).ne_nat m h.symm
  have hθ2 : (k : ℝ) * goldenRatio < m + 1 := Nat.lt_floor_add_one _
  have hk2 : (k : ℝ) * goldenRatio ^ 2 = (k : ℝ) * goldenRatio + k := by rw [goldenRatio_sq]; ring
  have hg1 := one_lt_goldenRatio
  have hg2 := goldenRatio_lt_two
  have key : lowerW m = m + k - 1 := by
    unfold lowerW
    rw [Nat.floor_eq_iff (by positivity)]
    have hcast : ((m + k - 1 : ℕ) : ℝ) = (m : ℝ) + k - 1 := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [hcast]
    constructor
    · nlinarith [mul_pos (sub_pos.mpr hθ2) (sub_pos.mpr hg1)]
    · nlinarith [mul_pos (sub_pos.mpr hθ1) (sub_pos.mpr hg1)]
  omega

lemma eq_of_le_iff {x y : ℕ} (h : ∀ k, 1 ≤ k → (k ≤ x ↔ k ≤ y)) : x = y := by
  rcases Nat.lt_trichotomy x y with hlt | heq | hgt
  · have := (h y (by omega)).mpr le_rfl
    omega
  · exact heq
  · have := (h x (by omega)).mp le_rfl
    omega

lemma cU_eq (n : ℕ) (hn : 1 ≤ n) : cU n = cL (cL (n - 1)) := by
  apply eq_of_le_iff
  intro k hk
  rw [← upper_le_iff, upper_eq_lower_lower k hk, ← lower_le_iff, ← lower_le_iff]
  omega

/-- c is the Hofstadter G-sequence. -/
lemma cL_rec (n : ℕ) (hn : 1 ≤ n) : cL n = n - cL (cL (n - 1)) := by
  have := cL_add_cU n
  rw [cU_eq n hn] at this
  omega

lemma G_eq (G : ℕ → ℕ) (hG : IsG G) : ∀ n, G n = cL n := by
  obtain ⟨h0, hrec⟩ := hG
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [h0, cL_zero]
    · rw [hrec n hn, ih (n - 1) (by omega), ih (cL (n - 1)) (by have := cL_le (n - 1); omega),
        cL_rec n hn]

/-! ### The values of L and U -/

/-- m is a value L(k) with k >= 1. -/
def isL (m : ℕ) : Prop := ∃ k, 1 ≤ k ∧ lowerW k = m

/-- m is a value U(k) with k >= 1. -/
def isU (m : ℕ) : Prop := ∃ k, 1 ≤ k ∧ upperW k = m

lemma isL_iff (m : ℕ) (hm : 1 ≤ m) : isL m ↔ cL m = cL (m - 1) + 1 := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    have h1 : k ≤ cL (lowerW k) := (lower_le_iff k _).mp le_rfl
    have h2 : ¬k + 1 ≤ cL (lowerW k) := fun h => by
      have := (lower_le_iff (k + 1) _).mpr h
      have := lowerW_succ k
      omega
    have h3 : ¬k ≤ cL (lowerW k - 1) := fun h => by
      have := (lower_le_iff k _).mpr h
      omega
    have h4 : k - 1 ≤ cL (lowerW k - 1) := by
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · omega
      · apply (lower_le_iff (k - 1) _).mp
        have := lowerW_strictMono (show k - 1 < k by omega)
        omega
    omega
  · intro h
    refine ⟨cL m, by omega, ?_⟩
    have h1 := (lower_le_iff (cL m) m).mpr le_rfl
    have h2 : ¬lowerW (cL m) ≤ m - 1 := fun h' => by
      have := (lower_le_iff (cL m) (m - 1)).mp h'
      omega
    omega

lemma isU_iff (m : ℕ) (hm : 1 ≤ m) : isU m ↔ cU m = cU (m - 1) + 1 := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    have h1 : k ≤ cU (upperW k) := (upper_le_iff k _).mp le_rfl
    have h2 : ¬k + 1 ≤ cU (upperW k) := fun h => by
      have := (upper_le_iff (k + 1) _).mpr h
      have := upperW_strictMono (show k < k + 1 by omega)
      omega
    have h3 : ¬k ≤ cU (upperW k - 1) := fun h => by
      have := (upper_le_iff k _).mpr h
      have := upperW_eq k
      have := lowerW_pos k hk
      omega
    have h4 : k - 1 ≤ cU (upperW k - 1) := by
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · omega
      · apply (upper_le_iff (k - 1) _).mp
        have := upperW_strictMono (show k - 1 < k by omega)
        omega
    omega
  · intro h
    refine ⟨cU m, by omega, ?_⟩
    have h1 := (upper_le_iff (cU m) m).mpr le_rfl
    have h2 : ¬upperW (cU m) ≤ m - 1 := fun h' => by
      have := (upper_le_iff (cU m) (m - 1)).mp h'
      omega
    omega

/-- Every m >= 1 is exactly one of an L-value and a U-value. -/
lemma one_of (m : ℕ) (hm : 1 ≤ m) : (isL m ∧ ¬isU m) ∨ (isU m ∧ ¬isL m) := by
  have e1 := cL_add_cU m
  have e2 := cL_add_cU (m - 1)
  have m1 := cL_mono (m - 1)
  have m2 := cU_mono (m - 1)
  rw [show m - 1 + 1 = m by omega] at m1 m2
  rw [isL_iff m hm, isU_iff m hm]
  omega

lemma swapW_L (k : ℕ) (hk : 1 ≤ k) : swapW (lowerW k) = upperW k := by
  have h : ∃ j, 1 ≤ j ∧ lowerW j = lowerW k := ⟨k, hk, rfl⟩
  unfold swapW
  rw [dif_pos h]
  congr 1
  exact lowerW_strictMono.injective h.choose_spec.2

lemma swapW_U (k : ℕ) (hk : 1 ≤ k) (hnot : ¬isL (upperW k)) : swapW (upperW k) = lowerW k := by
  have h : ∃ j, 1 ≤ j ∧ upperW j = upperW k := ⟨k, hk, rfl⟩
  have hnot' : ¬∃ j, 1 ≤ j ∧ lowerW j = upperW k := hnot
  unfold swapW
  rw [dif_neg hnot', dif_pos h]
  congr 1
  exact upperW_strictMono.injective h.choose_spec.2

lemma swapW_zero : swapW 0 = 0 := by
  have h1 : ¬∃ k, 1 ≤ k ∧ lowerW k = 0 := fun ⟨k, hk, h⟩ => by have := lowerW_pos k hk; omega
  have h2 : ¬∃ k, 1 ≤ k ∧ upperW k = 0 := fun ⟨k, hk, h⟩ => by
    have := lowerW_pos k hk
    rw [upperW_eq] at h
    omega
  unfold swapW
  rw [dif_neg h1, dif_neg h2]

/-- The partial sums of A002251 are (n + 1) c(n). -/
lemma a_eq (n : ℕ) : a n = (n + 1) * cL n := by
  induction n with
  | zero =>
    unfold a
    rw [Finset.sum_range_one, swapW_zero, cL_zero]
  | succ n ih =>
    have hsum : a (n + 1) = a n + swapW (n + 1) := Finset.sum_range_succ _ _
    rw [hsum, ih]
    have e1 := cL_add_cU (n + 1)
    have e2 := cL_add_cU n
    have m1 := cL_mono n
    have m2 := cU_mono n
    rcases one_of (n + 1) (by omega) with ⟨hL, hnU⟩ | ⟨hU, hnL⟩
    · have hc := (isL_iff (n + 1) (by omega)).mp hL
      rw [show n + 1 - 1 = n by omega] at hc
      obtain ⟨k, hk, hkm⟩ := hL
      have hkc : k = cL (n + 1) := by
        have h1 := (lower_le_iff k (n + 1)).mp (le_of_eq hkm)
        have h2 : ¬k + 1 ≤ cL (n + 1) := fun h => by
          have := (lower_le_iff (k + 1) (n + 1)).mpr h
          have := lowerW_succ k
          omega
        omega
      have hs : swapW (n + 1) = n + 1 + cL (n + 1) := by
        rw [← hkm, swapW_L k hk, upperW_eq, hkm, hkc]
      rw [hs, hc]
      ring
    · have hd := (isU_iff (n + 1) (by omega)).mp hU
      rw [show n + 1 - 1 = n by omega] at hd
      obtain ⟨k, hk, hkm⟩ := hU
      have hkd : k = cU (n + 1) := by
        have h1 := (upper_le_iff k (n + 1)).mp (le_of_eq hkm)
        have h2 : ¬k + 1 ≤ cU (n + 1) := fun h => by
          have := (upper_le_iff (k + 1) (n + 1)).mpr h
          have := upperW_strictMono (show k < k + 1 by omega)
          omega
        omega
      have hval : lowerW k = cL n := by
        have := upperW_eq k
        omega
      have hs : swapW (n + 1) = cL n := by
        rw [← hkm, swapW_U k hk (by rw [hkm]; exact hnL), hval]
      have hc : cL (n + 1) = cL n := by omega
      rw [hs, hc]
      ring

/-- The conjecture: a(n) = (n + 1) A005206(n). -/
theorem conjecture : ∀ G : ℕ → ℕ, IsG G → ∀ n : ℕ, a n = (n + 1) * G n := by
  intro G hG n
  rw [a_eq, G_eq G hG n]

end OMA.S_oeis_a293688

theorem OMA.solution : type_of% @OMA.S_oeis_a293688.main :=
  OMA.S_oeis_a293688.conjecture
