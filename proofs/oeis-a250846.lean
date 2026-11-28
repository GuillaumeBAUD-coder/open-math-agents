import OMAStatements.S_oeis_a250846

-- Credit: @Dariusthedoggie
-- Proof: transfer matrix over rows annihilated by the order-4 recurrence polynomial, giving the g.f., bridged to the index-pair encoding.

namespace OMA.P250846

open PowerSeries
/-- A `2 X 2` `0..3` subblock `(a, b / c, d)` has `b - a ≤ d - c` (in `ℤ`) and `min a c ≤ min b d`. -/
def okBlock (a b c d : Fin 4) : Prop :=
  (b.val : ℤ) - a.val ≤ (d.val : ℤ) - c.val ∧ min a.val c.val ≤ min b.val d.val

instance (a b c d : Fin 4) : Decidable (okBlock a b c d) := by
  unfold okBlock; infer_instance

/-- An `(m + 1) X 2` `0..3` array is valid when every `2 X 2` subblock satisfies `okBlock`. -/
def isValid (m : ℕ) (x : Fin (m + 1) → Fin 2 → Fin 4) : Prop :=
  ∀ i : Fin m, ∀ j : Fin 1,
    okBlock (x i.castSucc j.castSucc) (x i.castSucc j.succ)
      (x i.succ j.castSucc) (x i.succ j.succ)

instance (m : ℕ) (x : Fin (m + 1) → Fin 2 → Fin 4) : Decidable (isValid m x) := by
  unfold isValid; infer_instance

/-- A250846: Number of (n+1) X (1+1) 0..3 arrays with nondecreasing x(i,j)-x(i,j-1) in the i direction and nondecreasing min(x(i,j),x(i-1,j)) in the j direction. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (Finset.univ.filter (isValid (n + 1))).card

abbrev Row := Fin 2 → Fin 4

def okRow (r₁ r₂ : Row) : Prop :=
  ∀ j : Fin 1, okBlock (r₁ j.castSucc) (r₁ j.succ) (r₂ j.castSucc) (r₂ j.succ)

instance (r₁ r₂ : Row) : Decidable (okRow r₁ r₂) := by
  unfold okRow; infer_instance

def enc (r : Row) : Fin 16 :=
  ⟨4 * (r 0).val + (r 1).val, by
    have h0 := (r 0).isLt; have h1 := (r 1).isLt; omega⟩

def dec (k : Fin 16) : Row := fun c =>
  have hk := k.isLt
  if c.val = 0 then ⟨k.val / 4, by omega⟩ else ⟨k.val % 4, by omega⟩

lemma enc_dec : ∀ k : Fin 16, enc (dec k) = k := by
  intro k; have hk := k.isLt; ext; simp [enc, dec]; try omega

lemma dec_enc : ∀ r : Row, dec (enc r) = r := by
  intro r; ext c
  have h0 := (r 0).isLt; have h1 := (r 1).isLt
  fin_cases c
  · change (dec (enc r) 0).val = (r 0).val; simp [dec, enc]; try omega
  · change (dec (enc r) 1).val = (r 1).val; simp [dec, enc]; try omega

def ok2 (i j : Fin 16) : Prop := okRow (dec i) (dec j)

instance (i j : Fin 16) : Decidable (ok2 i j) := by
  unfold ok2; infer_instance

def adjMask (i : Fin 16) : ℕ := match i.val with
  | 0 => 36079
  | 1 => 2254
  | 2 => 140
  | 3 => 8
  | 4 => 15
  | 5 => 36079
  | 6 => 2254
  | 7 => 140
  | 8 => 15
  | 9 => 239
  | 10 => 36079
  | 11 => 2254
  | 12 => 15
  | 13 => 239
  | 14 => 3311
  | 15 => 36079
  | _ => 0

lemma ok2_iff : ∀ i j : Fin 16, ok2 i j ↔ (adjMask i / 2 ^ j.val) % 2 = 1 := by decide +kernel

def step (f : Fin 16 → ℕ) (i : Fin 16) : ℕ :=
  ∑ j : Fin 16, if ok2 i j then f j else 0

def v : ℕ → Fin 16 → ℕ
  | 0, _ => 1
  | m + 1, i => step (v m) i

lemma sum_cons {m : ℕ} (f : (Fin (m + 2) → Row) → ℕ) :
    ∑ x, f x = ∑ r : Row, ∑ y : Fin (m + 1) → Row, f (Fin.cons r y) := by
  rw [← (Fin.consEquiv (fun _ => Row)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma fiber (m : ℕ) (g : (Fin (m + 1) → Row) → ℕ) :
    ∑ y, g y = ∑ i : Fin 16, ∑ y : Fin (m + 1) → Row, if enc (y 0) = i then g y else 0 := by
  trans ∑ y : Fin (m + 1) → Row, ∑ i : Fin 16, if enc (y 0) = i then g y else 0
  · apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_eq_single (enc (y 0))]
    · simp
    · intro i _ hi; simp [Ne.symm hi]
    · simp
  · exact Finset.sum_comm

lemma isValid_zero (y : Fin 1 → Row) : isValid 0 y := by
  intro i; exact Fin.elim0 i

lemma isValid_cons (m : ℕ) (r : Row) (y : Fin (m + 1) → Row) :
    isValid (m + 1) (Fin.cons r y) ↔ okRow r (y 0) ∧ isValid m y := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro j
      simpa [Fin.castSucc_zero, Fin.succ_zero_eq_one] using h 0 j
    · intro i j
      simpa using h i.succ j
  · rintro ⟨h0, hy⟩ i j
    refine Fin.cases ?_ (fun i' => ?_) i
    · simpa [Fin.castSucc_zero, Fin.succ_zero_eq_one] using h0 j
    · simpa using hy i' j

lemma v_eq (m : ℕ) (i : Fin 16) :
    v m i = ∑ y : Fin (m + 1) → Row, if enc (y 0) = i ∧ isValid m y then 1 else 0 := by
  induction m generalizing i with
  | zero =>
    rw [v, ← (Equiv.funUnique (Fin 1) Row).symm.sum_comp]
    rw [Finset.sum_eq_single (dec i)]
    · have hu : (Equiv.funUnique (Fin 1) Row).symm (dec i) = fun _ : Fin 1 => dec i := funext fun _ => rfl
      rw [hu]
      simp [enc_dec, isValid_zero]
    · intro r _ hr
      have hne : enc r ≠ i := fun h => hr (by rw [← dec_enc r, h])
      have hu : (Equiv.funUnique (Fin 1) Row).symm r = fun _ : Fin 1 => r := funext fun _ => rfl
      rw [hu]
      simp [hne]
    · simp
  | succ m ih =>
    rw [v, step, sum_cons]
    rw [Finset.sum_eq_single (dec i)]
    · simp only [Fin.cons_zero, enc_dec, true_and, isValid_cons]
      rw [fiber]
      apply Finset.sum_congr rfl
      intro j _
      rw [ih j]
      by_cases h : ok2 i j
      · simp only [h, ↓reduceIte]
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : enc (y 0) = j
        · have hok : okRow (dec i) (y 0) := by
            rw [← dec_enc (y 0), hy]; exact h
          simp [hy, hok]
        · simp [hy]
      · simp only [h, ↓reduceIte]
        symm
        apply Finset.sum_eq_zero
        intro y _
        by_cases hy : enc (y 0) = j
        · have hnok : ¬ okRow (dec i) (y 0) := by
            rw [← dec_enc (y 0), hy]; exact h
          simp [hy, hnok]
        · simp [hy]
    · intro r _ hr
      have hne : enc r ≠ i := fun h => hr (by rw [← dec_enc r, h])
      apply Finset.sum_eq_zero
      intro y _
      simp [hne]
    · simp

lemma a_succ (n : ℕ) : a (n + 1) = ∑ i : Fin 16, v (n + 1) i := by
  simp only [a, Finset.card_filter]
  rw [fiber]
  apply Finset.sum_congr rfl
  intro i _
  rw [v_eq]
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> tauto

def vtab0 (i : Fin 16) : ℕ := match i.val with
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 1
  | 9 => 1
  | 10 => 1
  | 11 => 1
  | 12 => 1
  | 13 => 1
  | 14 => 1
  | 15 => 1
  | _ => 0

def vtab1 (i : Fin 16) : ℕ := match i.val with
  | 0 => 10
  | 1 => 6
  | 2 => 3
  | 3 => 1
  | 4 => 4
  | 5 => 10
  | 6 => 6
  | 7 => 3
  | 8 => 4
  | 9 => 7
  | 10 => 10
  | 11 => 6
  | 12 => 4
  | 13 => 7
  | 14 => 9
  | 15 => 10
  | _ => 0

def vtab2 (i : Fin 16) : ℕ := match i.val with
  | 0 => 65
  | 1 => 25
  | 2 => 7
  | 3 => 1
  | 4 => 20
  | 5 => 65
  | 6 => 25
  | 7 => 7
  | 8 => 20
  | 9 => 39
  | 10 => 65
  | 11 => 25
  | 12 => 20
  | 13 => 39
  | 14 => 55
  | 15 => 65
  | _ => 0

def vtab3 (i : Fin 16) : ℕ := match i.val with
  | 0 => 350
  | 1 => 90
  | 2 => 15
  | 3 => 1
  | 4 => 98
  | 5 => 350
  | 6 => 90
  | 7 => 15
  | 8 => 98
  | 9 => 195
  | 10 => 350
  | 11 => 90
  | 12 => 98
  | 13 => 195
  | 14 => 285
  | 15 => 350
  | _ => 0

def vtab4 (i : Fin 16) : ℕ := match i.val with
  | 0 => 1701
  | 1 => 301
  | 2 => 31
  | 3 => 1
  | 4 => 456
  | 5 => 1701
  | 6 => 301
  | 7 => 31
  | 8 => 456
  | 9 => 911
  | 10 => 1701
  | 11 => 301
  | 12 => 456
  | 13 => 911
  | 14 => 1351
  | 15 => 1701
  | _ => 0

lemma v_0 : ∀ i : Fin 16, v 0 i = vtab0 i := by decide +kernel
lemma v_1 : ∀ i : Fin 16, v 1 i = vtab1 i := by
  intro i; rw [show (1 : ℕ) = 0 + 1 from rfl, v, step]; simp only [v_0, ok2_iff]; revert i; decide +kernel
lemma v_2 : ∀ i : Fin 16, v 2 i = vtab2 i := by
  intro i; rw [show (2 : ℕ) = 1 + 1 from rfl, v, step]; simp only [v_1, ok2_iff]; revert i; decide +kernel
lemma v_3 : ∀ i : Fin 16, v 3 i = vtab3 i := by
  intro i; rw [show (3 : ℕ) = 2 + 1 from rfl, v, step]; simp only [v_2, ok2_iff]; revert i; decide +kernel
lemma v_4 : ∀ i : Fin 16, v 4 i = vtab4 i := by
  intro i; rw [show (4 : ℕ) = 3 + 1 from rfl, v, step]; simp only [v_3, ok2_iff]; revert i; decide +kernel

def err (m : ℕ) (i : Fin 16) : ℤ :=
  (v (m + 4) i : ℤ) - 10 * (v (m + 3) i : ℤ) + 35 * (v (m + 2) i : ℤ) - 50 * (v (m + 1) i : ℤ) + 24 * (v m i : ℤ)

lemma err_base : ∀ i : Fin 16, err 0 i = 0 := by
  intro i
  change (v 4 i : ℤ) - 10 * (v 3 i : ℤ) + 35 * (v 2 i : ℤ) - 50 * (v 1 i : ℤ) + 24 * (v 0 i : ℤ) = 0
  simp only [v_4, v_3, v_2, v_1, v_0]
  revert i; decide +kernel

lemma err_succ (m : ℕ) (i : Fin 16) :
    err (m + 1) i = ∑ j : Fin 16, if ok2 i j then err m j else 0 := by
  have hV : ∀ r, (v (r + 1) i : ℤ) = ∑ j : Fin 16, if ok2 i j then (v r j : ℤ) else 0 := by
    intro r; rw [v, step]; simp only [Nat.cast_sum, apply_ite Nat.cast, Nat.cast_zero]
  unfold err
  simp only [hV]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

lemma err_all (m : ℕ) (i : Fin 16) : err m i = 0 := by
  induction m generalizing i with
  | zero => exact err_base i
  | succ m ih =>
    rw [err_succ]
    exact Finset.sum_eq_zero (fun j _ => by simp [ih j])

lemma err_ge (m : ℕ) (i : Fin 16) : err (m + 1) i = 0 := err_all (m + 1) i

lemma a_rec_ge (m : ℕ) :
    (a (m + 5) : ℤ) = 10 * a (m + 4) - 35 * a (m + 3) + 50 * a (m + 2) - 24 * a (m + 1) := by
  have h : ∑ i : Fin 16, err (m + 1) i = 0 :=
    Finset.sum_eq_zero (fun i _ => err_ge m i)
  unfold err at h
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  have hsum : ∀ r : ℕ, (∑ i : Fin 16, (v (m + 1 + r) i : ℤ)) = (a (m + 1 + r) : ℤ) := by
    intro r
    have h1 : m + 1 + r = (m + 0 + r) + 1 := by omega
    rw [h1, a_succ, Nat.cast_sum]
  have hsum0 : (∑ i : Fin 16, (v (m + 1) i : ℤ)) = (a (m + 1) : ℤ) := by
    simpa only [Nat.add_zero] using hsum 0
  simp only [hsum, hsum0] at h
  have h2_1 : m + 1 + 1 = m + 2 := by omega
  have h2_2 : m + 1 + 2 = m + 3 := by omega
  have h2_3 : m + 1 + 3 = m + 4 := by omega
  have h2_4 : m + 1 + 4 = m + 5 := by omega
  simp only [h2_1, h2_2, h2_3, h2_4] at h
  linarith


lemma a_0 : a 0 = 0 := rfl
lemma a_1 : a 1 = 100 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, a_succ]
  change ∑ i : Fin 16, v 1 i = 100
  simp only [v_1]; decide +kernel
lemma a_2 : a 2 = 543 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, a_succ]
  change ∑ i : Fin 16, v 2 i = 543
  simp only [v_2]; decide +kernel
lemma a_3 : a 3 = 2670 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, a_succ]
  change ∑ i : Fin 16, v 3 i = 2670
  simp only [v_3]; decide +kernel
lemma a_4 : a 4 = 12311 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, a_succ]
  change ∑ i : Fin 16, v 4 i = 12311
  simp only [v_4]; decide +kernel

def cf (n : ℕ) : ℚ :=
  (832 * (4 : ℚ) ^ n - 846 * (3 : ℚ) ^ n + 204 * (2 : ℚ) ^ n + 2) / 12


theorem main_proof_ours :
    (∀ n : ℕ, 5 ≤ n → (a n : ℤ) = 10 * a (n - 1) - 35 * a (n - 2) + 50 * a (n - 3) - 24 * a (n - 4)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 2 * X) * (1 - 3 * X) * (1 - 4 * X)) =
      X * (100 - 457 * X + 740 * X ^ 2 - 384 * X ^ 3)) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (832 * (4 : ℚ) ^ n - 846 * (3 : ℚ) ^ n + 204 * (2 : ℚ) ^ n + 2) / 12) := by
  have hrec : ∀ n : ℕ, 5 ≤ n → (a n : ℤ) = 10 * a (n - 1) - 35 * a (n - 2) + 50 * a (n - 3) - 24 * a (n - 4) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    simpa using a_rec_ge m
  have hgf : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 2 * X) * (1 - 3 * X) * (1 - 4 * X)) =
      X * (100 - 457 * X + 740 * X ^ 2 - 384 * X ^ 3) := by
    have hl : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 2 * X) * (1 - 3 * X) * (1 - 4 * X)) =
        PowerSeries.mk (fun n => (a n : ℚ))
        - C (10 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1)
        + C (35 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2)
        - C (50 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 3)
        + C (24 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 4) := by
      simp only [map_ofNat, map_one]; ring
    have hr : (X * (100 - 457 * X + 740 * X ^ 2 - 384 * X ^ 3) : PowerSeries ℚ) =
        C (100 : ℚ) * X ^ 1 - C (457 : ℚ) * X ^ 2 + C (740 : ℚ) * X ^ 3 - C (384 : ℚ) * X ^ 4 := by
      simp only [map_ofNat, map_one]; ring
    rw [hl, hr]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    rcases Nat.lt_or_ge n 5 with hn | hn
    · interval_cases n <;> simp [a_0, a_1, a_2, a_3, a_4] <;> try norm_num
    · have hq : (a n : ℚ) = 10 * a (n - 1) - 35 * a (n - 2) + 50 * a (n - 3) - 24 * a (n - 4) := by
        exact_mod_cast hrec n (by omega)
      have c1 : 1 ≤ n := by omega
      have c2 : 2 ≤ n := by omega
      have c3 : 3 ≤ n := by omega
      have c4 : 4 ≤ n := by omega
      have e1 : n - 1 ≠ 0 := by omega
      have e2 : n - 2 ≠ 0 := by omega
      have e3 : n - 3 ≠ 0 := by omega
      have e4 : n - 4 ≠ 0 := by omega
      simp only [c1, c2, c3, c4, e1, e2, e3, e4, coeff_C, if_true, if_false, ite_self]
      rw [hq]; ring
  have hcf : ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (832 * (4 : ℚ) ^ n - 846 * (3 : ℚ) ^ n + 204 * (2 : ℚ) ^ n + 2) / 12 := by
    have hb_1 : (a 1 : ℚ) = cf 1 := by
      rw [a_1]; unfold cf
      push_cast
      norm_num
    have hb_2 : (a 2 : ℚ) = cf 2 := by
      rw [a_2]; unfold cf
      push_cast
      norm_num
    have hb_3 : (a 3 : ℚ) = cf 3 := by
      rw [a_3]; unfold cf
      push_cast
      norm_num
    have hb_4 : (a 4 : ℚ) = cf 4 := by
      rw [a_4]; unfold cf
      push_cast
      norm_num
    have cf_rec : ∀ m : ℕ, cf (m + 5) = 10 * cf (m + 4) - 35 * cf (m + 3) + 50 * cf (m + 2) - 24 * cf (m + 1) := by
      intro m
      unfold cf
      have hp_f_1 : (4 : ℚ) ^ (m + 2) = (4 : ℚ) ^ (m + 1) * (4 : ℚ) ^ 1 := by
        rw [show m + 2 = (m + 1) + 1 by omega, pow_add]
      have hp_f_2 : (4 : ℚ) ^ (m + 3) = (4 : ℚ) ^ (m + 1) * (4 : ℚ) ^ 2 := by
        rw [show m + 3 = (m + 1) + 2 by omega, pow_add]
      have hp_f_3 : (4 : ℚ) ^ (m + 4) = (4 : ℚ) ^ (m + 1) * (4 : ℚ) ^ 3 := by
        rw [show m + 4 = (m + 1) + 3 by omega, pow_add]
      have hp_f_4 : (4 : ℚ) ^ (m + 5) = (4 : ℚ) ^ (m + 1) * (4 : ℚ) ^ 4 := by
        rw [show m + 5 = (m + 1) + 4 by omega, pow_add]
      have hp_c_1 : (3 : ℚ) ^ (m + 2) = (3 : ℚ) ^ (m + 1) * (3 : ℚ) ^ 1 := by
        rw [show m + 2 = (m + 1) + 1 by omega, pow_add]
      have hp_c_2 : (3 : ℚ) ^ (m + 3) = (3 : ℚ) ^ (m + 1) * (3 : ℚ) ^ 2 := by
        rw [show m + 3 = (m + 1) + 2 by omega, pow_add]
      have hp_c_3 : (3 : ℚ) ^ (m + 4) = (3 : ℚ) ^ (m + 1) * (3 : ℚ) ^ 3 := by
        rw [show m + 4 = (m + 1) + 3 by omega, pow_add]
      have hp_c_4 : (3 : ℚ) ^ (m + 5) = (3 : ℚ) ^ (m + 1) * (3 : ℚ) ^ 4 := by
        rw [show m + 5 = (m + 1) + 4 by omega, pow_add]
      have hp_t_1 : (2 : ℚ) ^ (m + 2) = (2 : ℚ) ^ (m + 1) * (2 : ℚ) ^ 1 := by
        rw [show m + 2 = (m + 1) + 1 by omega, pow_add]
      have hp_t_2 : (2 : ℚ) ^ (m + 3) = (2 : ℚ) ^ (m + 1) * (2 : ℚ) ^ 2 := by
        rw [show m + 3 = (m + 1) + 2 by omega, pow_add]
      have hp_t_3 : (2 : ℚ) ^ (m + 4) = (2 : ℚ) ^ (m + 1) * (2 : ℚ) ^ 3 := by
        rw [show m + 4 = (m + 1) + 3 by omega, pow_add]
      have hp_t_4 : (2 : ℚ) ^ (m + 5) = (2 : ℚ) ^ (m + 1) * (2 : ℚ) ^ 4 := by
        rw [show m + 5 = (m + 1) + 4 by omega, pow_add]
      simp only [hp_f_1, hp_f_2, hp_f_3, hp_f_4, hp_c_1, hp_c_2, hp_c_3, hp_c_4, hp_t_1, hp_t_2, hp_t_3, hp_t_4]
      generalize (4 : ℚ) ^ (m + 1) = Xf
      generalize (3 : ℚ) ^ (m + 1) = Xc
      generalize (2 : ℚ) ^ (m + 1) = Xt
      push_cast
      ring
    have hR : ∀ m : ℕ,
        (a (m + 1) : ℚ) = cf (m + 1) ∧
        (a (m + 2) : ℚ) = cf (m + 2) ∧
        (a (m + 3) : ℚ) = cf (m + 3) ∧
        (a (m + 4) : ℚ) = cf (m + 4) := by
      intro m
      induction m with
      | zero =>
        simp only [Nat.zero_add]
        exact ⟨hb_1, hb_2, hb_3, hb_4⟩
      | succ m ih =>
        obtain ⟨h0, h1, h2, h3⟩ := ih
        refine ⟨(by simpa only [show m + 1 + 1 = m + 2 by omega] using h1), (by simpa only [show m + 1 + 2 = m + 3 by omega] using h2), (by simpa only [show m + 1 + 3 = m + 4 by omega] using h3), ?_⟩
        rw [show m + 1 + 4 = m + 5 by omega]
        have hr : (a (m + 5) : ℚ) = 10 * a (m + 4) - 35 * a (m + 3) + 50 * a (m + 2) - 24 * a (m + 1) := by
          have h0' := hrec (m + 5) (by omega)
          simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega, show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega] at h0'
          exact_mod_cast h0'
        rw [hr, h3, h2, h1, h0, ← cf_rec m]
    intro n hn
    have h := (hR (n - 1)).1
    rw [show n - 1 + 1 = n by omega] at h
    exact h
  exact ⟨hrec, hgf, hcf⟩


lemma col2 : ∀ j j' : Fin 2, j'.val = j.val + 1 → j = 0 ∧ j' = 1 := by decide

lemma pair_of {m : ℕ} (i i' : Fin (m + 1)) (hi : i'.val = i.val + 1) :
    ∃ k : Fin m, k.castSucc = i ∧ k.succ = i' :=
  ⟨⟨i.val, by have := i'.isLt; omega⟩, Fin.ext rfl, Fin.ext (by simp [hi])⟩

lemma valid_iff (m : ℕ) (x : Fin (m + 1) → Fin 2 → Fin 4) :
    (∀ i i' : Fin (m + 1), i'.val = i.val + 1 → ∀ j j' : Fin 2, j'.val = j.val + 1 →
      ((x i j').val : ℤ) - (x i j).val ≤ ((x i' j').val : ℤ) - (x i' j).val ∧
        min (x i j).val (x i' j).val ≤ min (x i j').val (x i' j').val) ↔ isValid m x := by
  constructor
  · intro h k j
    fin_cases j
    exact h k.castSucc k.succ (by simp) 0 1 rfl
  · intro h i i' hi j j' hj
    obtain ⟨k, rfl, rfl⟩ := pair_of i i' hi
    obtain ⟨rfl, rfl⟩ := col2 j j' hj
    exact h k 0

lemma a_eq (m : ℕ) : OMA.S_oeis_a250846.a (m + 1) = a (m + 1) := by
  unfold OMA.S_oeis_a250846.a
  show _ = (Finset.univ.filter (isValid (m + 1))).card
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact valid_iff (m + 1) x

theorem main_proof : type_of% @OMA.S_oeis_a250846.main := by
  obtain ⟨_, hgf, _⟩ := main_proof_ours
  have hser : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (OMA.S_oeis_a250846.a n : ℚ)) =
      PowerSeries.mk (fun n => (a n : ℚ)) := by
    ext n
    cases n with
    | zero => simp [a]
    | succ m => simp [a_eq]
  rw [hser]; exact hgf

end OMA.P250846

theorem OMA.solution : type_of% @OMA.S_oeis_a250846.main := OMA.P250846.main_proof
