import OMAStatements.S_oeis_a266251
import Mathlib

namespace A266251Aux
open OMA.S_oeis_a266251 PowerSeries

lemma rule9 (P Q R : Prop) [Decidable P] [Decidable Q] [Decidable R] :
    Nat.testBit 9 (4 * (decide P).toNat + 2 * (decide Q).toNat + (decide R).toNat) =
      decide ((¬P ∧ ¬Q ∧ ¬R) ∨ (¬P ∧ Q ∧ R)) := by
  by_cases hP : P <;> by_cases hQ : Q <;> by_cases hR : R <;> simp [hP, hQ, hR] <;> decide

lemma step_eq (n : ℕ) (x : ℤ) (P Q R : Prop) [Decidable P] [Decidable Q] [Decidable R]
    (hl : row 9 n (x - 1) = decide P) (hc : row 9 n x = decide Q)
    (hr : row 9 n (x + 1) = decide R) :
    row 9 (n + 1) x = decide ((¬P ∧ ¬Q ∧ ¬R) ∨ (¬P ∧ Q ∧ R)) := by
  have h : row 9 (n + 1) x = rule 9 (row 9 n (x - 1)) (row 9 n x) (row 9 n (x + 1)) := rfl
  rw [h, hl, hc, hr]
  unfold rule
  exact rule9 P Q R

lemma inv1 (x : ℤ) : row 9 1 x = decide (x < -1 ∨ 1 < x) :=
  (step_eq 0 x (x - 1 = 0) (x = 0) (x + 1 = 0) rfl rfl rfl).trans
    (decide_eq_decide.mpr (by omega))

lemma inv2 (x : ℤ) : row 9 2 x = decide (x = 0 ∨ x = 2) :=
  (step_eq 1 x _ _ _ (inv1 (x - 1)) (inv1 x) (inv1 (x + 1))).trans
    (decide_eq_decide.mpr (by omega))

lemma inv3 (x : ℤ) : row 9 3 x = decide (x < -1 ∨ 3 < x) :=
  (step_eq 2 x _ _ _ (inv2 (x - 1)) (inv2 x) (inv2 (x + 1))).trans
    (decide_eq_decide.mpr (by omega))

lemma inv4 (x : ℤ) : row 9 4 x = decide (x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 4) :=
  (step_eq 3 x _ _ _ (inv3 (x - 1)) (inv3 x) (inv3 (x + 1))).trans
    (decide_eq_decide.mpr (by omega))

lemma E_to_O (n : ℕ)
    (h : ∀ x : ℤ, row 9 n x = decide (x = (n : ℤ) - 4 ∨ x = (n : ℤ) - 3 ∨ x = (n : ℤ) - 2 ∨
      x = (n : ℤ))) :
    ∀ x : ℤ, row 9 (n + 1) x = decide (¬ (x = ((n + 1 : ℕ) : ℤ) - 6 ∨ x = ((n + 1 : ℕ) : ℤ) - 4 ∨
      x = ((n + 1 : ℕ) : ℤ) - 3 ∨ x = ((n + 1 : ℕ) : ℤ) - 2 ∨ x = ((n + 1 : ℕ) : ℤ) - 1 ∨
      x = ((n + 1 : ℕ) : ℤ))) := by
  intro x
  exact (step_eq n x _ _ _ (h (x - 1)) (h x) (h (x + 1))).trans
    (decide_eq_decide.mpr (by push_cast; omega))

lemma O_to_E (n : ℕ)
    (h : ∀ x : ℤ, row 9 n x = decide (¬ (x = (n : ℤ) - 6 ∨ x = (n : ℤ) - 4 ∨
      x = (n : ℤ) - 3 ∨ x = (n : ℤ) - 2 ∨ x = (n : ℤ) - 1 ∨ x = (n : ℤ)))) :
    ∀ x : ℤ, row 9 (n + 1) x = decide (x = ((n + 1 : ℕ) : ℤ) - 4 ∨ x = ((n + 1 : ℕ) : ℤ) - 3 ∨
      x = ((n + 1 : ℕ) : ℤ) - 2 ∨ x = ((n + 1 : ℕ) : ℤ)) := by
  intro x
  exact (step_eq n x _ _ _ (h (x - 1)) (h x) (h (x + 1))).trans
    (decide_eq_decide.mpr (by push_cast; omega))

lemma invE (j : ℕ) : ∀ x : ℤ, row 9 (2 * j + 4) x =
    decide (x = ((2 * j + 4 : ℕ) : ℤ) - 4 ∨ x = ((2 * j + 4 : ℕ) : ℤ) - 3 ∨
      x = ((2 * j + 4 : ℕ) : ℤ) - 2 ∨ x = ((2 * j + 4 : ℕ) : ℤ)) := by
  induction j with
  | zero =>
    intro x
    show row 9 4 x = _
    rw [inv4]
    exact decide_eq_decide.mpr (by push_cast; omega)
  | succ j ih =>
    rw [show 2 * (j + 1) + 4 = 2 * j + 4 + 1 + 1 by ring]
    exact O_to_E _ (E_to_O _ ih)

lemma invO (j : ℕ) : ∀ x : ℤ, row 9 (2 * j + 4 + 1) x =
    decide (¬ (x = ((2 * j + 4 + 1 : ℕ) : ℤ) - 6 ∨ x = ((2 * j + 4 + 1 : ℕ) : ℤ) - 4 ∨
      x = ((2 * j + 4 + 1 : ℕ) : ℤ) - 3 ∨ x = ((2 * j + 4 + 1 : ℕ) : ℤ) - 2 ∨
      x = ((2 * j + 4 + 1 : ℕ) : ℤ) - 1 ∨ x = ((2 * j + 4 + 1 : ℕ) : ℤ))) :=
  E_to_O _ (invE j)

lemma count_even (n : ℕ) (hn : 4 ≤ n)
    (h : ∀ x : ℤ, row 9 n x = decide (x = (n : ℤ) - 4 ∨ x = (n : ℤ) - 3 ∨ x = (n : ℤ) - 2 ∨
      x = (n : ℤ))) : a n + 3 = 2 * n := by
  unfold a
  have hf : (Finset.range (2 * n + 1)).filter (fun k : ℕ => row 9 n ((k : ℤ) - n) = false) =
      Finset.range (2 * n - 4) ∪ {2 * n - 1} := by
    ext k
    rw [Finset.mem_filter, Finset.mem_union, Finset.mem_range, Finset.mem_range,
      Finset.mem_singleton, h, decide_eq_false_iff_not]
    omega
  rw [hf, Finset.card_union_of_disjoint
    (Finset.disjoint_singleton_right.mpr (by rw [Finset.mem_range]; omega)),
    Finset.card_range, Finset.card_singleton]
  omega

lemma count_odd (n : ℕ) (hn : 5 ≤ n)
    (h : ∀ x : ℤ, row 9 n x = decide (¬ (x = (n : ℤ) - 6 ∨ x = (n : ℤ) - 4 ∨
      x = (n : ℤ) - 3 ∨ x = (n : ℤ) - 2 ∨ x = (n : ℤ) - 1 ∨ x = (n : ℤ)))) : a n = 6 := by
  unfold a
  have hf : (Finset.range (2 * n + 1)).filter (fun k : ℕ => row 9 n ((k : ℤ) - n) = false) =
      {2 * n - 6} ∪ Finset.Icc (2 * n - 4) (2 * n) := by
    ext k
    rw [Finset.mem_filter, Finset.mem_union, Finset.mem_range, Finset.mem_Icc,
      Finset.mem_singleton, h, decide_eq_false_iff_not]
    omega
  rw [hf, Finset.card_union_of_disjoint
    (Finset.disjoint_singleton_left.mpr (by rw [Finset.mem_Icc]; omega)),
    Nat.card_Icc, Finset.card_singleton]
  omega

lemma aE (n : ℕ) (hn : 4 ≤ n) (he : n % 2 = 0) : a n + 3 = 2 * n := by
  obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j + 4 := ⟨(n - 4) / 2, by omega⟩
  exact count_even _ hn (invE j)

lemma aO (n : ℕ) (hn : 5 ≤ n) (ho : n % 2 = 1) : a n = 6 := by
  obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j + 4 + 1 := ⟨(n - 5) / 2, by omega⟩
  exact count_odd _ hn (invO j)

lemma a_0 : a 0 = 0 := by decide
lemma a_1 : a 1 = 3 := by decide
lemma a_2 : a 2 = 3 := by decide
lemma a_3 : a 3 = 5 := by decide
lemma a_4 : a 4 = 5 := by have := aE 4 (by norm_num) (by norm_num); omega
lemma a_5 : a 5 = 6 := aO 5 (by norm_num) (by norm_num)
lemma a_6 : a 6 = 9 := by have := aE 6 (by norm_num) (by norm_num); omega
lemma a_7 : a 7 = 6 := aO 7 (by norm_num) (by norm_num)

lemma part1 (n : ℕ) (hn : 3 < n) :
    (a n : ℤ) = (2 * (-1) ^ n * n + 2 * n - 9 * (-1) ^ n + 3) / 2 := by
  rcases Nat.even_or_odd n with he | ho
  · have hs : (-1 : ℤ) ^ n = 1 := he.neg_one_pow
    have h := aE n (by omega) (Nat.even_iff.mp he)
    rw [hs]
    omega
  · have hs : (-1 : ℤ) ^ n = -1 := ho.neg_one_pow
    have ho' := Nat.odd_iff.mp ho
    have h := aO n (by omega) ho'
    rw [hs]
    omega

lemma recN (n : ℕ) (hn : 7 < n) : (a n : ℤ) = 2 * a (n - 2) - a (n - 4) := by
  rcases Nat.even_or_odd n with he | ho
  · have he' := Nat.even_iff.mp he
    have h0 := aE n (by omega) he'
    have h2 := aE (n - 2) (by omega) (by omega)
    have h4 := aE (n - 4) (by omega) (by omega)
    omega
  · have ho' := Nat.odd_iff.mp ho
    have h0 := aO n (by omega) ho'
    have h2 := aO (n - 2) (by omega) (by omega)
    have h4 := aO (n - 4) (by omega) (by omega)
    omega

lemma hD : ((1 - X) ^ 2 * (1 + X) ^ 2 : PowerSeries ℤ) = 1 - C 2 * X ^ 2 + X ^ 4 := by
  simp only [map_ofNat]
  ring

lemma dcoeff (k : ℕ) : coeff k ((1 - X) ^ 2 * (1 + X) ^ 2 : PowerSeries ℤ) =
    (if k = 0 then 1 else 0) - 2 * (if k = 2 then 1 else 0) + (if k = 4 then 1 else 0) := by
  rw [hD]
  simp only [map_add, map_sub, coeff_one, coeff_C_mul, coeff_X_pow]

lemma hN : (X * (3 + 3 * X - X ^ 2 - X ^ 3 - X ^ 4 + 2 * X ^ 5 - X ^ 6) : PowerSeries ℤ) =
    C 3 * X + C 3 * X ^ 2 - X ^ 3 - X ^ 4 - X ^ 5 + C 2 * X ^ 6 - X ^ 7 := by
  simp only [map_ofNat]
  ring

lemma ncoeff (k : ℕ) :
    coeff k (X * (3 + 3 * X - X ^ 2 - X ^ 3 - X ^ 4 + 2 * X ^ 5 - X ^ 6) : PowerSeries ℤ) =
    3 * (if k = 1 then 1 else 0) + 3 * (if k = 2 then 1 else 0) - (if k = 3 then 1 else 0) -
      (if k = 4 then 1 else 0) - (if k = 5 then 1 else 0) + 2 * (if k = 6 then 1 else 0) -
      (if k = 7 then 1 else 0) := by
  rw [hN]
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow, coeff_X]

lemma sum_d (f : ℕ → ℤ) (n : ℕ) (hn : 4 ≤ n) :
    ∑ k ∈ Finset.range (n + 1), coeff k ((1 - X) ^ 2 * (1 + X) ^ 2 : PowerSeries ℤ) * f k =
      f 0 - 2 * f 2 + f 4 := by
  rw [← Finset.sum_subset (Finset.range_mono (show 5 ≤ n + 1 by omega))]
  · norm_num [Finset.sum_range_succ, dcoeff]
    ring
  · intro k _ hk
    have hk' : 5 ≤ k := by
      rw [Finset.mem_range] at hk; omega
    rw [dcoeff]
    simp [show k ≠ 0 by omega, show k ≠ 2 by omega, show k ≠ 4 by omega]

lemma gf : PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) ^ 2 * (1 + X) ^ 2) =
    X * (3 + 3 * X - X ^ 2 - X ^ 3 - X ^ 4 + 2 * X ^ 5 - X ^ 6) := by
  ext n
  rw [mul_comm, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i ((1 - X) ^ 2 * (1 + X) ^ 2 : PowerSeries ℤ) *
      coeff j (PowerSeries.mk (fun n => (a n : ℤ))))]
  simp only [coeff_mk]
  by_cases hn : 8 ≤ n
  · rw [sum_d (fun k => (a (n - k) : ℤ)) n (by omega)]
    have hr := recN n (by omega)
    have hz : coeff n
        (X * (3 + 3 * X - X ^ 2 - X ^ 3 - X ^ 4 + 2 * X ^ 5 - X ^ 6) : PowerSeries ℤ) = 0 := by
      rw [ncoeff]
      simp [show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega,
        show n ≠ 5 by omega, show n ≠ 6 by omega, show n ≠ 7 by omega]
    rw [hz, Nat.sub_zero]
    linarith
  · have hn' : n ≤ 7 := by omega
    rw [ncoeff]
    interval_cases n <;>
      norm_num [Finset.sum_range_succ, dcoeff, a_0, a_1, a_2, a_3, a_4, a_5, a_6, a_7]
end A266251Aux

open A266251Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a266251.main :=
  ⟨part1, recN, gf⟩
