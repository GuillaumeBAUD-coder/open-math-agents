import OMAStatements.S_oeis_a266795
import Mathlib

namespace A266795Aux
open OMA.S_oeis_a266795 PowerSeries

lemma rule61 (P Q R : Prop) [Decidable P] [Decidable Q] [Decidable R] :
    Nat.testBit 61 (4 * (decide P).toNat + 2 * (decide Q).toNat + (decide R).toNat) =
      decide ((¬P ∧ (¬R ∨ Q)) ∨ (P ∧ ¬Q)) := by
  by_cases hP : P <;> by_cases hQ : Q <;> by_cases hR : R <;> simp [hP, hQ, hR] <;> decide

lemma step_eq (n : ℕ) (x : ℤ) (P Q R : Prop) [Decidable P] [Decidable Q] [Decidable R]
    (hl : row 61 n (x - 1) = decide P) (hc : row 61 n x = decide Q)
    (hr : row 61 n (x + 1) = decide R) :
    row 61 (n + 1) x = decide ((¬P ∧ (¬R ∨ Q)) ∨ (P ∧ ¬Q)) := by
  have h : row 61 (n + 1) x = rule 61 (row 61 n (x - 1)) (row 61 n x) (row 61 n (x + 1)) := rfl
  rw [h, hl, hc, hr]
  unfold rule
  exact rule61 P Q R

lemma inv1 (x : ℤ) : row 61 1 x = decide (x ≠ -1) :=
  (step_eq 0 x (x - 1 = 0) (x = 0) (x + 1 = 0) rfl rfl rfl).trans
    (decide_eq_decide.mpr (by omega))

lemma inv2 (x : ℤ) : row 61 2 x = decide (x = -1 ∨ x = 0) :=
  (step_eq 1 x _ _ _ (inv1 (x - 1)) (inv1 x) (inv1 (x + 1))).trans
    (decide_eq_decide.mpr (by omega))

lemma inv3 (x : ℤ) : row 61 3 x = decide (x ≠ -2 ∧ x ≠ 0) :=
  (step_eq 2 x _ _ _ (inv2 (x - 1)) (inv2 x) (inv2 (x + 1))).trans
    (decide_eq_decide.mpr (by omega))

lemma inv4 (x : ℤ) : row 61 4 x = decide (-2 ≤ x ∧ x ≤ 1) :=
  (step_eq 3 x _ _ _ (inv3 (x - 1)) (inv3 x) (inv3 (x + 1))).trans
    (decide_eq_decide.mpr (by omega))

lemma inv5 (x : ℤ) : row 61 5 x = decide (¬ (x = -3 ∨ x = -1 ∨ x = 0 ∨ x = 1)) :=
  (step_eq 4 x _ _ _ (inv4 (x - 1)) (inv4 x) (inv4 (x + 1))).trans
    (decide_eq_decide.mpr (by omega))

lemma O_to_E (n i : ℕ)
    (h : ∀ x : ℤ, row 61 n x = decide (¬ (x = -(i : ℤ) - 3 ∨ x = -(i : ℤ) - 1 ∨ x = -(i : ℤ) ∨
      x = -(i : ℤ) + 1))) :
    ∀ x : ℤ, row 61 (n + 1) x = decide (x = -(i : ℤ) - 3 ∨ x = -(i : ℤ) - 2 ∨
      x = -(i : ℤ) - 1 ∨ x = -(i : ℤ) ∨ x = -(i : ℤ) + 2) := by
  intro x
  exact (step_eq n x _ _ _ (h (x - 1)) (h x) (h (x + 1))).trans
    (decide_eq_decide.mpr (by omega))

lemma E_to_O (n i : ℕ)
    (h : ∀ x : ℤ, row 61 n x = decide (x = -(i : ℤ) - 3 ∨ x = -(i : ℤ) - 2 ∨
      x = -(i : ℤ) - 1 ∨ x = -(i : ℤ) ∨ x = -(i : ℤ) + 2)) :
    ∀ x : ℤ, row 61 (n + 1) x = decide (¬ (x = -((i + 1 : ℕ) : ℤ) - 3 ∨
      x = -((i + 1 : ℕ) : ℤ) - 1 ∨ x = -((i + 1 : ℕ) : ℤ) ∨ x = -((i + 1 : ℕ) : ℤ) + 1)) := by
  intro x
  exact (step_eq n x _ _ _ (h (x - 1)) (h x) (h (x + 1))).trans
    (decide_eq_decide.mpr (by push_cast; omega))

lemma invO (i : ℕ) : ∀ x : ℤ, row 61 (2 * i + 5) x =
    decide (¬ (x = -(i : ℤ) - 3 ∨ x = -(i : ℤ) - 1 ∨ x = -(i : ℤ) ∨ x = -(i : ℤ) + 1)) := by
  induction i with
  | zero =>
    intro x
    show row 61 5 x = _
    rw [inv5]
    exact decide_eq_decide.mpr (by push_cast; omega)
  | succ i ih =>
    rw [show 2 * (i + 1) + 5 = 2 * i + 5 + 1 + 1 by ring]
    exact E_to_O _ i (O_to_E _ i ih)

lemma invE (i : ℕ) : ∀ x : ℤ, row 61 (2 * i + 5 + 1) x =
    decide (x = -(i : ℤ) - 3 ∨ x = -(i : ℤ) - 2 ∨ x = -(i : ℤ) - 1 ∨ x = -(i : ℤ) ∨
      x = -(i : ℤ) + 2) :=
  O_to_E _ i (invO i)

lemma offO (i k : ℕ) (hk : k = 2 * i + 5) : off k = 4 := by
  subst hk
  unfold off
  have hf : (Finset.range (2 * (2 * i + 5) + 1)).filter
      (fun k : ℕ => row 61 (2 * i + 5) ((k : ℤ) - ((2 * i + 5 : ℕ) : ℤ)) = false) =
      {i + 2} ∪ Finset.Icc (i + 4) (i + 6) := by
    ext k
    rw [Finset.mem_filter, Finset.mem_union, Finset.mem_range, Finset.mem_Icc,
      Finset.mem_singleton, invO i, decide_eq_false_iff_not]
    push_cast
    omega
  rw [hf, Finset.card_union_of_disjoint
    (Finset.disjoint_singleton_left.mpr (by rw [Finset.mem_Icc]; omega)),
    Nat.card_Icc, Finset.card_singleton]
  omega

lemma offE (i k : ℕ) (hk : k = 2 * i + 5 + 1) : off k = 4 * i + 8 := by
  subst hk
  unfold off
  have hf : (Finset.range (2 * (2 * i + 5 + 1) + 1)).filter
      (fun k : ℕ => row 61 (2 * i + 5 + 1) ((k : ℤ) - ((2 * i + 5 + 1 : ℕ) : ℤ)) = false) =
      (Finset.range (i + 3) ∪ {i + 7}) ∪ Finset.Icc (i + 9) (4 * i + 12) := by
    ext k
    rw [Finset.mem_filter, Finset.mem_union, Finset.mem_union, Finset.mem_range,
      Finset.mem_range, Finset.mem_Icc, Finset.mem_singleton, invE i, decide_eq_false_iff_not]
    push_cast
    omega
  have h1 : Disjoint (Finset.range (i + 3) ∪ {i + 7}) (Finset.Icc (i + 9) (4 * i + 12)) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    rw [Finset.mem_union, Finset.mem_range, Finset.mem_singleton] at hk1
    rw [Finset.mem_Icc] at hk2
    omega
  have h2 : Disjoint (Finset.range (i + 3)) ({i + 7} : Finset ℕ) :=
    Finset.disjoint_singleton_right.mpr (by rw [Finset.mem_range]; omega)
  rw [hf, Finset.card_union_of_disjoint h1, Finset.card_union_of_disjoint h2, Finset.card_range,
    Finset.card_singleton, Nat.card_Icc]
  omega

lemma off_0 : off 0 = 0 := by decide
lemma off_1 : off 1 = 1 := by decide
lemma off_2 : off 2 = 3 := by decide
lemma off_3 : off 3 = 2 := by decide
lemma off_4 : off 4 = 5 := by decide

lemma a_succ (n k : ℕ) (hk : k = n + 1) : a k = a n + off k := by
  subst hk
  unfold a
  rw [Finset.sum_range_succ]

lemma a_0 : a 0 = 0 := by
  unfold a
  rw [Finset.sum_range_one, off_0]
lemma a_1 : a 1 = 1 := by rw [a_succ 0 1 rfl, a_0, off_1]
lemma a_2 : a 2 = 4 := by rw [a_succ 1 2 rfl, a_1, off_2]
lemma a_3 : a 3 = 6 := by rw [a_succ 2 3 rfl, a_2, off_3]
lemma a_4 : a 4 = 11 := by rw [a_succ 3 4 rfl, a_3, off_4]

lemma closed (i : ℕ) : a (2 * i + 4) = 2 * i * i + 10 * i + 11 ∧
    a (2 * i + 5) = 2 * i * i + 10 * i + 15 := by
  induction i with
  | zero =>
    refine ⟨a_4, ?_⟩
    show a 5 = 15
    rw [a_succ 4 5 rfl, a_4, offO 0 5 rfl]
  | succ i ih =>
    obtain ⟨h1, h2⟩ := ih
    have e1 : a (2 * (i + 1) + 4) = 2 * (i + 1) * (i + 1) + 10 * (i + 1) + 11 := by
      rw [a_succ (2 * i + 5) (2 * (i + 1) + 4) (by ring), h2,
        offE i (2 * (i + 1) + 4) (by ring)]
      ring
    have e2 : a (2 * (i + 1) + 5) = 2 * (i + 1) * (i + 1) + 10 * (i + 1) + 15 := by
      rw [a_succ (2 * (i + 1) + 4) (2 * (i + 1) + 5) rfl, e1, offO (i + 1) (2 * (i + 1) + 5) rfl]
    exact ⟨e1, e2⟩

lemma cl1 (i k : ℕ) (hk : k = 2 * i + 4) : (a k : ℤ) = 2 * i * i + 10 * i + 11 := by
  subst hk
  rw [(closed i).1]
  push_cast
  ring

lemma cl2 (i k : ℕ) (hk : k = 2 * i + 5) : (a k : ℤ) = 2 * i * i + 10 * i + 15 := by
  subst hk
  rw [(closed i).2]
  push_cast
  ring

lemma part1 (n : ℕ) (hn : 3 < n) :
    4 * (a n : ℤ) = 2 * n * (n + (-1) ^ n + 1) - 7 * (-1) ^ n + 3 := by
  obtain ⟨i, hi⟩ : ∃ i, n = 2 * i + 4 ∨ n = 2 * i + 5 := ⟨(n - 4) / 2, by omega⟩
  rcases hi with rfl | rfl
  · have hs : (-1 : ℤ) ^ (2 * i + 4) = 1 := Even.neg_one_pow ⟨i + 2, by ring⟩
    rw [cl1 i (2 * i + 4) rfl, hs]
    push_cast
    ring
  · have hs : (-1 : ℤ) ^ (2 * i + 5) = -1 := Odd.neg_one_pow ⟨i + 2, by ring⟩
    rw [cl2 i (2 * i + 5) rfl, hs]
    push_cast
    ring

lemma recN (n : ℕ) (hn : 8 < n) :
    (a n : ℤ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) - a (n - 4) + a (n - 5) := by
  obtain ⟨i, hi⟩ : ∃ i, n = 2 * i + 9 ∨ n = 2 * i + 10 := ⟨(n - 9) / 2, by omega⟩
  rcases hi with rfl | rfl
  · rw [show 2 * i + 9 - 1 = 2 * i + 8 by omega, show 2 * i + 9 - 2 = 2 * i + 7 by omega,
      show 2 * i + 9 - 3 = 2 * i + 6 by omega, show 2 * i + 9 - 4 = 2 * i + 5 by omega,
      show 2 * i + 9 - 5 = 2 * i + 4 by omega]
    rw [cl2 (i + 2) (2 * i + 9) (by ring), cl1 (i + 2) (2 * i + 8) (by ring),
      cl2 (i + 1) (2 * i + 7) (by ring), cl1 (i + 1) (2 * i + 6) (by ring),
      cl2 i (2 * i + 5) rfl, cl1 i (2 * i + 4) rfl]
    push_cast
    ring
  · rw [show 2 * i + 10 - 1 = 2 * i + 9 by omega, show 2 * i + 10 - 2 = 2 * i + 8 by omega,
      show 2 * i + 10 - 3 = 2 * i + 7 by omega, show 2 * i + 10 - 4 = 2 * i + 6 by omega,
      show 2 * i + 10 - 5 = 2 * i + 5 by omega]
    rw [cl1 (i + 3) (2 * i + 10) (by ring), cl2 (i + 2) (2 * i + 9) (by ring),
      cl1 (i + 2) (2 * i + 8) (by ring), cl2 (i + 1) (2 * i + 7) (by ring),
      cl1 (i + 1) (2 * i + 6) (by ring), cl2 i (2 * i + 5) rfl]
    push_cast
    ring

lemma a_5 : a 5 = 15 := (closed 0).2
lemma a_6 : a 6 = 23 := (closed 1).1
lemma a_7 : a 7 = 27 := (closed 1).2
lemma a_8 : a 8 = 39 := (closed 2).1

lemma hD : ((1 - X) ^ 3 * (1 + X) ^ 2 : PowerSeries ℤ) =
    1 - X - C 2 * X ^ 2 + C 2 * X ^ 3 + X ^ 4 - X ^ 5 := by
  simp only [map_ofNat]
  ring

lemma dcoeff (k : ℕ) : coeff k ((1 - X) ^ 3 * (1 + X) ^ 2 : PowerSeries ℤ) =
    (if k = 0 then 1 else 0) - (if k = 1 then 1 else 0) - 2 * (if k = 2 then 1 else 0) +
      2 * (if k = 3 then 1 else 0) + (if k = 4 then 1 else 0) - (if k = 5 then 1 else 0) := by
  rw [hD]
  simp only [map_add, map_sub, coeff_one, coeff_C_mul, coeff_X_pow, coeff_X]

lemma hN : (X * (1 + 3 * X - X ^ 3 + X ^ 4 + X ^ 5 - 2 * X ^ 6 + X ^ 7) : PowerSeries ℤ) =
    X + C 3 * X ^ 2 - X ^ 4 + X ^ 5 + X ^ 6 - C 2 * X ^ 7 + X ^ 8 := by
  simp only [map_ofNat]
  ring

lemma ncoeff (k : ℕ) :
    coeff k (X * (1 + 3 * X - X ^ 3 + X ^ 4 + X ^ 5 - 2 * X ^ 6 + X ^ 7) : PowerSeries ℤ) =
    (if k = 1 then 1 else 0) + 3 * (if k = 2 then 1 else 0) - (if k = 4 then 1 else 0) +
      (if k = 5 then 1 else 0) + (if k = 6 then 1 else 0) - 2 * (if k = 7 then 1 else 0) +
      (if k = 8 then 1 else 0) := by
  rw [hN]
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow, coeff_X]

lemma sum_d (f : ℕ → ℤ) (n : ℕ) (hn : 5 ≤ n) :
    ∑ k ∈ Finset.range (n + 1), coeff k ((1 - X) ^ 3 * (1 + X) ^ 2 : PowerSeries ℤ) * f k =
      f 0 - f 1 - 2 * f 2 + 2 * f 3 + f 4 - f 5 := by
  rw [← Finset.sum_subset (Finset.range_mono (show 6 ≤ n + 1 by omega))]
  · norm_num [Finset.sum_range_succ, dcoeff]
    ring
  · intro k _ hk
    have hk' : 6 ≤ k := by
      rw [Finset.mem_range] at hk; omega
    rw [dcoeff]
    simp [show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega, show k ≠ 3 by omega,
      show k ≠ 4 by omega, show k ≠ 5 by omega]

lemma gf : PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) ^ 3 * (1 + X) ^ 2) =
    X * (1 + 3 * X - X ^ 3 + X ^ 4 + X ^ 5 - 2 * X ^ 6 + X ^ 7) := by
  ext n
  rw [mul_comm, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i ((1 - X) ^ 3 * (1 + X) ^ 2 : PowerSeries ℤ) *
      coeff j (PowerSeries.mk (fun n => (a n : ℤ)))), ncoeff]
  simp only [coeff_mk]
  by_cases hn : 9 ≤ n
  · rw [sum_d (fun k => (a (n - k) : ℤ)) n (by omega)]
    have hr := recN n (by omega)
    simp only [show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 4 by omega,
      show n ≠ 5 by omega, show n ≠ 6 by omega, show n ≠ 7 by omega, show n ≠ 8 by omega,
      if_false]
    rw [Nat.sub_zero]
    linarith
  · have hn' : n ≤ 8 := by omega
    interval_cases n <;>
      norm_num [Finset.sum_range_succ, dcoeff, a_0, a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8]
end A266795Aux

open A266795Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a266795.main :=
  ⟨part1, recN, gf⟩
