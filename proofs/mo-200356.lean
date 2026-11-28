import OMAStatements.S_mo_200356
import Mathlib

/-!
# MathOverflow 200356: the total variation of a product is not a function of that of the factors

Take `k = 2` and `n = 2`.  The pairs

* `P = (1/2, 1/2)`, `Q = (3/5, 2/5)` and
* `P' = (1/10, 9/10)`, `Q' = (1/5, 4/5)`

both have total variation distance `1/10`, but the two-fold products have distances `11/100` and
`17/100` respectively.  So no function `φ` of `(k, n, tv)` can give both values.
-/

namespace OMA.S_mo_200356

/-- Total variation on two points. -/
lemma tv_two (P Q : Fin 2 → ℝ) : tv P Q = (|P 0 - Q 0| + |P 1 - Q 1|) / 2 := by
  unfold tv
  rw [Fin.sum_univ_two]

/-- Total variation of the two-fold products on two points. -/
lemma tv_prod_two (P Q : Fin 2 → ℝ) : tv (prodDist 2 P) (prodDist 2 Q) =
    (|P 0 * P 0 - Q 0 * Q 0| + |P 0 * P 1 - Q 0 * Q 1| + |P 1 * P 0 - Q 1 * Q 0| +
      |P 1 * P 1 - Q 1 * Q 1|) / 2 := by
  unfold tv prodDist
  rw [← (finTwoArrowEquiv (Fin 2)).symm.sum_comp, Fintype.sum_prod_type]
  simp [Fin.sum_univ_two, Fin.prod_univ_two, finTwoArrowEquiv]
  ring

end OMA.S_mo_200356

open OMA.S_mo_200356 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_200356.main) := by
  rintro ⟨φ, h⟩
  have d1 : IsDist (![1 / 2, 1 / 2] : Fin 2 → ℝ) := ⟨fun i => by fin_cases i <;> norm_num, by
    rw [Fin.sum_univ_two]; norm_num⟩
  have d2 : IsDist (![3 / 5, 2 / 5] : Fin 2 → ℝ) := ⟨fun i => by fin_cases i <;> norm_num, by
    rw [Fin.sum_univ_two]; norm_num⟩
  have d3 : IsDist (![1 / 10, 9 / 10] : Fin 2 → ℝ) := ⟨fun i => by fin_cases i <;> norm_num, by
    rw [Fin.sum_univ_two]; norm_num⟩
  have d4 : IsDist (![1 / 5, 4 / 5] : Fin 2 → ℝ) := ⟨fun i => by fin_cases i <;> norm_num, by
    rw [Fin.sum_univ_two]; norm_num⟩
  have h1 := h 2 2 _ _ d1 d2
  have h2 := h 2 2 _ _ d3 d4
  rw [tv_prod_two, tv_two] at h1 h2
  -- evaluate the absolute values
  have a1 : |(1 / 2 : ℝ) - 3 / 5| = 1 / 10 := by rw [abs_of_nonpos (by norm_num)]; norm_num
  have a2 : |(1 / 2 : ℝ) - 2 / 5| = 1 / 10 := by rw [abs_of_nonneg (by norm_num)]; norm_num
  have a3 : |(1 / 10 : ℝ) - 1 / 5| = 1 / 10 := by rw [abs_of_nonpos (by norm_num)]; norm_num
  have a4 : |(9 / 10 : ℝ) - 4 / 5| = 1 / 10 := by rw [abs_of_nonneg (by norm_num)]; norm_num
  have b1 : |(1 / 2 : ℝ) * (1 / 2) - 3 / 5 * (3 / 5)| = 11 / 100 := by
    rw [abs_of_nonpos (by norm_num)]; norm_num
  have b2 : |(1 / 2 : ℝ) * (1 / 2) - 3 / 5 * (2 / 5)| = 1 / 100 := by
    rw [abs_of_nonneg (by norm_num)]; norm_num
  have b3 : |(1 / 2 : ℝ) * (1 / 2) - 2 / 5 * (3 / 5)| = 1 / 100 := by
    rw [abs_of_nonneg (by norm_num)]; norm_num
  have b4 : |(1 / 2 : ℝ) * (1 / 2) - 2 / 5 * (2 / 5)| = 9 / 100 := by
    rw [abs_of_nonneg (by norm_num)]; norm_num
  have c1 : |(1 / 10 : ℝ) * (1 / 10) - 1 / 5 * (1 / 5)| = 3 / 100 := by
    rw [abs_of_nonpos (by norm_num)]; norm_num
  have c2 : |(1 / 10 : ℝ) * (9 / 10) - 1 / 5 * (4 / 5)| = 7 / 100 := by
    rw [abs_of_nonpos (by norm_num)]; norm_num
  have c3 : |(9 / 10 : ℝ) * (1 / 10) - 4 / 5 * (1 / 5)| = 7 / 100 := by
    rw [abs_of_nonpos (by norm_num)]; norm_num
  have c4 : |(9 / 10 : ℝ) * (9 / 10) - 4 / 5 * (4 / 5)| = 17 / 100 := by
    rw [abs_of_nonneg (by norm_num)]; norm_num
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2
  rw [a1, a2, b1, b2, b3, b4] at h1
  rw [a3, a4, c1, c2, c3, c4] at h2
  have e : ((1 : ℝ) / 10 + 1 / 10) / 2 = 1 / 10 := by norm_num
  rw [e] at h1 h2
  rw [← h2] at h1
  norm_num at h1
