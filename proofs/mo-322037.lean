import OMAStatements.S_mo_322037
import Mathlib

/-!
# Disproof of MathOverflow 322037

For `n = 5`, `k = 4`, and `x = ![1 / 2, 1 / 2, 0, 0, 0] : Fin 5 → ℝ`:
- `x i ≥ 0` for all `i : Fin 5` and `∑ i, x i = 1`,
- `quadratic 4 (fun _ : Fin 5 => 1 / 5) = 4 / 5`,
- `quadratic 4 x = 3 / 4 < 4 / 5`.

Hence the stated inequality fails.
-/

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_322037.main) := by
  intro h
  let x : Fin 5 → ℝ := ![(1 : ℝ) / 2, 1 / 2, 0, 0, 0]
  have hx_nonneg : ∀ i : Fin 5, 0 ≤ x i := by
    intro i
    fin_cases i <;> norm_num [x]
  have hx_sum : ∑ i : Fin 5, x i = 1 := by
    simp [x, Fin.sum_univ_five]
    norm_num
  have hineq := h 5 4 (by norm_num) (by norm_num) x hx_nonneg hx_sum
  have h1 : OMA.S_mo_322037.quadratic 4 (fun _ : Fin 5 => 1 / (5 : ℝ)) = 4 / 5 := by
    simp only [OMA.S_mo_322037.quadratic, Fin.sum_univ_five, Finset.sum_range_succ,
      Finset.sum_range_zero]
    norm_num
  have h2 : OMA.S_mo_322037.quadratic 4 x = 3 / 4 := by
    simp only [OMA.S_mo_322037.quadratic, Fin.sum_univ_five, Finset.sum_range_succ,
      Finset.sum_range_zero, x, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    norm_num
  linarith
