import OMAStatements.S_mo_454408
import Mathlib

-- Problem: mo-454408, is tr(A |A^T P|) <= tr(A A^T P) for P = U diag(sigma) U^T positive
-- semidefinite, where |.| is the entrywise absolute value?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. Take A = (1, 1)^T, U = [3/5 4/5; 4/5 -3/5] (orthogonal) and sigma = (0, 25), so that
-- P = [16 -12; -12 9] and A^T P = (4, -3). Then tr(A |A^T P|) = 4 + 3 = 7, while
-- tr(A A^T P) = 4 - 3 = 1.

namespace MO454408

noncomputable def A : Matrix (Fin 2) (Fin 1) ℝ := !![1; 1]

noncomputable def U : Matrix (Fin 2) (Fin 2) ℝ := !![3 / 5, 4 / 5; 4 / 5, -3 / 5]

noncomputable def σ : Fin 2 → ℝ := ![0, 25]

theorem hU : U.transpose * U = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [U, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

theorem hσ : ∀ i, 0 ≤ σ i := by
  intro i
  fin_cases i <;> norm_num [σ]

end MO454408

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_454408.main) := by
  intro h
  have key := h 2 1 (by norm_num) (by norm_num) MO454408.A MO454408.U MO454408.σ
    MO454408.hU MO454408.hσ
  norm_num [MO454408.A, MO454408.U, MO454408.σ, Matrix.trace, Matrix.mul_apply,
    Matrix.map_apply, Matrix.diagonal_apply, Fin.sum_univ_two, Fin.sum_univ_one,
    Matrix.transpose_apply, Matrix.vecMul, Matrix.mulVec, dotProduct] at key
