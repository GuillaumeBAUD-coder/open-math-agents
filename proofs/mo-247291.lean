import OMAStatements.S_mo_247291
import Mathlib

/-!
MathOverflow 247291: `U = [[0, 1], [i, 0]]` is unitary and `Ū U = diag(i, -i)`, a diagonal
unitary matrix whose square is `-I ≠ I`.
-/

open Matrix OMA.S_mo_247291

namespace OMA.P247291

/-- `U = [[0, 1], [i, 0]]`. -/
def U : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; Complex.I, 0]

/-- `D = diag(i, -i)`. -/
def d : Fin 2 → ℂ := ![Complex.I, -Complex.I]

lemma U_unitary : U ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [U, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]

lemma d_norm (i : Fin 2) : ‖d i‖ = 1 := by
  fin_cases i <;> simp [d]

lemma conj_mul : U.map star * U = diagonal d := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [U, d, Matrix.mul_apply, Fin.sum_univ_two, diagonal]

lemma sq_ne : diagonal d ^ 2 ≠ 1 := by
  intro h
  rw [sq, diagonal_mul_diagonal] at h
  have := congrFun (congrFun h 0) 0
  simp [d] at this
  norm_num at this

end OMA.P247291

open OMA.P247291 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_247291.main) := by
  intro h
  exact sq_ne (h 2 U U_unitary d d_norm conj_mul)
