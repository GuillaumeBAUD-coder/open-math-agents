import OMAStatements.S_mo_406611
import Mathlib

-- Problem: mo-406611, must a nonnegative matrix A with zero diagonal, I - A invertible and
-- ((I - A)^{-1})^T o A = 0 (Hadamard product) be upper or lower triangular?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. Take A = [0 1 0; 0 0 0; 0 1 0]. Then A^2 = 0, so (I - A)^{-1} = I + A, and
-- (I + A)^T o A = A^T o A = 0 because A and A^T have disjoint supports. But A has a nonzero
-- entry above the diagonal (position (0, 1)) and one below it (position (2, 1)).

open Matrix

namespace MO406611

noncomputable def A : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, 0; 0, 0, 0; 0, 1, 0]

theorem sq : A * A = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A, Matrix.mul_apply, Fin.sum_univ_three]

theorem hmul : (1 - A) * (1 + A) = 1 := by
  have h : (1 - A) * (1 + A) = 1 - A * A := by noncomm_ring
  rw [h, sq, sub_zero]

theorem hinv : (1 - A)⁻¹ = 1 + A := Matrix.inv_eq_right_inv hmul

-- Apply the standard determinant consequence of the existing right inverse.
theorem hdet : (1 - A).det ≠ 0 := Matrix.det_ne_zero_of_right_inverse hmul

theorem hnn : ∀ i j, 0 ≤ A i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [A]

theorem hdiag : ∀ i, A i i = 0 := by
  intro i
  fin_cases i <;> simp [A]

theorem hhad : Matrix.hadamard ((1 - A)⁻¹)ᵀ A = 0 := by
  rw [hinv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A, Matrix.hadamard_apply, Matrix.one_apply]

end MO406611

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_406611.main) := by
  intro h
  rcases h 3 MO406611.A MO406611.hnn MO406611.hdiag MO406611.hdet MO406611.hhad with hU | hL
  · have h1 := hU (show id (1 : Fin 3) < id 2 by decide)
    simp [MO406611.A] at h1
  · have h1 := hL (show OrderDual.toDual (1 : Fin 3) < OrderDual.toDual 0 from
      OrderDual.toDual_lt_toDual.mpr (by decide))
    simp [MO406611.A] at h1
