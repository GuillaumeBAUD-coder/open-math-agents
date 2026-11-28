import OMAStatements.S_mo_427947
import Mathlib

-- Problem mo-427947: the statement claims that if H is an invertible Hermitian matrix, A is invertible with
-- A = H^-1 A^* H and A^* H A != H, then every eigenvector v of A for an eigenvalue mu of modulus 1 satisfies
-- A^* v = conj(mu) v.
-- Upstream: statements/mo-427947.lean (declaration OMA.S_mo_427947.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Refutation: take n = 2, H = (0 1; 1 0) and A = (1 1; 0 1). H is Hermitian with H H = 1, A has determinant 1,
-- and H A^* H = A. A^* H A = (0 1; 1 2) is not H. The vector v = (1, 0) satisfies A v = v, so mu = 1, but
-- A^* v = (1, 1), which is not v.

open Matrix

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_427947.main) := by
  intro h
  have hHH : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, 1; 1, 0] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hinv : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ = !![0, 1; 1, 0] :=
    Matrix.inv_eq_right_inv hHH
  have hHerm : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ).IsHermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  have hHdet : IsUnit (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ).det := by
    rw [Matrix.det_fin_two_of, isUnit_iff_ne_zero]
    norm_num
  have hAdet : IsUnit (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ).det := by
    rw [Matrix.det_fin_two_of, isUnit_iff_ne_zero]
    norm_num
  have hAH : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = !![1, 0; 1, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  have hself : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) =
      (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ * (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ *
        !![0, 1; 1, 0] := by
    rw [hinv, hAH]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hne : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * !![0, 1; 1, 0] * !![1, 1; 0, 1] ≠
      (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) := by
    intro heq
    rw [hAH] at heq
    have h11 := congrFun (congrFun heq 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h11
  have hv : (![1, 0] : Fin 2 → ℂ) ≠ 0 := by
    intro h0
    have h1 := congrFun h0 0
    simp at h1
  have heig : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ ![1, 0] = (1 : ℂ) • ![1, 0] := by
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have key := h 2 !![1, 1; 0, 1] !![0, 1; 1, 0] hHerm hHdet hself hAdet hne 1 ![1, 0] (by simp) hv heig
  rw [hAH] at key
  have h1 := congrFun key 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h1
