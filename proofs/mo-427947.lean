import OMAStatements.S_mo_427947
import Mathlib
open OMA.S_mo_427947

open Matrix Complex

/-- The matrix `A = [[1, -2], [1, -1]]`, with eigenvalues `± i`. -/
def A0 : Matrix (Fin 2) (Fin 2) ℂ := !![1, -2; 1, -1]

/-- The indefinite Hermitian matrix `H = [[1, -1], [-1, 0]]`. -/
def H0 : Matrix (Fin 2) (Fin 2) ℂ := !![1, -1; -1, 0]

/-- The inverse of `H`. -/
def H0inv : Matrix (Fin 2) (Fin 2) ℂ := !![0, -1; -1, -1]

/-- An eigenvector of `A` for the eigenvalue `i`. -/
def v0 : Fin 2 → ℂ := ![1 + I, 1]

lemma A0_conj : A0ᴴ = !![1, 1; -2, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A0, Matrix.conjTranspose_apply]

lemma H0_herm : H0.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H0, Matrix.conjTranspose_apply]

lemma H0_det : H0.det = -1 := by
  simp [H0, Matrix.det_fin_two]

lemma H0_inv : H0⁻¹ = H0inv := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H0, H0inv, Matrix.mul_apply, Fin.sum_univ_two]

lemma A0_det : A0.det = 1 := by
  simp [A0, Matrix.det_fin_two]
  ring

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_427947.main) := by
  intro h
  have hsa : A0 = H0⁻¹ * A0ᴴ * H0 := by
    rw [H0_inv, A0_conj]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A0, H0, H0inv, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hnu : A0ᴴ * H0 * A0 ≠ H0 := by
    rw [A0_conj]
    intro heq
    have := congrFun (congrFun heq 0) 0
    simp [A0, H0, Matrix.mul_apply, Fin.sum_univ_two] at this
    norm_num at this
  have hv : v0 ≠ 0 := by
    intro hv
    have := congrFun hv 1
    simp [v0] at this
  have hev : A0 *ᵥ v0 = I • v0 := by
    ext i
    fin_cases i <;> simp [A0, v0, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring_nf <;>
      simp [Complex.ext_iff] <;> norm_num
  have key := h 2 A0 H0 H0_herm (by rw [H0_det]; exact isUnit_one.neg) hsa
    (by rw [A0_det]; exact isUnit_one) hnu I v0 (by simp) hv hev
  rw [A0_conj] at key
  have := congrFun key 0
  simp [v0, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.ext_iff] at this
  try norm_num at this
