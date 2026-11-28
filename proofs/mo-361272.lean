import OMAStatements.S_mo_361272
import Mathlib

-- Problem: Characterization of "PSD-Squared" Matrices
-- Upstream: formal-conjectures statements/mo-361272.lean:0 (declaration OMA.S_mo_361272.main)
-- Credit: @amtamaddon (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open scoped ComplexOrder Matrix
open OMA.S_mo_361272

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_361272.main) := by
  intro h
  have h3 := h 3
  let A : Matrix (Fin 3) (Fin 3) ℂ := !![1,1,0;1,2,1;0,1,1]
  let B : Matrix (Fin 2) (Fin 3) ℂ := !![1,1,0;0,1,1]
  have hAB : A = Bᴴ * B := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A, B, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  have hA : A ∈ doublyNonnegative 3 := by
    refine ⟨?_, ?_⟩
    · rw [hAB]; exact Matrix.posSemidef_conjTranspose_mul_self B
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [A]
  rw [← h3] at hA
  obtain ⟨X, hX, hAX⟩ := hA
  have e : ∀ i j, A i j = X i j * star (X i j) := by
    intro i j; rw [hAX]; simp [Matrix.hadamard_apply]
  have herm : ∀ i j, X j i = star (X i j) := by
    intro i j
    exact (hX.isHermitian.apply j i).symm
  have d0 := Complex.nonneg_iff.1 (hX.diag_nonneg (i := 0))
  have d1 := Complex.nonneg_iff.1 (hX.diag_nonneg (i := 1))
  have d2 := Complex.nonneg_iff.1 (hX.diag_nonneg (i := 2))
  have e00 : (1:ℂ) = X 0 0 * star (X 0 0) := by simpa [A] using e 0 0
  have e11 : (2:ℂ) = X 1 1 * star (X 1 1) := by simpa [A] using e 1 1
  have e22 : (1:ℂ) = X 2 2 * star (X 2 2) := by simpa [A] using e 2 2
  have e01 : (1:ℂ) = X 0 1 * star (X 0 1) := by simpa [A] using e 0 1
  have e12 : (1:ℂ) = X 1 2 * star (X 1 2) := by simpa [A] using e 1 2
  have e02 : X 0 2 = 0 := by simpa [A] using e 0 2
  have hd : X.det = X 0 0 * X 1 1 * X 2 2 - X 0 0 - X 2 2 := by
    rw [Matrix.det_fin_three, herm 0 1, herm 1 2, herm 0 2, e02]
    simp only [star_zero]
    linear_combination X 0 0 * e12 + X 2 2 * e01
  have hdet := Complex.nonneg_iff.1 hX.det_nonneg
  rw [hd] at hdet
  have r00 := congrArg Complex.re e00
  have r11 := congrArg Complex.re e11
  have r22 := congrArg Complex.re e22
  have hdr := hdet.1
  simp [d0.2.symm, d1.2.symm, d2.2.symm] at r00 r11 r22 hdr
  have ha : (X 0 0).re = 1 := by nlinarith [d0.1]
  have hc : (X 2 2).re = 1 := by nlinarith [d2.1]
  rw [ha, hc] at hdr
  nlinarith [d1.1]
