import OMAStatements.S_mo_336842
import Mathlib

-- Problem: mo-336842, must an orthogonal matrix conjugating one irreducible 0-1 matrix into
-- another be a permutation matrix?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. Take both matrices equal to the 3 x 3 all-ones matrix J and let S be the rotation
-- (1/3) [[2, 2, -1], [-1, 2, 2], [2, -1, 2]] about the axis (1, 1, 1). Its rows and columns
-- sum to 1, so S J S^T = J, it is orthogonal, and it has the entry 2/3.

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_336842.main) := by
  intro h
  have hJ : ∀ i j : Fin 3, (!![1, 1, 1; 1, 1, 1; 1, 1, 1] : Matrix (Fin 3) (Fin 3) ℝ) i j = 0 ∨
      (!![1, 1, 1; 1, 1, 1; 1, 1, 1] : Matrix (Fin 3) (Fin 3) ℝ) i j = 1 := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  have hirr : OMA.S_mo_336842.IsIrreducible
      (!![1, 1, 1; 1, 1, 1; 1, 1, 1] : Matrix (Fin 3) (Fin 3) ℝ) := by
    intro i j
    refine ⟨1, one_pos, ?_⟩
    rw [pow_one]
    fin_cases i <;> fin_cases j <;> simp
  have horth : (!![2/3, 2/3, -1/3; -1/3, 2/3, 2/3; 2/3, -1/3, 2/3] : Matrix (Fin 3) (Fin 3) ℝ)
      * (!![2/3, 2/3, -1/3; -1/3, 2/3, 2/3; 2/3, -1/3, 2/3] : Matrix (Fin 3) (Fin 3) ℝ).transpose
      = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;> norm_num
  have hconj : (!![1, 1, 1; 1, 1, 1; 1, 1, 1] : Matrix (Fin 3) (Fin 3) ℝ)
      = (!![2/3, 2/3, -1/3; -1/3, 2/3, 2/3; 2/3, -1/3, 2/3] : Matrix (Fin 3) (Fin 3) ℝ)
        * (!![1, 1, 1; 1, 1, 1; 1, 1, 1] : Matrix (Fin 3) (Fin 3) ℝ)
        * (!![2/3, 2/3, -1/3; -1/3, 2/3, 2/3; 2/3, -1/3, 2/3] :
            Matrix (Fin 3) (Fin 3) ℝ).transpose := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num
  obtain ⟨σ, hσ⟩ := h 3 _ _ _ hJ hJ hirr hirr horth hconj
  have h00 := hσ 0 0
  split_ifs at h00 <;> norm_num at h00
