import OMAStatements.S_mo_336842

-- Problem: mo-336842, must an orthogonal matrix conjugating one irreducible 0-1 matrix into
-- another be a permutation matrix?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. Take both matrices equal to the 3 x 3 all-ones matrix J and let S be the rotation
-- (1/3) [[2, 2, -1], [-1, 2, 2], [2, -1, 2]] about the axis (1, 1, 1). Its rows and columns
-- sum to 1, so S J S^T = J, it is orthogonal, and it has the entry 2/3.

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_336842.main) := by
  intro h
  let J : Matrix (Fin 3) (Fin 3) ℝ := fun _ _ => 1
  let S : Matrix (Fin 3) (Fin 3) ℝ :=
    !![2/3, 2/3, -1/3; -1/3, 2/3, 2/3; 2/3, -1/3, 2/3]
  have hJ : ∀ i j, J i j = 0 ∨ J i j = 1 := fun _ _ => Or.inr rfl
  have hirr : OMA.S_mo_336842.IsIrreducible J := by
    intro i j
    exact ⟨1, one_pos, by rw [pow_one]; exact zero_lt_one⟩
  have horth : S * S.transpose = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [S, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num
  have hconj : J = S * J * S.transpose := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_three]
    all_goals norm_num [J, S, Matrix.cons_val_two]
  obtain ⟨σ, hσ⟩ := h 3 J J S hJ hJ hirr hirr horth hconj
  have h00 := hσ 0 0
  split_ifs at h00 <;> norm_num [S] at h00
