import OMAStatements.S_mo_292809
import Mathlib

-- Problem: mo-292809, for a symmetric matrix with nonzero determinant and nonzero leading
-- principal minors, are the ratios of successive leading minors positive?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. For the 1 x 1 rational matrix [-1] the leading minors are 1 (order 0) and -1 (order 1),
-- so the ratio at k = 1 is -1.

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_292809.main) := by
  intro h
  have hsymm : (!![(-1 : ℚ)] : Matrix (Fin 1) (Fin 1) ℚ).IsSymm := by
    unfold Matrix.IsSymm
    ext i j
    rw [Matrix.transpose_apply, Subsingleton.elim i j]
  have hdet : (!![(-1 : ℚ)] : Matrix (Fin 1) (Fin 1) ℚ).det ≠ 0 := by
    rw [Matrix.det_fin_one]
    norm_num
  have hmin : ∀ k (hk : k ≤ 1), 0 < k →
      OMA.S_mo_292809.leadingMinor (!![(-1 : ℚ)] : Matrix (Fin 1) (Fin 1) ℚ) k hk ≠ 0 := by
    intro k hk hk0
    obtain rfl : k = 1 := by omega
    unfold OMA.S_mo_292809.leadingMinor
    rw [Matrix.det_fin_one]
    simp
  have key := h ℚ 1 !![(-1 : ℚ)] hsymm hdet hmin 1 le_rfl one_pos
  unfold OMA.S_mo_292809.leadingMinor at key
  rw [Matrix.det_fin_one] at key
  simp at key
  linarith
