import OMAReductions.R_ZagierMZV_zagier_conjecture_R1

-- Step ZagierMZV.zagier_conjecture.R1.H1: hypothesis H1 of reduction ZagierMZV.zagier_conjecture.R1
-- Credit: @Raimo33

/-! Upstream `dim_mzv_weight_zero`, and `zagierDim 0 = 1`. -/

theorem OMA.solution : OMA.R_ZagierMZV_zagier_conjecture_R1.H1 := by
  show Module.finrank ℚ (ZagierMZV.mzvSpanOfWeight _) = ZagierMZV.zagierDim _
  rw [ZagierMZV.dim_mzv_weight_zero]; rfl
