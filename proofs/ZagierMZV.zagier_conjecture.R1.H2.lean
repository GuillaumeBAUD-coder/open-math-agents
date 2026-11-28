import OMAReductions.R_ZagierMZV_zagier_conjecture_R1

-- Step ZagierMZV.zagier_conjecture.R1.H2: hypothesis H2 of reduction ZagierMZV.zagier_conjecture.R1
-- Credit: @Raimo33

/-! Upstream `dim_mzv_weight_one`, and `zagierDim 1 = 0`. -/

theorem OMA.solution : OMA.R_ZagierMZV_zagier_conjecture_R1.H2 := by
  show Module.finrank ℚ (ZagierMZV.mzvSpanOfWeight _) = ZagierMZV.zagierDim _
  rw [ZagierMZV.dim_mzv_weight_one]; rfl
