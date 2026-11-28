import OMAReductions.R_oeis_a088112_R1

/-! The square seed is 4: `4^2 = 16` and its digit reversal is `61`, which is prime. -/

theorem OMA.solution : OMA.R_oeis_a088112_R1.H1 := by
  refine ⟨4, by norm_num, ?_⟩
  decide
