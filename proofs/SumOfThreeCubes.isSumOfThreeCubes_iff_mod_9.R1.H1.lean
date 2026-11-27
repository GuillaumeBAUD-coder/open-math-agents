import OMAReductions.R_SumOfThreeCubes_isSumOfThreeCubes_iff_mod_9_R1

-- The forward implication is already proved in the pinned SumOfThreeCubes module.
theorem OMA.solution : OMA.R_SumOfThreeCubes_isSumOfThreeCubes_iff_mod_9_R1.H1 := by
  exact SumOfThreeCubes.mod_9_of_isSumOfThreeCubes
