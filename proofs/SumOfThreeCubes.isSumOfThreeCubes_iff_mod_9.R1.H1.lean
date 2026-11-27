import OMAReductions.R_SumOfThreeCubes_isSumOfThreeCubes_iff_mod_9_R1

-- Step SumOfThreeCubes.isSumOfThreeCubes_iff_mod_9.R1.H1: hypothesis H1 of reduction SumOfThreeCubes.isSumOfThreeCubes_iff_mod_9.R1
-- Credit: @Ciphore
-- H1 := ∀ n : ℤ, SumOfThreeCubes.IsSumOfThreeCubes n →     ¬(n ≡ 4 [ZMOD 9] ∨ n ≡ 5 [ZMOD 9])  /-- The open direction: every integer that is not `4` or `5` mod `9` is a sum of three cubes. -/

theorem OMA.solution : OMA.R_SumOfThreeCubes_isSumOfThreeCubes_iff_mod_9_R1.H1 := by
  intro n hn
  exact SumOfThreeCubes.mod_9_of_isSumOfThreeCubes n hn

