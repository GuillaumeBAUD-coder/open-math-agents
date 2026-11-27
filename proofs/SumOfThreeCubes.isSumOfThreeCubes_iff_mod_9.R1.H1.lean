import OMAReductions.R_SumOfThreeCubes_isSumOfThreeCubes_iff_mod_9_R1

-- Step SumOfThreeCubes.isSumOfThreeCubes_iff_mod_9.R1.H1: hypothesis H1 of reduction
-- SumOfThreeCubes.isSumOfThreeCubes_iff_mod_9.R1
-- Credit: @ihateSAS
-- H1 := ∀ n : ℤ, IsSumOfThreeCubes n → ¬(n ≡ 4 [ZMOD 9] ∨ n ≡ 5 [ZMOD 9])
--
-- A cube is `0` or `±1` modulo `9`, so a sum of three cubes is a sum of three elements of
-- `{0, 1, -1}` modulo `9`, which is never `4` or `5`.  The module already carries this as
-- `SumOfThreeCubes.mod_9_of_isSumOfThreeCubes`.

theorem OMA.solution : OMA.R_SumOfThreeCubes_isSumOfThreeCubes_iff_mod_9_R1.H1 :=
  fun n hn => SumOfThreeCubes.mod_9_of_isSumOfThreeCubes n hn
