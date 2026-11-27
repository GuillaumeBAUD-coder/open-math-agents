import OMAReductions.R_SumOfThreeCubes_isSumOfThreeCubes_iff_mod_9_R1

-- Step SumOfThreeCubes.isSumOfThreeCubes_iff_mod_9.R1.H1: hypothesis H1 of reduction SumOfThreeCubes.isSumOfThreeCubes_iff_mod_9.R1
-- Credit: @anmolspace
-- Proof: cubes are 0, 1 or 8 mod 9, so a sum of three cubes is never 4 or 5 mod 9; this is the
-- already-proved upstream lemma SumOfThreeCubes.mod_9_of_isSumOfThreeCubes.

theorem OMA.solution : OMA.R_SumOfThreeCubes_isSumOfThreeCubes_iff_mod_9_R1.H1 :=
  fun n hn => SumOfThreeCubes.mod_9_of_isSumOfThreeCubes n hn
