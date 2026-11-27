import OMAReductions.R_SumOfThreeCubes_isSumOfThreeCubes_iff_mod_9_R1

/- The pinned Formal Conjectures module proves this obstruction by reducing the three
integer cubes in ZMod 9. This connects its theorem to the step isolated by @ihateSAS. -/
theorem OMA.solution : OMA.R_SumOfThreeCubes_isSumOfThreeCubes_iff_mod_9_R1.H1 :=
  SumOfThreeCubes.mod_9_of_isSumOfThreeCubes
