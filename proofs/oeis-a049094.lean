import OMAStatements.S_oeis_a049094

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a049094.main) := fun h =>
  absurd ((h 364 (by decide)).mpr (by decide) 1093 (by decide)) (by norm_num)
