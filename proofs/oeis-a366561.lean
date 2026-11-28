import OMAStatements.S_oeis_a366561

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a366561.main) := fun h =>
  absurd ((h 4 2 (by norm_num) (by norm_num)).mp (by decide +kernel)) (by norm_num)
