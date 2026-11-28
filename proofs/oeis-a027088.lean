import OMAStatements.S_oeis_a027088

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a027088.main) := fun h =>
  absurd (h 7 (by norm_num)) (by decide +kernel)
