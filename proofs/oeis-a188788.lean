import OMAStatements.S_oeis_a188788

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a188788.main) := fun h =>
  absurd (h.2 0) (by decide +kernel)
