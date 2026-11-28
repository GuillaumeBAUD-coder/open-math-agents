import OMAStatements.S_oeis_a211924

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a211924.main) := fun h =>
  absurd (h.2 0) (by decide +kernel)
