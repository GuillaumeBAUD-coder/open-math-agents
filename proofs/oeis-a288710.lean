import OMAStatements.S_oeis_a288710

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a288710.main) := fun h =>
  absurd (h 3) (by decide +kernel)
