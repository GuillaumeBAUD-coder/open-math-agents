import OMAStatements.S_oeis_a286772

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a286772.main) := by
  rintro ⟨_, h1, h2, _⟩
  have e1 := h1 3 (by decide)
  have e2 := h2 3 (by decide)
  omega
