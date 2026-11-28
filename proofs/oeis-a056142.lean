import OMAStatements.S_oeis_a056142

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a056142.main) := by
  intro h
  have := h 101
  rw [show OMA.S_oeis_a056142.decimalWord 101 = [1, 0, 1] by
    norm_num [OMA.S_oeis_a056142.decimalWord]] at this
  exact absurd (this (by decide) (by decide) 1 (by decide) 0 (by decide)) (by decide)
