import OMAStatements.S_oeis_a037250

theorem OMA.solution : type_of% @OMA.S_oeis_a037250.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  simp only [OMA.S_oeis_a037250.a, show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega, show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega, show m + 6 - 5 = m + 1 by omega, show m + 6 - 6 = m + 0 by omega]
  push_cast
  ring
