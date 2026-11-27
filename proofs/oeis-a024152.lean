import OMAStatements.S_oeis_a024152

theorem OMA.solution : type_of% @OMA.S_oeis_a024152.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 14 := ⟨n - 14, by omega⟩
  simp only [OMA.S_oeis_a024152.a, show m + 14 - 1 = m + 13 by omega, show m + 14 - 2 = m + 12 by omega, show m + 14 - 3 = m + 11 by omega, show m + 14 - 4 = m + 10 by omega, show m + 14 - 5 = m + 9 by omega, show m + 14 - 6 = m + 8 by omega, show m + 14 - 7 = m + 7 by omega, show m + 14 - 8 = m + 6 by omega, show m + 14 - 9 = m + 5 by omega, show m + 14 - 10 = m + 4 by omega, show m + 14 - 11 = m + 3 by omega, show m + 14 - 12 = m + 2 by omega, show m + 14 - 13 = m + 1 by omega, show m + 14 - 14 = m + 0 by omega]
  push_cast
  ring
