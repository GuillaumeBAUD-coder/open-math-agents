import OMAStatements.S_oeis_a177265

theorem OMA.solution : type_of% @OMA.S_oeis_a177265.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  simp [OMA.S_oeis_a177265.a, numDerangements_add_two]
  ring
