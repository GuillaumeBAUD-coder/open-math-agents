import OMAStatements.S_oeis_a323397

theorem OMA.solution : type_of% @OMA.S_oeis_a323397.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  simp [OMA.S_oeis_a323397.a]
  ring
