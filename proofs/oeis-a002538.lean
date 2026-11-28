import OMAStatements.S_oeis_a002538

theorem OMA.solution : type_of% @OMA.S_oeis_a002538.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  simp only [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega, OMA.S_oeis_a002538.a, Nat.factorial_succ]
  push_cast
  ring
