import OMAStatements.S_oeis_a002538
theorem OMA.solution : type_of% @OMA.S_oeis_a002538.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 3 := ⟨n - 3, by omega⟩
  simp only [Nat.reduceSubDiff, OMA.S_oeis_a002538.a, Nat.factorial_succ,
    Nat.cast_add, Nat.cast_one, Nat.cast_mul]
  ring
