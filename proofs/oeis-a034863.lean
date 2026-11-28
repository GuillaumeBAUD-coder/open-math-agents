import OMAStatements.S_oeis_a034863

-- With a(n) = n! * p(n) / 24, dividing by (n-2)! turns the recurrence into a polynomial identity.
theorem OMA.solution : type_of% @OMA.S_oeis_a034863.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h1 : m + 2 - 1 = m + 1 := rfl
  have h2 : m + 2 - 2 = m := rfl
  rw [h1, h2]
  simp only [OMA.S_oeis_a034863.a]
  have f1 : ((m + 1).factorial : ℚ) = ((m : ℚ) + 1) * (m.factorial : ℚ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have f2 : ((m + 2).factorial : ℚ) = ((m : ℚ) + 2) * (((m : ℚ) + 1) * (m.factorial : ℚ)) := by
    rw [Nat.factorial_succ, Nat.cast_mul, f1]
    push_cast
    ring
  rw [f2, f1]
  push_cast
  ring
