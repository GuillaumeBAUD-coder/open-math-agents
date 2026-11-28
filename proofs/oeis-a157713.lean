import OMAStatements.S_oeis_a157713

theorem OMA.solution : type_of% @OMA.S_oeis_a157713.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp only [OMA.S_oeis_a157713.a]
  rw [show m + 2 - 1 = m + 1 by omega, show m + 1 - 1 = m by omega,
    show 2 * (m + 2) + 1 = 2 * m + 5 by ring, show 2 * (m + 2) - 2 = 2 * m + 2 by omega,
    show 2 * (m + 1) + 1 = 2 * m + 3 by ring, show 2 * (m + 1) - 2 = 2 * m by omega]
  have f1 : (2 * m + 5).factorial = (2 * m + 5) * ((2 * m + 4) * (2 * m + 3).factorial) := by
    rw [show 2 * m + 5 = (2 * m + 3 + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
  have f2 : (2 * m + 2).factorial = (2 * m + 2) * ((2 * m + 1) * (2 * m).factorial) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
  have f3 : (m + 1).factorial = (m + 1) * m.factorial := Nat.factorial_succ m
  have f4 : (m + 2).factorial = (m + 2) * ((m + 1) * m.factorial) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
  rw [f1, f2, f3, f4]
  have : ((2 * m).factorial : ℚ) ≠ 0 := by positivity
  have : ((2 * m + 3).factorial : ℚ) ≠ 0 := by positivity
  have : (m.factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring
