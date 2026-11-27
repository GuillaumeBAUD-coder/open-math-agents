import OMAStatements.S_oeis_a052204

theorem OMA.solution : type_of% @OMA.S_oeis_a052204.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  unfold OMA.S_oeis_a052204.a
  rw [Nat.cast_choose ℚ (by omega : m + 2 ≤ 4 * (m + 2)),
    Nat.cast_choose ℚ (by omega : m + 1 ≤ 4 * (m + 1)), Nat.cast_choose ℚ (by omega : m ≤ 4 * m)]
  rw [show 4 * (m + 2) - (m + 2) = 3 * m + 1 + 1 + 1 + 1 + 1 + 1 by omega,
    show 4 * (m + 1) - (m + 1) = 3 * m + 1 + 1 + 1 by omega,
    show 4 * m - m = 3 * m by omega,
    show 4 * (m + 2) = 4 * m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by ring,
    show 4 * (m + 1) = 4 * m + 1 + 1 + 1 + 1 by ring,
    show m + 2 = m + 1 + 1 by ring]
  simp only [Nat.factorial_succ]
  push_cast
  have h1 : ((4 * m).factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((3 * m).factorial : ℚ) ≠ 0 := by positivity
  have h3 : (m.factorial : ℚ) ≠ 0 := by positivity
  have h4 : (3 * (m : ℚ) + 1) ≠ 0 := by positivity
  have h5 : (3 * ((m : ℚ) + 1) + 1) ≠ 0 := by positivity
  have h6 : (3 * ((m : ℚ) + 1 + 1) + 1) ≠ 0 := by positivity
  field_simp
  ring
