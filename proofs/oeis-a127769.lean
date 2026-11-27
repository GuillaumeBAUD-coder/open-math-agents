import OMAStatements.S_oeis_a127769

theorem OMA.solution : type_of% @OMA.S_oeis_a127769.main := by
  intro t
  dsimp only
  unfold OMA.S_oeis_a127769.term
  rw [show 4 * (t + 1) + 2 = 4 * t + 2 + 1 + 1 + 1 + 1 by ring,
    show 2 * (t + 1) + 3 = 2 * t + 3 + 1 + 1 by ring,
    show 2 * (t + 1) = 2 * t + 1 + 1 by ring]
  simp only [Nat.factorial_succ]
  push_cast
  have h1 : ((4 * t + 2).factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((2 * t + 3).factorial : ℚ) ≠ 0 := by positivity
  have h3 : ((2 * t).factorial : ℚ) ≠ 0 := by positivity
  have h4 : ((4 * t).factorial : ℚ) ≠ 0 := by positivity
  have h5 : ((2 * t + 1).factorial : ℚ) ≠ 0 := by positivity
  field_simp
  ring
