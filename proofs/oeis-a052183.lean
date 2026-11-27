import OMAStatements.S_oeis_a052183

theorem OMA.solution : type_of% @OMA.S_oeis_a052183.main := by
  intro t
  dsimp only
  unfold OMA.S_oeis_a052183.a
  rw [show 3 * (t + 2) = 3 * t + 1 + 1 + 1 + 1 + 1 + 1 by ring,
    show 2 * (t + 2) + 1 = 2 * t + 1 + 1 + 1 + 1 + 1 by ring,
    show 3 * (t + 1) = 3 * t + 1 + 1 + 1 by ring,
    show 2 * (t + 1) + 1 = 2 * t + 1 + 1 + 1 by ring,
    show t + 2 = t + 1 + 1 by ring]
  simp only [Nat.factorial_succ]
  push_cast
  have h1 : ((3 * t).factorial : ℚ) ≠ 0 := by positivity
  have h2 : (t.factorial : ℚ) ≠ 0 := by positivity
  have h3 : ((2 * t).factorial : ℚ) ≠ 0 := by positivity
  field_simp
  ring
