import OMAStatements.S_oeis_a285834

open OMA.S_oeis_a285834 (a)

/-- Counting the corner-to-origin diagonal at the four even stages gives a counterexample. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a285834.main) := by
  intro claims
  have atEight := claims.2 8 (by decide)
  have counterexample :
      (a 8 : ℤ) ≠ 7 * a 6 - 14 * a 4 + 8 * a 2 := by decide +kernel
  exact counterexample atEight
