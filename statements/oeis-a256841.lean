import Mathlib

/-!
# OEIS A256841: Primes of form n^2 + 28561.

Source: https://oeis.org/A256841
Credit: @unserus

OEIS: "Conjecture: sequence is infinite."
-/

namespace OMA.S_oeis_a256841

/-- The terms of A256841: primes of the form `n^2 + 28561`. -/
def a256841Set : Set ℕ := {p : ℕ | p.Prime ∧ ∃ n : ℕ, p = n ^ 2 + 28561}

/-- A256841 is infinite. -/
theorem main : a256841Set.Infinite := by
  sorry

end OMA.S_oeis_a256841
