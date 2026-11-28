import Mathlib

/-!
# OEIS A256838: Primes of form n^2 + 10000.

Source: https://oeis.org/A256838
Credit: @unserus

OEIS: "Conjecture: sequence is infinite."
-/

namespace OMA.S_oeis_a256838

/-- The terms of A256838: primes of the form `n^2 + 10000`. -/
def a256838Set : Set ℕ := {p : ℕ | p.Prime ∧ ∃ n : ℕ, p = n ^ 2 + 10000}

/-- A256838 is infinite. -/
theorem main : a256838Set.Infinite := by
  sorry

end OMA.S_oeis_a256838
