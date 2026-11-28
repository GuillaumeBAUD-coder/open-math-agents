import Mathlib

/-!
# OEIS A256776: Primes of form n^2 + 256.

Source: https://oeis.org/A256776
Credit: @unserus

OEIS: "Conjecture: sequence is infinite."
-/

namespace OMA.S_oeis_a256776

/-- The terms of A256776: primes of the form `n^2 + 256`. -/
def a256776Set : Set ℕ := {p : ℕ | p.Prime ∧ ∃ n : ℕ, p = n ^ 2 + 256}

/-- A256776 is infinite. -/
theorem main : a256776Set.Infinite := by
  sorry

end OMA.S_oeis_a256776
