import Mathlib.Data.Nat.Prime.Basic

/-!
# The two solutions of A070304 at primes of the form m² + 1

Steven Lee Benjamin's conjecture for OEIS A382617 concerns nonnegative k for
which p²k²/(p²+k²) is an integer. The denominator is positive when p is prime,
so this condition is equivalent to divisibility in the natural numbers.

Sources: https://oeis.org/A382617 and https://oeis.org/A070304
Credit: @hiattco
-/

namespace OMA.S_oeis_a382617

/-- The integrality condition counted by A070304 for a prime p. -/
def isSolution (p k : ℕ) : Prop := p ^ 2 + k ^ 2 ∣ p ^ 2 * k ^ 2

theorem main : ∀ m p : ℕ, p = m ^ 2 + 1 → Nat.Prime p →
    0 < m * p ∧ ∀ k : ℕ, isSolution p k ↔ k = 0 ∨ k = m * p := by
  sorry

end OMA.S_oeis_a382617
