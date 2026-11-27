import Mathlib

/-!
# A300984: squarefree sums of squarefree and nonsquarefree divisors

Source: https://oeis.org/A300984
Credit: @dwilfand-sys

The exponents in the stated factorization are nonnegative integers.
Exponent zero allows a power of two or a power of a single prime.
-/

namespace OMA.S_oeis_a300984

def squarefreeSum (n : ℕ) : ℕ := ∑ d ∈ n.divisors with Squarefree d, d

def nonsquarefreeSum (n : ℕ) : ℕ := ∑ d ∈ n.divisors with ¬ Squarefree d, d

theorem main : ∀ n : ℕ, 0 < n → Squarefree (squarefreeSum n) →
    Squarefree (nonsquarefreeSum n) →
    ∃ p i j : ℕ, p.Prime ∧ n = 2^i * p^j := by
  sorry

end OMA.S_oeis_a300984
