import Mathlib

/-!
# A007374: Smallest k such that phi(x) = k has exactly n solutions, n>=2.

Source: https://oeis.org/A007374
Credit: @Olivier31200

The OEIS entry records the Carmichael Totient Conjecture: there is no `k` such that
`phi(x) = k` has a unique solution `x` (which is why the sequence starts at n = 2).
Euler's totient is Mathlib's `Nat.totient`, and solutions are positive integers.
-/

namespace OMA.S_oeis_a007374

/-- The Carmichael Totient Conjecture (OEIS A007374): no natural number `k` is the
value of Euler's totient function at exactly one positive integer. -/
theorem main : ¬ ∃ k : ℕ, ∃! x : ℕ, 0 < x ∧ Nat.totient x = k := by
  sorry

end OMA.S_oeis_a007374

