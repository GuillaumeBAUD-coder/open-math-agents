import Mathlib

/-!
# A001511: The ruler function: exponent of the highest power of 2 dividing 2n. Equivalently, the 2-adic valuation of 2n.

Source: https://oeis.org/A001511
Credit: @duramson

The comments of A001511 carry one open conjecture:

*Conjecture: For any nonnegative integer k, the sum of the k-th powers of even divisors of n is
always divisible by the sum of the k-th powers of odd divisors of n.*

It generalizes the preceding comment, the case k = 0 (the number of even divisors of 2n is
divisible by the number of odd divisors of 2n). The other comments quoted with this entry are not
open: Ianakiev's conjecture is marked true in the entry, and the curling number property is stated
as a fact.

Conventions:
* n ranges over the positive integers, the indices of A001511 (offset 1).
* k ranges over all natural numbers, k = 0 included, as in the source.
* The divisors of n are the positive divisors, `Nat.divisors n`.
-/

namespace OMA.S_oeis_a001511

/-- For every positive integer n and every k ≥ 0, the sum of the k-th powers of the odd divisors
of n divides the sum of the k-th powers of the even divisors of n. -/
theorem main : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
    (∑ d ∈ n.divisors with Odd d, d ^ k) ∣ ∑ d ∈ n.divisors with Even d, d ^ k := by
  sorry

end OMA.S_oeis_a001511
