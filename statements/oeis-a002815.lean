import Mathlib.NumberTheory.PrimeCounting
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# A002815: Partial sums of the prime-counting function plus the index

Source: https://oeis.org/A002815
Numerator exponents: https://oeis.org/A008578
Credit: @MMexicann
-/

open scoped BigOperators

namespace OMA.S_oeis_a002815

/-- The sequence starts at index zero. -/
def a (n : ℕ) : ℕ :=
  n + ∑ k ∈ Finset.Icc 1 n, Nat.primeCounting k

/-- The numerator has coefficient one at exponent one and at prime exponents.
Clearing the denominator preserves the ordinary generating function identity
because the denominator has constant term one. -/
theorem main :
    (PowerSeries.mk fun n ↦ (a n : ℤ)) * (1 - PowerSeries.X) ^ 2 =
      PowerSeries.mk (fun n ↦ (if n = 1 ∨ Nat.Prime n then 1 else 0 : ℤ)) := by
  sorry

end OMA.S_oeis_a002815
