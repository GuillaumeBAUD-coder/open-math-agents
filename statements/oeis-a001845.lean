import Mathlib

/-!
# A001845: Centered octahedral numbers

The sequence starts at index zero. Its ordinary generating function is
$(1+x)^3/(1-x)^4$, as conjectured by Simon Plouffe.

Source: https://oeis.org/A001845
Credit: @MMexicann
-/

namespace OMA.S_oeis_a001845

/-- The closed formula for the centered octahedral numbers, used as coefficients
of their ordinary generating function. -/
def centeredOctahedral (n : ℕ) : ℚ :=
  ((2 * (n : ℚ) + 1) * (2 * (n : ℚ) ^ 2 + 2 * (n : ℚ) + 3)) / 3

/-- The denominator has constant term one, so this identity is equivalent to
the ordinary generating function formula. -/
theorem main :
    (1 - (PowerSeries.X : PowerSeries ℚ)) ^ 4 * PowerSeries.mk centeredOctahedral =
      (1 + (PowerSeries.X : PowerSeries ℚ)) ^ 3 := by
  sorry

end OMA.S_oeis_a001845
