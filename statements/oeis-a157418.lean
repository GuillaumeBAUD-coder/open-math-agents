import Mathlib

/-!
# A157418: a(n) is the number of ways to insert single pairs of parenthesis to completely separate n identical objects in a straight line such that at least one of the objects at the two ends is not enclosed.

Source: https://oeis.org/A157418
Credit: @vivanpoddar

The sequence (offset 1) begins 1, 2, 5, 16, 55, 202, 773, 3052, 12339, ...
The entry gives the generating function
  (2-t-2t^2-(t+2)*sqrt(1-4t-4t^2))/(2(t+1)^2)
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = -4*x^2 - 4*x + 1 the series is, in normalised form,
  (-2*x^2 - x + 2 + (-x - 2)*sqrt(R)) / (2*x^2 + 4*x + 2),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jul 24 2012) reads
  Conjecture: n*(7*n-29)*a(n) +(-21*n^2+136*n-192)*a(n-1) +2*(-28*n^2+165*n-210)*a(n-2) -4*(n-3)*(7*n-22)*a(n-3)=0
It involves a(n-3) and the offset is 1, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a157418

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X - 4 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A157418: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((2 - X - 2 * X ^ 2 + (-2 - X) * S)
      * (2 + 4 * X + 2 * X ^ 2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A157418. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (7 * (n : ℚ) ^ 2 - 29 * (n : ℚ)) * a n
      + (-21 * (n : ℚ) ^ 2 + 136 * (n : ℚ) - 192) * a (n - 1)
      + (-56 * (n : ℚ) ^ 2 + 330 * (n : ℚ) - 420) * a (n - 2)
      + (-28 * (n : ℚ) ^ 2 + 172 * (n : ℚ) - 264) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a157418
