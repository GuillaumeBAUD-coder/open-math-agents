import Mathlib

/-!
# A122920: Diagonal sums of number triangle A122919.

Source: https://oeis.org/A122920
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 4, 12, 39, 129, 436, 1498, 5218, ...
The entry gives the generating function
  ((1-x)*(1-2*x-2*x^2-sqrt(1-4*x))/(2*(2+x)*x^3))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x the series is, in normalised form,
  (2*x^3 - 3*x + 1 + (x - 1)*sqrt(R)) / (2*x^4 + 4*x^3),
which is the expression used below (the division by x^3 is the shift of the index by 3).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Nov 05 2012) reads
  Conjecture: 2*n*(n+3)*a(n) - (7*n^2+9*n+4)*a(n-1) - 2*(n+1)*(2*n+1)*a(n-2) = 0
It involves a(n-2) and the offset is 0, so it is stated for n >= 2.
-/

namespace OMA.S_oeis_a122920

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A122920: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 3)
    ((1 - 3 * X + 2 * X ^ 3 + (-1 + X) * S)
      * (4 + 2 * X : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A122920. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    (2 * (n : ℚ) ^ 2 + 6 * (n : ℚ)) * a n + (-7 * (n : ℚ) ^ 2 - 9 * (n : ℚ) - 4) * a (n - 1)
      + (-4 * (n : ℚ) ^ 2 - 6 * (n : ℚ) - 2) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a122920
