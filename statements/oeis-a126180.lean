import Mathlib

/-!
# A126180: Number of branches in all hex trees with n edges (n>=1).

Source: https://oeis.org/A126180
Credit: @vivanpoddar

The sequence (offset 1) begins 3, 11, 48, 224, 1071, 5169, 25053, 121711, 592233, ...
The entry gives the generating function
  (1-3z)[2-9z+5z^2-(2-3z)sqrt(1-6z+5z^2)]/[2z^2*sqrt(1-6z+5z^2)]
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 5*x^2 - 6*x + 1 the series is, in normalised form,
  (-45*x^4 + 99*x^3 - 73*x^2 + 21*x - 2 + (-15*x^3 + 32*x^2 - 15*x + 2)*sqrt(R)) / (10*x^4 - 12*x^3 + 2*x^2),
which is the expression used below (the division by x^2 is the shift of the index by 2).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 17 2016) reads
  Conjecture: -2*(n+2)*(239*n-1252)*a(n) +21*(220*n^2-997*n-578)*a(n-1) +(-12902*n^2+76676*n-77157)*a(n-2) +15*(n-3)*(584*n-2237)*a(n-3)=0
It involves a(n-3) and the offset is 1, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a126180

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 6 * X + 5 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A126180: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 2)
    ((-2 + 21 * X - 73 * X ^ 2 + 99 * X ^ 3 - 45 * X ^ 4 + (2 - 15 * X + 32 * X ^ 2 - 15 * X ^ 3) * S)
      * (2 - 12 * X + 10 * X ^ 2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A126180. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (-478 * (n : ℚ) ^ 2 + 1548 * (n : ℚ) + 5008) * a n
      + (4620 * (n : ℚ) ^ 2 - 20937 * (n : ℚ) - 12138) * a (n - 1)
      + (-12902 * (n : ℚ) ^ 2 + 76676 * (n : ℚ) - 77157) * a (n - 2)
      + (8760 * (n : ℚ) ^ 2 - 59835 * (n : ℚ) + 100665) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a126180
