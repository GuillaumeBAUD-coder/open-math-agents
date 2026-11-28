import Mathlib

/-!
# A114464: Number of Dyck paths of semilength n having no ascents of length 2 that start at an even level.

Source: https://oeis.org/A114464
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 1, 2, 6, 18, 54, 166, 522, ...
The entry gives the generating function
  [1-z+3z^2-z^3-(1-z)sqrt((1-4z+z^2)(1+z^2))]/(2z)
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = x^4 - 4*x^3 + 2*x^2 - 4*x + 1 the series is, in normalised form,
  (-x^3 + 3*x^2 - x + 1 + (x - 1)*sqrt(R)) / (2*x),
which is the expression used below (the division by x^1 is the shift of the index by 1).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Nov 26 2012) reads
  Conjecture: (n+1)*a(n) +(-5*n+3)*a(n-1) +2*(3*n-7)*a(n-2) +2*(-3*n+11)*a(n-3) +(5*n-27)*a(n-4) +(-n+7)*a(n-5)=0
It involves a(n-5) and the offset is 0, so it is stated for n >= 5.
-/

namespace OMA.S_oeis_a114464

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X + 2 * X ^ 2 - 4 * X ^ 3 + X ^ 4

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A114464: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 1)
    ((1 - X + 3 * X ^ 2 - X ^ 3 + (-1 + X) * S)
      * (2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A114464. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    ((n : ℚ) + 1) * a n + (-5 * (n : ℚ) + 3) * a (n - 1) + (6 * (n : ℚ) - 14) * a (n - 2)
      + (-6 * (n : ℚ) + 22) * a (n - 3) + (5 * (n : ℚ) - 27) * a (n - 4)
      + (-(n : ℚ) + 7) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a114464
