import Mathlib

/-!
# A135335: Number of Dyck paths of semilength n having no DDUU's starting at level 2.

Source: https://oeis.org/A135335
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 2, 5, 13, 36, 106, 327, 1045, ...
The entry gives the generating function
  (1-2*C+z*C)/(2*z*C-C*z^2-C-z), where C = (1-sqrt(1-4*z))/(2*z)
(Emeric Deutsch, Dec 13 2007). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x the series is, in normalised form,
  (-2*x^3 + 4*x^2 - 6*x + 3 + (-1)*sqrt(R)) / (2*x^4 - 4*x^3 + 8*x^2 - 6*x + 2),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 17 2016) reads
  Conjecture: n*a(n) +(-7*n+6)*a(n-1) +2*(8*n-9)*a(n-2) +6*(-3*n+4)*a(n-3) +3*(3*n-4)*a(n-4) +2*(-2*n+3)*a(n-5)=0
It involves a(n-5) and the offset is 0, so it is stated for n >= 5.
-/

namespace OMA.S_oeis_a135335

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A135335: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((3 - 6 * X + 4 * X ^ 2 - 2 * X ^ 3 - S)
      * (2 - 6 * X + 8 * X ^ 2 - 4 * X ^ 3 + 2 * X ^ 4 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A135335. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    (n : ℚ) * a n + (-7 * (n : ℚ) + 6) * a (n - 1) + (16 * (n : ℚ) - 18) * a (n - 2)
      + (-18 * (n : ℚ) + 24) * a (n - 3) + (9 * (n : ℚ) - 12) * a (n - 4)
      + (-4 * (n : ℚ) + 6) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a135335
