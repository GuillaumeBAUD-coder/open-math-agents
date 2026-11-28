import Mathlib

/-!
# A274295: a(n) = n+binomial(2*n-6,n-3)+binomial(2*n-5,n-3)+binomial(n-1,n-3)+Sum_{i=1..n-3} (binomial(n+i-3,n-3)+2*n-i-5).

Source: https://oeis.org/A274295
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 3, 6, 16, 43, 120, 369, 1244, ...
The entry gives the generating function
  -11-12/(x - 1)^3 + x*(-4 + 31/(x-1)^3 + x*(1/sqrt(1 - 4*x) - 23/(x - 1)^3 + x/sqrt(1 - 4*x)))
(Benedict W. J. Irwin, Aug 09 2016). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x the series is, in normalised form,
  (-16*x^5 + 8*x^4 - 9*x^3 + 10*x^2 - 6*x + 1 + (-x^6 + 2*x^5 - 2*x^3 + x^2)*sqrt(R)) / (4*x^4 - 13*x^3 + 15*x^2 - 7*x + 1),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Oct 07 2016) reads
  Conjecture: (-n+2)*a(n) +(7*n-18)*a(n-1) +14*(-n+3)*a(n-2) +2*(3*n-2)*a(n-3) +(11*n-90)*a(n-4) +(-13*n+102)*a(n-5) +2*(2*n-17)*a(n-6)=0
The recurrence fails for n in [6, 7] (small n, where the inhomogeneous part of the differential
equation is felt), so it is stated for n >= 8.
-/

namespace OMA.S_oeis_a274295

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A274295: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((1 - 6 * X + 10 * X ^ 2 - 9 * X ^ 3 + 8 * X ^ 4 - 16 * X ^ 5 + (X ^ 2 - 2 * X ^ 3 + 2 * X ^ 5 - X ^ 6) * S)
      * (1 - 7 * X + 15 * X ^ 2 - 13 * X ^ 3 + 4 * X ^ 4 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A274295. -/
theorem main : ∀ n : ℕ, 8 ≤ n →
    (-(n : ℚ) + 2) * a n + (7 * (n : ℚ) - 18) * a (n - 1) + (-14 * (n : ℚ) + 42) * a (n - 2)
      + (6 * (n : ℚ) - 4) * a (n - 3) + (11 * (n : ℚ) - 90) * a (n - 4)
      + (-13 * (n : ℚ) + 102) * a (n - 5) + (4 * (n : ℚ) - 34) * a (n - 6) = 0 := by
  sorry

end OMA.S_oeis_a274295
