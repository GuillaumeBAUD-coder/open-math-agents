import Mathlib

/-!
# A228771: The number of skew sum indecomposable permutations which avoid the patterns 3124 and 4312.

Source: https://oeis.org/A228771
Credit: @vivanpoddar

The sequence (offset 1) begins 1, 1, 3, 12, 53, 234, 1013, 4306, 18051, ...
The entry gives the generating function
  (8*x^6 - 28*x^5 + 50*x^4 - 35*x^3 + 10*x^2 - sqrt(-4*x + 1)*(6*x^5 - 18*x^4 + 21*x^3 - 8*x^2 + x) - x)/(8*x^5 - 46*x^4 + 71*x^3 - 43*x^2 - sqrt(-4*x + 1)*(12*x^4 - 31*x^3 + 27*x^2 - 9*x + 1) + 11*x - 1)
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x the series is, in normalised form,
  (8*x^5 - 28*x^4 + 35*x^3 - 27*x^2 + 9*x - 1 + (6*x^4 - 13*x^3 + 15*x^2 - 7*x + 1)*sqrt(R)) / (8*x^4 - 10*x^3 + 2*x^2),
which is the expression used below (the division by x^2 is the shift of the index by 2).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 14 2016) reads
  Conjecture: -163*(n+2)*(4*n-413) *a(n) +(-652*n^2-725425*n-452889) *a(n-1) +5*(14473*n^2+512276*n-443094) *a(n-2) +(-410045*n^2-2408964*n+8429009) *a(n-3) +2*(404156*n^2-1297075*n-1518084)*a(n-4) -8*(29333*n-32490)*(2*n-11)*a(n-5)=0
The recurrence fails for n in [6] (small n, where the inhomogeneous part of the differential
equation is felt), so it is stated for n >= 7.
-/

namespace OMA.S_oeis_a228771

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A228771: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 2)
    ((-1 + 9 * X - 27 * X ^ 2 + 35 * X ^ 3 - 28 * X ^ 4 + 8 * X ^ 5 + (1 - 7 * X + 15 * X ^ 2 - 13 * X ^ 3 + 6 * X ^ 4) * S)
      * (2 - 10 * X + 8 * X ^ 2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A228771. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    (-652 * (n : ℚ) ^ 2 + 66015 * (n : ℚ) + 134638) * a n
      + (-652 * (n : ℚ) ^ 2 - 725425 * (n : ℚ) - 452889) * a (n - 1)
      + (72365 * (n : ℚ) ^ 2 + 2561380 * (n : ℚ) - 2215470) * a (n - 2)
      + (-410045 * (n : ℚ) ^ 2 - 2408964 * (n : ℚ) + 8429009) * a (n - 3)
      + (808312 * (n : ℚ) ^ 2 - 2594150 * (n : ℚ) - 3036168) * a (n - 4)
      + (-469328 * (n : ℚ) ^ 2 + 3101144 * (n : ℚ) - 2859120) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a228771
