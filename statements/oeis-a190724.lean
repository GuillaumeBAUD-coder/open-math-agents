import Mathlib

/-!
# A190724: Row sums of Riordan matrix A118384.

Source: https://oeis.org/A190724
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 4, 20, 106, 576, 3174, 17648, 98746, 555104, ...
The entry gives the generating function
  (1-7*x+sqrt(1-6*x+x^2))/((2-12*x)*sqrt(1-6*x+x^2))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = x^2 - 6*x + 1 the series is, in normalised form,
  (x^2 - 6*x + 1 + (1 - 7*x)*sqrt(R)) / (-12*x^3 + 74*x^2 - 24*x + 2),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jul 24 2012) reads
  Conjecture: n*(2*n+3)*a(n) +2*(-12*n^2-15*n+22)*a(n-1) +(74*n^2+73*n-274)*a(n-2) -6*(2*n+5)*(n-2)*a(n-3)=0
It involves a(n-3) and the offset is 0, so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a190724

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 6 * X + X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A190724: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((1 - 6 * X + X ^ 2 + (1 - 7 * X) * S)
      * (2 - 24 * X + 74 * X ^ 2 - 12 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A190724. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    (2 * (n : ℚ) ^ 2 + 3 * (n : ℚ)) * a n + (-24 * (n : ℚ) ^ 2 - 30 * (n : ℚ) + 44) * a (n - 1)
      + (74 * (n : ℚ) ^ 2 + 73 * (n : ℚ) - 274) * a (n - 2)
      + (-12 * (n : ℚ) ^ 2 - 6 * (n : ℚ) + 60) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a190724
