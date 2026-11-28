import Mathlib

/-!
# A188460: Diagonal sums of number triangle A119308.

Source: https://oeis.org/A188460
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 2, 4, 9, 20, 45, 103, 238, 555, ...
The entry gives the generating function
  (1-2*x-x^3-(1-x)*sqrt((x^2-3*x+1)*(x^2+x+1)))/(2*x^5)
(Mark van Hoeij, May 10 2013). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = x^4 - 2*x^3 - x^2 - 2*x + 1 the series is, in normalised form,
  (-x^3 - 2*x + 1 + (x - 1)*sqrt(R)) / (2*x^5),
which is the expression used below (the division by x^5 is the shift of the index by 5).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Feb 13 2015) reads
  Conjecture: (n+5)*(n+1)*a(n) -(2*n+5)*(n+2)*a(n-1) -(n+2)*(n+1)*a(n-2) -(n+1)*(2*n+1)*a(n-3) +(n-2)*(n+2)*a(n-4)=0
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a188460

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A188460: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 5)
    ((1 - 2 * X - X ^ 3 + (-1 + X) * S)
      * (2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A188460. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℚ) ^ 2 + 6 * (n : ℚ) + 5) * a n + (-2 * (n : ℚ) ^ 2 - 9 * (n : ℚ) - 10) * a (n - 1)
      + (-(n : ℚ) ^ 2 - 3 * (n : ℚ) - 2) * a (n - 2)
      + (-2 * (n : ℚ) ^ 2 - 3 * (n : ℚ) - 1) * a (n - 3) + ((n : ℚ) ^ 2 - 4) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a188460
