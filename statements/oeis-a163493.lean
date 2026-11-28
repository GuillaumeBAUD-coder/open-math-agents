import Mathlib

/-!
# A163493: Number of binary strings of length n which have the same number of 00 and 01 substrings.

Source: https://oeis.org/A163493
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 2, 2, 3, 6, 9, 15, 30, 54, ...
The entry gives the generating function
  1/2/(1-x) + (1+2*x)/2/sqrt((1-x)*(1-2*x)*(1+x+2*x^2))
(Richard Stanley, corrected Apr 29 2011). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 4*x^4 - 4*x^3 + x^2 - 2*x + 1 the series is, in normalised form,
  (-4*x^3 - x + 1 + (2*x + 1)*sqrt(R)) / (8*x^4 - 8*x^3 + 2*x^2 - 4*x + 2),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Nov 28 2011) reads
  Conjecture: -n*a(n) +(2+n)*a(n-1) +(3n-12)*a(n-2) +(12-n)*a(n-3) +(2n-18)*a(n-4)+(56-12n)*a(n-5) +(8n-40)*a(n-6)=0
It involves a(n-6) and the offset is 0, so it is stated for n >= 6.
-/

namespace OMA.S_oeis_a163493

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 2 * X + X ^ 2 - 4 * X ^ 3 + 4 * X ^ 4

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A163493: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((1 - X - 4 * X ^ 3 + (1 + 2 * X) * S)
      * (2 - 4 * X + 2 * X ^ 2 - 8 * X ^ 3 + 8 * X ^ 4 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A163493. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    (-(n : ℚ)) * a n + ((n : ℚ) + 2) * a (n - 1) + (3 * (n : ℚ) - 12) * a (n - 2)
      + (-(n : ℚ) + 12) * a (n - 3) + (2 * (n : ℚ) - 18) * a (n - 4)
      + (-12 * (n : ℚ) + 56) * a (n - 5) + (8 * (n : ℚ) - 40) * a (n - 6) = 0 := by
  sorry

end OMA.S_oeis_a163493
