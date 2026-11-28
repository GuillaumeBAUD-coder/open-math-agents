import Mathlib

/-!
# A273343: The sum of the first-column lengths of all bargraphs of semiperimeter n (n>=2).

Source: https://oeis.org/A273343
Credit: @vivanpoddar

The sequence (offset 2) begins 1, 3, 9, 26, 75, 218, 640, 1898, 5682, ...
The entry gives the generating function
  (z^6 + z^5 + z^4 - 2z^3 - 5z^2 +5z - 1 - (z^3 + 2z^2 + 2z - 1)Z)/(2 Z z^2), where Z = (1 - z)sqrt((1 - z)(1 - 3z - z^2 - z^3))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = x^4 + 2*x^2 - 4*x + 1 the series is, in normalised form,
  (x^4 + x^3 - 3*x + 1 + (x^2 + x - 1)*sqrt(R)) / (-2*x^3 + 2*x^2),
which is the expression used below (the division by x^2 is the shift of the index by 2).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 02 2016) reads
  Conjecture: (n+2)*a(n) +(-5*n-3)*a(n-1) +(5*n-2)*a(n-2) +(2*n-9)*a(n-3) +(-n+3)*a(n-4) +(-n+4)*a(n-5) +(-n+7)*a(n-6)=0
It involves a(n-6) and the offset is 2, so it is stated for n >= 8.
-/

namespace OMA.S_oeis_a273343

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X + 2 * X ^ 2 + X ^ 4

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A273343: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 2)
    ((1 - 3 * X + X ^ 3 + X ^ 4 + (-1 + X + X ^ 2) * S)
      * (2 - 2 * X : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A273343. -/
theorem main : ∀ n : ℕ, 8 ≤ n →
    ((n : ℚ) + 2) * a n + (-5 * (n : ℚ) - 3) * a (n - 1) + (5 * (n : ℚ) - 2) * a (n - 2)
      + (2 * (n : ℚ) - 9) * a (n - 3) + (-(n : ℚ) + 3) * a (n - 4)
      + (-(n : ℚ) + 4) * a (n - 5) + (-(n : ℚ) + 7) * a (n - 6) = 0 := by
  sorry

end OMA.S_oeis_a273343
