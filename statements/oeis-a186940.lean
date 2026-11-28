import Mathlib

/-!
# A186940: Diagonal sums of number triangle A114709.

Source: https://oeis.org/A186940
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 0, 3, 6, 31, 126, 589, 2772, 13485, ...
The entry gives the generating function
  (1+3*x-2*x^2-sqrt(1-6*x+x^2))/(2*(3+x-3*x^2+x^3))
(see the entry), taken times x^(-1) so that the exponent of x is the index n of the entry. It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = x^2 - 6*x + 1 the series is, in normalised form,
  (-2*x^2 + 3*x + 1 + (-1)*sqrt(R)) / (2*x^4 - 6*x^3 + 2*x^2 + 6*x),
which is the expression used below (the division by x^1 is the shift of the index by 1).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Nov 17 2011) reads
  Conjecture: 3*(n+1)*a(n) +(10-17*n)*a(n-1) -6*(n+1)*a(n-2) +10*(2*n-1)*a(n-3) +9*(1-n)*a(n-4) +(n-2)*a(n-5) =0
It involves a(n-5) and the offset is 0, so it is stated for n >= 5.
-/

namespace OMA.S_oeis_a186940

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 6 * X + X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A186940: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 1)
    ((1 + 3 * X - 2 * X ^ 2 - S)
      * (6 + 2 * X - 6 * X ^ 2 + 2 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A186940. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    (3 * (n : ℚ) + 3) * a n + (-17 * (n : ℚ) + 10) * a (n - 1) + (-6 * (n : ℚ) - 6) * a (n - 2)
      + (20 * (n : ℚ) - 10) * a (n - 3) + (-9 * (n : ℚ) + 9) * a (n - 4)
      + ((n : ℚ) - 2) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a186940
