import Mathlib

/-!
# A176332: Row sums of triangle A176331.

Source: https://oeis.org/A176332
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 2, 5, 16, 56, 202, 741, 2752, 10318, ...
The entry gives the generating function
  1 / ( sqrt(1-4*x) * (1 + x^2 * c(x)^2) )
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x the series is, in normalised form,
  (1 - 4*x + (3 - 2*x)*sqrt(R)) / (-8*x^3 + 18*x^2 - 20*x + 4),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Nov 24 2012) reads
  Conjecture: 6*n*a(n) + 2*(-17*n+10)*a(n-1) + (47*n-60)*a(n-2) + 10*(-3*n+5)*a(n-3) + 4*(2*n-5)*a(n-4) = 0
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a176332

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A176332: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((1 - 4 * X + (3 - 2 * X) * S)
      * (4 - 20 * X + 18 * X ^ 2 - 8 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A176332. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (6 * (n : ℚ)) * a n + (-34 * (n : ℚ) + 20) * a (n - 1) + (47 * (n : ℚ) - 60) * a (n - 2)
      + (-30 * (n : ℚ) + 50) * a (n - 3) + (8 * (n : ℚ) - 20) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a176332
