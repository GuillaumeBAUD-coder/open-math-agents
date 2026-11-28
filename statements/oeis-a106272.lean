import Mathlib

/-!
# A106272: Antidiagonal sums of number triangle A106270.

Source: https://oeis.org/A106272
Credit: @vivanpoddar

The sequence (offset 0) begins 1, -1, -1, -6, -15, -48, -147, -477, -1577, ...
The entry gives the generating function
  c(x)*sqrt(1 - 4*x)/(1 - x^2)
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x the series is, in normalised form,
  (4*x - 1 + (1)*sqrt(R)) / (-2*x^3 + 2*x),
which is the expression used below (the division by x^1 is the shift of the index by 1).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Nov 09 2012) reads
  Conjecture: (n+1)*a(n) + 2*(1-2*n)*a(n-1) - (n+1)*a(n-2) + 2*(2*n-1)*a(n-3) = 0
It involves a(n-3) and the offset is 0, so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a106272

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A106272: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 1)
    ((-1 + 4 * X + S)
      * (2 - 2 * X ^ 2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A106272. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    ((n : ℚ) + 1) * a n + (-4 * (n : ℚ) + 2) * a (n - 1) + (-(n : ℚ) - 1) * a (n - 2)
      + (4 * (n : ℚ) - 2) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a106272
