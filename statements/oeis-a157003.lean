import Mathlib

/-!
# A157003: Transform of Catalan numbers whose Hankel transform gives the Somos-4 sequence.

Source: https://oeis.org/A157003
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 2, 4, 10, 27, 78, 234, 722, ...
The entry gives the generating function
  c(x*(1-x^2))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 4*x^3 - 4*x + 1 the series is, in normalised form,
  (1 + (-1)*sqrt(R)) / (-2*x^3 + 2*x),
which is the expression used below (the division by x^1 is the shift of the index by 1).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Nov 19 2014) reads
  Conjecture: (n+1)*a(n) +(n+2)*a(n-1) +(-21*n+29)*a(n-2) +(3*n-16)*a(n-3) +40*(n-3)*a(n-4) +2*(-2*n+7)*a(n-5) +10*(-2*n+9)*a(n-6)=0
It involves a(n-6) and the offset is 0, so it is stated for n >= 6.
-/

namespace OMA.S_oeis_a157003

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X + 4 * X ^ 3

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A157003: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 1)
    ((1 - S)
      * (2 - 2 * X ^ 2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A157003. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    ((n : ℚ) + 1) * a n + ((n : ℚ) + 2) * a (n - 1) + (-21 * (n : ℚ) + 29) * a (n - 2)
      + (3 * (n : ℚ) - 16) * a (n - 3) + (40 * (n : ℚ) - 120) * a (n - 4)
      + (-4 * (n : ℚ) + 14) * a (n - 5) + (-20 * (n : ℚ) + 90) * a (n - 6) = 0 := by
  sorry

end OMA.S_oeis_a157003
