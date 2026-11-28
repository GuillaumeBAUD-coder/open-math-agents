import Mathlib

/-!
# A257515: Number of 3-generalized 2-Motzkin paths of length n with no level steps H=(3,0) at odd level.

Source: https://oeis.org/A257515
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 0, 1, 2, 2, 4, 9, 12, 26, ...
The entry gives the generating function
  (1-2*x^3-sqrt((1-2x^3)*(1-4*x^2-2*x^3)))/(2*x^2*(1-2*x^3))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 4*x^6 + 8*x^5 - 4*x^3 - 4*x^2 + 1 the series is, in normalised form,
  (1 - 2*x^3 + (-1)*sqrt(R)) / (-4*x^5 + 2*x^2),
which is the expression used below (the division by x^2 is the shift of the index by 2).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 07 2016) reads
  Conjecture: (n+2)*a(n) +(n+1)*a(n-1) +(n+4)*a(n-2) +4*(-2*n+3)*a(n-3) +4*(-6*n+17)*a(n-4) +4*(-3*n+10)*a(n-5) +4*(3*n-11)*a(n-6) +4*(11*n-50)*a(n-7) +20*(n-6)*a(n-8)=0
It involves a(n-8) and the offset is 0, so it is stated for n >= 8.
-/

namespace OMA.S_oeis_a257515

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X ^ 2 - 4 * X ^ 3 + 8 * X ^ 5 + 4 * X ^ 6

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A257515: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 2)
    ((1 - 2 * X ^ 3 - S)
      * (2 - 4 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A257515. -/
theorem main : ∀ n : ℕ, 8 ≤ n →
    ((n : ℚ) + 2) * a n + ((n : ℚ) + 1) * a (n - 1) + ((n : ℚ) + 4) * a (n - 2)
      + (-8 * (n : ℚ) + 12) * a (n - 3) + (-24 * (n : ℚ) + 68) * a (n - 4)
      + (-12 * (n : ℚ) + 40) * a (n - 5) + (12 * (n : ℚ) - 44) * a (n - 6)
      + (44 * (n : ℚ) - 200) * a (n - 7) + (20 * (n : ℚ) - 120) * a (n - 8) = 0 := by
  sorry

end OMA.S_oeis_a257515
