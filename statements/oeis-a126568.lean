import Mathlib

/-!
# A126568: Binomial transform of A026641.

Source: https://oeis.org/A126568
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 2, 7, 29, 127, 572, 2623, 12182, 57115, ...
The entry gives the generating function
  (11*x^4 -12*x^3 -x^2 +3*x -1  -sqrt(5*x^2-6*x+1)*(5*x^3-3*x^2-1))/( sqrt(5*x^2-6*x+1)*(4*x^4-8*x^3-3*x^2+7*x-2) -10*x^5 +32*x^4 -31*x^3 + 20*x^2 -13*x +2)
(Vladimir Kruchinin, Apr 08 2014). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 5*x^2 - 6*x + 1 the series is, in normalised form,
  (1 - 5*x + (3)*sqrt(R)) / (10*x^2 - 22*x + 4),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 30 2013) reads
  Conjecture: 4*n*a(n) +2*(2*n-7)*a(n-1) +(-163*n+267)*a(n-2) +10*(23*n-58)*a(n-3) +75*(-n+3)*a(n-4) = 0
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a126568

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 6 * X + 5 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A126568: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((1 - 5 * X + (3) * S)
      * (4 - 22 * X + 10 * X ^ 2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A126568. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (4 * (n : ℚ)) * a n + (4 * (n : ℚ) - 14) * a (n - 1) + (-163 * (n : ℚ) + 267) * a (n - 2)
      + (230 * (n : ℚ) - 580) * a (n - 3) + (-75 * (n : ℚ) + 225) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a126568
