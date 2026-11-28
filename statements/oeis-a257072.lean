import Mathlib

/-!
# A257072: Number of 3-colored Schroeder paths of semilength n in which there are no (2,0)-steps at level 1.

Source: https://oeis.org/A257072
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 4, 17, 77, 374, 1959, 11085, 67500, 438485, ...
The entry gives the generating function
  8/(7-27*z+sqrt(1-10*z+9*z^2))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 9*x^2 - 10*x + 1 the series is, in normalised form,
  (7 - 27*x + (-1)*sqrt(R)) / (90*x^2 - 46*x + 6),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Sep 24 2016) reads
  Conjecture: 3*n*a(n) +(-53*n+45)*a(n-1) +2*(151*n-213)*a(n-2) +9*(-73*n+144)*a(n-3) +405*(n-3)*a(n-4)=0
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a257072

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 10 * X + 9 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A257072: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((7 - 27 * X - S)
      * (6 - 46 * X + 90 * X ^ 2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A257072. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (3 * (n : ℚ)) * a n + (-53 * (n : ℚ) + 45) * a (n - 1) + (302 * (n : ℚ) - 426) * a (n - 2)
      + (-657 * (n : ℚ) + 1296) * a (n - 3) + (405 * (n : ℚ) - 1215) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a257072
