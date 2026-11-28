import Mathlib

/-!
# A128746: Height of the last peak summed over all skew Dyck paths of semilength n.

Source: https://oeis.org/A128746
Credit: @vivanpoddar

The sequence (offset 1) begins 1, 5, 22, 94, 401, 1723, 7475, 32749, 144803, ...
The entry gives the generating function
  2*z*(1+z+sqrt(1-6*z+5*z^2))/(1-3*z+sqrt(1-6*z+5*z^2))^2
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 5*x^2 - 6*x + 1 the series is, in normalised form,
  (11*x^2 - 11*x + 2 + (5*x - 2)*sqrt(R)) / (2*x^2),
which is the expression used below (the division by x^2 is the shift of the index by 2).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Aug 08 2015) reads
  Conjecture: -(n+2)*(n-1)*a(n) +(6*n^2-3*n+2)*a(n-1) -5*n*(n-2)*a(n-2)=0
It involves a(n-2) and the offset is 1, so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a128746

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 6 * X + 5 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A128746: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 2)
    ((2 - 11 * X + 11 * X ^ 2 + (-2 + 5 * X) * S)
      * (2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A128746. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    (-(n : ℚ) ^ 2 - (n : ℚ) + 2) * a n + (6 * (n : ℚ) ^ 2 - 3 * (n : ℚ) + 2) * a (n - 1)
      + (-5 * (n : ℚ) ^ 2 + 10 * (n : ℚ)) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a128746
