import Mathlib

/-!
# A143955: Sum of the altitudes of the leftmost valleys of all Dyck paths of semilength n (if path has no valley, then this altitude is taken to be 0).

Source: https://oeis.org/A143955
Credit: @vivanpoddar

The sequence (offset 0) begins 0, 0, 0, 1, 6, 26, 101, 376, 1377, ...
The entry gives the generating function
  z^3*C^5/(1-z), where C = (1-sqrt(1-4*z))/(2*z)
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x the series is, in normalised form,
  (5*x^2 - 5*x + 1 + (-x^2 + 3*x - 1)*sqrt(R)) / (-2*x^3 + 2*x^2),
which is the expression used below (the division by x^2 is the shift of the index by 2).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jul 24 2012) reads
  Conjecture: (n+2)*a(n) -4*(2*n+1)*a(n-1) +2*(10*n-9)*a(n-2) +17*(2-n)*a(n-3) +2*(2*n-7)*a(n-4)=0
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a143955

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A143955: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 2)
    ((1 - 5 * X + 5 * X ^ 2 + (-1 + 3 * X - X ^ 2) * S)
      * (2 - 2 * X : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A143955. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℚ) + 2) * a n + (-8 * (n : ℚ) - 4) * a (n - 1) + (20 * (n : ℚ) - 18) * a (n - 2)
      + (-17 * (n : ℚ) + 34) * a (n - 3) + (4 * (n : ℚ) - 14) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a143955
