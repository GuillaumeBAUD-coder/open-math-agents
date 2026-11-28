import Mathlib

/-!
# A143954: Number of peaks in the peak plateaux of all Dyck paths of semilength n.

Source: https://oeis.org/A143954
Credit: @vivanpoddar

The sequence (offset 0) begins 0, 0, 1, 5, 19, 68, 243, 880, 3233, ...
The entry gives the generating function
  z^2*C/[(1-z)^2*sqrt(1-4z)], where C = [1-sqrt(1-4z)]/(2z)
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x the series is, in normalised form,
  (4*x^2 - x + (x)*sqrt(R)) / (-8*x^3 + 18*x^2 - 12*x + 2),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 16 2016) reads
  Conjecture: (-n+1)*a(n) +2*(3*n-4)*a(n-1) +(-9*n+13)*a(n-2) +2*(2*n-3)*a(n-3)=0
It involves a(n-3) and the offset is 0, so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a143954

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A143954: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((-X + 4 * X ^ 2 + (X) * S)
      * (2 - 12 * X + 18 * X ^ 2 - 8 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A143954. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    (-(n : ℚ) + 1) * a n + (6 * (n : ℚ) - 8) * a (n - 1) + (-9 * (n : ℚ) + 13) * a (n - 2)
      + (4 * (n : ℚ) - 6) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a143954
