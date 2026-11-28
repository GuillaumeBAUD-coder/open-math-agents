import Mathlib

/-!
# A135334: Number of Dyck paths of semilength n having no UDDU's starting at level 1.

Source: https://oeis.org/A135334
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 2, 4, 10, 29, 90, 290, 960, ...
The entry gives the generating function
  1 + z*C^2/(1 + z^2*C^2), where C = (1-sqrt(1-4z))/(2z)
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x the series is, in normalised form,
  (2*x^3 - 2*x^2 + 2*x + 1 + (-1)*sqrt(R)) / (2*x^3 - 4*x^2 + 4*x),
which is the expression used below (the division by x^1 is the shift of the index by 1).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Dec 18 2011) reads
  Conjecture: 2*(n+1)*a(n) + 2*(1-5n)*a(n-1) + 3*(3n-1)*a(n-2) + 2*(1-2n)*a(n-3) = 0
The recurrence fails for n in [3] (small n, where the inhomogeneous part of the differential
equation is felt), so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a135334

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A135334: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 1)
    ((1 + 2 * X - 2 * X ^ 2 + 2 * X ^ 3 - S)
      * (4 - 4 * X + 2 * X ^ 2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A135334. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (2 * (n : ℚ) + 2) * a n + (-10 * (n : ℚ) + 2) * a (n - 1) + (9 * (n : ℚ) - 3) * a (n - 2)
      + (-4 * (n : ℚ) + 2) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a135334
