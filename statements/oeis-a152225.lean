import Mathlib

/-!
# A152225: Number of Dyck paths of semilength n with no peaks at height 0 (mod 3) and no valleys at height 2 (mod 3).

Source: https://oeis.org/A152225
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 2, 4, 9, 22, 56, 146, 388, ...
The entry gives the generating function
  (1 - 2*x + 2*x^2 - sqrt(1 - 4*x + 4*x^2 - 4*x^3))/(2*x^2)
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = -4*x^3 + 4*x^2 - 4*x + 1 the series is, in normalised form,
  (2*x^2 - 2*x + 1 + (-1)*sqrt(R)) / (2*x^2),
which is the expression used below (the division by x^2 is the shift of the index by 2).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Aug 14 2012) reads
  Conjecture: (n+2)*a(n) - 2*(2*n+1)*a(n-1) + 4*(n-1)*a(n-2) + 2*(5-2*n)*a(n-3)=0
The recurrence fails for n in [3] (small n, where the inhomogeneous part of the differential
equation is felt), so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a152225

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X + 4 * X ^ 2 - 4 * X ^ 3

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A152225: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 2)
    ((1 - 2 * X + 2 * X ^ 2 - S)
      * (2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A152225. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℚ) + 2) * a n + (-4 * (n : ℚ) - 2) * a (n - 1) + (4 * (n : ℚ) - 4) * a (n - 2)
      + (-4 * (n : ℚ) + 10) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a152225
