import Mathlib

/-!
# A121320: Number of vertices in all ordered (plane) trees with n edges that are at distance two from all the leaves above them.

Source: https://oeis.org/A121320
Credit: @vivanpoddar

The sequence (offset 0) begins 0, 0, 1, 2, 6, 18, 59, 203, 724, ...
The entry gives the generating function
  x^2*(1 + 1/sqrt(1 - 4*x))/(2 - 2*x - 2*x^2)
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x the series is, in normalised form,
  (-4*x^3 + x^2 + (x^2)*sqrt(R)) / (8*x^3 + 6*x^2 - 10*x + 2),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 22 2016) reads
  Conjecture: (-n+2)*a(n) +(5*n-12)*a(n-1) +(-3*n+8)*a(n-2) +2*(-2*n+5)*a(n-3)=0
The recurrence fails for n in [3] (small n, where the inhomogeneous part of the differential
equation is felt), so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a121320

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A121320: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((X ^ 2 - 4 * X ^ 3 + (X ^ 2) * S)
      * (2 - 10 * X + 6 * X ^ 2 + 8 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A121320. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (-(n : ℚ) + 2) * a n + (5 * (n : ℚ) - 12) * a (n - 1) + (-3 * (n : ℚ) + 8) * a (n - 2)
      + (-4 * (n : ℚ) + 10) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a121320
