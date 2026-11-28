import Mathlib

/-!
# A182892: Number of weighted lattice paths in L_n having no (1,0)-steps of weight 2 at level 0.

Source: https://oeis.org/A182892
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 1, 3, 7, 15, 35, 83, 197, ...
The entry gives the generating function
  1/( z^2+sqrt((1+z+z^2)*(1-3*z+z^2)) )
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = x^4 - 2*x^3 - x^2 - 2*x + 1 the series is, in normalised form,
  (-x^2 + (1)*sqrt(R)) / (-2*x^3 - x^2 - 2*x + 1),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 14 2016) reads
  Conjecture: n*a(n) +(n-2)*a(n-1) +2*(-9*n+16)*a(n-2) +5*(2*n-5)*a(n-3) +(10*n-33) *a(n-4) +2*(26*n-109)*a(n-5) +(13*n-37)*a(n-6) +(13*n-63) *a(n-7) +10*(-n+7) *a(n-8)=0
It involves a(n-8) and the offset is 0, so it is stated for n >= 8.
-/

namespace OMA.S_oeis_a182892

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A182892: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((-X ^ 2 + S)
      * (1 - 2 * X - X ^ 2 - 2 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A182892. -/
theorem main : ∀ n : ℕ, 8 ≤ n →
    (n : ℚ) * a n + ((n : ℚ) - 2) * a (n - 1) + (-18 * (n : ℚ) + 32) * a (n - 2)
      + (10 * (n : ℚ) - 25) * a (n - 3) + (10 * (n : ℚ) - 33) * a (n - 4)
      + (52 * (n : ℚ) - 218) * a (n - 5) + (13 * (n : ℚ) - 37) * a (n - 6)
      + (13 * (n : ℚ) - 63) * a (n - 7) + (-10 * (n : ℚ) + 70) * a (n - 8) = 0 := by
  sorry

end OMA.S_oeis_a182892
