import Mathlib

/-!
# A126323: Number of branches of length 1 in all hex trees with n edges.

Source: https://oeis.org/A126323
Credit: @vivanpoddar

The sequence (offset 0) begins 0, 3, 2, 15, 80, 399, 1956, 9546, 46552, ...
The entry gives the generating function
  (1-3z)^2*[2-9z+5z^2-(2-3z)sqrt(1-6z+5z^2)]/[2z^2*sqrt(1-6z+5z^2)]
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 5*x^2 - 6*x + 1 the series is, in normalised form,
  (135*x^5 - 342*x^4 + 318*x^3 - 136*x^2 + 27*x - 2 + (45*x^4 - 111*x^3 + 77*x^2 - 21*x + 2)*sqrt(R)) / (10*x^4 - 12*x^3 + 2*x^2),
which is the expression used below (the division by x^2 is the shift of the index by 2).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 17 2016) reads
  Conjecture: -(n+2)*(1176*n^2+350135*n-2095015)*a(n) +3*(-392*n^3+1110577*n^2-6230546*n-1231580)*a(n-1) +(43512*n^3-9103273*n^2+68264245*n-103131090) *a(n-2) -15*(n-4)*(2744*n^2-398547*n+1917624)*a(n-3)=0
The recurrence fails for n in [3] (small n, where the inhomogeneous part of the differential
equation is felt), so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a126323

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 6 * X + 5 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A126323: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 2)
    ((-2 + 27 * X - 136 * X ^ 2 + 318 * X ^ 3 - 342 * X ^ 4 + 135 * X ^ 5 + (2 - 21 * X + 77 * X ^ 2 - 111 * X ^ 3 + 45 * X ^ 4) * S)
      * (2 - 12 * X + 10 * X ^ 2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A126323. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (-1176 * (n : ℚ) ^ 3 - 352487 * (n : ℚ) ^ 2 + 1394745 * (n : ℚ) + 4190030) * a n
      + (-1176 * (n : ℚ) ^ 3 + 3331731 * (n : ℚ) ^ 2 - 18691638 * (n : ℚ) - 3694740) * a (n - 1)
      + (43512 * (n : ℚ) ^ 3 - 9103273 * (n : ℚ) ^ 2 + 68264245 * (n : ℚ) - 103131090) * a (n - 2)
      + (-41160 * (n : ℚ) ^ 3 + 6142845 * (n : ℚ) ^ 2 - 52677180 * (n : ℚ) + 115057440) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a126323
