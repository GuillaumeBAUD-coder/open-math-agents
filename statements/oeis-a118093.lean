import Mathlib

/-!
# A118093: Numbers of rooted hypermaps on the torus with n darts (darts are semi-edges in the particular case of ordinary maps).

Source: https://oeis.org/A118093
Credit: @vivanpoddar

The sequence (offset 3) begins 1, 15, 165, 1611, 14805, 131307, 1138261, 9713835, 81968469, ...
The entry gives the generating function
  (1 - 7*x + 4*x^2 - (1 - 3*x)*sqrt(1 - 8*x))/(8*(1 + x)*(1 - 8*x))
(Gheorghe Coserea, Nov 06 2018). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 8*x the series is, in normalised form,
  (4*x^2 - 7*x + 1 + (3*x - 1)*sqrt(R)) / (-64*x^2 - 56*x + 8),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Apr 05 2018) reads
  Conjecture: +n*(5*n-17)*a(n) -15*(n-1)*(5*n-16)*a(n-1) +12*(20*n^2-103*n+140)*a(n-2) +32*(5*n-12)*(2*n-5)*a(n-3)=0
It involves a(n-3) and the offset is 3, so it is stated for n >= 6.
-/

namespace OMA.S_oeis_a118093

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 8 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A118093: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((1 - 7 * X + 4 * X ^ 2 + (-1 + 3 * X) * S)
      * (8 - 56 * X - 64 * X ^ 2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A118093. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    (5 * (n : ℚ) ^ 2 - 17 * (n : ℚ)) * a n
      + (-75 * (n : ℚ) ^ 2 + 315 * (n : ℚ) - 240) * a (n - 1)
      + (240 * (n : ℚ) ^ 2 - 1236 * (n : ℚ) + 1680) * a (n - 2)
      + (320 * (n : ℚ) ^ 2 - 1568 * (n : ℚ) + 1920) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a118093
