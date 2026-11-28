import Mathlib

/-!
# A165540: Number of permutations of length n which avoid the patterns 1234 and 2341.

Source: https://oeis.org/A165540
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 2, 6, 22, 89, 376, 1611, 6901, ...
The entry gives the generating function
  1 + ((2-10*z+9*z^2+7*z^3-4*z^4)*sqrt(1-4*z) - (2-16*z+41*z^2-39*z^3+12*z^4)) / ((1-4*z)*(1-3*z+z^2)*((1-z)*sqrt(1-4*z) + (1-3*z)))
(David Bevan, Jun 23 2014). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x the series is, in normalised form,
  (20*x^5 - 77*x^4 + 122*x^3 - 78*x^2 + 21*x - 2 + (13*x^4 - 50*x^3 + 48*x^2 - 17*x + 2)*sqrt(R)) / (-8*x^6 + 26*x^5 - 14*x^4 + 2*x^3),
which is the expression used below (the division by x^3 is the shift of the index by 3).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 14 2016) reads
  Conjecture: +(14681*n+187954)*(n+3) *a(n) +(14681*n^2-2696783*n-4897218) *a(n-1) +(-888761*n^2+12771539*n+5490342) *a(n-2) +2*(1635223*n^2-14850835*n+13281012) *a(n-3) +2*(-1908503*n^2+15402653*n-25889820) *a(n-4) +156*(2*n-7)*(3301*n-14374) *a(n-5)=0
It involves a(n-5) and the offset is 0, so it is stated for n >= 5.
-/

namespace OMA.S_oeis_a165540

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A165540: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 3)
    ((-2 + 21 * X - 78 * X ^ 2 + 122 * X ^ 3 - 77 * X ^ 4 + 20 * X ^ 5 + (2 - 17 * X + 48 * X ^ 2 - 50 * X ^ 3 + 13 * X ^ 4) * S)
      * (2 - 14 * X + 26 * X ^ 2 - 8 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A165540. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    (14681 * (n : ℚ) ^ 2 + 231997 * (n : ℚ) + 563862) * a n
      + (14681 * (n : ℚ) ^ 2 - 2696783 * (n : ℚ) - 4897218) * a (n - 1)
      + (-888761 * (n : ℚ) ^ 2 + 12771539 * (n : ℚ) + 5490342) * a (n - 2)
      + (3270446 * (n : ℚ) ^ 2 - 29701670 * (n : ℚ) + 26562024) * a (n - 3)
      + (-3817006 * (n : ℚ) ^ 2 + 30805306 * (n : ℚ) - 51779640) * a (n - 4)
      + (1029912 * (n : ℚ) ^ 2 - 8089380 * (n : ℚ) + 15696408) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a165540
