import Mathlib

/-!
# A190736: Diagonal sums of the Riordan matrix A121576.

Source: https://oeis.org/A190736
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 2, 7, 29, 139, 731, 4096, 24005, 145420, ...
The entry gives the generating function
  (4-5*x-2*x^2-(2+x)*sqrt(1-8*x+4*x^2))/(2*(1-x+2*x^2+x^3))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 4*x^2 - 8*x + 1 the series is, in normalised form,
  (-2*x^2 - 5*x + 4 + (-x - 2)*sqrt(R)) / (2*x^3 + 4*x^2 - 2*x + 2),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jul 24 2012) reads
  Conjecture: n*(11*n-35)*a(n) + 3*(-33*n^2+149*n-136)*a(n-1) +2*(77*n^2-377*n+396)*a(n-2) +(-209*n^2+1061*n-1200)*a(n-3) +12*(-11*n+30)*a(n-4) +4*(11*n-24)*(n-4)*a(n-5)=0
It involves a(n-5) and the offset is 0, so it is stated for n >= 5.
-/

namespace OMA.S_oeis_a190736

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 8 * X + 4 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A190736: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((4 - 5 * X - 2 * X ^ 2 + (-2 - X) * S)
      * (2 - 2 * X + 4 * X ^ 2 + 2 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A190736. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    (11 * (n : ℚ) ^ 2 - 35 * (n : ℚ)) * a n
      + (-99 * (n : ℚ) ^ 2 + 447 * (n : ℚ) - 408) * a (n - 1)
      + (154 * (n : ℚ) ^ 2 - 754 * (n : ℚ) + 792) * a (n - 2)
      + (-209 * (n : ℚ) ^ 2 + 1061 * (n : ℚ) - 1200) * a (n - 3)
      + (-132 * (n : ℚ) + 360) * a (n - 4)
      + (44 * (n : ℚ) ^ 2 - 272 * (n : ℚ) + 384) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a190736
