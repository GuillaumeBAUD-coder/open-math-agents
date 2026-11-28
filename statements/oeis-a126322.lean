import Mathlib

/-!
# A126322: Number of hex trees with n edges and no branches of length 1.

Source: https://oeis.org/A126322
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 0, 9, 27, 90, 297, 1053, 3888, 14742, ...
The entry gives the generating function
  (1-3z+9z^2)[1-3z-sqrt(1-6z+9z^2-36z^4)]/(18z^4)
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = -36*x^4 + 9*x^2 - 6*x + 1 the series is, in normalised form,
  (-27*x^3 + 18*x^2 - 6*x + 1 + (-9*x^2 + 3*x - 1)*sqrt(R)) / (18*x^4),
which is the expression used below (the division by x^4 is the shift of the index by 4).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 17 2016) reads
  Conjecture: (n+4)*(25*n^2+230*n+1137)*a(n) +3*(-50*n^3-585*n^2-3169*n-4248) *a(n-1) +9*(25*n^3+255*n^2+932*n-1764) *a(n-2) +29484*a(n-3) -36*(n-4) *(25*n^2+280*n+1392) *a(n-4)=0
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a126322

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 6 * X + 9 * X ^ 2 - 36 * X ^ 4

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A126322: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 4)
    ((1 - 6 * X + 18 * X ^ 2 - 27 * X ^ 3 + (-1 + 3 * X - 9 * X ^ 2) * S)
      * (18 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A126322. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (25 * (n : ℚ) ^ 3 + 330 * (n : ℚ) ^ 2 + 2057 * (n : ℚ) + 4548) * a n
      + (-150 * (n : ℚ) ^ 3 - 1755 * (n : ℚ) ^ 2 - 9507 * (n : ℚ) - 12744) * a (n - 1)
      + (225 * (n : ℚ) ^ 3 + 2295 * (n : ℚ) ^ 2 + 8388 * (n : ℚ) - 15876) * a (n - 2)
      + (29484) * a (n - 3)
      + (-900 * (n : ℚ) ^ 3 - 6480 * (n : ℚ) ^ 2 - 9792 * (n : ℚ) + 200448) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a126322
