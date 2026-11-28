import Mathlib

/-!
# A026031: a(n) = number of (s(0), s(1), ..., s(2n)) such that s(i) is a nonnegative integer and |s(i) - s(i-1)| = 1 for i = 1,2,...,n, s(0) = 3, s(2n) = 7. Also a(n) = T(2n,n-2), where T is defined in A026022.

Source: https://oeis.org/A026031
Credit: @vivanpoddar

The sequence (offset 2) begins 1, 6, 28, 120, 494, 1988, 7888, 31008, 121125, ...
The entry gives the generating function
  (1+x^2C^4)*C^6, where C = (1-sqrt(1-4x))/(2x)
(see the entry), taken times x^2 so that the exponent of x is the index n of the entry. It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x the series is, in normalised form,
  (-4*x^5 + 34*x^4 - 56*x^3 + 36*x^2 - 10*x + 1 + (-8*x^4 + 24*x^3 - 22*x^2 + 8*x - 1)*sqrt(R)) / (2*x^6),
which is the expression used below (the division by x^6 is the shift of the index by 6).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 22 2013) reads
  Conjecture: (n+6)*a(n) +10*(-n-4)*a(n-1) +2*(17*n+32)*a(n-2) +4*(-11*n+4)*a(n-3) +8*(2*n-5)*a(n-4)=0
It involves a(n-4) and the offset is 2, so it is stated for n >= 6.
-/

namespace OMA.S_oeis_a026031

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A026031: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 6)
    ((1 - 10 * X + 36 * X ^ 2 - 56 * X ^ 3 + 34 * X ^ 4 - 4 * X ^ 5 + (-1 + 8 * X - 22 * X ^ 2 + 24 * X ^ 3 - 8 * X ^ 4) * S)
      * (2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A026031. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    ((n : ℚ) + 6) * a n + (-10 * (n : ℚ) - 40) * a (n - 1) + (34 * (n : ℚ) + 64) * a (n - 2)
      + (-44 * (n : ℚ) + 16) * a (n - 3) + (16 * (n : ℚ) - 40) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a026031
