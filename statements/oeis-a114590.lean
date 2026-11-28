import Mathlib

/-!
# A114590: Number of peaks at even levels in all hill-free Dyck paths of semilength n+2 (a hill in a Dyck path is a peak at level 1).

Source: https://oeis.org/A114590
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 2, 8, 28, 103, 382, 1432, 5408, 20546, ...
The entry gives the generating function
  (1+2*z^2-(1+2*z)*sqrt(1-4*z))/(2*z^2*(2+z)^2*sqrt(1-4*z))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x the series is, in normalised form,
  (8*x^2 + 2*x - 1 + (2*x^2 + 1)*sqrt(R)) / (-8*x^5 - 30*x^4 - 24*x^3 + 8*x^2),
which is the expression used below (the division by x^2 is the shift of the index by 2).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Nov 15 2012) reads
  Conjecture: 2*(n+2)*a(n) +(-7*n-9)*a(n-1) -18*a(n-2) +2*(-7*n+19)*a(n-3) +4*(-2*n+3)*a(n-4)=0
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a114590

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A114590: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 2)
    ((-1 + 2 * X + 8 * X ^ 2 + (1 + 2 * X ^ 2) * S)
      * (8 - 24 * X - 30 * X ^ 2 - 8 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A114590. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (2 * (n : ℚ) + 4) * a n + (-7 * (n : ℚ) - 9) * a (n - 1) + (-18) * a (n - 2)
      + (-14 * (n : ℚ) + 38) * a (n - 3) + (-8 * (n : ℚ) + 12) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a114590
