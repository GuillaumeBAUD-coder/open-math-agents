import Mathlib

/-!
# A191526: Number left factors of Dyck paths of length n and having no hills; a hill is a (1,1)-step starting at level 0 and followed by a (1,-1)-step.

Source: https://oeis.org/A191526
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 1, 2, 4, 7, 13, 24, 46, ...
The entry gives the generating function
  (((1+z)*sqrt(1-4*z^2)-(1-z)*(1-2*z))*1/2)/(z*(1-2*z)*(2+z^2))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x^2 the series is, in normalised form,
  (-2*x^2 + 3*x - 1 + (x + 1)*sqrt(R)) / (-4*x^4 + 2*x^3 - 8*x^2 + 4*x),
which is the expression used below (the division by x^1 is the shift of the index by 1).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 14 2016) reads
  Conjecture: -2*(n+1)*(3*n-10)*a(n) +12*(n-5)*a(n-1) +(21*n^2-97*n+122)*a(n-2) +6*(n-5)*a(n-3) +4*(n-2)*(3*n-7)*a(n-4)=0
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a191526

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A191526: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 1)
    ((-1 + 3 * X - 2 * X ^ 2 + (1 + X) * S)
      * (4 - 8 * X + 2 * X ^ 2 - 4 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A191526. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (-6 * (n : ℚ) ^ 2 + 14 * (n : ℚ) + 20) * a n + (12 * (n : ℚ) - 60) * a (n - 1)
      + (21 * (n : ℚ) ^ 2 - 97 * (n : ℚ) + 122) * a (n - 2) + (6 * (n : ℚ) - 30) * a (n - 3)
      + (12 * (n : ℚ) ^ 2 - 52 * (n : ℚ) + 56) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a191526
