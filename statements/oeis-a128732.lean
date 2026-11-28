import Mathlib

/-!
# A128732: Number DL's in all skew Dyck paths of semilength n.

Source: https://oeis.org/A128732
Credit: @vivanpoddar

The sequence (offset 0) begins 0, 0, 1, 5, 23, 106, 493, 2312, 10917, ...
The entry gives the generating function
  z*(1 - z - sqrt(1 - 6*z + 5*z^2))/(1 - 6*z + 5*z^2 +(1+z)*sqrt(1 - 6*z + 5*z^2))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 5*x^2 - 6*x + 1 the series is, in normalised form,
  (5*x - 1 + (1 - 2*x)*sqrt(R)) / (10*x^2 - 22*x + 4),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 17 2016) reads
  Conjecture: +2*n*(3*n-1)*a(n) -n*(39*n-37)*a(n-1) +4*(12*n^2-22*n-15)*a(n-2) -5*(3*n+2)*(n-3)*a(n-3)=0
It involves a(n-3) and the offset is 0, so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a128732

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 6 * X + 5 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A128732: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((-1 + 5 * X + (1 - 2 * X) * S)
      * (4 - 22 * X + 10 * X ^ 2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A128732. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    (6 * (n : ℚ) ^ 2 - 2 * (n : ℚ)) * a n + (-39 * (n : ℚ) ^ 2 + 37 * (n : ℚ)) * a (n - 1)
      + (48 * (n : ℚ) ^ 2 - 88 * (n : ℚ) - 60) * a (n - 2)
      + (-15 * (n : ℚ) ^ 2 + 35 * (n : ℚ) + 30) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a128732
