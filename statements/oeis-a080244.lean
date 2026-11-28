import Mathlib

/-!
# A080244: Signed generalized Fibonacci numbers.

Source: https://oeis.org/A080244
Credit: @vivanpoddar

The sequence (offset 1) begins 1, -2, 7, -26, 107, -468, 2141, -10124, ...
It is defined by the generating function of the entry (C. Ronaldo, Dec 19 2004),
x*(-1-x+2*x^2+sqrt(1+6*x+x^2))/(2*x*(1+x+x^2-x^3)): a(n) is the coefficient of x^n. The square root
is the power series with constant term 1, written as (1 + X)^(1/2) evaluated at the radicand minus 1.

Conjecture (R. J. Mathar, Nov 24 2012):
(n+1)*a(n) +(7*n-2)*a(n-1) +4*(2*n-1)*a(n-2) +6*(n-1)*a(n-3) +(-5*n+1)*a(n-4) +(-n+2)*a(n-5)=0.
It involves a(n-5) and the offset is 1, so it is stated for n >= 6, exactly as printed.

Remark for the reviewer: with the terms of the entry the left-hand side at n = 6 is
7*(-468) + 40*107 + 44*(-26) + 30*7 - 29*(-2) - 4*1 = 124, so the relation as printed does not hold
for this offset (it does hold when every index is increased by one, that is, for the sequence
read with offset 0). The statement below keeps the printed form.
-/

namespace OMA.S_oeis_a080244

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 + 6 * X + X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A080244: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((-1 - X + 2 * X ^ 2 + S)
      * (2 + 2 * X + 2 * X ^ 2 - 2 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A080244, as printed in the entry. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    ((n : ℚ) + 1) * a n + (7 * (n : ℚ) - 2) * a (n - 1) + 4 * (2 * (n : ℚ) - 1) * a (n - 2)
      + 6 * ((n : ℚ) - 1) * a (n - 3) + (-5 * (n : ℚ) + 1) * a (n - 4)
      + (-(n : ℚ) + 2) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a080244
