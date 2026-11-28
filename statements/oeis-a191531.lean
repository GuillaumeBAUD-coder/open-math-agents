import Mathlib

/-!
# A191531: Sum of lengths of initial and final horizontal segments over all dispersed Dyck paths of semilength n (i.e., over all Motzkin paths of length n with no (1,0)-steps at positive heights).

Source: https://oeis.org/A191531
Credit: @vivanpoddar

The sequence (offset 0) begins 0, 1, 2, 5, 10, 21, 40, 79, 148, ...
The entry gives the generating function
  z*(3-2*z-sqrt(1-4*z^2))/((1-z)^2*(1-2*z+sqrt(1-4*z^2)))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x^2 the series is, in normalised form,
  (2*x - 1 + (1 - x)*sqrt(R)) / (-2*x^3 + 5*x^2 - 4*x + 1),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 14 2016) reads
  Conjecture: +n*(n-3)*a(n) -2*(n^2-2*n-2)*a(n-1) -(3*n^2-21*n+32)*a(n-2) +2*(n-2)*(4*n-13)*a(n-3) -4*(n-2)*(n-3)*a(n-4)=0
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a191531

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A191531: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((-1 + 2 * X + (1 - X) * S)
      * (1 - 4 * X + 5 * X ^ 2 - 2 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A191531. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℚ) ^ 2 - 3 * (n : ℚ)) * a n + (-2 * (n : ℚ) ^ 2 + 4 * (n : ℚ) + 4) * a (n - 1)
      + (-3 * (n : ℚ) ^ 2 + 21 * (n : ℚ) - 32) * a (n - 2)
      + (8 * (n : ℚ) ^ 2 - 42 * (n : ℚ) + 52) * a (n - 3)
      + (-4 * (n : ℚ) ^ 2 + 20 * (n : ℚ) - 24) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a191531
