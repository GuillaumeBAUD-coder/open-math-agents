import Mathlib

/-!
# A089324: Number of lattice paths from (0,0) to the line x+y=n that use the step set {(0,1),(1,0),(2,0),(3,0),...} and never pass below y=x.

Source: https://oeis.org/A089324
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 2, 3, 7, 12, 29, 53, 130, ...
The entry gives the generating function
  2/[(1-z)^2+sqrt(1-6z^2+z^4)]
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = x^4 - 6*x^2 + 1 the series is, in normalised form,
  (-x^2 + 2*x - 1 + (1)*sqrt(R)) / (2*x^3 - 6*x^2 + 2*x),
which is the expression used below (the division by x^1 is the shift of the index by 1).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Nov 24 2012) reads
  Conjecture: (n+1)*a(n) +3*(-n-1)*a(n-1) +(-5*n+13)*a(n-2) +18*(n-2)*a(n-3) +(-5*n+7)*a(n-4) +3*(-n+5)*a(n-5) +(n-5)*a(n-6)=0
It involves a(n-6) and the offset is 0, so it is stated for n >= 6.
-/

namespace OMA.S_oeis_a089324

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 6 * X ^ 2 + X ^ 4

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A089324: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 1)
    ((-1 + 2 * X - X ^ 2 + S)
      * (2 - 6 * X + 2 * X ^ 2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A089324. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    ((n : ℚ) + 1) * a n + (-3 * (n : ℚ) - 3) * a (n - 1) + (-5 * (n : ℚ) + 13) * a (n - 2)
      + (18 * (n : ℚ) - 36) * a (n - 3) + (-5 * (n : ℚ) + 7) * a (n - 4)
      + (-3 * (n : ℚ) + 15) * a (n - 5) + ((n : ℚ) - 5) * a (n - 6) = 0 := by
  sorry

end OMA.S_oeis_a089324
