import Mathlib

/-!
# A100095: An inverse Chebyshev transform of the Fibonacci numbers.

Source: https://oeis.org/A100095
Credit: @vivanpoddar

The sequence (offset 0) begins 0, 1, 1, 5, 7, 25, 41, 125, 225, ...
The entry gives the generating function
  (x^2*sqrt(1-4*x^2)+x*(1-4*x^2))/((1-4*x^2)*(1-5*x^2))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x^2 the series is, in normalised form,
  (-4*x^3 + x + (x^2)*sqrt(R)) / (20*x^4 - 9*x^2 + 1),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Nov 24 2012) reads
  Conjecture: (-n+2)*a(n) +(-n+3)*a(n-1) +(9*n-22)*a(n-2) +(9*n-31)*a(n-3) +20*(-n+3)*a(n-4) +20*(-n+4)*a(n-5)=0
It involves a(n-5) and the offset is 0, so it is stated for n >= 5.
-/

namespace OMA.S_oeis_a100095

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A100095: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((X - 4 * X ^ 3 + (X ^ 2) * S)
      * (1 - 9 * X ^ 2 + 20 * X ^ 4 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A100095. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    (-(n : ℚ) + 2) * a n + (-(n : ℚ) + 3) * a (n - 1) + (9 * (n : ℚ) - 22) * a (n - 2)
      + (9 * (n : ℚ) - 31) * a (n - 3) + (-20 * (n : ℚ) + 60) * a (n - 4)
      + (-20 * (n : ℚ) + 80) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a100095
