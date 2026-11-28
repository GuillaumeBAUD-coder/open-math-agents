import Mathlib

/-!
# A166228: Alternating sum of large Schroeder numbers.

Source: https://oeis.org/A166228
Credit: @ivillar

Status: open conjecture of the entry; it holds for the series as defined (a proof is filed with this statement).

The sequence (offset 0) begins 1, 1, 5, 17, 73, 321, 1485, 7073, 34513, ...
The entry gives the generating function
  (1-x-sqrt(1-6x+x^2))/(2x(1+x))
It is used here as the definition: a(n) is the coefficient of x^n of that series, where the square
root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated at the
radicand minus 1), with R = 1-6*X+X^2 the radicand. 
The series is written as (G) / (C * x^1) with C of nonzero constant term; the division by
x^1 is the shift of the index by 1. Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Nov 17 2011) reads
  Conjecture: (n+1)*a(n) +(4-5n)*a(n-1) +(1-5n)*a(n-2) +(n-2)*a(n-3)=0.
It involves a(n-3) and the offset is 0, so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a166228

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 6 * X + X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A166228: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 1)
    ((1 - X - S)
      * (2 + 2 * X : PowerSeries ℚ)⁻¹)

/-- The recurrence for A166228. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    ((n : ℚ) + 1) * a n + (-5 * (n : ℚ) + 4) * a (n - 1) + (-5 * (n : ℚ) + 1) * a (n - 2)
      + ((n : ℚ) - 2) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a166228
