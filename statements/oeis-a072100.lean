import Mathlib

/-!
# A072100: Column 2 of the array m(i,1)=m(1,j)=1 m(i,j)=m(i-1,j-1)+m(i-1,j+1) (a(n)=m(n,2)).

Source: https://oeis.org/A072100
Credit: @vivanpoddar

The sequence (offset 1) begins 1, 2, 3, 5, 8, 14, 24, 44, 79, ...
The entry gives the generating function
  x*(sqrt(1+2*x)+1/sqrt(1-2*x))/((1-x)*(sqrt(1+2*x)+sqrt(1-2*x)))
(Paul Barry, Oct 12 2004). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x^2 the series is, in normalised form,
  (-2*x^2 + x + (x)*sqrt(R)) / (4*x^2 - 6*x + 2),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Nov 26 2012) reads
  Conjecture: (-n+1)*a(n) +(n+1)*a(n-1) +2*(2*n-7)*a(n-2) +4*(-n+3)*a(n-3)=0
It involves a(n-3) and the offset is 1, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a072100

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A072100: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((X - 2 * X ^ 2 + (X) * S)
      * (2 - 6 * X + 4 * X ^ 2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A072100. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (-(n : ℚ) + 1) * a n + ((n : ℚ) + 1) * a (n - 1) + (4 * (n : ℚ) - 14) * a (n - 2)
      + (-4 * (n : ℚ) + 12) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a072100
