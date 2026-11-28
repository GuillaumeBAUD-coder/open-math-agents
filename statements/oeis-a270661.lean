import Mathlib

/-!
# A270661: a(n) = Sum_{k=0..n}((binomial(2*k,k)*Sum_{i=0..n-k}(binomial(k+1,n-k-i)*binomial(k+i,k)))/(k+1)^2)*(n+1).

Source: https://oeis.org/A270661
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 5, 14, 45, 164, 662, 2862, 12957, 60590, ...
The entry gives the generating function
  C((x^2+x)/(1-x))*((x^2-2*x-1)/(x^2-1)*(1+x)/(1-x))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 4*x^3 + x^2 - 6*x + 1 the series is, in normalised form,
  (x^3 - 3*x^2 + x + 1 + (x^2 - 2*x - 1)*sqrt(R)) / (2*x^4 - 2*x^3 - 2*x^2 + 2*x),
which is the expression used below (the division by x^1 is the shift of the index by 1).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 07 2016) reads
  Conjecture: (n+1)*a(n) -4* n*a(n-1) +(-13*n+33)*a(n-2) +2*(8*n-17)*a(n-3) +(19*n-69)*a(n-4) +4*(-4*n+15)*a(n-5) +7*(-n+5)*a(n-6) +2*(2*n-13)*a(n-7)=0
It involves a(n-7) and the offset is 0, so it is stated for n >= 7.
-/

namespace OMA.S_oeis_a270661

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 6 * X + X ^ 2 + 4 * X ^ 3

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A270661: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 1)
    ((1 + X - 3 * X ^ 2 + X ^ 3 + (-1 - 2 * X + X ^ 2) * S)
      * (2 - 2 * X - 2 * X ^ 2 + 2 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A270661. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    ((n : ℚ) + 1) * a n + (-4 * (n : ℚ)) * a (n - 1) + (-13 * (n : ℚ) + 33) * a (n - 2)
      + (16 * (n : ℚ) - 34) * a (n - 3) + (19 * (n : ℚ) - 69) * a (n - 4)
      + (-16 * (n : ℚ) + 60) * a (n - 5) + (-7 * (n : ℚ) + 35) * a (n - 6)
      + (4 * (n : ℚ) - 26) * a (n - 7) = 0 := by
  sorry

end OMA.S_oeis_a270661
