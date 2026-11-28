import Mathlib

/-!
# A116881: Row sums of triangle A116880 (generalized Catalan C(1,2)).

Source: https://oeis.org/A116881
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 4, 23, 150, 1037, 7408, 54035, 399850, 2990105, ...
The entry gives the generating function
  (32*x^2+12*sqrt(1-8*x)*x-4*x)/(-32*x^3+sqrt(1-8*x)*(8*x^2+7*x-1)-36*x^2-3*x+1)
(Vladimir Kruchinin, Nov 23 2014). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 8*x the series is, in normalised form,
  (16*x^2 - 10*x + 1 + (10*x + 1)*sqrt(R)) / (-16*x^3 - 30*x^2 - 12*x + 2),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 22 2016) reads
  Conjecture: n*(3*n-4)*a(n) +(-21*n^2+43*n-10)*a(n-1) -4*(3*n-1)*(2*n-1)*a(n-2)=0
It involves a(n-2) and the offset is 0, so it is stated for n >= 2.
-/

namespace OMA.S_oeis_a116881

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 8 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A116881: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((1 - 10 * X + 16 * X ^ 2 + (1 + 10 * X) * S)
      * (2 - 12 * X - 30 * X ^ 2 - 16 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A116881. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    (3 * (n : ℚ) ^ 2 - 4 * (n : ℚ)) * a n + (-21 * (n : ℚ) ^ 2 + 43 * (n : ℚ) - 10) * a (n - 1)
      + (-24 * (n : ℚ) ^ 2 + 20 * (n : ℚ) - 4) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a116881
