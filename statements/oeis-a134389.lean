import Mathlib

/-!
# A134389: A transform of floor((n+2)/2) with Hankel transform floor((n+2)/2)*(cos(Pi*n/2) + sin(Pi*n/2)).

Source: https://oeis.org/A134389
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 2, 5, 11, 24, 51, 108, 226, 472, ...
The entry gives the generating function
  ((2-x)/(1-2*x) + x*sqrt(1-4*x^2)/(1-2*x)^2)/2
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x^2 the series is, in normalised form,
  (2*x^2 - 5*x + 2 + (x)*sqrt(R)) / (8*x^2 - 8*x + 2),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Oct 25 2012) reads
  Conjecture: (n-1)*a(n) - 2*n*a(n-1) + 4*(4-n)*a(n-2) + 8*(n-3)*a(n-3) = 0
It involves a(n-3) and the offset is 0, so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a134389

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A134389: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((2 - 5 * X + 2 * X ^ 2 + (X) * S)
      * (2 - 8 * X + 8 * X ^ 2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A134389. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    ((n : ℚ) - 1) * a n + (-2 * (n : ℚ)) * a (n - 1) + (-4 * (n : ℚ) + 16) * a (n - 2)
      + (8 * (n : ℚ) - 24) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a134389
