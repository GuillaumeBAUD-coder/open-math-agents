import Mathlib

/-!
# A114851: Number of lambda calculus terms of size n, where size(lambda x.M) = 2 + size(M), size(M N) = 2 + size(M) + size(N), and size(V) = 1 + i for a variable V bound by the i-th enclosing lambda (corresponding to a binary encoding).

Source: https://oeis.org/A114851
Credit: @vivanpoddar

The sequence (offset 0) begins 0, 0, 1, 1, 2, 2, 4, 5, 10, ...
The entry gives the generating function
  ( 1 - x - x^2 + x^3 - sqrt((1 + x - x^2 - x^3)^2 - 4*(x - 2*x^3 + x^4)) ) / (2*(x^2 - x^3))
(Michael Somos, Jan 28 2014). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = x^6 + 2*x^5 - 5*x^4 + 4*x^3 - x^2 - 2*x + 1 the series is, in normalised form,
  (x^3 - x^2 - x + 1 + (-1)*sqrt(R)) / (-2*x^3 + 2*x^2),
which is the expression used below (the division by x^2 is the shift of the index by 2).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Mar 04 2015) reads
  Conjecture: (n+2)*a(n) + 2*(-n-1)*a(n-1) + (-n+2)*a(n-2) + 4*(n-2)*a(n-3) + (-5*n+18)*a(n-4) + 2*(n-4)*a(n-5) + (n-6)*a(n-6) = 0
It involves a(n-6) and the offset is 0, so it is stated for n >= 6.
-/

namespace OMA.S_oeis_a114851

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 2 * X - X ^ 2 + 4 * X ^ 3 - 5 * X ^ 4 + 2 * X ^ 5 + X ^ 6

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A114851: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 2)
    ((1 - X - X ^ 2 + X ^ 3 - S)
      * (2 - 2 * X : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A114851. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    ((n : ℚ) + 2) * a n + (-2 * (n : ℚ) - 2) * a (n - 1) + (-(n : ℚ) + 2) * a (n - 2)
      + (4 * (n : ℚ) - 8) * a (n - 3) + (-5 * (n : ℚ) + 18) * a (n - 4)
      + (2 * (n : ℚ) - 8) * a (n - 5) + ((n : ℚ) - 6) * a (n - 6) = 0 := by
  sorry

end OMA.S_oeis_a114851
