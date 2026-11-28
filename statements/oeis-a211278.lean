import Mathlib

/-!
# A211278: a(n) is the number of n-lettered words in the alphabet {1, 2, 3} with as many occurrences of the substring (consecutive subword) [1, 1] as of [2, 3].

Source: https://oeis.org/A211278
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 3, 7, 16, 38, 95, 248, 668, 1838, ...
The entry gives the generating function
  (1 + sqrt((1 + x) / (1 - 3*x))) / (1 - x)^2 / 2
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = -3*x^2 - 2*x + 1 the series is, in normalised form,
  (1 - 3*x + (1)*sqrt(R)) / (-6*x^3 + 14*x^2 - 10*x + 2),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 09 2013) reads
  Conjecture: n*a(n) - 4*n*a(n-1) +2*(n+3)*a(n-2) + 4*(n-3)*a(n-3) + 3*(-n+2)*a(n-4) = 0
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a211278

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 2 * X - 3 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A211278: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((1 - 3 * X + S)
      * (2 - 10 * X + 14 * X ^ 2 - 6 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A211278. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (n : ℚ) * a n + (-4 * (n : ℚ)) * a (n - 1) + (2 * (n : ℚ) + 6) * a (n - 2)
      + (4 * (n : ℚ) - 12) * a (n - 3) + (-3 * (n : ℚ) + 6) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a211278
