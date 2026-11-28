import Mathlib

/-!
# A141342: A transform of the Fibonacci numbers.

Source: https://oeis.org/A141342
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, -1, 3, -13, 65, -353, 2025, -12077, ...
The entry gives the generating function
  1/(1-2*x-2*x^2+x*sqrt(1+8*x+4*x^2))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 4*x^2 + 8*x + 1 the series is, in normalised form,
  (-2*x^2 - 2*x + 1 + (-x)*sqrt(R)) / (-x^2 - 4*x + 1),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Nov 14 2011) reads
  Conjecture: (n-1)*a(n) +4*(n-4)*a(n-1) + (65-29*n)*a(n-2) +12*(7-2*n)*a(n-3)+ 4*(4-n)*a(n-4) =0
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a141342

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 + 8 * X + 4 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A141342: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((1 - 2 * X - 2 * X ^ 2 + (-X) * S)
      * (1 - 4 * X - X ^ 2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A141342. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℚ) - 1) * a n + (4 * (n : ℚ) - 16) * a (n - 1) + (-29 * (n : ℚ) + 65) * a (n - 2)
      + (-24 * (n : ℚ) + 84) * a (n - 3) + (-4 * (n : ℚ) + 16) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a141342
