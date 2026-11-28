import Mathlib

/-!
# A190725: Diagonal sums of Riordan matrix A118384.

Source: https://oeis.org/A190725
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 3, 14, 69, 355, 1872, 10037, 54459, 298138, ...
The entry gives the generating function
  (3+3*x-sqrt(1-6*x+x^2))/(2*(1+3*x+x^2)*sqrt(1-6*x+x^2))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = x^2 - 6*x + 1 the series is, in normalised form,
  (-x^2 + 6*x - 1 + (3*x + 3)*sqrt(R)) / (2*x^4 - 6*x^3 - 32*x^2 - 6*x + 2),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jul 24 2012) reads
  Conjecture: conjecture: n*(2*n-3)*a(n) +(-6*n^2+15*n-8)*a(n-1) +2*(-16*n^2+32*n-11)*a(n-2) +(-6*n^2+9*n-2)*a(n-3) +(2*n-1)*(n-2)*a(n-4) =0
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a190725

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 6 * X + X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A190725: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((-1 + 6 * X - X ^ 2 + (3 + 3 * X) * S)
      * (2 - 6 * X - 32 * X ^ 2 - 6 * X ^ 3 + 2 * X ^ 4 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A190725. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (2 * (n : ℚ) ^ 2 - 3 * (n : ℚ)) * a n + (-6 * (n : ℚ) ^ 2 + 15 * (n : ℚ) - 8) * a (n - 1)
      + (-32 * (n : ℚ) ^ 2 + 64 * (n : ℚ) - 22) * a (n - 2)
      + (-6 * (n : ℚ) ^ 2 + 9 * (n : ℚ) - 2) * a (n - 3)
      + (2 * (n : ℚ) ^ 2 - 5 * (n : ℚ) + 2) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a190725
