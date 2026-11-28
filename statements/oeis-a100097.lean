import Mathlib

/-!
# A100097: An inverse Chebyshev transform of the Pell numbers.

Source: https://oeis.org/A100097
Credit: @vivanpoddar

The sequence (offset 0) begins 0, 1, 2, 8, 20, 64, 172, 512, 1416, ...
The entry gives the generating function
  x*sqrt(1-4*x^2)*(sqrt(1-4*x^2)+2*x)/((1-4*x^2)*(1-8*x^2))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x^2 the series is, in normalised form,
  (-4*x^3 + x + (2*x^2)*sqrt(R)) / (32*x^4 - 12*x^2 + 1),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Nov 24 2012) reads
  Conjecture: (-n+2)*a(n) +(-n+3)*a(n-1) +4*(3*n-7)*a(n-2) +4*(3*n-10)*a(n-3) +32*(-n+3)*a(n-4) +32*(-n+4)*a(n-5)=0
It involves a(n-5) and the offset is 0, so it is stated for n >= 5.
-/

namespace OMA.S_oeis_a100097

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A100097: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((X - 4 * X ^ 3 + (2 * X ^ 2) * S)
      * (1 - 12 * X ^ 2 + 32 * X ^ 4 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A100097. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    (-(n : ℚ) + 2) * a n + (-(n : ℚ) + 3) * a (n - 1) + (12 * (n : ℚ) - 28) * a (n - 2)
      + (12 * (n : ℚ) - 40) * a (n - 3) + (-32 * (n : ℚ) + 96) * a (n - 4)
      + (-32 * (n : ℚ) + 128) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a100097
