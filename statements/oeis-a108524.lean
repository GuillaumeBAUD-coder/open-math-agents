import Mathlib

/-!
# A108524: Number of ordered rooted trees with n generators.

Source: https://oeis.org/A108524
Credit: @vivanpoddar

The sequence (offset 1) begins 1, 2, 7, 32, 166, 926, 5419, 32816, 203902, ...
The entry gives the generating function
  (sqrt(4*x^2-8*x+1) - 1)/(2*x-4)
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 4*x^2 - 8*x + 1 the series is, in normalised form,
  (1 + (-1)*sqrt(R)) / (4 - 2*x),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Nov 14 2011) reads
  Conjecture: 2*n*a(n) +(24-17*n)*a(n-1) +4*(4*n-9)*a(n-2) +4*(3-n)*a(n-3)=0
It involves a(n-3) and the offset is 1, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a108524

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 8 * X + 4 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A108524: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((1 - S)
      * (4 - 2 * X : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A108524. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (2 * (n : ℚ)) * a n + (-17 * (n : ℚ) + 24) * a (n - 1) + (16 * (n : ℚ) - 36) * a (n - 2)
      + (-4 * (n : ℚ) + 12) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a108524
