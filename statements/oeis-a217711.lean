import Mathlib

/-!
# A217711: Total number of 321 patterns in the set of permutations avoiding 123.

Source: https://oeis.org/A217711
Credit: @vivanpoddar

The sequence (offset 3) begins 1, 16, 144, 1016, 6271, 35584, 190628, 979496, 4876530, ...
The entry gives the generating function
  1/2*(32*x^4 - 88*x^3 + 52*x^2 + sqrt(-4*x + 1)*(36*x^3 - 34*x^2 + 10*x - 1) - 12*x + 1)/(64*x^4 - 48*x^3 + 12*x^2 - x)
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x the series is, in normalised form,
  (-32*x^4 + 88*x^3 - 52*x^2 + 12*x - 1 + (-36*x^3 + 34*x^2 - 10*x + 1)*sqrt(R)) / (-128*x^4 + 96*x^3 - 24*x^2 + 2*x),
which is the expression used below (the division by x^1 is the shift of the index by 1).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Oct 08 2016) reads
  Conjecture: -(n+1)*(25*n-3314)*a(n) -5*n*(5*n+9446)*a(n-1) +2*(594*n^2 +128863*n -142613)*a(n-2) +16*(-119*n^2-39230*n+87888)*a(n-3) -32*(2*n-7)*(53*n-8687)*a(n-4)=0
It involves a(n-4) and the offset is 3, so it is stated for n >= 7.
-/

namespace OMA.S_oeis_a217711

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A217711: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 1)
    ((-1 + 12 * X - 52 * X ^ 2 + 88 * X ^ 3 - 32 * X ^ 4 + (1 - 10 * X + 34 * X ^ 2 - 36 * X ^ 3) * S)
      * (2 - 24 * X + 96 * X ^ 2 - 128 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A217711. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    (-25 * (n : ℚ) ^ 2 + 3289 * (n : ℚ) + 3314) * a n
      + (-25 * (n : ℚ) ^ 2 - 47230 * (n : ℚ)) * a (n - 1)
      + (1188 * (n : ℚ) ^ 2 + 257726 * (n : ℚ) - 285226) * a (n - 2)
      + (-1904 * (n : ℚ) ^ 2 - 627680 * (n : ℚ) + 1406208) * a (n - 3)
      + (-3392 * (n : ℚ) ^ 2 + 567840 * (n : ℚ) - 1945888) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a217711
