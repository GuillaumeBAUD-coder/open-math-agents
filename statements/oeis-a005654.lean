import Mathlib

/-!
# A005654: Number of bracelets (turn over necklaces) with n red, 1 pink and n-1 blue beads.

Source: https://oeis.org/A005654
Credit: @MartinFoxy

The entry carries the formula (R. J. Mathar, Nov 09 2013):
`Conjecture: n*(n-2)*a(n) - (5*n-3)*(n-2)*a(n-1) + 4*(n-2)*a(n-2) + 4*(5*n^2-27*n+37)*a(n-3)
- 8*(2*n-7)*(n-4)*a(n-4) = 0.`

Formalization notes:
* The sequence has offset 1 and is given by the closed form recorded in its OEIS entry
  (Michael Somos): `a(n) = (1/2) * (binomial(2n-1, n) + binomial(n-1, floor(n/2)))`
  (data from n = 1: 1, 2, 6, 19, 66, 236, 868, 3235, ...). The sum of the two binomial
  coefficients is always even; the natural-number division below is that exact halving.
* The recurrence involves `a(n-4)`, so with offset 1 it is stated for every `n ≥ 5`. It is
  stated in `ℤ`, where the subtractions in the coefficients and between the terms are exact.
-/

namespace OMA.S_oeis_a005654

/-- A005654 (offset 1): `a(n) = (binomial(2n-1, n) + binomial(n-1, floor(n/2))) / 2`. -/
def a (n : ℕ) : ℕ := (Nat.choose (2 * n - 1) n + Nat.choose (n - 1) (n / 2)) / 2

/-- R. J. Mathar's conjectured recurrence for A005654 (OEIS Formula section). -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    (n : ℤ) * ((n : ℤ) - 2) * (a n : ℤ)
      - (5 * (n : ℤ) - 3) * ((n : ℤ) - 2) * (a (n - 1) : ℤ)
      + 4 * ((n : ℤ) - 2) * (a (n - 2) : ℤ)
      + 4 * (5 * (n : ℤ) ^ 2 - 27 * (n : ℤ) + 37) * (a (n - 3) : ℤ)
      - 8 * (2 * (n : ℤ) - 7) * ((n : ℤ) - 4) * (a (n - 4) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a005654
