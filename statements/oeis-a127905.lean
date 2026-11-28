import Mathlib

/-!
# A recurrence for OEIS A127905

Source: https://oeis.org/A127905
Credit: @hermitokatt

The sequence (offset 0): the next-to-central column of the triangle whose n-th row is the
expansion of `(1+x+x^3)^n`. The entry gives
`a(n) = Sum_{k=0..floor((n-1)/3)} (3k+1) C(n, 3k+1) C(3k, k) / (2k+1)`, used as the definition.
Data: 0, 1, 2, 3, 8, 25, 66, 168, 456, ….

The conjecture (R. J. Mathar, Feb 23 2015):
`2(2n+1)(n-1)^2 a(n) - 2n(6n^2-12n+5) a(n-1) + 6n(n-1)(2n-3) a(n-2) - 31n(n-1)(n-2) a(n-3) = 0`.

Reading.
* The recurrence is stated for every `n` for which all four terms are defined, i.e. `n ≥ 3`
  (checked numerically for `3 ≤ n ≤ 39`).
* The summand has a division, so it is computed in `ℚ`; for `n = 0` the upper limit
  `floor((n-1)/3)` is read as `0` (natural-number subtraction), and the single term is `0`,
  matching `a(0) = 0`.
* Terms and coefficients are in `ℚ`.
-/

namespace OMA.S_oeis_a127905

/-- A127905. -/
def a (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range ((n - 1) / 3 + 1),
    (3 * (k : ℚ) + 1) * (n.choose (3 * k + 1) : ℚ) * ((3 * k).choose k : ℚ) / (2 * (k : ℚ) + 1)

/-- Mathar's conjectured recurrence, for all `n ≥ 3`. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    2 * (2 * (n : ℚ) + 1) * ((n : ℚ) - 1) ^ 2 * a n - 2 * (n : ℚ) * (6 * (n : ℚ) ^ 2 - 12 * (n : ℚ) + 5) * a (n - 1) +
      6 * (n : ℚ) * ((n : ℚ) - 1) * (2 * (n : ℚ) - 3) * a (n - 2) -
      31 * (n : ℚ) * ((n : ℚ) - 1) * ((n : ℚ) - 2) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a127905
