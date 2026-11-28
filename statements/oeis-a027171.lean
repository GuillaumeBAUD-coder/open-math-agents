import Mathlib

/-!
# The affine recurrence for OEIS A027171

Sources: https://oeis.org/A027171 and https://oeis.org/A027170

The sequence is the main diagonal of the 4-diamondization of Pascal's
triangle. Use the explicit four-binomial-coefficient formula for A027170
at its even row `2n` and central column `n`. The conjectured recurrence
by R. J. Mathar is stated at index `n + 2`, so all subscripts are natural.
-/

namespace OMA.S_oeis_a027171

/-- The diagonal entry of the 4-diamondization of Pascal's triangle. -/
def a (n : ℕ) : ℤ :=
  ((2 * n + 2).choose (n + 1) : ℤ) + ((2 * n + 1).choose n : ℤ) +
    ((2 * n + 1).choose (n + 1) : ℤ) + ((2 * n).choose n : ℤ) - 4

theorem main : ∀ n : ℕ,
    2 * ((n : ℤ) + 3) * a (n + 2) + (-7 * (n : ℤ) - 19) * a (n + 1) +
      2 * (-2 * (n : ℤ) - 1) * a n + 12 * (-3 * (n : ℤ) - 5) = 0 := by
  sorry

end OMA.S_oeis_a027171
