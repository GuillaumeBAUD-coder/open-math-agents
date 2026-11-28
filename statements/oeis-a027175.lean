import Mathlib

/-!
# The affine recurrence for OEIS A027175

Sources: https://oeis.org/A027175 and https://oeis.org/A027170

The original entry starts at index 1 and has term `T(2n-1,n-1)`, where `T`
is the 4-diamondization of Pascal's triangle. Here `a n` denotes that term
at original index `n+1`. R. J. Mathar's recurrence is stated at original
index `n+3`, so its oldest term is in the published domain.
-/

namespace OMA.S_oeis_a027175

/-- The central entry of the odd rows. -/
def a (n : ℕ) : ℤ :=
  ((2 * n + 3).choose (n + 1) : ℤ) + ((2 * n + 2).choose n : ℤ) +
    ((2 * n + 2).choose (n + 1) : ℤ) + ((2 * n + 1).choose n : ℤ) - 4

theorem main : ∀ n : ℕ,
    2 * ((n : ℤ) + 4) * a (n + 2) + (-7 * (n : ℤ) - 26) * a (n + 1) +
      2 * (-2 * (n : ℤ) - 3) * a n + 12 * (-3 * (n : ℤ) - 8) = 0 := by
  sorry

end OMA.S_oeis_a027175
