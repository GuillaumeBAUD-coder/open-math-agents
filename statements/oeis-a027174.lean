import Mathlib

/-!
# The affine recurrence for OEIS A027174

Sources: https://oeis.org/A027174 and https://oeis.org/A027170

The original entry starts at index 2 and has term `T(2n,n-2)`, where `T`
is the 4-diamondization of Pascal's triangle. Here `a n` denotes that term
at original index `n+2`. R. J. Mathar's recurrence is stated at original
index `n+4`, so its oldest term is in the published domain.
-/

namespace OMA.S_oeis_a027174

/-- The entry of the second off-center even diagonal. -/
def a (n : ℕ) : ℤ :=
  ((2 * n + 6).choose (n + 1) : ℤ) + ((2 * n + 5).choose n : ℤ) +
    ((2 * n + 5).choose (n + 1) : ℤ) + ((2 * n + 4).choose n : ℤ) - 4

theorem main : ∀ n : ℕ,
    let m := (n : ℤ) + 4;
    -2 * (m + 3) * (139 * m - 175) * a (n + 2) +
      (1279 * m ^ 2 + 1334 * m - 1089) * a (n + 1) -
      2 * (167 * m + 121) * (2 * m - 3) * a n +
      12 * (111 * m ^ 2 + 456 * m + 229) = 0 := by
  sorry

end OMA.S_oeis_a027174
