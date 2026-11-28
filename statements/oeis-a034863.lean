import Mathlib

/-!
# OEIS A034863

Source: https://oeis.org/A034863. The sequence starts at index 4.
R. J. Mathar proposed the recurrence on April 3, 2017.
Credit: @dreamzzz-dev
-/

namespace OMA.S_oeis_a034863

/-- The signed factorial formula for A034863, used at indices at least four. -/
def a (n : ℕ) : ℤ :=
  (n.factorial : ℤ) * (4 * (n : ℤ) ^ 3 - 30 * (n : ℤ) ^ 2 + 40 * (n : ℤ) + 3) / 24

/-- All three indices are in the sequence as soon as n is at least six. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    (-96 * (n : ℤ) + 27161) * a n +
      (96 * (n : ℤ) ^ 2 - 99580 * (n : ℤ) + 199917) * a (n - 1) +
      (72707 * (n : ℤ) - 61983) * ((n : ℤ) - 1) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a034863
