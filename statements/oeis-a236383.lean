import Mathlib.Data.Nat.Basic

/-! Michel Lagneau's existence conjecture, OEIS A236383 (offset 1).
The two decimal blocks have d+1 digits, and their concatenation is the square.
Existence of a witness is equivalent to existence of a least witnessing root.
Source: https://oeis.org/A236383 -/

namespace OMA.S_oeis_a236383

theorem main : ∀ n : ℕ, 0 < n →
    ∃ d k x y : ℕ, 10^d ≤ x ∧ x ≤ y ∧ y < 10^(d+1) ∧
      y = x + n^2 ∧ k^2 = x * 10^(d+1) + y := by
  sorry

end OMA.S_oeis_a236383
