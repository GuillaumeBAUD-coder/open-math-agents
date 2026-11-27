import Mathlib.Data.Int.Basic

/-!
# The ceiling Pisot sequence L(8,9)

Source: https://oeis.org/A048590/internal
Harvey P. Dale's conjectured signature is (2,-1,0,1,-1).
The source specifies n > 5 for the recurrence and a zero-based index.
For positive integer d, the ceiling of u/d is (u+d-1)/d in integer division.
-/

namespace OMA.S_oeis_a048590

def a : ℕ → ℤ
  | 0 => 8
  | 1 => 9
  | n + 2 => (a (n + 1) ^ 2 + a n - 1) / a n

theorem main : ∀ n : ℕ, 5 < n →
    a n = 2 * a (n - 1) - a (n - 2) + a (n - 4) - a (n - 5) := by
  sorry

end OMA.S_oeis_a048590
