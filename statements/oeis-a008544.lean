import Mathlib

/-!
# OEIS A008544: the Mathar recurrence for the triple factorials ∏ (3k+2)

Source: https://oeis.org/A008544
Credit: @SudharsanAnimations

`a(n) = ∏_{k=0}^{n-1} (3k+2)`. The entry records that "the Mathar conjecture is true"
(Bill McEachen, Jan 2016), deriving from the product form the four-term recurrence
`a(n) + (1 - 3n) a(n-1) + a(n-2) + (7 - 3n) a(n-3) = 0`. We state this recurrence for all
`n ≥ 3` (the range where every index is defined).

Conventions: offset `0` with `a 0 = 1` (empty product); the identity is taken in `ℤ`.
-/

namespace OMA.S_oeis_a008544

/-- Triple factorial numbers: `a n = ∏_{k=0}^{n-1} (3k + 2)` (offset `0`, `a 0 = 1`). -/
def a (n : ℕ) : ℕ := ∏ k ∈ Finset.range n, (3 * k + 2)

theorem main : ∀ n : ℕ, 3 ≤ n →
    (a n : ℤ) + (1 - 3 * n) * a (n - 1) + a (n - 2) + (7 - 3 * n) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a008544
