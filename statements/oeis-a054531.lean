import Mathlib

/-!
# A054531: Triangular array T read by rows: T(n,k) = n/gcd(n,k) (n >= 1, 1 <= k <= n).

Source: https://oeis.org/A054531
Credit: @<your GitHub handle>

The entry records (Andrew V. Sutherland, Nov 27 2011): "Read as a linear sequence, this is
conjectured to be the length of the shortest cycle of pebble-moves among the partitions of n
(cf. A201144)."

Conventions (please review):
* Pebble-moves (A201144, "Bulgarian solitaire"): "You have n pebbles arranged in several piles. At
  each turn you take one pebble from each pile and put them into a new pile." On the multiset of
  pile sizes this is `step s = {card s} + {x - 1 | x ∈ s, x ≥ 2}`, which maps partitions of `N` to
  partitions of `N`.
* A cycle of pebble-moves among the partitions of `N` is a periodic orbit of `step` on partitions
  of `N`. Its length is the minimal period of any of its points, so the length of the shortest cycle
  is the least `p ≥ 1` such that some partition `μ` of `N` satisfies `step^[p] μ = μ`.
* Read as a linear sequence (offset 1), the entry `T(n,k)` (`n ≥ 1`, `1 ≤ k ≤ n`) is term number
  `N = n(n-1)/2 + k`. The conjecture says the shortest cycle among partitions of that `N` has
  length `n / gcd(n, k)`.
-/

namespace OMA.S_oeis_a054531

/-- One pebble-move: take one pebble from each pile and put them into a new pile. -/
def step (s : Multiset ℕ) : Multiset ℕ :=
  Multiset.card s ::ₘ ((s.map (· - 1)).filter (0 < ·))

/-- Sutherland's conjecture in OEIS A054531: for `n ≥ 1` and `1 ≤ k ≤ n`, the shortest cycle of
pebble-moves among the partitions of `N = n(n-1)/2 + k` has length `n / gcd(n, k)`. -/
theorem main : ∀ n k : ℕ, 1 ≤ k → k ≤ n →
    IsLeast {p : ℕ | 0 < p ∧
        ∃ μ : Nat.Partition (n * (n - 1) / 2 + k), step^[p] μ.parts = μ.parts}
      (n / Nat.gcd n k) := by
  sorry

end OMA.S_oeis_a054531
