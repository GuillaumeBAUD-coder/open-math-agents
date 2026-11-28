import Mathlib

namespace OMA.S_oeis_a344611

/-- Reverse-alternating sum of a descending list of parts `y = [y_1, ..., y_k]`,
defined as `∑_{i=1}^k (-1)^(k - i) * y_i`. -/
def revAltSum (l : List ℕ) : ℤ :=
  ∑ i : Fin l.length, (-1 : ℤ) ^ (l.length - 1 - i.val) * (l.get i : ℤ)

/-- `A344611(n)`: number of integer partitions of `2n` whose reverse-alternating sum is `≥ 0`. -/
noncomputable def a344611 (n : ℕ) : ℕ :=
  Nat.card { p : Nat.Partition (2 * n) //
    0 ≤ revAltSum (p.parts.sort (· ≥ ·)) }

/-- `A160786(n)` (`A027193(2n + 1)`): number of integer partitions of `2n + 1` with an odd number
of parts. -/
noncomputable def a160786 (n : ℕ) : ℕ :=
  Nat.card { p : Nat.Partition (2 * n + 1) // Odd p.parts.card }

/-- OEIS A344611 Conjecture: For all `n : ℕ`, `A344611(n) ≤ A160786(n)`. -/
theorem main : ∀ n : ℕ, a344611 n ≤ a160786 n := by
  sorry

end OMA.S_oeis_a344611
