import Mathlib

/-!
# The second-order recurrence proposed for OEIS A182959

Source: https://oeis.org/A182959
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A182/A182959.seq
Credit: @Heart-galaxy

The sequence uses the initial values `a(0) = 1` and `a(1) = 5` and Peter Bala's
closed form for `n ≥ 2`. Here `Nat.centralBinom (n - 1)` is `choose (2*n-2) (n-1)`.

R. J. Mathar proposed this recurrence as a D-finite recurrence without specifying
a starting index. The statement uses eventual validity. The left-hand side is
`9` at `n = 2` and `4` at `n = 3`, and the recurrence holds from `n = 4` onward.
Bala's 2023 first-order recurrence gives the second-order relation.
-/

namespace OMA.S_oeis_a182959

/-- OEIS A182959 using Bala's closed form and the two initial values. -/
def a : ℕ → ℚ
  | 0 => 1
  | 1 => 5
  | k + 2 =>
      (3 * (2 : ℚ) ^ (k + 2) * (3 * (k : ℚ) + 5) * (Nat.centralBinom (k + 1) : ℚ)) /
        (((k : ℚ) + 2) * ((k : ℚ) + 3))

/-- Mathar's proposed recurrence eventually holds for A182959. -/
theorem main : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ((n : ℚ) + 1) * a n + (-7 * (n : ℚ) + 3) * a (n - 1) +
      4 * (-2 * (n : ℚ) + 5) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a182959
