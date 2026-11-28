import Mathlib

/-!
# OEIS A352092

Amiram Eldar's conjecture that five consecutive positive integers cannot all be
Tribonacci–Niven numbers. See https://oeis.org/A352092 and https://oeis.org/A352089.

The greedy weights are 1, 2, 4 and then the sum of the previous three weights.
At a fixed width, the binary words without `111` list the greedy representations
in increasing order. The three leading prefixes `0`, `10`, `110` give consecutive
integer intervals of lengths equal to the previous three greedy weights.
`repWeights m` lists their numbers of ones in increasing numerical order, allowing
leading zeroes, so its index `n` is the greedy digit sum as soon as the width suffices.
-/

namespace OMA.S_oeis_a352092

/-- Greedy digit sums at a fixed width, in increasing order of the represented integer. -/
def repWeights : ℕ → List ℕ
  | 0 => [0]
  | 1 => [0, 1]
  | 2 => [0, 1, 1, 2]
  | m + 3 => repWeights (m + 2) ++ (repWeights (m + 1)).map (1 + ·) ++
      (repWeights m).map (2 + ·)

/-- A width of `n + 5` suffices to represent `n`. -/
def digitSum (n : ℕ) : ℕ := ((repWeights (n + 5))[n]?).getD 0

def NoFive : Prop := ∀ n : ℕ, 0 < n → ¬ ∀ i : ℕ, i < 5 → digitSum (n + i) ∣ n + i

theorem main : NoFive := by
  sorry

end OMA.S_oeis_a352092
