import Mathlib

/-!
# A100348: Numbers n such that n-4^k is a prime for all k > 0 with 4^k < n.

Source: https://oeis.org/A100348
Credit: @keiichisince1986-bot

A100348 lists the numbers `n` such that `n - 4^k` is prime for every `k > 0` with `4^k < n`:
`6, 7, 9, 11, 15, 21, 23, 27, 33, 35, 45, 47, 57, 63, 75, 77, 83, 87, 105, 117, 143, 153, …`
The entry states: The largest term appears to be 5833497. No others < 10^9; conjectured to be
finite.

Conventions:
- For `n ≤ 4` there is no `k > 0` with `4^k < n`, so the condition would hold vacuously; the data
  start at `6` (and `5` fails since `5 - 4 = 1`), so the sequence only considers `n > 4`, where
  `k = 1` is always tested. We state the conjecture for `n > 4`; this changes the set only by
  finitely many numbers, so it does not affect finiteness.
- The conjecture stated in the entry is that the sequence is finite (the value `5833497` is only
  described as the apparent largest term).
-/

namespace OMA.S_oeis_a100348

theorem main :
    {n : ℕ | 4 < n ∧ ∀ k : ℕ, 0 < k → 4 ^ k < n → (n - 4 ^ k).Prime}.Finite := by
  sorry

end OMA.S_oeis_a100348
