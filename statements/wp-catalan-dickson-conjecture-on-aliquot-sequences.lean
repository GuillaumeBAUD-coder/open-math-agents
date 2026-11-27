import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Set.Finite.Basic

/-!
# Catalan–Dickson conjecture on aliquot sequences

Source: https://en.wikipedia.org/wiki/Aliquot_sequence#Catalan-Dickson_conjecture

For every positive integer `n`, the aliquot sequence `a 0 = n`, `a (k + 1) = s (a k)` (where `s m`
is the sum of the proper positive divisors of `m`, with `s 0 = 0`) is bounded — equivalently, it
eventually terminates at `0` or enters a periodic cycle, i.e. its set of visited values is finite
(no aliquot sequence is infinite and non-repeating).
-/

namespace OMA.S_wp_catalan_dickson_conjecture_on_aliquot_sequences

/-- The aliquot sum `s(n)`: the sum of all proper positive divisors of `n` (with `s(0) = 0`). -/
def aliquotSum (n : ℕ) : ℕ :=
  ∑ d ∈ n.properDivisors, d

/-- The aliquot sequence starting at `n`: `a 0 = n` and `a (k + 1) = aliquotSum (a k)`. -/
def aliquotSeq (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 => aliquotSum (aliquotSeq n k)

theorem main : ∀ n : ℕ, 0 < n → (Set.range (aliquotSeq n)).Finite := by
  sorry

end OMA.S_wp_catalan_dickson_conjecture_on_aliquot_sequences
