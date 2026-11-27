import Mathlib

/-!
# Are there infinitely many Woodall primes?

Source: https://en.wikipedia.org/wiki/Woodall_number#Woodall_primes
Credit: @sauronsoul-bit

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_wp_are_there_infinitely_many_woodall_primes

-- definitions the statement needs (no sorry, no axiom)

theorem main : {k : ℕ | 1 < k ∧ (k * 2 ^ k - 1).Prime}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_woodall_primes

