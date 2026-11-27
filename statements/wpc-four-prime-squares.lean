import Mathlib

/-!
# Sums of four squares of primes

Source: https://en.wikipedia.org/wiki/Waring%E2%80%93Goldbach_problem
Credit: @Ciphore

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_wpc_four_prime_squares

/-- Every sufficiently large integer congruent to `4` modulo `24` is a sum of four squares of
prime numbers. -/
theorem main : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → n ≡ 4 [MOD 24] →
    ∃ p q r s : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ s.Prime ∧
      n = p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2 := by
  sorry

end OMA.S_wpc_four_prime_squares
