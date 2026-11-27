import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Defs

namespace OMA.S_wpc_four_prime_squares

/-- Every sufficiently large natural number congruent to 4 modulo 24 is a sum of four
prime squares. The primes may repeat.

See Liu, Wooley, and Yu, *The quadratic Waring–Goldbach problem*, §1, equation (1.1).
https://www.math.purdue.edu/~twooley/publ/2004WGP4SQ.pdf -/
theorem main :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → n ≡ 4 [MOD 24] →
      ∃ p₁ p₂ p₃ p₄ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ p₄.Prime ∧
        n = p₁ ^ 2 + p₂ ^ 2 + p₃ ^ 2 + p₄ ^ 2 := by
  sorry

end OMA.S_wpc_four_prime_squares
