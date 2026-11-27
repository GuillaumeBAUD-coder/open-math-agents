import Mathlib

/-!
# Sums of four squares of primes (Waring–Goldbach)

Source: https://en.wikipedia.org/wiki/Waring%E2%80%93Goldbach_problem
Credit: @Andyi955

Waring's problem for prime variables asks whether every sufficiently large integer in a fixed
residue class is a sum of a fixed number of squares of primes. Hua proved the analogue with five
squares for integers `n ≡ 5 (mod 24)`. The question formalised here is the four-square version:
is every sufficiently large `n ≡ 4 (mod 24)` a sum of four squares of primes?

The residue class `4 (mod 24)` is the one forced by local conditions: a sum of four odd squares is
`≡ 4 (mod 8)`, and modulo `3` four squares of primes not equal to `3` give `≡ 4 (mod 3)`, so
`n ≡ 4 (mod 24)` is the only class in which a representation is possible at all.
-/

namespace OMA.S_wpc_four_prime_squares

/-- **Waring–Goldbach, four prime squares**: every sufficiently large integer congruent to `4`
modulo `24` is a sum of four squares of primes. -/
theorem main :
    ∀ᶠ n : ℕ in Filter.atTop, n % 24 = 4 →
      ∃ p q r s : ℕ,
        Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ Nat.Prime s ∧
          n = p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2 := by
  sorry

end OMA.S_wpc_four_prime_squares
