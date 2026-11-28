import Mathlib

/-!
# A020744: Pisot sequence T(8, 10) and even sums of four primes

Source: https://oeis.org/A020744
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

Conjecture:
Every term of the Pisot sequence `T(8, 10)` (defined by `a(0) = 8`, `a(1) = 10`, and
`a(n + 2) = ⌊a(n + 1)^2 / a(n)⌋`) is an even sum of four primes.

Conventions:
- `tSeq` is defined by natural number floor division `a(n + 1)^2 / a(n)`.
-/

namespace OMA.S_oeis_a020744

def tSeq : ℕ → ℕ
  | 0 => 8
  | 1 => 10
  | n + 2 => tSeq (n + 1) ^ 2 / tSeq n

theorem main :
    ∀ n : ℕ,
      Even (tSeq n) ∧
        ∃ p₁ p₂ p₃ p₄ : ℕ,
          Nat.Prime p₁ ∧ Nat.Prime p₂ ∧ Nat.Prime p₃ ∧ Nat.Prime p₄ ∧
          p₁ + p₂ + p₃ + p₄ = tSeq n := by
  sorry

end OMA.S_oeis_a020744
