import Mathlib

/-!
# A079665: Triangular array of integers (2^s+1)/(2^r+1)

Source: https://oeis.org/A079665
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Triangular array read by rows: row s contains integers of the form (2^s+1)/(2^r+1)
in order of increasing r <= s-1.
Conjecture: (b^s+1)/(b^r+1) is an integer if and only if:
1) r < s/2,
2) if s == 1 (mod 2) then r is a divisor of s,
3) if s = k*2^t with gcd(k, 2^t) = 1 then r is 2^t*u with u dividing k.
-/

namespace OMA.S_oeis_a079665

theorem main :
    ∀ b : ℕ, 2 ≤ b → ∀ s r : ℕ, 1 ≤ r → r < s →
      ((b ^ r + 1) ∣ (b ^ s + 1) ↔
        2 * r < s ∧
        (s % 2 = 1 → r ∣ s) ∧
        (∀ k t : ℕ, s = k * 2 ^ t → Nat.Coprime k (2 ^ t) →
          ∃ u : ℕ, r = 2 ^ t * u ∧ u ∣ k)) := by
  sorry

end OMA.S_oeis_a079665
