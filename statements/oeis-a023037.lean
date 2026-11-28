import Mathlib

/-!
# A023037: Minimal period of Bell numbers modulo a prime p

Source: https://oeis.org/A023037
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

Conjecture:
Let `a(p) = 1 + p + p^2 + ... + p^(p - 1) = (p^p - 1) / (p - 1)`.
For every prime `p`, `a(p)` is the minimal positive period of the Bell numbers modulo `p`.

Conventions:
- `bell` is defined by `bell 0 = 1` and `bell (n + 1) = ∑ k : Fin (n + 1), C(n, k) * bell k`.
- Minimal positive period means `a(p)` is a period modulo `p`, and no `1 ≤ d < a(p)` is a period.
-/

namespace OMA.S_oeis_a023037

def bell : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ k : Fin (n + 1), Nat.choose n k.1 * bell k.1

def aSeq (p : ℕ) : ℕ :=
  ∑ k ∈ Finset.range p, p ^ k

theorem main :
    ∀ p : ℕ, Nat.Prime p →
      (∀ n : ℕ, bell (n + aSeq p) ≡ bell n [MOD p]) ∧
      (∀ d : ℕ, 1 ≤ d → d < aSeq p → ∃ n : ℕ, ¬ (bell (n + d) ≡ bell n [MOD p])) := by
  sorry

end OMA.S_oeis_a023037
