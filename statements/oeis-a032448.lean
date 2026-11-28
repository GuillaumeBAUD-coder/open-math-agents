import Mathlib

/-!
# OEIS A032448: Smallest Prime Congruent to -1 Modulo prime(n)

Source: https://oeis.org/A032448
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

Let $a(n)$ be the smallest prime $q \equiv -1 \pmod{p_n}$, where $p_n$ is the $n$-th prime.

Conjecture: For every $n \ge 1$, $a(n) \le p_n^2 - 1$.
Equivalently, for every prime $p$, there exists a prime $q \le p^2 - 1$ such that $p \mid (q + 1)$.
-/

namespace OMA.S_oeis_a032448

theorem main :
    ∀ p : ℕ, Nat.Prime p → ∃ q : ℕ, Nat.Prime q ∧ p ∣ (q + 1) ∧ q ≤ p ^ 2 - 1 := by
  sorry

end OMA.S_oeis_a032448
