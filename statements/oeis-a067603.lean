import Mathlib

/-!
# OEIS A067603: Least k with gcd(prime(k) + 1, prime(k + 1) + 1) = 2n

Source: https://oeis.org/A067603
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

For $n \ge 1$, let $a(n)$ be the least $k \ge 1$ such that
$\gcd(p_k + 1, p_{k+1} + 1) = 2n$, where $p_k$ is the $k$-th prime.

Conjecture: For every $n \ge 1$, $a(n)$ equals the least $k \ge 1$ such that
$p_{k+1} - p_k = 2n$ and $p_k \equiv -1 \pmod{2n}$.
-/

namespace OMA.S_oeis_a067603

/-- The 1-indexed `k`-th prime (`p 1 = 2`, `p 2 = 3`, ...). -/
noncomputable def nthPrime (k : ℕ) : ℕ :=
  Nat.nth Nat.Prime (k - 1)

/-- `IsLeastGcd n k` holds when `k ≥ 1` is minimal with `gcd(p_k + 1, p_{k+1} + 1) = 2n`. -/
def IsLeastGcd (n k : ℕ) : Prop :=
  1 ≤ k ∧ Nat.gcd (nthPrime k + 1) (nthPrime (k + 1) + 1) = 2 * n ∧
    ∀ j, 1 ≤ j → j < k → Nat.gcd (nthPrime j + 1) (nthPrime (j + 1) + 1) ≠ 2 * n

/-- `IsLeastGapCong n k` holds when `k ≥ 1` is minimal with `p_{k+1} - p_k = 2n`
and `(2n) ∣ (p_k + 1)`. -/
def IsLeastGapCong (n k : ℕ) : Prop :=
  1 ≤ k ∧ nthPrime (k + 1) - nthPrime k = 2 * n ∧ (2 * n) ∣ (nthPrime k + 1) ∧
    ∀ j, 1 ≤ j → j < k →
      ¬ (nthPrime (j + 1) - nthPrime j = 2 * n ∧ (2 * n) ∣ (nthPrime j + 1))

theorem main :
    ∀ n k : ℕ, 1 ≤ n → (IsLeastGcd n k ↔ IsLeastGapCong n k) := by
  sorry

end OMA.S_oeis_a067603
