import Mathlib

/-!
# A040976: Infinitely Many Primes of the Form p_n - 2 (Twin Prime Conjecture)

Source: https://oeis.org/A040976
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

A040976 is the sequence `a(n) = p_n - 2`, where `p_n` is the `n`-th prime.

Conjecture (Twin Prime Conjecture): The sequence `a(n) = p_n - 2` contains infinitely many primes.
-/

namespace OMA.S_oeis_a040976

theorem main :
    Set.Infinite { n : ℕ | Nat.Prime (Nat.nth Nat.Prime n - 2) } := by
  sorry

end OMA.S_oeis_a040976
