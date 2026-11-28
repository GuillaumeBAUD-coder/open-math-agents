import Mathlib

/-!
# A090738: Integers n such that the concatenation of n^2 and (n+1)^2 is prime.

Source: https://oeis.org/A090738
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

I conjecture this sequence to be infinite. Searching through the first 200000 values,
I found 7000 primes, of which over 400 were "twins", i.e. both n^2*(n+1)^2 and
(n+2)^2*(n+3)^2 were prime, where "*" denotes concatenation. I conjecture there to be
an infinitude of such twins and the obvious generalizations.
-/

namespace OMA.S_oeis_a090738

def concat10 (a b : ℕ) : ℕ :=
  a * 10 ^ (Nat.digits 10 b).length + b

theorem main :
    {n : ℕ | Nat.Prime (concat10 (n ^ 2) ((n + 1) ^ 2))}.Infinite := by
  sorry

end OMA.S_oeis_a090738
