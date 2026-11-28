import Mathlib

/-!
# A089609: Prime number of primes between squares of consecutive primes

Source: https://oeis.org/A089609
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Prime number of primes between squares of consecutive primes; or, primes
occurring in A050216.
Conjecture: There exists an n such that seq(n1) < seq(n1 + 1) for all n1 >= n.
-/

namespace OMA.S_oeis_a089609

/-- Number of primes strictly between p_k^2 and p_{k+1}^2 (A050216). -/
noncomputable def primesBetweenPrimeSquares (k : ℕ) : ℕ :=
  ((Finset.Ioo ((Nat.nth Nat.Prime k) ^ 2) ((Nat.nth Nat.Prime (k + 1)) ^ 2)).filter Nat.Prime).card

/-- The n-th term of A089609: the subsequence of prime values of A050216. -/
noncomputable def a (n : ℕ) : ℕ :=
  primesBetweenPrimeSquares (Nat.nth (fun k => Nat.Prime (primesBetweenPrimeSquares k)) n)

theorem main :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a n < a (n + 1) := by
  sorry

end OMA.S_oeis_a089609
