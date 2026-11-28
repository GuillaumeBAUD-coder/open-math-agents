import Mathlib

/-!
# Infinite chains of primes with p(n+1) = 2p(n) - 1 or p(n+1) = 2p(n) + 1

The question: "For each k ∈ ℕ, does there exist a k-tuple of primes, (p_n)_{n=1}^k, such that
for each n, the following is satisfied: p_{n+1} = 2p_n - 1 or p_{n+1} = 2p_n + 1?
If yes then further question: does there exist an infinitely long tuple of such primes
(i.e. an infinite sequence)?"

Only the further question is settled in the source, so only it is formalized here:
there is a sequence `p : ℕ → ℕ` of primes such that for every `n`,
`p (n+1) = 2 * p n - 1` or `p (n+1) = 2 * p n + 1`.
Reading choices: the sequence is indexed from 0 instead of 1 (immaterial); the sign may be
chosen independently at each step, as in the source. Natural subtraction is harmless since
every term is a prime, hence at least 2. The finite-k question is open and is not stated.

The statement relies on the top-voted (and only) answer, which shows that no such infinite sequence exists (mod 3 forces a constant sign, then
Fermat's little theorem makes a later term divisible by an earlier one), so the statement
below is false and is refuted.

Source: https://math.stackexchange.com/questions/4930059/for-each-integer-k-does-there-exist-a-k-tuple-of-primes-p-n-n-1k
Credit: @xor2k
-/

namespace OMA.S_mse_4930059

theorem main : ∃ p : ℕ → ℕ, (∀ n, (p n).Prime) ∧
    ∀ n, p (n + 1) = 2 * p n - 1 ∨ p (n + 1) = 2 * p n + 1 := by
  sorry

end OMA.S_mse_4930059
