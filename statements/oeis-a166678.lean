import Mathlib

/-!
# A166678: primes between the n-th primorial and (sqrt(P(n)) + 1)^2

Source: https://oeis.org/A166678 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A166678 (offset 1): a(n) = pi((sqrt(P(n))+1)^2) - pi(P(n)), where pi(n) = number of primes <= n
and P(n) = n-th primorial; data 2, 2, 3, 6, 14, 34, 110, ...

The entry records:

  Conjecture: pi((sqrt(P(n))+1)^2) - pi(P(n)) >= n.

Reading of the source:
* `P(n)`, the n-th primorial, is the product of the first `n` primes (P(1) = 2, P(2) = 6,
  P(3) = 30); this is not Mathlib's `primorial n`, the product of the primes `≤ n`.
* `pi` is the prime-counting function `Nat.primeCounting` (primes `≤ x`); at the real number
  `(√P(n) + 1)^2` it is evaluated at its floor.
* The conjecture is for every `n ≥ 1`. (Data check: for n = 1, (√2 + 1)^2 = 5.83..., and
  pi(5) - pi(2) = 3 - 1 = 2.)
-/

namespace OMA.S_oeis_a166678

/-- The `n`-th primorial: the product of the first `n` primes. -/
noncomputable def P (n : ℕ) : ℕ := ∏ i ∈ Finset.range n, Nat.nth Nat.Prime i

/-- For every `n ≥ 1`, at least `n` primes lie in `(P(n), (√P(n) + 1)^2]`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    n ≤ Nat.primeCounting ⌊(Real.sqrt (P n) + 1) ^ 2⌋₊ - Nat.primeCounting (P n) := by
  sorry

end OMA.S_oeis_a166678
