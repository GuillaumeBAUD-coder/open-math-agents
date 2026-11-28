import Mathlib

/-!
# A217564: number of primes between prime(n)/2 and prime(n+1)/2

Source: https://oeis.org/A217564 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A217564 (offset 1): number of primes between prime(n)/2 and prime(n+1)/2, i.e.
a(n) = pi(prime(n+1)/2) - pi(prime(n)/2); data 0, 1, 1, 1, 0, 1, 0, 1, ...
(a(30) = 2: the primes 59 and 61 lie between 113/2 and 127/2).

The entry records two conjectures:

  Conjecture: this sequence is unbounded, as implied by Dickson's conjecture.
  (Charles R Greathouse IV, Oct 09 2012)
  Conjecture: 0 appears infinitely often. (Jon Perry, Oct 10 2012)

Both are stated here, as a conjunction.

Reading of the source:
* `prime n` is the `n`-th prime with `prime 1 = 2` (`Nat.nth Nat.Prime (n - 1)`), and `pi` is
  `Nat.primeCounting`. `pi(x/2)` for a natural `x` is `pi` of `⌊x/2⌋`, computed with natural
  division (no prime lies strictly between `⌊x/2⌋` and `x/2`).
* "unbounded": for every bound `B` some term exceeds `B`; "0 appears infinitely often": for every
  `N` there is an index `n ≥ N` with `a n = 0`. Indices are `n ≥ 1`.
-/

namespace OMA.S_oeis_a217564

/-- `prime n`: the `n`-th prime, with `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- A217564(n) = π(prime(n+1)/2) - π(prime(n)/2). -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.primeCounting (prime (n + 1) / 2) - Nat.primeCounting (prime n / 2)

/-- The sequence is unbounded, and it takes the value 0 infinitely often. -/
theorem main :
    (∀ B : ℕ, ∃ n, 1 ≤ n ∧ B < a n) ∧ (∀ N : ℕ, ∃ n, N ≤ n ∧ 1 ≤ n ∧ a n = 0) := by
  sorry

end OMA.S_oeis_a217564
