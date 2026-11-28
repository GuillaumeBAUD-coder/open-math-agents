import Mathlib

/-!
# A005384: Sophie Germain primes p: 2p+1 is also prime.

Source: https://oeis.org/A005384
Credit: @MartinFoxy

The entry carries the comment: In the spirit of the conjecture related to A217788, we
conjecture that for any integers `n >= m > 0` there are infinitely many integers `b > a(n)`
such that the number `Sum_{k=m..n} a(k)*b^(n-k)` is prime.

Formalization notes:
* The sequence has offset 1: `a(n)` is the `n`-th prime `p` such that `2p+1` is also prime
  (data from n = 1: 2, 3, 5, 11, 23, 29, 41, ...). Mathlib's `Nat.nth` counts from 0, so
  `a(n) = Nat.nth (fun p => p.Prime ∧ (2 * p + 1).Prime) (n - 1)` for `n ≥ 1`. If there were
  only finitely many Sophie Germain primes, `Nat.nth` would return 0 beyond the last one.
* All quantities are natural numbers; in `b^(n-k)` the index satisfies `k ≤ n`, so the
  natural-number subtraction is exact.
-/

namespace OMA.S_oeis_a005384

/-- A005384 (offset 1): the `n`-th Sophie Germain prime. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun p => p.Prime ∧ (2 * p + 1).Prime) (n - 1)

/-- For any `n ≥ m > 0` there are infinitely many `b > a(n)` such that
`Sum_{k=m..n} a(k)*b^(n-k)` is prime. -/
theorem main : ∀ m n : ℕ, 0 < m → m ≤ n →
    {b : ℕ | a n < b ∧ (∑ k ∈ Finset.Icc m n, a k * b ^ (n - k)).Prime}.Infinite := by
  sorry

end OMA.S_oeis_a005384
