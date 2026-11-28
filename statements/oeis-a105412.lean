import Mathlib

/-!
# A105412: Primes p = prime(k) such that both p+2 and prime(k+5)-2 are prime numbers.

Source: https://oeis.org/A105412
Credit: @gblacher2

Conjecture (stated in A105412): "There are infinitely many primes p(k) such that p(k)+2 and
p(k+m)-2 are both primes for all m > 1."

Formalization notes:
* `p(k)` is the `k`-th prime. We index it as `Nat.nth Nat.Prime k` (so `p 0 = 2`); a shift of
  the index does not change whether the set of such `k` is infinite.
* "for all m > 1" is read as: for each fixed `m > 1` there are infinitely many such `k`. The
  other reading (one `k` that works for every `m > 1` simultaneously) would make the set empty,
  since infinitely many primes `q` have `q - 2` composite. The case `m = 5` is A105412 itself,
  and `m = 6` is A105413.
* Since `k ↦ p(k)` is injective, "infinitely many primes p(k)" is the same as infinitely many
  indices `k`.
* With this definition and `m = 5`, the primes `p(k)` below 11718 are exactly the 42 data terms
  of A105412 (and with `m = 6` the 40 data terms of A105413).
-/

namespace OMA.S_oeis_a105412

/-- For every `m > 1` there are infinitely many `k` such that `p(k) + 2` and `p(k + m) - 2` are
both prime, where `p(k)` is the `k`-th prime. -/
theorem main : ∀ m : ℕ, 1 < m →
    {k : ℕ | (Nat.nth Nat.Prime k + 2).Prime ∧ (Nat.nth Nat.Prime (k + m) - 2).Prime}.Infinite := by
  sorry

end OMA.S_oeis_a105412
