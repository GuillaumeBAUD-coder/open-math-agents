import Mathlib

/-!
# A053728: For n=1,2,3,..., compute sum of aliquot divisors of n; if result is prime append this
prime to sequence.

Source: https://oeis.org/A053728
Credit: @<your GitHub handle>

The entry records (Robert Israel, Mar 26 2018): "If p is a prime > 7, a slightly stronger form of
the Goldbach conjecture implies there are two distinct primes q,r such that p-1=q+r. Then
sigma(q*r)-q*r=q+r+1=p. Thus every prime > 7 should appear at least once in this sequence."

Conventions (please review):
* The sum of aliquot divisors of `n` (A001065) is `∑ d ∈ n.properDivisors, d`, the sum of the
  divisors of `n` other than `n` itself.
* The sequence lists exactly the prime values of A001065 (with repetition), so "the prime `p`
  appears in this sequence" means: `p` is the aliquot sum of some `n ≥ 1`.
* We state the conjectural part only: every prime `p > 7` appears. (The remarks that 3 and 7 appear,
  that 2 and 5 do not, and that `a(n) → ∞`, are proved in the entry and are not stated here.)
-/

namespace OMA.S_oeis_a053728

/-- A001065: the sum of the aliquot (proper) divisors of `n`. -/
def aliquotSum (n : ℕ) : ℕ := ∑ d ∈ n.properDivisors, d

/-- Israel's conjecture in OEIS A053728: every prime `p > 7` is the sum of the aliquot divisors of
some positive integer `n`, i.e. appears in A053728. -/
theorem main : ∀ p : ℕ, p.Prime → 7 < p → ∃ n : ℕ, 1 ≤ n ∧ aliquotSum n = p := by
  sorry

end OMA.S_oeis_a053728
