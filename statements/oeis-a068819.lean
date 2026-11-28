import Mathlib

/-!
# A068819: n!/((n+1)*(n+2)*...*(n+k)) where k is largest value that gives an integer quotient.

Source: https://oeis.org/A068819
Credit: @divmxnd0x

Conjecture (stated in A068819): for `n > 3`, `n!` is divisible by the product
`(n+1)(n+2)...(n+k)`, where `n + k + 1` is the smallest prime greater than `n`.

Formalization notes:
* `nextPrime n` is the smallest prime greater than `n` (it exists, there being infinitely many
  primes); the product runs over the integers strictly between `n` and `nextPrime n`, i.e.
  `n + 1, ..., n + k` with `n + k + 1 = nextPrime n` (an empty product, equal to `1`, when
  `nextPrime n = n + 1`).
-/

namespace OMA.S_oeis_a068819

/-- The smallest prime greater than `n`. -/
noncomputable def nextPrime (n : ℕ) : ℕ := sInf {p : ℕ | n < p ∧ p.Prime}

/-- For `n > 3`, `n!` is divisible by the product of the integers strictly between `n` and the
next prime. -/
theorem main : ∀ n : ℕ, 3 < n → (∏ i ∈ Finset.Ioo n (nextPrime n), i) ∣ n.factorial := by
  sorry

end OMA.S_oeis_a068819
