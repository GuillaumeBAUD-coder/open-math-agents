import Mathlib

/-!
# De Polignac's conjecture

Source: https://en.wikipedia.org/wiki/Polignac%27s_conjecture
Credit: @ihateSAS

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source: for any positive even number `n` there are infinitely many prime gaps of size `n`,
that is, infinitely many pairs of consecutive primes `p` and `q` with `q - p = n`.  The case
`n = 2` is the twin prime conjecture.

So the proposition formalized below is: for every positive even `n` there are infinitely many
primes `p` such that `p + n` is prime and no prime lies strictly between `p` and `p + n`.
-/

namespace OMA.S_wp_de_polignac_s_conjecture

-- definitions the statement needs (no sorry, no axiom)

/-- `n` is the size of a prime gap starting at `p`: `p` and `p + n` are both prime and no number
strictly between them is prime, so they are consecutive primes. -/
def IsPrimeGap (p n : ℕ) : Prop :=
  p.Prime ∧ (p + n).Prime ∧ ∀ q : ℕ, p < q → q < p + n → ¬ q.Prime

/-- De Polignac's conjecture: every positive even number occurs infinitely often as a prime gap. -/
theorem main : ∀ n : ℕ, 0 < n → Even n → {p : ℕ | IsPrimeGap p n}.Infinite := by
  sorry

end OMA.S_wp_de_polignac_s_conjecture
