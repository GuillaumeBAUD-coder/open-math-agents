import Mathlib

/-!
# Are there infinitely many Giuga numbers?

Source: https://en.wikipedia.org/wiki/Giuga_number
Credit: @Madelyyn

Statement of the problem, transcribed from the source:

* "a **Giuga number** is a composite number `n` such that for each of its distinct prime factors
  `p_i` we have `p_i | (n / p_i - 1)`" (the page gives the equivalent form `p_i ^ 2 | (n - p_i)`);
* "It is not known if there are infinitely many Giuga numbers", and the page poses the unsolved
  problem "Are there infinitely many Giuga numbers?".

So: infinitely many composite `n` such that every distinct prime factor `p` of `n` divides
`n / p - 1`. Since `p` is a prime factor of `n`, `n / p >= 1` and the truncated subtraction in `ℕ`
is the honest integer difference.

No proof here: `main` stays `sorry` (this file only states the problem).
-/

namespace OMA.S_wp_are_there_infinitely_many_giuga_numbers

/-- A Giuga number: a composite `n` such that `p ∣ n / p - 1` for every distinct prime factor `p`
of `n` (Wikipedia, "Giuga number"). -/
def IsGiuga (n : ℕ) : Prop := ¬ n.Prime ∧ 1 < n ∧ ∀ p ∈ n.primeFactors, p ∣ n / p - 1

/-- Are there infinitely many Giuga numbers? -/
theorem main : {n : ℕ | IsGiuga n}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_giuga_numbers
