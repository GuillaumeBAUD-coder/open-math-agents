import Mathlib

/-!
# Sum of prime and semiprime conjecture

Source: https://www.openproblemgarden.org/op/sum_of_prime_and_semiprime_conjecture
Credit: @Hyvok

Conjecture (Geoffrey R. Marnell, [M] G. R. Marnell, Ten Prime Conjectures, Journal of Recreational
Mathematics 33:3 (2004–2005), 193–196): every even number greater than `10` can be written as the sum
of an odd prime and an odd semiprime.

Formalization notes:
* A semiprime is a product of two primes, not necessarily distinct (so `9 = 3 * 3` counts).
* "Odd semiprime" is a semiprime that is odd, i.e. a product of two odd primes.
* The bound is strict: `10` itself is not such a sum (and neither are 2, 4, 6, 8).
* By Chen's theorem every sufficiently large even number is a prime plus a product of at most two
  primes; this conjecture asks for exactly two (odd) primes in the second summand, and for all
  even numbers above `10`.
-/

namespace OMA.S_opg_sum_of_prime_and_semiprime_conjecture

/-- `n` is a semiprime: a product of two (not necessarily distinct) primes. -/
def IsSemiprime (n : ℕ) : Prop := ∃ q r : ℕ, q.Prime ∧ r.Prime ∧ n = q * r

/-- Marnell's conjecture: every even `n > 10` is an odd prime plus an odd semiprime. -/
theorem main :
    ∀ n : ℕ, Even n → 10 < n →
      ∃ p s : ℕ, p.Prime ∧ Odd p ∧ IsSemiprime s ∧ Odd s ∧ n = p + s := by
  sorry

end OMA.S_opg_sum_of_prime_and_semiprime_conjecture
