import Mathlib

/-!
# A046060: 5-multiperfect numbers.

Source: https://oeis.org/A046060
Credit: @darealpandaboi

Conjecture (Georgi Guninski, Jul 25 2012): the sequence is finite (and probably the listed terms
are the only ones; cf. Flammenkamp's link).

Translation notes.
* n is 5-multiperfect when sigma(n) = 5n, where sigma is the sum of divisors,
  ArithmeticFunction.sigma 1. n = 0 is excluded (sigma 0 = 0 = 5 * 0 in Mathlib).
* Only the finiteness is stated; the parenthetical probably these are the only terms is a
  heuristic remark, not a precise claim about an explicit list.
-/

namespace OMA.S_oeis_a046060

theorem main : {n : ℕ | 0 < n ∧ ArithmeticFunction.sigma 1 n = 5 * n}.Finite := by
  sorry

end OMA.S_oeis_a046060
