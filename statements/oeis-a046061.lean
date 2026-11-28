import Mathlib

/-!
# A046061: 6-multiperfect numbers.

Source: https://oeis.org/A046061
Credit: @darealpandaboi

Conjecture (Georgi Guninski, Jul 25 2012): the sequence is finite (and probably the listed terms
are the only ones; cf. Flammenkamp's link).

Translation notes.
* n is 6-multiperfect when sigma(n) = 6n, where sigma is the sum of divisors,
  ArithmeticFunction.sigma 1. n = 0 is excluded (sigma 0 = 0 = 6 * 0 in Mathlib).
* Only the finiteness is stated; the parenthetical probably these are the only terms is a
  heuristic remark, not a precise claim about an explicit list.
-/

namespace OMA.S_oeis_a046061

theorem main : {n : ℕ | 0 < n ∧ ArithmeticFunction.sigma 1 n = 6 * n}.Finite := by
  sorry

end OMA.S_oeis_a046061
