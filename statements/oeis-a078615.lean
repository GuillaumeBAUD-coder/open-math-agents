import Mathlib

/-!
# A078615: a(n) = rad(n)^2, where rad is the squarefree kernel of n (A007947)

Source: https://oeis.org/A078615
Credit: @niclorusso

Conjecture (in the comments of A078615, see the Broughan link there): only 1 and 1782 satisfy
a(k) = sigma(k).

Conventions:
* rad(k) is the squarefree kernel of k, the product of the distinct primes dividing k (rad(1) = 1):
  `∏ p ∈ k.primeFactors, p`.
* sigma(k) is the sum of the divisors of k, Mathlib's `ArithmeticFunction.sigma 1 k`.
* k ranges over the positive integers (the offset of the sequence is 1).
* "only 1 and 1782 satisfy" is stated as a set equality; both do satisfy it:
  rad(1782) = rad(2 * 3^4 * 11) = 66 and 66^2 = 4356 = sigma(1782).
-/

namespace OMA.S_oeis_a078615

open ArithmeticFunction

/-- The squarefree kernel of `k`: the product of the distinct primes dividing `k`. -/
def rad (k : ℕ) : ℕ := ∏ p ∈ k.primeFactors, p

/-- The conjecture on A078615: the positive `k` with `rad(k)^2 = sigma(k)` are exactly 1 and 1782. -/
theorem main : {k : ℕ | 0 < k ∧ rad k ^ 2 = sigma 1 k} = {1, 1782} := by
  sorry

end OMA.S_oeis_a078615
