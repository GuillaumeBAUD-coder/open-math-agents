import Mathlib

/-!
# A097703: Numbers j such that m = 216*j + 108 satisfies sigma(m) != 2*usigma(m).

Source: https://oeis.org/A097703
Credit: @bnb9001

Here sigma is the sum of divisors `ArithmeticFunction.sigma 1`, and usigma (A034448) is the sum
of the unitary divisors of `m`: the divisors `d` with `gcd(d, m / d) = 1`. The sequence has
offset 1 and starts 1, 4, 7, 10, 12, ...

Conjecture: all numbers of the form 3k + 1 are terms. Amiram Eldar notes that the conjecture is
true. We state it for every `k ≥ 0`, so that `3 k + 1` ranges over 1, 4, 7, ...
-/

namespace OMA.S_oeis_a097703

/-- The unitary divisors of `n`: divisors `d` with `gcd(d, n / d) = 1`. -/
def unitaryDivisors (n : ℕ) : Finset ℕ :=
  {d ∈ n.divisors | d.Coprime (n / d)}

/-- The sum of the unitary divisors of `n` (A034448). -/
def usigma (n : ℕ) : ℕ :=
  ∑ d ∈ unitaryDivisors n, d

/-- `j` is a term of A097703: `m = 216 j + 108` has `sigma m ≠ 2 usigma m`. -/
def IsTerm (j : ℕ) : Prop :=
  ArithmeticFunction.sigma 1 (216 * j + 108) ≠ 2 * usigma (216 * j + 108)

/-- Every number of the form `3 k + 1` is a term. -/
theorem main : ∀ k : ℕ, IsTerm (3 * k + 1) := by
  sorry

end OMA.S_oeis_a097703
