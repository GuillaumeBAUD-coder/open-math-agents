import Mathlib

/-!
# A394399: Numbers k in A014574 (averages of twin prime pairs) such that gcd(k, sigma(k)) = 3

Source: https://oeis.org/A394399
Credit: @xor2k

Formalizes the OEIS A394399 conjecture: all terms are of the form 2*m^2 (twice a perfect square;
A001105).

Conventions:
- A014574 (averages of twin prime pairs) is the set of `k` with `k - 1` and `k + 1` both prime
  (natural subtraction; for `k = 0` the number `k - 1 = 0` is not prime, so nothing changes).
- `sigma(k)` is the sum of divisors, `ArithmeticFunction.sigma 1 k`; `gcd` is `Nat.gcd`.
- A term is any `k` in A014574 with `gcd(k, sigma(k)) = 3`; the claim is that every such `k`
  equals `2 * m ^ 2` for some natural `m`.
-/

namespace OMA.S_oeis_a394399

/-- `k` is in A014574, the averages of twin prime pairs: `k - 1` and `k + 1` are both prime. -/
def IsTwinAverage (k : ℕ) : Prop :=
  (k - 1).Prime ∧ (k + 1).Prime

/-- Every average `k` of a twin prime pair with `gcd(k, sigma(k)) = 3` is twice a square. -/
theorem main :
    ∀ k : ℕ, IsTwinAverage k → Nat.gcd k (ArithmeticFunction.sigma 1 k) = 3 →
      ∃ m : ℕ, k = 2 * m ^ 2 := by
  sorry

end OMA.S_oeis_a394399
