import Mathlib

/-!
# A019434: conjectures on the Fermat primes

Source: https://oeis.org/A019434
Credit: @jagraj28

A019434 lists the Fermat primes: primes of the form `2^(2^k) + 1` for some `k ≥ 0`
(3, 5, 17, 257, 65537). The entry records these conjectures:

0. (Dmitry Kamenetsky, 2008) there are only 5 terms;
and, from Jaroslav Krizek (2016), the Fermat primes are exactly:
1. the primes `p` such that `phi(p) = 2 * phi(p - 2)`;
2. the primes `p` such that `phi(p) = 2 * phi(p - 1) = 2 * phi(p - 2)`;
3. the primes `p` such that `p = sigma(phi(p - 2)) + 2`;
4. the primes `p` such that `phi(p - 1) + 1` divides `p + 1`;
5. the numbers `n` such that `sigma(n - 1) = 2 * sigma(n) - 5`.

`main` is the conjunction of 0 to 4.

Conventions and choices:
* Conjecture 0 is stated as: the set of Fermat primes is `{3, 5, 17, 257, 65537}`, the five
  known terms (all five are prime, so this is the same as having exactly 5 terms).
* In 1 to 4 the primes range over `p ≥ 3`. For `p = 2` the expressions use `phi(0)`, which the
  OEIS leaves undefined (Mathlib sets `phi 0 = 0` and `sigma 0 = 0`). With Mathlib values,
  `p = 2` would satisfy condition 3 (`2 = sigma(phi 0) + 2`), an artifact of the convention
  that the source does not intend. 2 is not a Fermat prime.
* Conjecture 5 is left out: read literally, it is false at `n = 2`, because
  `sigma(1) = 1 = 2 * sigma(2) - 5` and 2 is not a Fermat prime. Any repair (for example
  `n ≥ 3`) would be a guess at the author's intent.
* All equalities between values of `phi` and `sigma` are in `ℕ`; no subtraction occurs in them
  except `p - 1` and `p - 2` with `p ≥ 3`.
-/

namespace OMA.S_oeis_a019434

/-- `p` is a Fermat prime (OEIS A019434): a prime of the form `2^(2^k) + 1` with `k ≥ 0`. -/
def IsFermatPrime (p : ℕ) : Prop :=
  p.Prime ∧ ∃ k : ℕ, p = 2 ^ (2 ^ k) + 1

/-- Conjectures 0 to 4 of OEIS A019434. -/
theorem main :
    {p : ℕ | IsFermatPrime p} = {3, 5, 17, 257, 65537} ∧
    (∀ p : ℕ, 3 ≤ p → (IsFermatPrime p ↔
      p.Prime ∧ Nat.totient p = 2 * Nat.totient (p - 2))) ∧
    (∀ p : ℕ, 3 ≤ p → (IsFermatPrime p ↔
      p.Prime ∧ Nat.totient p = 2 * Nat.totient (p - 1) ∧
        2 * Nat.totient (p - 1) = 2 * Nat.totient (p - 2))) ∧
    (∀ p : ℕ, 3 ≤ p → (IsFermatPrime p ↔
      p.Prime ∧ p = (ArithmeticFunction.sigma 1) (Nat.totient (p - 2)) + 2)) ∧
    (∀ p : ℕ, 3 ≤ p → (IsFermatPrime p ↔
      p.Prime ∧ Nat.totient (p - 1) + 1 ∣ p + 1)) := by
  sorry

end OMA.S_oeis_a019434
