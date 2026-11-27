import Mathlib

/-!
# OEIS A387043

Source: https://oeis.org/A387043 (OEIS Foundation, CC BY-SA 4.0).
Credit: @bcrowther86-eng

A387043(n) is the number of ways to write `n` as
`(1 + (n mod 2)) * p + prime(k) + prime(k+1) + prime(k+2)`, where `p` is a prime and `k` is a
positive integer (`prime(k)` is the `k`-th prime, `prime(1) = 2`).

Conjecture (from the sequence entry):
(i) a(2n) > 0 for all n > 12. In other words, any even number greater than 25 is the sum of a
prime and three consecutive primes.
(ii) a(2n+1) > 0 for all n > 135. In other words, any odd number greater than 272 can be written
as the sum of twice a prime and three consecutive primes.

We state both parts. `Nat.nth Nat.Prime i` is the `(i+1)`-th prime (`Nat.nth Nat.Prime 0 = 2`),
so the positive index `k` of the source corresponds to `i = k - 1 : ℕ`.
-/

namespace OMA.S_oeis_a387043

/-- `m` is a sum of three consecutive primes `prime(k) + prime(k+1) + prime(k+2)`, `k ≥ 1`. -/
def IsSumOfThreeConsecutivePrimes (m : ℕ) : Prop :=
  ∃ i : ℕ, m = Nat.nth Nat.Prime i + Nat.nth Nat.Prime (i + 1) + Nat.nth Nat.Prime (i + 2)

theorem main :
    (∀ n : ℕ, 12 < n → ∃ p m : ℕ, p.Prime ∧ IsSumOfThreeConsecutivePrimes m ∧ 2 * n = p + m) ∧
    (∀ n : ℕ, 135 < n →
      ∃ p m : ℕ, p.Prime ∧ IsSumOfThreeConsecutivePrimes m ∧ 2 * n + 1 = 2 * p + m) := by
  sorry

end OMA.S_oeis_a387043
