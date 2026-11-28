import Mathlib

/-!
# A364303: Square array T(n,k) = [x^k] (1 - x)^(2*k) * Legendre_P(n*k, (1 + x)/(1 - x))

Source: https://oeis.org/A364303

Definition: square array read by ascending antidiagonals,
T(n,k) = [x^k] (1 - x)^(2*k) * Legendre_P(n*k, (1 + x)/(1 - x)) for n, k >= 0 (offset 0).
The entry gives the formula T(n,k) = Sum_{i = 0..k} binomial(n*k, k-i)^2 * binomial((n-2)*k+i-1, i),
which follows from P_N(y) = Sum_j C(N,j)^2 ((y-1)/2)^(N-j) ((y+1)/2)^j.

Conjecture (Peter Bala, 2023, comment line of the entry): each row sequence k -> T(n,k)
satisfies the supercongruences T(n, m*p^r) == T(n, m*p^(r-1)) (mod p^(3*r)) for all primes
p >= 5 and all positive integers m and r. (The case n = 0, the signed central binomial
coefficients, is cited as known; it is included since the conjecture is stated for each row.)

Formalized: a(n) is valued in ℤ via the entry's sum formula; binomial((n-2)*k+i-1, i) is the
generalized binomial coefficient `Ring.choose` with an integer (possibly negative) top argument,
which is what the Legendre expansion yields for n = 0, 1. The congruence is written as
divisibility of the difference in ℤ. Quantifiers: all n >= 0, primes p >= 5, m >= 1, r >= 1.
-/

namespace OMA.S_oeis_a364303

/-- T(n,k) = Sum_{i=0..k} C(n*k, k-i)^2 * C((n-2)*k + i - 1, i), generalized binomial. -/
def T (n k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (k + 1),
    ((Nat.choose (n * k) (k - i) : ℤ)) ^ 2 *
      Ring.choose (((n : ℤ) - 2) * (k : ℤ) + (i : ℤ) - 1) i

theorem main : ∀ n p m r : ℕ, p.Prime → 5 ≤ p → 1 ≤ m → 1 ≤ r →
    ((p : ℤ) ^ (3 * r)) ∣ T n (m * p ^ r) - T n (m * p ^ (r - 1)) := by
  sorry

end OMA.S_oeis_a364303
