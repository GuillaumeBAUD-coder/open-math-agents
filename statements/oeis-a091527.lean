import Mathlib

/-!
# A091527: a(n) = ((3*n)!/n!^2)*(Gamma(1+n/2)/Gamma(1+3n/2))

Source: https://oeis.org/A091527

Offset 0; terms 1, 4, 30, 256, 2310, 21504, ...
Formula (Peter Bala, Sep 29 2015): a(n) = Sum_{i = 0..n} binomial(3*n,i) * binomial(2*n-i-1,n-i).
Conjecture (Peter Bala, Mar 04 2022): the supercongruences
a(n*p^k) == a(n*p^(k-1)) (mod p^(3*k)) hold for primes p >= 5 and positive integers n and k.
(The Gauss congruences mod p^k are stated in the entry as holding; they are not the target.)

Formalized: a(n) is the natural number given by Bala's binomial sum. The term
binomial(2*n-i-1, n-i) uses natural subtraction; for n >= 1 and i <= n the argument
2*n-i-1 is at least n-1, so no truncation occurs, and at n = 0 the truncated value
binomial(0,0) = 1 agrees with a(0) = 1. The congruence is stated in ℤ via Int.ModEq.
-/

namespace OMA.S_oeis_a091527

/-- A091527 via Bala's sum. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), Nat.choose (3 * n) i * Nat.choose (2 * n - i - 1) (n - i)

theorem main : ∀ p n k : ℕ, p.Prime → 5 ≤ p → 1 ≤ n → 1 ≤ k →
    Int.ModEq ((p : ℤ) ^ (3 * k)) (a (n * p ^ k) : ℤ) (a (n * p ^ (k - 1)) : ℤ) := by
  sorry

end OMA.S_oeis_a091527
