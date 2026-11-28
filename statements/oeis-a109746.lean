import Mathlib

/-!
# A109746: Number of distinct sequences of the type m^k mod n for n fixed, k>=1.

Source: https://oeis.org/A109746
Credit: @esracummings31-blip

For fixed n ≥ 2 (offset 2) and k ≥ 1, the sequence (m^k mod n)_{m ≥ 0} is periodic in m with period
n, so it is determined by the function `m ↦ m ^ k` on `ZMod n`; a(n) is the number of distinct such
functions, k = 1, 2, 3, ...

Conjectures in the entry:
* (Speculation in the original comment) a(p) = p - 1 for prime p, and a(2p) = p - 1 for odd prime p.
* (Lars Blomberg, Oct 27 2015) if n is squarefree, a(n) = lcm of (p - 1) over the primes p | n;
  if n = p^2 then a(n) = n - p + 1; if n = 2^k with k > 2 then a(n) = 2^(k-2) + k - 1.
* (Ben Whitmore, Jul 23 2020) a(n) = A002322(n) + A051903(n) - 1, where A002322 is Carmichael's
  lambda function and A051903(n) is the maximal exponent in the prime factorization of n.
-/

namespace OMA.S_oeis_a109746

/-- A109746: the number of distinct functions `m ↦ m ^ k` on `ZMod n`, `k ≥ 1`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard (Set.range fun k : ℕ => fun m : ZMod n => m ^ (k + 1))

/-- A002322: Carmichael's lambda function (Mathlib's `ArithmeticFunction.carmichael`). -/
def A002322 (n : ℕ) : ℕ := ArithmeticFunction.carmichael n

/-- A051903: maximal exponent in the prime factorization of `n` (0 for `n = 1`). -/
def A051903 (n : ℕ) : ℕ := n.primeFactors.sup n.factorization

theorem main :
    (∀ p : ℕ, p.Prime → a p = p - 1) ∧
    (∀ p : ℕ, p.Prime → p ≠ 2 → a (2 * p) = p - 1) ∧
    (∀ n : ℕ, 2 ≤ n → Squarefree n → a n = n.primeFactors.lcm (fun p => p - 1)) ∧
    (∀ p : ℕ, p.Prime → a (p ^ 2) = p ^ 2 - p + 1) ∧
    (∀ k : ℕ, 2 < k → a (2 ^ k) = 2 ^ (k - 2) + k - 1) ∧
    (∀ n : ℕ, 2 ≤ n → a n = A002322 n + A051903 n - 1) := by
  sorry

end OMA.S_oeis_a109746
