import Mathlib

/-!
# A112399: a(n) = Sum_{k=1..n, gcd(k,n)=1} mu(k), where mu(k) = A008683(k) (the Moebius function).

Source: https://oeis.org/A112399 (conjectures of Jamie Morken, Sep 18 2026).
Credit: @esracummings31-blip

Conjectures, for n >= 1:
  a(n) = Sum_{d|n, mu(d)!=0} (Sum_{m=1..n/d, gcd(m,d)=1} mu(m)).
  a(n) = Sum_{q=1..n, A007947(q)|n} A002321(floor(n/q)),
where A007947(q) is the squarefree kernel (product of the distinct primes dividing q) and
A002321(x) = Sum_{k=1..x} mu(k) is the Mertens function. Natural division `n / q` is floor.
-/

namespace OMA.S_oeis_a112399

open scoped ArithmeticFunction.Moebius

/-- A112399: the sum of `μ k` over `1 ≤ k ≤ n` with `gcd(k, n) = 1`. -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 n with Nat.Coprime k n, μ k

/-- The Mertens function A002321. -/
def mertens (x : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 x, μ k

/-- The squarefree kernel A007947. -/
def rad (q : ℕ) : ℕ := ∏ p ∈ q.primeFactors, p

theorem main :
    (∀ n, 1 ≤ n → a n = ∑ d ∈ n.divisors with μ d ≠ 0,
      ∑ m ∈ Finset.Icc 1 (n / d) with Nat.Coprime m d, μ m) ∧
    (∀ n, 1 ≤ n → a n = ∑ q ∈ Finset.Icc 1 n with rad q ∣ n, mertens (n / q)) := by
  sorry

end OMA.S_oeis_a112399
