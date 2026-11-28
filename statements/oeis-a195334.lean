import Mathlib

/-!
# A195334: Numbers the sum of whose even divisors is 2 times a prime.

Source: https://oeis.org/A195334
Credit: @marcelopierry

Conjecture (R. J. Mathar, Sep 15 2011, in the formulas of A195334): a(n) = 2*A023194(n).

Conventions:
* Both sequences have offset 1 and list, in increasing order, the positive integers with their
  property; the n-th term is `Nat.nth` at index n - 1 (if a sequence were finite, `Nat.nth`
  gives 0 past its end, for both sides alike).
* A195334: k such that the sum of the even divisors of k equals 2*q for a prime q (data 4, 8,
  18, 32, 50, 128, ...). For k = 0 there are no divisors, so 0 is not a term.
* A023194: m such that sigma(m), the sum of the divisors of m, is prime (data 2, 4, 9, 16, 25,
  64, ...).
-/

namespace OMA.S_oeis_a195334

/-- The sum of the even divisors of k. -/
def evenDivSum (k : ℕ) : ℕ := ∑ d ∈ k.divisors.filter Even, d

/-- Membership in A195334. -/
def InA195334 (k : ℕ) : Prop := ∃ q : ℕ, q.Prime ∧ evenDivSum k = 2 * q

/-- Membership in A023194: sigma(m) is prime. -/
def InA023194 (m : ℕ) : Prop := (∑ d ∈ m.divisors, d).Prime

/-- Mathar's conjecture: a(n) = 2*A023194(n). -/
theorem main : ∀ n : ℕ, 1 ≤ n → Nat.nth InA195334 (n - 1) = 2 * Nat.nth InA023194 (n - 1) := by
  sorry

end OMA.S_oeis_a195334
