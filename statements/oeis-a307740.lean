import Mathlib

/-!
# A307740: Numbers k such that k divides lcm(tau(k), sigma(k))

Source: https://oeis.org/A307740
Credit: @xor2k

Formalizes the OEIS A307740 conjecture: multiply-perfect numbers (A007691) are terms.

Conventions: `tau(k)` is the number of divisors `(Nat.divisors k).card` and `sigma(k)` is
`ArithmeticFunction.sigma 1 k`. A multiply-perfect number (A007691, offset 1) is a positive
integer `k` with `k ∣ sigma(k)`; A307740 likewise ranges over positive integers.
-/

namespace OMA.S_oeis_a307740

open ArithmeticFunction

/-- Membership in A307740: `k` is positive and divides `lcm(tau(k), sigma(k))`. -/
def InA307740 (k : ℕ) : Prop :=
  0 < k ∧ k ∣ Nat.lcm (Nat.divisors k).card (sigma 1 k)

/-- Membership in A007691: `k` is positive and divides `sigma(k)`. -/
def MultiplyPerfect (k : ℕ) : Prop :=
  0 < k ∧ k ∣ sigma 1 k

/-- Every multiply-perfect number is a term of A307740. -/
theorem main : ∀ k : ℕ, MultiplyPerfect k → InA307740 k := by
  sorry

end OMA.S_oeis_a307740
