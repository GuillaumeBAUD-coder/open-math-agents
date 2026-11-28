import Mathlib

/-!
# A085710: Smallest k such that kn+1 is a semiprime.

Source: https://oeis.org/A085710
Credit: @divmxnd0x

Conjecture (stated in A085710): for every `n > 2` there exists a number `k < n` such that
`n k + 1` is a semiprime.

Formalization notes:
* A semiprime is a product of two primes (not necessarily distinct): exactly two prime factors
  counted with multiplicity. `k` ranges over the positive integers (the terms of A085710 are
  `≥ 1`).
-/

namespace OMA.S_oeis_a085710

/-- `m` is a semiprime. -/
def IsSemiprime (m : ℕ) : Prop := (Nat.primeFactorsList m).length = 2

/-- For `n > 2` there is `0 < k < n` with `n k + 1` a semiprime. -/
theorem main : ∀ n : ℕ, 2 < n → ∃ k : ℕ, 0 < k ∧ k < n ∧ IsSemiprime (n * k + 1) := by
  sorry

end OMA.S_oeis_a085710
