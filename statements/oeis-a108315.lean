import Mathlib

/-!
# A108315: composites `n` whose prime-factor power sum `a^v + b^v + ⋯` is prime.

Source: https://oeis.org/A108315
Credit: @cjchaffin

If `n` has prime factorization `a * b * c * ⋯` written with repetition, and `v` is the
number of prime factors counted with multiplicity, the term condition is that
`a^v + b^v + c^v + ⋯` is prime. Example: `26 = 2*13` has `v = 2` and
`2^2 + 13^2 = 173`, a prime. Consecutive terms include `(74, 75)`, `(152, 153)`,
`(325, 326)`, …

Conjecture (on the OEIS page): there are infinitely many consecutive values.

Conventions: offset 1; `Nat.primeFactorsList` is the factorization with repetition;
composite means `1 < n` and `n` is not prime.
-/

namespace OMA.S_oeis_a108315

def factorPowerSum (n : ℕ) : ℕ :=
  let fac := n.primeFactorsList
  let v := fac.length
  (fac.map (fun p => p ^ v)).sum

def IsA108315 (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ (factorPowerSum n).Prime

theorem main : {n : ℕ | IsA108315 n ∧ IsA108315 (n + 1)}.Infinite := by
  sorry

end OMA.S_oeis_a108315
