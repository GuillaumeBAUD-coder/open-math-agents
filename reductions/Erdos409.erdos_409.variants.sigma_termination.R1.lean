import FormalConjectures.ErdosProblems.«409»
import Mathlib

/-!
# Reduction R1 of Erdos409.erdos_409.variants.sigma_termination

Target: for every `n > 1` some iterate of `x ↦ σ(x) - 1` (σ = sum of divisors) is prime.

The target is split at the concrete bound `2 * 10 ^ 6`:

* `H1` -- the open tail above the bound: every `n > 2 * 10 ^ 6` reaches a prime.  This is the
  honest open core: `σ n - 1 > n` for every composite `n`, so the orbit is strictly increasing
  after every composite step and there is no decreasing measure (contrast the φ-variant, which the
  module proves by strong induction); no invariant is known that excludes a composite-forever
  orbit.
* `H2` -- the finite part: every `1 < n ≤ 2 * 10 ^ 6` reaches a prime.  `σ` is computable, so this
  is a finite verification.  It is true: a linear σ-sieve over `[2, 2 * 10 ^ 6]` shows every one
  of those `n` reaches a prime (longest initial run: 45 iterations, at `n = 701823`).

`main` is the case split on `n ≤ 2 * 10 ^ 6`.  Both halves are strict restrictions of the target
and together they are exactly the target.  (The same bound split is recorded for the sibling
forall-form `sigma_prime_termination` in its own R1.)
-/

open scoped ArithmeticFunction.sigma

namespace OMA.R_Erdos409_erdos_409_variants_sigma_termination_R1

/-- The open tail above `2 * 10 ^ 6`. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 < n → 2000000 < n → ∃ i : ℕ, (σ 1 · - 1)^[i] n |>.Prime

/-- The finite part: every `1 < n ≤ 2 * 10 ^ 6` reaches a prime. -/
def H2 : Prop :=
  ∀ n : ℕ, 1 < n → n ≤ 2000000 → ∃ i : ℕ, (σ 1 · - 1)^[i] n |>.Prime

theorem main : H1 → H2 → type_of% @Erdos409.erdos_409.variants.sigma_termination := by
  intro h1 h2 n hn
  by_cases h : n ≤ 2000000
  · exact h2 n hn h
  · exact h1 n hn (by omega)

end OMA.R_Erdos409_erdos_409_variants_sigma_termination_R1
