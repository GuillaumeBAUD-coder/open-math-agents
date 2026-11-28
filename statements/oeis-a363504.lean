import Mathlib.Data.Nat.Factors
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Bounds.Basic

/-!
# OEIS A363504: the prime-Omega greedy permutation

Source: https://oeis.org/A363504 (Scott R. Shannon, June 6, 2023).

The sequence starts with 1, 2. Each later term is the least unused positive
multiple of prime(Omega(previous term)), where Omega counts prime factors
with multiplicity. `primeFactorsList.length` is exactly this count.
`Nat.nth Nat.Prime` is zero-indexed, so its index is Omega-1. The previous
term is always greater than 1 in this rule; the natural subtraction only
extends the selector to irrelevant inputs 0 and 1.

Lean indexing starts at zero: `a 0 = 1`, `a 1 = 2`. The step at `n` produces
`a (n+2)` and excludes the entire prefix through `a (n+1)`. The target is
existence and the full permutation assertion recorded as a conjecture.
-/

namespace OMA.S_oeis_a363504

noncomputable def selectedPrime (x : ℕ) : ℕ :=
  Nat.nth Nat.Prime (x.primeFactorsList.length - 1)

def Greedy (a : ℕ → ℕ) : Prop :=
  a 0 = 1 ∧ a 1 = 2 ∧ ∀ n,
    IsLeast {m : ℕ | 0 < m ∧ selectedPrime (a (n+1)) ∣ m ∧
      ∀ i ≤ n+1, a i ≠ m} (a (n+2))

theorem main : (∃ a, Greedy a) ∧ ∀ a, Greedy a →
    Function.Injective a ∧ Set.range a = Set.Ioi 0 := by
  sorry

end OMA.S_oeis_a363504
