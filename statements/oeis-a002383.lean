import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Defs

/-!
# A002383: intersection of two sets of primes defined by repunits

Thomas Ordowski conjectured that the primes of the form `b² + b + 1`,
with 3 omitted, are exactly the primes in both A085104 and A059055.
A085104 uses repunits with at least three digits in a base of at least two.
The quotient in A059055 is an exact division.

Sources
- https://oeis.org/A002383
- https://oeis.org/A085104
- https://oeis.org/A059055
- https://oeis.org/A225148
-/

namespace OMA.S_oeis_a002383

open Finset

def quadraticRepunit (p : ℕ) : Prop :=
  ∃ b : ℕ, 2 ≤ b ∧ p = b ^ 2 + b + 1

def repunit (p : ℕ) : Prop :=
  ∃ b k : ℕ, 2 ≤ b ∧ 3 ≤ k ∧ p = ∑ j ∈ range k, b ^ j

def successorQuotient (p : ℕ) : Prop :=
  ∃ b k : ℕ, 0 < b ∧ 0 < k ∧ p * (b + 1) = b ^ k + 1

theorem main : ∀ p : ℕ, p.Prime →
    (quadraticRepunit p ↔ repunit p ∧ successorQuotient p) := by
  sorry

end OMA.S_oeis_a002383
