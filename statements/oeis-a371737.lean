import Mathlib

/-!
# A371737: Number of quanimous strict integer partitions of n, meaning there is more than one set
partition with all equal block-sums.

Source: https://oeis.org/A371737
Credit: @esracummings31-blip

Conjecture: (1) Positions of 0's are A327782. (2) Positions of terms > 0 are A368459.

This file states conjecture (1) only, for n >= 1 (A327782 has offset 1). Conjecture (2), about
the Bacher-type sequence A368459, is not formalized here.

Conventions.
* A strict integer partition of n is a finite set of positive integers with sum n (necessarily a
  subset of {1..n}).
* A strict partition y is quanimous iff it can be partitioned into two or more blocks with equal
  sums (the trivial one-block set partition always has all block-sums equal, so "more than one
  set partition with all equal block-sums" means exactly this). A set partition of y is a finite
  family of nonempty, pairwise disjoint finite sets whose union is y.
* A327782: numbers n >= 1 that cannot be written as a sum of two or more distinct (positive)
  parts with the largest part dividing n.
-/

namespace OMA.S_oeis_a371737

/-- The strict integer partitions of `n`, as finite sets of positive integers. -/
def strictPartitions (n : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 n).powerset.filter (fun y => y.sum id = n)

/-- `y` can be partitioned into two or more blocks with equal sums. -/
def Quanimous (y : Finset ℕ) : Prop :=
  ∃ B : Finset (Finset ℕ), 2 ≤ B.card ∧ (∀ b ∈ B, b.Nonempty) ∧
    (∀ b ∈ B, ∀ c ∈ B, b ≠ c → Disjoint b c) ∧ B.biUnion id = y ∧
    ∃ s, ∀ b ∈ B, b.sum id = s

/-- A371737(n). -/
noncomputable def a (n : ℕ) : ℕ :=
  open Classical in ((strictPartitions n).filter Quanimous).card

/-- Membership in A327782. -/
def InA327782 (n : ℕ) : Prop :=
  1 ≤ n ∧ ¬ ∃ T : Finset ℕ, 2 ≤ T.card ∧ (∀ x ∈ T, 0 < x) ∧ T.sum id = n ∧
    ∃ L ∈ T, (∀ x ∈ T, x ≤ L) ∧ L ∣ n

/-- Conjecture (1): for n >= 1, a(n) = 0 iff n is in A327782. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (a n = 0 ↔ InA327782 n) := by
  sorry

end OMA.S_oeis_a371737
