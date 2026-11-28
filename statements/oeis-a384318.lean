import Mathlib

/-!
# A384318: Number of strict integer partitions of n that are not maximally refined.

Source: https://oeis.org/A384318
Credit: @esracummings31-blip

Conjecture (Gus Wiseman): a(n) is also the number of strict integer partitions of n such that
it is possible in more than one way to choose a disjoint family of strict integer partitions,
one of each part.

Conventions.
* A strict integer partition of n is a finite set of positive integers with sum n (necessarily
  a subset of {1..n}).
* Following the entry ("This is the number of strict integer partitions of n containing at
  least one sum of distinct non-parts"), a strict partition y is not maximally refined iff some
  part s of y equals the sum of a finite set T of positive integers none of which is a part of y.
* A disjoint family of strict integer partitions, one of each part of y, is a choice `f s` of a
  strict partition of s for every part s, with `f s` and `f t` disjoint for s ≠ t. Two choices
  are the same way iff they agree at every part; "more than one way" means two such families
  differ at some part.
-/

namespace OMA.S_oeis_a384318

/-- The strict integer partitions of `n`, as finite sets of positive integers. -/
def strictPartitions (n : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 n).powerset.filter (fun y => y.sum id = n)

/-- Some part of `y` is a sum of distinct non-parts (i.e. `y` is not maximally refined). -/
def NotMaximallyRefined (y : Finset ℕ) : Prop :=
  ∃ s ∈ y, ∃ T : Finset ℕ, (∀ t ∈ T, 0 < t ∧ t ∉ y) ∧ T.sum id = s

/-- `f` is a disjoint family of strict integer partitions, one of each part of `y`. -/
def IsFamily (y : Finset ℕ) (f : ℕ → Finset ℕ) : Prop :=
  (∀ s ∈ y, (∀ x ∈ f s, 0 < x) ∧ (f s).sum id = s) ∧
  (∀ s ∈ y, ∀ t ∈ y, s ≠ t → Disjoint (f s) (f t))

/-- There is more than one way to choose such a family. -/
def MoreThanOneWay (y : Finset ℕ) : Prop :=
  ∃ f g : ℕ → Finset ℕ, IsFamily y f ∧ IsFamily y g ∧ ∃ s ∈ y, f s ≠ g s

/-- A384318(n). -/
noncomputable def a (n : ℕ) : ℕ :=
  open Classical in ((strictPartitions n).filter NotMaximallyRefined).card

theorem main : ∀ n : ℕ,
    a n = (open Classical in ((strictPartitions n).filter MoreThanOneWay).card) := by
  sorry

end OMA.S_oeis_a384318
