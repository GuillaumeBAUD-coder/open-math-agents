import Mathlib

/-!
# 1/3–2/3 conjecture

Source: https://en.wikipedia.org/wiki/1/3–2/3_conjecture
Credit: @cosmaticdev

Wikipedia (1/3–2/3 conjecture, Kislitsyn 1968; Fredman and Linial 1984): in every finite
partially ordered set that is not totally ordered, there exists a pair of elements `x` and
`y` such that at least 1/3 and at most 2/3 of the linear extensions of the partial order
place `x` earlier than `y`. Equivalently, under the uniform distribution on the linear
extensions, the probability that `x` appears before `y` in a random linear extension is
between 1/3 and 2/3. A linear extension of a finite partial order is a total order compatible
with it, i.e. a listing of all elements in which `a ≤ b` implies `a` comes before `b`.

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_wp_1_3_2_3_conjecture

/-- The linear extensions of a finite partial order on `α`, represented as the listings
`f : Fin n ≃ α` (with `n = card α`) that place `a` before `b` whenever `a ≤ b`. This is a
finite set, being a subset of the fintype `Fin n ≃ α`. -/
def linearExtensions {α : Type*} [Fintype α] [PartialOrder α] : Set (Fin (Fintype.card α) ≃ α) :=
  {f | ∀ a b : α, a ≤ b → f.symm a ≤ f.symm b}

/-- The total number of linear extensions of a finite partial order on `α`. -/
noncomputable def numExtensions {α : Type*} [Fintype α] [PartialOrder α] : ℕ :=
  (linearExtensions (α := α)).ncard

/-- The number of linear extensions of a finite partial order on `α` in which `x` appears
before `y`. -/
noncomputable def extensionsBefore {α : Type*} [Fintype α] [PartialOrder α] (x y : α) : ℕ :=
  ({f ∈ linearExtensions (α := α) | f.symm x < f.symm y}).ncard

/-- The 1/3–2/3 conjecture: every finite partially ordered set that is not totally ordered
has two distinct elements `x`, `y` such that the number of linear extensions placing `x`
before `y` is between 1/3 and 2/3 of the total number of linear extensions. -/
theorem main :
    ∀ (α : Type*) [Fintype α] [PartialOrder α], ¬ Std.Total (· ≤ · : α → α → Prop) →
      ∃ x y : α, x ≠ y ∧
        numExtensions (α := α) ≤ 3 * extensionsBefore x y ∧
        3 * extensionsBefore x y ≤ 2 * numExtensions (α := α) := by
  sorry

end OMA.S_wp_1_3_2_3_conjecture
