import Mathlib

/-!
# 1/3–2/3 conjecture

Source: https://en.wikipedia.org/wiki/1/3%E2%80%932/3_conjecture
Credit: @ihateSAS

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source: the 1/3–2/3 conjecture asks whether every finite partially ordered set that is not
totally ordered contains two elements `x` and `y` such that the probability that `x` appears before
`y` in a random linear extension is between `1/3` and `2/3`.

So the proposition formalized below is: for every finite partial order that is not total there are
distinct `x` and `y` with `3 * (number of linear extensions putting x before y)` at least the total
number of linear extensions and at most twice it.
-/

namespace OMA.S_wp_1_3_2_3_conjecture

-- definitions the statement needs (no sorry, no axiom)

/-- A permutation of `α` is a **linear extension** of the order when it is strictly order
preserving. -/
def IsLinearExtension (α : Type) [Fintype α] [PartialOrder α]
    (e : α ≃ Fin (Fintype.card α)) : Prop :=
  ∀ a b : α, a < b → e a < e b

/-- The number of linear extensions of the order. -/
noncomputable def linearExtensionCount (α : Type) [Fintype α] [PartialOrder α] : ℕ :=
  Nat.card { e : α ≃ Fin (Fintype.card α) // IsLinearExtension α e }

/-- The number of linear extensions in which `x` appears before `y`. -/
noncomputable def linearExtensionCountBefore (α : Type) [Fintype α] [PartialOrder α]
    (x y : α) : ℕ :=
  Nat.card { e : α ≃ Fin (Fintype.card α) // IsLinearExtension α e ∧ e x < e y }

/-- The 1/3–2/3 conjecture. -/
theorem main : ∀ (α : Type) [Fintype α] [DecidableEq α] [PartialOrder α],
    (∃ x y : α, ¬ x ≤ y ∧ ¬ y ≤ x) →
      ∃ x y : α, x ≠ y ∧
        3 * linearExtensionCountBefore α x y ≥ linearExtensionCount α ∧
          3 * linearExtensionCountBefore α x y ≤ 2 * linearExtensionCount α := by
  sorry

end OMA.S_wp_1_3_2_3_conjecture
