import Mathlib

/-!
# 1/3–2/3 conjecture

Source: https://en.wikipedia.org/wiki/1/3–2/3_conjecture
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_wp_1_3_2_3_conjecture

universe u

/-- A linear extension of a finite partial order, represented by the bijection sending each
element to its position in the extension. -/
noncomputable def linearExtensions (α : Type u) [Finite α] [PartialOrder α] :
    Set (α ≃ Fin (Nat.card α)) :=
  {e | ∀ x y : α, x ≤ y → e x ≤ e y}

/-- The uniform probability that `x` occurs before `y` in a random linear extension,
expressed as the ratio of the corresponding finite counts. -/
noncomputable def probBefore (α : Type u) [Finite α] [PartialOrder α] (x y : α) : ℝ :=
  (((linearExtensions α) ∩ {e | e x < e y}).ncard : ℝ) /
    ((linearExtensions α).ncard : ℝ)

theorem main :
    ∀ {α : Type u} [Finite α] [PartialOrder α], ¬ Std.Total (α := α) (· ≤ ·) →
      ∃ x y : α, (1 / 3 : ℝ) ≤ probBefore α x y ∧ probBefore α x y ≤ (2 / 3 : ℝ) := by
  sorry

end OMA.S_wp_1_3_2_3_conjecture
