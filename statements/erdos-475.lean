import Mathlib

/-!
# Erdős Problem 475

Source: https://www.erdosproblems.com/475
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_erdos_475

/-- A rearrangement is valid when its positive-length partial sums are all distinct. -/
def validOrdering {α : Type} [AddCommMonoid α] (l : List α) : Prop :=
  ∀ m n : ℕ, 1 ≤ m → m ≤ l.length → 1 ≤ n → n ≤ l.length →
    (l.take m).sum = (l.take n).sum → m = n

theorem main :
    ∀ (p : ℕ) [Fact p.Prime] (A : Finset (ZMod p)), (∀ a ∈ A, a ≠ 0) →
      ∃ l : List (ZMod p), l.Nodup ∧ l.toFinset = A ∧ validOrdering l := by
  sorry

end OMA.S_erdos_475
