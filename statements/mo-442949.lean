import Mathlib

namespace OMA.S_mo_442949

open scoped BigOperators

/-- Direction of segment `i` after the preceding counterclockwise turns. -/
def headingAngle {n : ℕ} (turn : Fin n → ℝ) (i : Fin (n + 1)) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val), turn j

/-- The endpoint's squared distance from the starting point in the plane. -/
noncomputable def endpointSquared {n : ℕ} (len : Fin (n + 1) → ℝ) (turn : Fin n → ℝ) : ℝ :=
  Complex.normSq (∑ i, (len i : ℂ) *
    (⟨Real.cos (headingAngle turn i), Real.sin (headingAngle turn i)⟩ : ℂ))

/-- The current orders achieve a maximum among all permutations of lengths and turns. -/
def IsOptimal {n : ℕ} (len : Fin (n + 1) → ℝ) (turn : Fin n → ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin (n + 1))) (τ : Equiv.Perm (Fin n)),
    endpointSquared (len ∘ σ) (turn ∘ τ) ≤ endpointSquared len turn

/-- Any optimal length order is unimodal, and a descending length order
cannot maximize the distance with any turn order if there are at least three segments. -/
theorem main :
    ∀ (n : ℕ) (len : Fin (n + 1) → ℝ) (turn : Fin n → ℝ),
      (∀ i, 0 < len i) → Function.Injective len →
      (∀ j, 0 < turn j) → Function.Injective turn →
      (∑ j, turn j) ≤ Real.pi / 2 →
      (IsOptimal len turn →
        ∀ i j k : Fin (n + 1), i < j → j < k → min (len i) (len k) ≤ len j) ∧
      (2 ≤ n → StrictAnti len → ¬ IsOptimal len turn) := by
  sorry

end OMA.S_mo_442949
