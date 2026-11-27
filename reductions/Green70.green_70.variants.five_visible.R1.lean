import FormalConjectures.GreensOpenProblems.«70»

/-!
# Reduction R1 of Green70.green_70.variants.five_visible

The case ℓ = 5 of the big-line-big-clique question follows from the empty-pentagon
theorem (H1) together with the trivial small-k case (H2).
-/

open scoped Finset

namespace OMA.R_Green70_green_70_variants_five_visible_R1

/-- Generalised empty pentagon theorem [ABBCDHKLPW11, Theorem 3]: for every k ≥ 2, every
sufficiently large finite planar set contains k collinear points or an empty pentagon. -/
def H1 : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ n₀ : ℕ, ∀ P : Finset (ℝ × ℝ),
    n₀ ≤ #P → Green70.HasCollinear k P ∨ Green70.HasEmptyPentagon P

/-- The case k = 1: any nonempty point set has a collinear singleton. -/
def H2 : Prop := ∀ P : Finset (ℝ × ℝ), 1 ≤ #P → Green70.HasCollinear 1 P

theorem main : H1 → H2 → type_of% @Green70.green_70.variants.five_visible := by
  intro h1 h2 k
  by_cases hk : k < 2
  · interval_cases k
    · exact ⟨0, fun P _ => Or.inl ⟨∅, Finset.empty_subset P, by simp,
        by simpa using collinear_empty ℝ (ℝ × ℝ)⟩⟩
    · exact ⟨1, fun P hP => Or.inl (h2 P hP)⟩
  · obtain ⟨n₀, hn₀⟩ := h1 k (by omega)
    exact ⟨n₀, fun P hP => (hn₀ P hP).imp_right Green70.HasEmptyPentagon.hasMutuallyVisible⟩

end OMA.R_Green70_green_70_variants_five_visible_R1
