import Mathlib

/-!
# Two-sided subgroup sums of a positive semidefinite matrix

Source: Malkoun, https://mathoverflow.net/questions/456248 (CC BY-SA 4.0).
Credit: @connoranderson.

The proposed positive lower bound fails even for a rank-two Gram matrix
with positive diagonal and for groups that are products of symmetric groups
on disjoint blocks. The explicit example has 48 indices.
-/

namespace OMA.S_mo_456248

open scoped ComplexOrder

noncomputable def twoSided {α : Type} [Fintype α] (H : Matrix α α ℂ)
    (G K : Subgroup (Equiv.Perm α)) : ℂ := by
  classical
  exact ∑ σ : G, ∑ τ : K, ∏ i, H (σ.val i) (τ.val i)

/-- All permutations preserving each fiber of a labeling. -/
def IsPartitionGroup {α : Type} (G : Subgroup (Equiv.Perm α)) : Prop :=
  ∃ c : α → α, ∀ σ : Equiv.Perm α, σ ∈ G ↔ ∀ i, c (σ i) = c i

theorem main : ¬ ∀ (α : Type) [Fintype α] (G K : Subgroup (Equiv.Perm α)),
    IsPartitionGroup G → IsPartitionGroup K → ∃ c : ℝ, 0 < c ∧
      ∀ H : Matrix α α ℂ, H.PosSemidef → H.rank = 2 →
        c * (∏ i, (H i i).re) ≤ (twoSided H G K).re := by
  sorry

end OMA.S_mo_456248
