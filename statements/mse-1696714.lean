import Mathlib

/-!
# Centers and derived subgroups of finite groups of equal order

Question by bfhaha on Mathematics Stack Exchange (2016), CC BY-SA 3.0.
Source: https://math.stackexchange.com/questions/1696714
Credit: @RobVanProd

For finite groups G1 and G2 of the same order, does a strictly smaller derived
subgroup in G1 force its center to have at least as many elements as G2's center?

The statement preserves the question's two hypotheses and the direction of both
cardinality comparisons. Mathlib's commutator is the derived subgroup.
-/

namespace OMA.S_mse_1696714

theorem main : ∀ (G₁ G₂ : Type) [Group G₁] [Group G₂] [Finite G₁] [Finite G₂],
    Nat.card G₁ = Nat.card G₂ →
    Nat.card (commutator G₁) < Nat.card (commutator G₂) →
    Nat.card (Subgroup.center G₂) ≤ Nat.card (Subgroup.center G₁) := by
  sorry

end OMA.S_mse_1696714
