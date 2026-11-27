import OMAReductions.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1

/-! Divide the upper-bound graph table at order nine. -/

open SimpleGraph

namespace OMA.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1_H2_R1

/-- The first six orders, where small families of explicit triangle-free hosts suffice. -/
def H1 : Prop := ∀ k : Fin 9,
  let n := k.val + 4
  let q := (![5, 8, 12, 16, 20, 27, 33, 41, 49] : Fin 9 → ℕ) k
  n ≤ 9 → ∀ G : SimpleGraph (Fin n), G.Connected → G.edgeSet.ncard = q + 1 →
    ∃ C : SimpleGraph (Fin (2*n-1)), C.CliqueFree 3 ∧ ¬ G ⊑ Cᶜ

/-- The orders ten, eleven and twelve. -/
def H2 : Prop := ∀ k : Fin 9,
  let n := k.val + 4
  let q := (![5, 8, 12, 16, 20, 27, 33, 41, 49] : Fin 9 → ℕ) k
  10 ≤ n → ∀ G : SimpleGraph (Fin n), G.Connected → G.edgeSet.ncard = q + 1 →
    ∃ C : SimpleGraph (Fin (2*n-1)), C.CliqueFree 3 ∧ ¬ G ⊑ Cᶜ

theorem main : H1 → H2 → OMA.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1.H2 := by
  intro small large k
  by_cases h : k.val + 4 ≤ 9
  · exact small k h
  · exact large k (by omega)

end OMA.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1_H2_R1