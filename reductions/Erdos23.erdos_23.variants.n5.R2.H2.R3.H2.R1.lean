import OMAReductions.R_Erdos23_erdos_23_variants_n5_R2_H2_R3

namespace OMA.R_Erdos23_erdos_23_variants_n5_R2_H2_R3_H2_R1

open Finset SimpleGraph
open scoped BigOperators Classical

private noncomputable def cost (K : SimpleGraph (Fin 22)) (c : Fin 22 → Bool) : ℕ :=
  ∑ i, ∑ j, if K.Adj i j ∧ c i = c j then (1 : ℕ) else 0

private def conclusion (K : SimpleGraph (Fin 22)) : Prop :=
  (∃ i, K.degree i ≤ 6) ∨
    10 ≤ (univ.filter (fun i => K.degree i ≤ 7)).card

def H1 : Prop :=
  ∀ K : SimpleGraph (Fin 22), K.CliqueFree 3 →
    IsLeast (Set.range (cost K)) 34 →
    (∃ i, K.degree i ≤ 6) → conclusion K

def H2 : Prop :=
  ∀ K : SimpleGraph (Fin 22), K.CliqueFree 3 →
    IsLeast (Set.range (cost K)) 34 →
    (∀ i, 7 ≤ K.degree i) → conclusion K

theorem main : H1 → H2 →
    OMA.R_Erdos23_erdos_23_variants_n5_R2_H2_R3.H2 := by
  intro low high K tri least
  by_cases h : ∃ i, K.degree i ≤ 6
  · exact low K tri least h
  · apply high K tri least
    intro i
    have hi : ¬K.degree i ≤ 6 := fun hle => h ⟨i, hle⟩
    omega

end OMA.R_Erdos23_erdos_23_variants_n5_R2_H2_R3_H2_R1
