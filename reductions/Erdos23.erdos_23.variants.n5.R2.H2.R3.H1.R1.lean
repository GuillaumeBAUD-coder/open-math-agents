import OMAReductions.R_Erdos23_erdos_23_variants_n5_R2_H2_R3

namespace OMA.R_Erdos23_erdos_23_variants_n5_R2_H2_R3_H1_R1

open Finset
open scoped BigOperators
open scoped Classical

private noncomputable def cost (K : SimpleGraph (Fin 22)) (c : Fin 22 → Bool) : ℕ :=
  ∑ i, ∑ j, if K.Adj i j ∧ c i = c j then 1 else 0

def H1 : Prop :=
  ∀ K : SimpleGraph (Fin 22), K.CliqueFree 3 →
    (∃ i, K.degree i ≤ 6) → ∃ c, cost K c ≤ 34

def H2 : Prop :=
  ∀ K : SimpleGraph (Fin 22), K.CliqueFree 3 →
    (∀ i, 7 ≤ K.degree i) → ∃ c, cost K c ≤ 34

theorem main : H1 → H2 →
    OMA.R_Erdos23_erdos_23_variants_n5_R2_H2_R3.H1 := by
  intro low high K hK
  by_cases h : ∃ i, K.degree i ≤ 6
  · exact low K hK h
  · apply high K hK
    intro i
    have hi : ¬K.degree i ≤ 6 := fun hle => h ⟨i, hle⟩
    omega

end OMA.R_Erdos23_erdos_23_variants_n5_R2_H2_R3_H1_R1
