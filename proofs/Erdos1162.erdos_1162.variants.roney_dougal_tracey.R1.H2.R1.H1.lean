import OMAReductions.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R1
import Mathlib

theorem OMA.solution : OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R1.H1 := by
  classical
  intro n R h
  let F (x : R × Equiv.Perm (Fin n)) := x.1.val.map (MulAut.conj x.2).toMonoidHom
  have hs : Function.Surjective F := by
    intro H
    obtain ⟨K,hK,g,hg⟩ := h H
    exact ⟨(⟨K,hK⟩,g),hg⟩
  simpa [Erdos1162.f, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_perm] using
    Nat.card_le_card_of_surjective F hs
