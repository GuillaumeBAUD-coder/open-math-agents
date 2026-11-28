import OMAReductions.R_Erdos711_erdos_711_parts_i_R2_H2_R1_H2_R1_H2_R1
import Mathlib

theorem OMA.aux711 (T : ℕ → Finset ℕ) : ∀ n : ℕ, ∀ U : Finset ℕ, U.card = n →
    (U.biUnion T).card < U.card →
    ∃ V ⊆ U, V.Nonempty ∧ (V.biUnion T).card + 1 = V.card ∧
      (∀ W ⊂ V, W.card ≤ (W.biUnion T).card) ∧
      (∀ d ∈ V, (V.erase d).biUnion T = V.biUnion T) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro U hn hU
    by_cases h : ∀ W ⊂ U, W.card ≤ (W.biUnion T).card
    · have hne : U.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        rintro rfl
        simp at hU
      have key : ∀ d ∈ U, (U.erase d).biUnion T ⊆ U.biUnion T ∧
          U.card - 1 ≤ ((U.erase d).biUnion T).card := by
        intro d hd
        refine ⟨Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.erase_subset d U), ?_⟩
        have h3 := h _ (Finset.erase_ssubset hd)
        rwa [Finset.card_erase_of_mem hd] at h3
      refine ⟨U, subset_rfl, hne, ?_, h, ?_⟩
      · obtain ⟨d, hd⟩ := hne
        have h1 := Finset.card_le_card (key d hd).1
        have h2 := (key d hd).2
        omega
      · intro d hd
        have h2 := (key d hd).2
        exact Finset.eq_of_subset_of_card_le (key d hd).1 (by omega)
    · push_neg at h
      obtain ⟨W, hW, hlt⟩ := h
      obtain ⟨V, hV, rest⟩ := ih W.card (hn ▸ Finset.card_lt_card hW) W rfl hlt
      exact ⟨V, hV.trans hW.subset, rest⟩

theorem OMA.solution : OMA.R_Erdos711_erdos_711_parts_i_R2_H2_R1_H2_R1_H2_R1.H1 := by
  intro U T hU
  exact OMA.aux711 T _ U rfl hU
