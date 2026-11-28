import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R1
import Mathlib

open Finset in
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R1.H2 := by
  classical
  intro N q S B hS hB
  have hle : ∀ i, (B i).card ≤ Erdos142.r 3 N := by
    intro i
    apply le_csSup
    · refine ⟨N, ?_⟩
      rintro _ ⟨T, hT, -, rfl⟩
      simpa using card_le_card hT
    · exact ⟨B i, (hB i).1, by simpa using (hB i).2, rfl⟩
  calc S.card ≤ (Finset.univ.biUnion B).card := card_le_card hS
    _ ≤ ∑ i, (B i).card := card_biUnion_le
    _ ≤ ∑ _i : Fin q, Erdos142.r 3 N := sum_le_sum (fun i _ => hle i)
    _ = q * Erdos142.r 3 N := by simp
