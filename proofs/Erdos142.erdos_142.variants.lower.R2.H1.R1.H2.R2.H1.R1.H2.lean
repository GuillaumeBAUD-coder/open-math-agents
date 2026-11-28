import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R1

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R1.H2 := by
  intro N q S B hcover hB
  apply (Finset.card_le_card hcover).trans
  simpa using Finset.card_biUnion_le_card_mul Finset.univ B (Erdos142.r 3 N)
    (fun i _ => OMA.R_Erdos142_erdos_142_variants_lower_R2.card_le_maxCard (hB i).1 (hB i).2)
