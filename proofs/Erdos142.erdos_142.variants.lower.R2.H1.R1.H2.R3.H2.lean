import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R3

/-!
Step H2 of the reduction Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R3: Cauchy condensation with an inverse-square majorant.
The reduction file already proves it as the lemma condensation_bridge.
-/

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R3.H2 :=
  OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R3.condensation_bridge
