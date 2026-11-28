import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R2

/-!
Step H2 of the reduction Erdos142.erdos_142.variants.lower.R1.H2.R3.H1.R2: the popular-shift averaging step.
The reduction file already proves it as the lemma popularShift (grouping U x A by the difference).
-/

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R2.H2 :=
  OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R2.popularShift
