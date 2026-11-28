import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1_H1_R2

/-!
Step H2 of the reduction Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R1.H1.R2: a modular progression inside a short
interval lifts to an integer progression of positive step. The reduction file already proves it
as the theorem lift_progression.
-/

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1_H1_R2.H2 :=
  OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1_H1_R2.lift_progression
