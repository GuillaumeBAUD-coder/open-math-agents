import OMAReductions.R_Erdos711_erdos_711_parts_i_R2_H2_R1_H2_R1

/-!
The reduction file already proves this hypothesis as `small_centres_separate`; this file applies it.
-/

theorem OMA.solution : OMA.R_Erdos711_erdos_711_parts_i_R2_H2_R1_H2_R1.H1 :=
  OMA.R_Erdos711_erdos_711_parts_i_R2_H2_R1_H2_R1.small_centres_separate
