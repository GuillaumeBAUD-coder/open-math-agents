import OMAReductions.R_SnakeInBox_coil_small_dimensions_R1_H3_R1

/-!
# Proof of `SnakeInBox.coil_small_dimensions.R1.H3.R1.H2`

Directly applies `OMA.R_SnakeInBox_coil_small_dimensions_R1_H3_R1.evenCuts`.
-/

theorem OMA.solution : OMA.R_SnakeInBox_coil_small_dimensions_R1_H3_R1.H2 :=
  OMA.R_SnakeInBox_coil_small_dimensions_R1_H3_R1.evenCuts
