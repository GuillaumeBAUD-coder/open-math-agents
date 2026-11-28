import OMAReductions.R_SnakeInBox_coil_small_dimensions_R1_H3_R1

-- Step SnakeInBox.coil_small_dimensions.R1.H3.R1.H2: hypothesis H2 of reduction SnakeInBox.coil_small_dimensions.R1.H3.R1
-- Credit: the reduction itself (PR #9486 by @steveDOTdigital) proves H2 as `evenCuts`;
-- this step only applies it. Filed by @ivillar.

/-! Step SnakeInBox.coil_small_dimensions.R1.H3.R1.H2: apply the reduction's own `evenCuts`. -/

open OMA.R_SnakeInBox_coil_small_dimensions_R1_H3_R1 in
theorem OMA.solution : H2 :=
  evenCuts
