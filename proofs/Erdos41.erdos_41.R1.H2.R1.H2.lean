import OMAReductions.R_Erdos41_erdos_41_R1_H2_R1
import Mathlib

-- Step Erdos41.erdos_41.R1.H2.R1.H2: hypothesis H2 of reduction Erdos41.erdos_41.R1.H2.R1
-- Credit: the reduction itself (PR #9972 by @Iraeeee) proves H2 as `finite_packing`;
-- this step only applies it. Filed by @ivillar.

/-! Step Erdos41.erdos_41.R1.H2.R1.H2: apply the reduction's own `finite_packing`. -/

theorem OMA.solution : OMA.R_Erdos41_erdos_41_R1_H2_R1.H2 :=
  OMA.R_Erdos41_erdos_41_R1_H2_R1.finite_packing
