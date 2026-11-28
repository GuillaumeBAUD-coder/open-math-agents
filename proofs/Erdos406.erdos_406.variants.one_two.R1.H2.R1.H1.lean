import OMAReductions.R_Erdos406_erdos_406_variants_one_two_R1_H2_R1

-- Step Erdos406.erdos_406.variants.one_two.R1.H2.R1.H1: hypothesis H1 of reduction
-- Erdos406.erdos_406.variants.one_two.R1.H2.R1
-- Credit: @ivillar. The reduction file itself proves H1 as `finiteSeed` (a kernel-checked finite table);
-- this step applies it.

/-! The finite seed table of base-3 digit zeros. -/

open OMA.R_Erdos406_erdos_406_variants_one_two_R1_H2_R1 in
theorem OMA.solution : H1 :=
  finiteSeed
