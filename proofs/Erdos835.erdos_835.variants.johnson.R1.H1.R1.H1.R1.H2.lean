import OMAReductions.R_Erdos835_erdos_835_variants_johnson_R1_H1_R1_H1_R1

-- Step Erdos835.erdos_835.variants.johnson.R1.H1.R1.H1.R1.H2: hypothesis H2 of reduction
-- Erdos835.erdos_835.variants.johnson.R1.H1.R1.H1.R1
-- Credit: @ivillar. The reduction file itself proves H2 as `binary_implications`; this step applies it.

/-! Satisfiability of consistent binary implication systems. -/

open OMA.R_Erdos835_erdos_835_variants_johnson_R1_H1_R1_H1_R1 in
theorem OMA.solution : H2 :=
  binary_implications
