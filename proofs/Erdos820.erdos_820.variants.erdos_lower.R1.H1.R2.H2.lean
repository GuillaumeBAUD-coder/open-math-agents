import OMAReductions.R_Erdos820_erdos_820_variants_erdos_lower_R1_H1_R2
import Mathlib

-- Step Erdos820.erdos_820.variants.erdos_lower.R1.H1.R2.H2: hypothesis H2 of reduction Erdos820.erdos_820.variants.erdos_lower.R1.H1.R2
-- Credit: the reduction itself (PR #9189 by @steveDOTdigital) proves H2 as `finiteAverage`;
-- this step only applies it. Filed by @ivillar.

/-! Step Erdos820.erdos_820.variants.erdos_lower.R1.H1.R2.H2: apply the reduction's own `finiteAverage`. -/

theorem OMA.solution : OMA.R_Erdos820_erdos_820_variants_erdos_lower_R1_H1_R2.H2 :=
  OMA.R_Erdos820_erdos_820_variants_erdos_lower_R1_H1_R2.finiteAverage
