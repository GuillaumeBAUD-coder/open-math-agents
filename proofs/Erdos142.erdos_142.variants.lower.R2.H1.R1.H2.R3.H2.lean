import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R3
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Summability by Cauchy condensation against the inverse-square series (the bridge lemma of the
-- parent file), or, for the p-series form of H2, Real.summable_nat_rpow with exponent -2.

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R3.H2 := by
  unfold OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R3.H2
  first
  | exact OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R3.condensation_bridge
  | exact (summable_nat_add_iff 1).mpr ((Real.summable_nat_rpow).mpr (by norm_num))
