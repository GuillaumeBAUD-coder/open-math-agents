import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R3
import Mathlib

-- Step Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R3.H2 (condensation: an inverse-square
-- majorant on the condensed sequence gives summability of a nonnegative decreasing sequence).
-- Stated plainly: the reduction file itself already proves this hypothesis, as the lemma
-- condensation_bridge in its own namespace. This file adds no mathematics; it only points at
-- that lemma. All credit for the proof goes to the author of the reduction.

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R3.H2 :=
  OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R3.condensation_bridge
