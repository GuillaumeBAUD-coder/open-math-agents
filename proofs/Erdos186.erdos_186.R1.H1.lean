import OMAReductions.R_Erdos186_erdos_186_R1
import Mathlib

-- Step Erdos186.erdos_186.R1.H1: hypothesis H1 of reduction Erdos186.erdos_186.R1
-- Credit: the reduction itself (PR #9824 by @steveDOTdigital) proves H1 as `centered_lower`;
-- this step only applies it. Filed by @ivillar.

/-! Step Erdos186.erdos_186.R1.H1: apply the reduction's own `centered_lower`. -/

theorem OMA.solution : OMA.R_Erdos186_erdos_186_R1.H1 :=
  OMA.R_Erdos186_erdos_186_R1.centered_lower
