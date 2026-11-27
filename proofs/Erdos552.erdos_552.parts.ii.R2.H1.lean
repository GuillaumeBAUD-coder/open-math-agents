import OMAReductions.R_Erdos552_erdos_552_parts_ii_R2
import Mathlib

-- Step Erdos552.erdos_552.parts.ii.R2.H1: hypothesis H1 of reduction Erdos552.erdos_552.parts.ii.R2
-- Credit: the reduction itself (PR #9073 by @Deldor14, credited there to @TheWaler) proves H1 as
-- `finite_obstruction`; this step only applies it. Filed by @ivillar.

/-! Step Erdos552.erdos_552.parts.ii.R2.H1: apply the reduction's own `finite_obstruction`. -/

theorem OMA.solution : OMA.R_Erdos552_erdos_552_parts_ii_R2.H1 :=
  OMA.R_Erdos552_erdos_552_parts_ii_R2.finite_obstruction
