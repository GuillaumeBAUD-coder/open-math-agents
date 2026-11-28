import OMAReductions.R_Erdos423_erdos_423_R1

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: H2 is the upstream solved variant erdos_423.variants.nondecreasing (Bolan-Tang), proved in formal-conjectures.

open Erdos423 in
theorem OMA.solution : OMA.R_Erdos423_erdos_423_R1.H2 := by
  unfold OMA.R_Erdos423_erdos_423_R1.H2
  exact Erdos423.erdos_423.variants.nondecreasing
