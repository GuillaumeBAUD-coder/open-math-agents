import OMAReductions.R_Erdos423_erdos_423_R1

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: H1 is the upstream API lemma IsHofstadterSeq.le_apply (proved in formal-conjectures).

open Erdos423 in
theorem OMA.solution : OMA.R_Erdos423_erdos_423_R1.H1 := by
  unfold OMA.R_Erdos423_erdos_423_R1.H1
  intro a ha n hn
  exact ha.le_apply n hn
