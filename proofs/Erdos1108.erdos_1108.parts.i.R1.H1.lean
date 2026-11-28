import OMAReductions.R_Erdos1108_erdos_1108_parts_i_R1

-- Step Erdos1108.erdos_1108.parts.i.R1.H1: hypothesis H1 of reduction Erdos1108.erdos_1108.parts.i.R1
-- Credit: @Raimo33

theorem OMA.solution : OMA.R_Erdos1108_erdos_1108_parts_i_R1.H1 := by
  intro k _
  exact (Set.finite_Iic 1).subset (fun a h => h.2.2)
