import OMAReductions.R_Erdos5_erdos_5_R1
import Mathlib

theorem OMA.solution : OMA.R_Erdos5_erdos_5_R1.H2 := by
  intro x hx
  exact (Erdos5.mem_limitPointSet_iff x).1 hx
