import OMAReductions.R_Erdos885_erdos_885_R1
import Mathlib

theorem OMA.solution : OMA.R_Erdos885_erdos_885_R1.H2 := by
  intro k h2 h4
  interval_cases k
  · exact Erdos885.erdos_885.variants.k_eq_2
  · exact Erdos885.erdos_885.variants.k_eq_3
  · exact Erdos885.erdos_885.variants.k_eq_4
