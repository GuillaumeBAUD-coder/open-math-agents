import OMAReductions.R_Mathoverflow75792_complexity_two_pow_R1
import Mathlib

theorem OMA.solution : OMA.R_Mathoverflow75792_complexity_two_pow_R1.H1 := by
  intro n hn
  exact Mathoverflow75792.Reachable.pow 2 n (by norm_num) hn
