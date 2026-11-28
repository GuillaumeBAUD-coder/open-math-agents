import OMAReductions.R_Erdos1002_erdos_1002_R1
import Mathlib

open MeasureTheory Set

theorem OMA.solution : OMA.R_Erdos1002_erdos_1002_R1.H4 := by
  intro c n
  beta_reduce
  rw [Measure.map_apply (by fun_prop) measurableSet_Iic, Measure.restrict_apply' measurableSet_Ioo]
  congr 2
  ext α
  simp [and_comm]
