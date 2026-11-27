import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1

/-! A halt by step k, with k at most 107, is a halt by step 107. -/

open Turing Turing.BusyBeaver

theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1.H2 := by
  intro M _first ⟨k, hk, hhalt⟩
  exact Machine.multiStep_eq_none_mono hhalt (by omega)
