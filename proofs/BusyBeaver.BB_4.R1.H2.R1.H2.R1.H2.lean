import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1

/-! A machine that has halted after at most 107 steps is still halted after 107 steps.
The argument is the one in the merged proof of the sibling step
BusyBeaver.BB_4.R1.H2.R1.H1.R1.H2 by @pageman, for the other first transition. -/

open Turing Turing.BusyBeaver

theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1.H2 := by
  intro M _hFirst
  rintro ⟨k, hk, hhalt⟩
  exact Machine.multiStep_eq_none_mono hhalt (Nat.succ_le_succ hk)
