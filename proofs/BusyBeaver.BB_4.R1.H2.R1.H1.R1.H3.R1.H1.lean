import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1_H3_R1

/-! Total write-0 machines (every transition continues) never halt. -/
-- Credit: @pageman

open Turing Turing.BusyBeaver

theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1_H3_R1.H1 := by
  intro M _hFirst hTot
  exact Machine.not_isHalting_of_forall_isSome (M := M) hTot
