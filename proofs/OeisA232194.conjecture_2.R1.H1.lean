import OMAReductions.R_OeisA232194_conjecture_2_R1

/-!
Credit: Hanan Beer (@hananzlt).
Kernel-checked finite prime-decomposition counts at the five listed indices.
This discharges the finite direction of the reduction by @ihateSAS;
the assertion that no other index has count one remains open.
-/

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem OMA.solution : OMA.R_OeisA232194_conjecture_2_R1.H1 := by
  intro n hn
  fin_cases hn <;> decide
