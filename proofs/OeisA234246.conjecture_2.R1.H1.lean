import OMAReductions.R_OeisA234246_conjecture_2_R1

/-!
Credit: Hanan Beer (@hananzlt).
Kernel-checked finite totient and square counts at the nine listed indices.
This discharges the finite direction of the reduction by @ihateSAS;
the assertion that no other index has count one remains open.
-/

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem OMA.solution : OMA.R_OeisA234246_conjecture_2_R1.H1 := by
  intro n hn
  fin_cases hn <;> decide
