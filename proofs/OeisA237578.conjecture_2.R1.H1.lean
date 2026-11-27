import OMAReductions.R_OeisA237578_conjecture_2_R1

/-!
Credit: Hanan Beer (@hananzlt).
Verifies the three finite values in the reduction by @ihateSAS.
All arithmetic is checked by the Lean kernel.
The uniqueness direction remains open.
-/

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem OMA.solution : OMA.R_OeisA237578_conjecture_2_R1.H1 := by
  intro n hn
  rcases hn with rfl | rfl | rfl <;> decide +kernel
