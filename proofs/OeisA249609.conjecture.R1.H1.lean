import OMAReductions.R_OeisA249609_conjecture_R1

/-!
Credit: Hanan Beer (@hananzlt).
Kernel-checked finite verification of the five indicated Pascal rows.
This discharges the finite direction of the reduction by @ihateSAS.
-/

theorem OMA.solution : OMA.R_OeisA249609_conjecture_R1.H1 := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide
