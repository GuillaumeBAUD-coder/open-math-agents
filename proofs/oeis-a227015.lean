import OMAStatements.S_oeis_a227015
import Mathlib.Tactic

/-! The eight integer floors, obtained from the defining rational sums,
are 2, 8, 26, 60, 117, 203, 324 and 487. Substitution of the first seven
into the proposed recurrence would give 484 for the eighth term. -/

open OMA.S_oeis_a227015

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a227015.main) := by
  rintro ⟨recurrence, _⟩
  have actual : a 8 = 487 := by decide +kernel
  have predicted : 3*a 7 - 3*a 6 + a 5 + a 4 - 3*a 3 + 3*a 2 - a 1 = 484 := by
    decide +kernel
  have step := recurrence 8 (by decide) (by decide)
  change a 8 = 3*a 7 - 3*a 6 + a 5 + a 4 - 3*a 3 + 3*a 2 - a 1 at step
  omega
