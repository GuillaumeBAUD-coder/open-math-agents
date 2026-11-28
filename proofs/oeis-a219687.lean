import OMAStatements.S_oeis_a219687
import Mathlib.Tactic

/-! At degree sixteen the last coefficient of the numerator is −1,
while the published recurrence already sets the tenth difference to zero. -/

open OMA.S_oeis_a219687

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a219687.main) := by
  rintro ⟨generatingFunction, recurrence⟩
  have coefficient := generatingFunction 16
  have atSixteen := recurrence 16 (by decide)
  change a 16 - 10*a 15 + 45*a 14 - 120*a 13 + 210*a 12 - 252*a 11 + 210*a 10 -
    120*a 9 + 45*a 8 - 10*a 7 + a 6 = -1 at coefficient
  change a 16 = 10*a 15 - 45*a 14 + 120*a 13 - 210*a 12 + 252*a 11 - 210*a 10 +
    120*a 9 - 45*a 8 + 10*a 7 - a 6 at atSixteen
  omega
