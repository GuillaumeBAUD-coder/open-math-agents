import OMAStatements.S_oeis_a219520
import Mathlib.Tactic

/-! The coefficient of degree 8 in the numerator is -4. The homogeneous
recurrence would make it zero. Equivalently, the OEIS table gives 172
at this index, while its previous five entries predict 176. -/

open OMA.S_oeis_a219520

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a219520.main) := by
  rintro ⟨series, recurrence⟩
  have coefficient := series 8
  have step := recurrence 8 (by decide)
  change a 8 - 5*a 7 + 10*a 6 - 10*a 5 + 5*a 4 - a 3 = -4 at coefficient
  change a 8 = 5*a 7 - 10*a 6 + 10*a 5 - 5*a 4 + a 3 at step
  omega
