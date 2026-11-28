import OMAStatements.S_oeis_a219211
import Mathlib.Tactic

/-! The coefficient of degree 7 in the numerator is 4. The homogeneous
recurrence would make it zero. Equivalently, the OEIS table gives 57
at this index, while its previous five entries predict 53. -/

open OMA.S_oeis_a219211

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a219211.main) := by
  rintro ⟨series, recurrence⟩
  have coefficient := series 7
  have step := recurrence 7 (by decide)
  change a 7 - 5*a 6 + 10*a 5 - 10*a 4 + 5*a 3 - a 2 = 4 at coefficient
  change a 7 = 5*a 6 - 10*a 5 + 10*a 4 - 5*a 3 + a 2 at step
  omega
