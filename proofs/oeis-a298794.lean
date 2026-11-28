import OMAStatements.S_oeis_a298794
import Mathlib.Tactic

/-! At index 20 the coefficient of the numerator is −1. The stated
homogeneous recurrence sets the same coefficient to zero. -/

open OMA.S_oeis_a298794

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a298794.main) := by
  rintro ⟨series, recurrence⟩
  have coefficient := series 20
  have stepAt := recurrence 20 (by decide)
  change a 20 - a 19 + a 18 - a 17 +
      2 * a 16 - 3 * a 15 + 3 * a 14 - 3 * a 13 +
      3 * a 12 - 4 * a 11 + 3 * a 10 - 3 * a 9 +
      3 * a 8 - 3 * a 7 + 2 * a 6 - a 5 +
      a 4 - a 3 + a 2 = -1 at coefficient
  change a 20 = a 19 - a 18 + a 17 - 2 * a 16 +
      3 * a 15 - 3 * a 14 + 3 * a 13 - 3 * a 12 +
      4 * a 11 - 3 * a 10 + 3 * a 9 - 3 * a 8 +
      3 * a 7 - 2 * a 6 + a 5 - a 4 +
      a 3 - a 2 at stepAt
  omega
