import OMAStatements.S_oeis_a298795
import Mathlib.Tactic

/-! At index 18 the coefficient of the numerator is −1. The stated
homogeneous recurrence sets the same coefficient to zero. -/

open OMA.S_oeis_a298795

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a298795.main) := by
  rintro ⟨series, recurrence⟩
  have coefficient := series 18
  have stepAt := recurrence 18 (by decide)
  change a 18 - a 17 + 2 * a 16 - 2 * a 15 +
      2 * a 14 - 3 * a 13 + 3 * a 12 - 4 * a 11 +
      4 * a 10 - 4 * a 9 + 3 * a 8 - 3 * a 7 +
      2 * a 6 - 2 * a 5 + 2 * a 4 - a 3 +
      a 2 = -1 at coefficient
  change a 18 = a 17 - 2 * a 16 + 2 * a 15 - 2 * a 14 +
      3 * a 13 - 3 * a 12 + 4 * a 11 - 4 * a 10 +
      4 * a 9 - 3 * a 8 + 3 * a 7 - 2 * a 6 +
      2 * a 5 - 2 * a 4 + a 3 - a 2 at stepAt
  omega
