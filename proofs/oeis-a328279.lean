import OMAStatements.S_oeis_a328279
import Mathlib.Tactic

/-! The homogeneous recurrence starts at index 18, where the displayed
numerator still has coefficient −460. The two assertions therefore give
incompatible values for the same linear combination of terms. -/

open OMA.S_oeis_a328279

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a328279.main) := by
  rintro ⟨series, recurrence⟩
  have coefficient := series 18
  have stepAt := recurrence 18 (by decide)
  change a 18 - a 17 - 9*a 14 + 9*a 13 - 10*a 10 + 10*a 9 = -460 at coefficient
  change a 18 = a 17 + 9*a 14 - 9*a 13 + 10*a 10 - 10*a 9 at stepAt
  omega
