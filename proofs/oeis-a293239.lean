import OMAStatements.S_oeis_a293239
import Mathlib.Tactic

/-! Collecting like terms in the eighth derivative leaves 35 distinct
monomials. The proposed homogeneous recurrence predicts 36. -/

open OMA.S_oeis_a293239

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a293239.main) := by
  intro h
  have stepAt := h.2.2.2.2 8 (by decide)
  change a 8 = 2*a 7 - a 6 + a 4 - 2*a 3 + a 2 at stepAt
  have values : a 2 = 4 ∧ a 3 = 7 ∧ a 4 = 11 ∧ a 6 = 21 ∧ a 7 = 28 ∧ a 8 = 35 := by
    decide +kernel
  omega
