import OMAStatements.S_mo_85023
import Mathlib

/-!
# Failure of the bound at zero

Set the degree to one and evaluate at zero, where only the constant term survives.
With parameter three halves the proposed upper bound is the square root of pi divided by two.
Since pi is less than four, this bound lies strictly below the constant term one.
-/

namespace OMA.S_mo_85023
end OMA.S_mo_85023

open OMA.S_mo_85023 in
theorem OMA.solution : type_of% @OMA.S_mo_85023.main := by
  intro h
  have bad := h 1 (1/2+1) 0 (by decide) (by norm_num)
  rw [Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq] at bad
  norm_num [kummerNeg, Finset.sum_range_succ] at bad
  nlinarith [Real.sq_sqrt Real.pi_pos.le, Real.pi_lt_four]
