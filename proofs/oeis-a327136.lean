import OMAStatements.S_oeis_a327136
import Mathlib

/-!
# The first bounds exclude every natural number

At index zero the proposed upper bound and π > 3 force the term
to exceed 1. The lower bound and π < 3.1416 force it to be below 2.
This interval contains no natural number.
-/

open OMA.S_oeis_a327136 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a327136.main) := by
  intro h
  obtain ⟨hl, hu⟩ := h 0
  simp only [Nat.cast_zero, zero_add, one_mul] at hl hu
  have hlo : (1 : ℝ) < (term 0 : ℝ) := by linarith [Real.pi_gt_three]
  have hhi : (term 0 : ℝ) < (2 : ℝ) := by linarith [Real.pi_lt_d4]
  have hlo' : 1 < term 0 := by exact_mod_cast hlo
  have hhi' : term 0 < 2 := by exact_mod_cast hhi
  omega
