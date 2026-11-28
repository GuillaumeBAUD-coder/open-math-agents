import OMAStatements.S_oeis_a073023
import Mathlib

open OMA.S_oeis_a073023

set_option maxRecDepth 35000 in
set_option maxHeartbeats 0 in
private theorem total : (∑ k ∈ Finset.Icc 1 102, a k) = 1025 := by
  unfold a
  decide +kernel

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a073023.main) := by
  intro h
  have strict := h 102 (by decide)
  rw [total] at strict
  change (102 : ℝ)^((3 : ℝ)/2) < 1025 at strict
  have root : (1025/102 : ℝ) ≤ Real.sqrt 102 :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have power : (102 : ℝ)^((3 : ℝ)/2) = 102 * Real.sqrt 102 := by
    rw [show (3 : ℝ)/2 = 1 + 1/2 by norm_num,
      Real.rpow_add (by norm_num : (0 : ℝ) < 102), Real.rpow_one, Real.sqrt_eq_rpow]
  have lower : (1025 : ℝ) ≤ (102 : ℝ)^((3 : ℝ)/2) := calc
    _ = 102 * (1025/102) := by norm_num
    _ ≤ 102 * Real.sqrt 102 := mul_le_mul_of_nonneg_left root (by norm_num)
    _ = _ := power.symm
  exact (not_lt_of_ge lower) strict