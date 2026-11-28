import OMAStatements.S_mo_220167
import Mathlib

open OMA.S_mo_220167
open MeasureTheory

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_220167.main) := by
  intro H
  have h := H (Fin 2) Measure.count ℝ ℝ Real.sinh Real.contDiff_sinh
    ⟨Real.arsinh, Real.contDiff_arsinh, Real.arsinh_sinh, Real.sinh_arsinh⟩
    ![1, 2] (Integrable.of_finite) (Integrable.of_finite)
  rw [integral_fintype, integral_fintype] at h
  rotate_left
  · exact Integrable.of_finite
  · exact Integrable.of_finite
  simp [Fin.sum_univ_two, Measure.real] at h
  norm_num at h
  have h3 : Real.sinh 3 = Real.sinh 1 * Real.cosh 2 + Real.cosh 1 * Real.sinh 2 := by
    rw [show (3 : ℝ) = 1 + 2 by norm_num, Real.sinh_add]
  have hc1 : 1 < Real.cosh 1 := Real.one_lt_cosh.2 one_ne_zero
  have hc2 : 1 < Real.cosh 2 := Real.one_lt_cosh.2 two_ne_zero
  have hs1 : 0 < Real.sinh 1 := Real.sinh_pos_iff.2 one_pos
  have hs2 : 0 < Real.sinh 2 := Real.sinh_pos_iff.2 two_pos
  rw [h3] at h
  nlinarith
