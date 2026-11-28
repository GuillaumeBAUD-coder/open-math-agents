import OMAStatements.S_mo_383745
import Mathlib

open Finset

open OMA.S_mo_383745

private noncomputable def negativeHalfMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => if i = j then 1 else -1/2

private theorem negativeHalf_psd : SymmetricPSD negativeHalfMatrix := by
  constructor
  · ext i j
    by_cases h : i = j
    · subst j
      rfl
    · simp [Matrix.transpose_apply,negativeHalfMatrix,h,Ne.symm h]
  · intro v
    have he : quadratic negativeHalfMatrix v =
        ((v 0-v 1)^2 + (v 0-v 2)^2 + (v 1-v 2)^2)/2 := by
      simp only [quadratic,Fin.sum_univ_three,negativeHalfMatrix]
      norm_num [Fin.ext_iff]
      ring
    rw [he]
    positivity

private theorem half_arcsine : Real.arcsin (1/2 : ℝ) = Real.pi/6 := by
  rw [←Real.sin_pi_div_six]
  exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

private theorem negative_arc_quadratic (a : ℝ) :
    quadratic (a • negativeHalfMatrix - entryArcsine negativeHalfMatrix) (fun _ => 1) =
      -Real.pi/2 := by
  simp only [quadratic,Fin.sum_univ_three,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
    entryArcsine,negativeHalfMatrix,one_mul,mul_one]
  norm_num [Fin.ext_iff,Real.arcsin_neg,Real.arcsin_one,half_arcsine]
  ring

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_383745.main) := by
  intro h
  obtain ⟨a,_,ha⟩ := h 3 negativeHalfMatrix negativeHalf_psd (by intro i; simp [negativeHalfMatrix])
  have hz := ha.2 (fun _ => 1)
  rw [negative_arc_quadratic] at hz
  linarith [Real.pi_pos]
