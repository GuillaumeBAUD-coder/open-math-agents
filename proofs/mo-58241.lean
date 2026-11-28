import OMAStatements.S_mo_58241
import Mathlib

-- Problem: mo-58241, is the variance of an eigenfunction along an ergodic finite Markov chain
-- started at a single state nondecreasing in time?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. Take the two-state chain P = [2/5 3/5; 1/10 9/10] (all entries positive) with the
-- eigenfunction f = (6, -1), P f = (3/10) f, started at state 0. Then
--   Var_1 = (P f^2)(0) - ((P f)(0))^2 = 15 - (9/5)^2 = 11.76,
--   Var_2 = (P^2 f^2)(0) - ((P^2 f)(0))^2 = 8.7 - (27/50)^2 = 8.4084 < Var_1.
-- (The mass of state 1 increases past 1/2 towards its stationary value 6/7.)

open Matrix

namespace MO58241

noncomputable def P : Matrix (Fin 2) (Fin 2) ℝ := !![2 / 5, 3 / 5; 1 / 10, 9 / 10]

noncomputable def f : Fin 2 → ℝ := ![6, -1]

theorem hpos : ∀ i j, 0 ≤ P i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [P]

theorem hrow : ∀ i, ∑ j, P i j = 1 := by
  intro i
  fin_cases i <;> norm_num [P, Fin.sum_univ_two]

theorem hprim : ∃ m : ℕ, ∀ i j, 0 < (P ^ m) i j := by
  refine ⟨1, ?_⟩
  intro i j
  rw [pow_one]
  fin_cases i <;> fin_cases j <;> norm_num [P]

theorem hne : f ≠ 0 := by
  intro h0
  have h1 := congrFun h0 0
  norm_num [f] at h1

theorem heig : P *ᵥ f = (3 / 10 : ℝ) • f := by
  ext i
  fin_cases i <;> norm_num [P, f, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

end MO58241

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_58241.main) := by
  intro h
  have h1 := h 2 MO58241.P MO58241.hpos MO58241.hrow MO58241.hprim (3 / 10) MO58241.f
    MO58241.hne MO58241.heig 0 1
  norm_num [MO58241.P, MO58241.f, Matrix.mulVec, dotProduct, Fin.sum_univ_two, pow_two,
    Matrix.mul_apply] at h1
