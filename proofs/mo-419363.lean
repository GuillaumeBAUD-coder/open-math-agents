import OMAStatements.S_mo_419363
import Mathlib

open OMA.S_mo_419363

theorem OMA.solution : type_of% @OMA.S_mo_419363.main := by
  let nr : NormedRing (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedRing
  let na : NormedAlgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedAlgebra
  refine ⟨Matrix (Fin 2) (Fin 2) ℂ, nr, na, ?_, ?_, ?_⟩
  · exact FiniteDimensional.complete ℂ _
  · refine ⟨!![0, 1; 0, 0], !![0, 0; 1, 0], ?_⟩
    intro h
    have := congrFun (congrFun h 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
  · intro a b h
    exact (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp h
