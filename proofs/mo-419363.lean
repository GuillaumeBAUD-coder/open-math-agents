import OMAStatements.S_mo_419363
import Mathlib

-- Problem: mo-419363, is there a noncommutative complex Banach algebra in which every left
-- inverse is also a right inverse?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Yes: the algebra of 2 x 2 complex matrices (with the operator norm for the sup norm). It is
-- finite dimensional, hence complete; it is not commutative; and for square matrices
-- b a = 1 implies a b = 1.

theorem OMA.solution : type_of% @OMA.S_mo_419363.main := by
  refine ⟨Matrix (Fin 2) (Fin 2) ℂ, Matrix.linftyOpNormedRing, Matrix.linftyOpNormedAlgebra,
    ?_, ?_, ?_⟩
  · let _nr : NormedRing (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedRing
    let _na : NormedAlgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedAlgebra
    exact FiniteDimensional.complete ℂ _
  · refine ⟨!![0, 1; 0, 0], !![0, 0; 1, 0], ?_⟩
    intro h
    have h' : (!![0, 1; 0, 0] * !![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) =
        !![0, 0; 1, 0] * !![0, 1; 0, 0] := h
    have h0 := congrFun (congrFun h' 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h0
  · intro a b h
    have h' : (b * a : Matrix (Fin 2) (Fin 2) ℂ) = 1 := h
    have h2 : (a * b : Matrix (Fin 2) (Fin 2) ℂ) = 1 := mul_eq_one_comm.mp h'
    exact h2
