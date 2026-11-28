import OMAStatements.S_mo_419363
import Mathlib

-- Problem mo-419363: there is a noncommutative complex Banach algebra in which every left-invertible element
-- is invertible (b a = 1 implies a b = 1).
-- Upstream: statements/mo-419363.lean (declaration OMA.S_mo_419363.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: take the algebra of linear maps of C^2 to itself with the operator norm. It is a complete normed
-- algebra. It is not commutative: the maps given by the matrices (0 1; 0 0) and (0 0; 1 0) do not commute, as
-- applying both products to the vector (1, 0) shows. And if b a = 1 then a b = 1, because the same holds for
-- 2 x 2 matrices over a field.

theorem OMA.solution : type_of% @OMA.S_mo_419363.main := by
  refine ⟨(Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ), inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · refine ⟨LinearMap.toContinuousLinearMap (Matrix.toLin' !![0, 1; 0, 0]),
      LinearMap.toContinuousLinearMap (Matrix.toLin' !![0, 0; 1, 0]), fun h => ?_⟩
    have h1 := congrArg (fun T : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) => T ![1, 0] 0) h
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h1
  · intro a b h
    have h1 : (b : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) * (a : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) = 1 := by
      apply LinearMap.ext
      intro v
      have h2 := congrArg (fun T : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) => T v) h
      simpa using h2
    have h3 : LinearMap.toMatrixAlgEquiv' (b : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) *
        LinearMap.toMatrixAlgEquiv' (a : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) = 1 := by
      rw [← map_mul, h1, map_one]
    have h4 := mul_eq_one_comm.mp h3
    have h5 : (a : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) * (b : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) = 1 := by
      apply LinearMap.toMatrixAlgEquiv'.injective
      rw [map_mul, h4, map_one]
    apply ContinuousLinearMap.ext
    intro v
    have h6 := congrArg (fun T : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) => T v) h5
    simpa using h6
