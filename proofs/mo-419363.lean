import OMAStatements.S_mo_419363

-- Problem mo-419363: there is a noncommutative complex Banach algebra in which every left-invertible element
-- is invertible (b a = 1 implies a b = 1).
-- Upstream: statements/mo-419363.lean (declaration OMA.S_mo_419363.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: take the algebra of linear maps of C^2 to itself with the operator norm. It is a complete normed
-- algebra. It is not commutative: the maps given by the matrices (0 1; 0 0) and (0 0; 1 0) do not commute, as
-- applying both products to the vector (1, 0) shows. And if b a = 1 then a b = 1, because the same holds for
-- 2 x 2 matrices over a field.

-- Use injectivity of the coercion to finite-dimensional linear maps for the inverse identity.
theorem OMA.solution : type_of% @OMA.S_mo_419363.main := by
  refine ⟨(Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ), inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · refine ⟨LinearMap.toContinuousLinearMap (Matrix.toLin' !![0, 1; 0, 0]),
      LinearMap.toContinuousLinearMap (Matrix.toLin' !![0, 0; 1, 0]), fun h => ?_⟩
    have h1 := congrArg (fun T : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) => T ![1, 0] 0) h
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h1
  · intro a b h
    rw [← ContinuousLinearMap.coe_inj] at h ⊢
    exact mul_eq_one_comm.mp h
