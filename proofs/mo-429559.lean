import OMAStatements.S_mo_429559

/-! Zariski's lemma applied directly to the finitely generated adjoin algebra. -/
theorem OMA.solution : type_of% @OMA.S_mo_429559.main := by
  intro F E _ _ _ a b h
  let K := IntermediateField.adjoin F ({a, b} : Set E)
  have : Algebra.FiniteType F K := by
    change Algebra.FiniteType F K.toSubalgebra
    rw [← h]
    exact Algebra.FiniteType.adjoin_of_finite ((Set.finite_singleton b).insert a)
  have : Module.Finite F K := finite_of_finite_type_of_isJacobsonRing F K
  have ha (x : K) : IsAlgebraic F (x : E) :=
    (Algebra.IsIntegral.isIntegral x).isAlgebraic.algHom K.val
  exact ⟨ha ⟨a, IntermediateField.subset_adjoin F _ (by simp)⟩,
    ha ⟨b, IntermediateField.subset_adjoin F _ (by simp)⟩⟩
