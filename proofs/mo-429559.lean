import OMAStatements.S_mo_429559
import Mathlib



open OMA.S_mo_429559



theorem OMA.solution : type_of% @OMA.S_mo_429559.main := by
  classical
  intro F E _ _ _ a b h
  let K := IntermediateField.adjoin F ({a, b} : Set E)
  have ha : a ∈ K := IntermediateField.subset_adjoin F _ (by simp)
  have hb : b ∈ K := IntermediateField.subset_adjoin F _ (by simp)
  let a' : K := ⟨a, ha⟩
  let b' : K := ⟨b, hb⟩
  have he : Algebra.adjoin F ({a', b'} : Set K) = ⊤ := by
    apply Subalgebra.map_injective (f := K.val) Subtype.val_injective
    have htop : (⊤ : Subalgebra F K).map K.val = K.toSubalgebra := by
      ext y
      rw [Subalgebra.mem_map]
      constructor
      · rintro ⟨x, _, rfl⟩
        exact x.property
      · intro hy
        exact ⟨⟨y, hy⟩, by simp, rfl⟩
    have himage : K.val '' ({a', b'} : Set K) = ({a, b} : Set E) := by
      rw [Set.image_insert_eq, Set.image_singleton]
      rfl
    rw [← Algebra.adjoin_image, htop, himage]
    exact h
  have : Algebra.FiniteType F K := by
    refine ⟨⟨{a', b'}, ?_⟩⟩
    simpa only [Finset.coe_insert, Finset.coe_singleton] using he
  have : Module.Finite F K := finite_of_finite_type_of_isJacobsonRing F K
  exact ⟨(Algebra.IsIntegral.isIntegral a').isAlgebraic.algHom K.val,
    (Algebra.IsIntegral.isIntegral b').isAlgebraic.algHom K.val⟩
