import OMAStatements.S_mo_202224
import Mathlib

-- Problem: mo-202224, an algebraic integer all of whose conjugates lie on the unit circle is a
-- root of unity (Kronecker's theorem).
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Apply Mathlib's version of Kronecker's theorem to the generator x of the number field
-- K = Q(alpha): every embedding of K into the complex numbers sends x to a root of the minimal
-- polynomial of alpha, hence to a number of absolute value 1.

theorem OMA.solution : type_of% @OMA.S_mo_202224.main := by
  intro α hα hconj
  have hαQ : IsIntegral ℚ α := hα.tower_top
  have hfin : FiniteDimensional ℚ (IntermediateField.adjoin ℚ ({α} : Set ℂ)) :=
    IntermediateField.adjoin.finiteDimensional hαQ
  have hnf : NumberField (IntermediateField.adjoin ℚ ({α} : Set ℂ)) :=
    { to_charZero := inferInstance, to_finiteDimensional := hfin }
  have hgen : algebraMap (IntermediateField.adjoin ℚ ({α} : Set ℂ)) ℂ
      (IntermediateField.AdjoinSimple.gen ℚ α) = α :=
    IntermediateField.AdjoinSimple.algebraMap_gen ℚ α
  have hx : IsIntegral ℤ (IntermediateField.AdjoinSimple.gen ℚ α) := by
    apply (isIntegral_algebraMap_iff
      (algebraMap (IntermediateField.adjoin ℚ ({α} : Set ℂ)) ℂ).injective).mp
    rw [hgen]
    exact hα
  have hnorm : ∀ φ : (IntermediateField.adjoin ℚ ({α} : Set ℂ)) →+* ℂ,
      ‖φ (IntermediateField.AdjoinSimple.gen ℚ α)‖ = 1 := by
    intro φ
    apply hconj
    have h1 : minpoly ℚ (IntermediateField.AdjoinSimple.gen ℚ α) = minpoly ℚ α :=
      IntermediateField.minpoly_gen ℚ α
    have h2 : Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ α) (minpoly ℚ α) = 0 := by
      rw [← h1]
      exact minpoly.aeval ℚ _
    have h3 := Polynomial.aeval_algHom_apply φ.toRatAlgHom
      (IntermediateField.AdjoinSimple.gen ℚ α) (minpoly ℚ α)
    rw [h2, map_zero] at h3
    exact h3
  obtain ⟨n, hn, hxn⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one
    (IntermediateField.adjoin ℚ ({α} : Set ℂ)) ℂ hx hnorm
  refine ⟨n, hn, ?_⟩
  have h4 := congrArg (algebraMap (IntermediateField.adjoin ℚ ({α} : Set ℂ)) ℂ) hxn
  rw [map_pow, hgen, map_one] at h4
  exact h4
