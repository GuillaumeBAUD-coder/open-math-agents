import OMAStatements.S_mo_429559
import Mathlib

-- Problem: mo-429559, if the subalgebra F[a, b] of a field extension E / F is already the
-- field F(a, b), then a and b are algebraic over F.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- This is Zariski's lemma: F(a, b) = F[a, b] is a field that is finitely generated as an
-- F-algebra, hence a finite extension of F, so all of its elements are algebraic over F.

theorem OMA.solution : type_of% @OMA.S_mo_429559.main := by
  intro F E _ _ _ a b h
  classical
  have hfg : (Algebra.adjoin F ({a, b} : Set E)).FG := by
    have h1 := Subalgebra.fg_adjoin_finset (R := F) ({a, b} : Finset E)
    simpa using h1
  rw [h] at hfg
  haveI hft : Algebra.FiniteType F (IntermediateField.adjoin F ({a, b} : Set E)) :=
    (Subalgebra.fg_iff_finiteType _).mp hfg
  haveI hfin : Module.Finite F (IntermediateField.adjoin F ({a, b} : Set E)) :=
    finite_of_finite_type_of_isJacobsonRing F (IntermediateField.adjoin F ({a, b} : Set E))
  have hmem : ∀ x ∈ ({a, b} : Set E), IsAlgebraic F x := by
    intro x hx
    have hxL : x ∈ IntermediateField.adjoin F ({a, b} : Set E) :=
      IntermediateField.subset_adjoin F _ hx
    have h2 : IsAlgebraic F (⟨x, hxL⟩ : IntermediateField.adjoin F ({a, b} : Set E)) :=
      Algebra.IsAlgebraic.isAlgebraic _
    exact IntermediateField.isAlgebraic_iff.mp h2
  exact ⟨hmem a (by simp), hmem b (by simp)⟩
