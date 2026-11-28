import OMAStatements.S_mo_342399
import Mathlib

theorem OMA.solution : type_of% @OMA.S_mo_342399.main := by
  intro R _ C D _ _ _ _ _ _ F G _ adj
  constructor
  intro X Y f r
  apply (adj.homEquiv _ _).symm.injective
  simp [CategoryTheory.Adjunction.homEquiv_counit]
