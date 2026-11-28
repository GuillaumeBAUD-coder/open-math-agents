import OMAStatements.S_mo_490476
import Mathlib

-- Problem: mo-490476, precomposition with f is injective iff f is surjective, and surjective
-- iff f is injective: false for a one-point codomain, true for a codomain with two elements.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- For Z a one-point type and f the empty map into a one-point type, precomposition is
-- injective but f is not surjective. For nontrivial Z both equivalences are standard.

theorem OMA.solution : type_of% @OMA.S_mo_490476.main := by
  unfold OMA.S_mo_490476.precomp
  constructor
  · intro h
    have h1 := (h Empty Unit Unit (fun e => e.elim)).1
    have hsurj := h1.mp (fun g₁ g₂ _ => funext fun u => Subsingleton.elim _ _)
    obtain ⟨e, _⟩ := hsurj ()
    exact e.elim
  · intro X Y Z _ f
    exact ⟨Function.injective_comp_right_iff_surjective,
      Function.surjective_comp_right_iff_injective⟩
