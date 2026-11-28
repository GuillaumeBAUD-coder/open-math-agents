import OMAStatements.S_mo_381980
import Mathlib

-- Problem mo-381980: for an infinite integral domain R, the polynomial ring in n variables over R is isomorphic
-- to its ring of polynomial functions, by the map sending a polynomial to its function.
-- Upstream: statements/mo-381980.lean (declaration OMA.S_mo_381980.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: over an infinite integral domain two polynomials with the same values everywhere are equal, so the
-- evaluation homomorphism is injective. Restricting its codomain to its range gives a bijective ring
-- homomorphism, hence a ring isomorphism, and by construction it sends p to its function.

open OMA.S_mo_381980

theorem OMA.solution : type_of% @OMA.S_mo_381980.main := by
  intro R _ _ _ n
  have hinj : Function.Injective (evalHom R n) := by
    intro p q h
    apply MvPolynomial.funext
    intro x
    exact congrFun h x
  refine ⟨RingEquiv.ofBijective (evalHom R n).rangeRestrict
    ⟨?_, (evalHom R n).rangeRestrict_surjective⟩, ?_⟩
  · intro p q h
    apply hinj
    exact congrArg Subtype.val h
  · intro p
    rfl
