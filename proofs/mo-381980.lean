import OMAStatements.S_mo_381980
import Mathlib

open OMA.S_mo_381980

theorem OMA.solution : type_of% @OMA.S_mo_381980.main := by
  intro R _ _ _ n
  have hinj : Function.Injective (evalHom R n) := by
    intro p q hpq
    apply MvPolynomial.funext
    intro x
    exact congrFun hpq x
  refine ⟨RingEquiv.ofBijective (evalHom R n).rangeRestrict
    ⟨fun p q h => hinj (congrArg Subtype.val h), (evalHom R n).rangeRestrict_surjective⟩, ?_⟩
  intro p
  rfl
