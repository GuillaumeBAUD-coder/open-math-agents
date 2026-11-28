import OMAStatements.S_mo_49546
import Mathlib

open CategoryTheory Opposite

namespace OMA.S_mo_49546

theorem aux : ∀ (C D : Type) [SmallCategory C] [SmallCategory D] (f : C ⥤ D),
    Nonempty (extendPresheaf f ⊣ restrictPresheaf f) ∧
      Nonempty (yoneda ⋙ extendPresheaf f ≅ f ⋙ yoneda) := by
  intro C D _ _ f
  refine ⟨⟨f.op.lanAdjunction (Type)⟩, ⟨?_⟩⟩
  exact (Functor.isoWhiskerRight uliftYonedaIsoYoneda.symm (extendPresheaf f)).trans
    ((Presheaf.compULiftYonedaIsoULiftYonedaCompLan.{0} f).symm.trans
      (Functor.isoWhiskerLeft f uliftYonedaIsoYoneda))

end OMA.S_mo_49546

theorem OMA.solution : type_of% @OMA.S_mo_49546.main := OMA.S_mo_49546.aux
