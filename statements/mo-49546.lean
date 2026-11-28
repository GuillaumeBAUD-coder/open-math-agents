import Mathlib

/-!
# MathOverflow 49546

Source: https://mathoverflow.net/questions/49546
-/

namespace OMA.S_mo_49546

open CategoryTheory Opposite

/-- Restriction of a presheaf by precomposition with the opposite functor. -/
abbrev restrictPresheaf {C D : Type} [SmallCategory C] [SmallCategory D] (f : C ⥤ D) :
    (Dᵒᵖ ⥤ Type) ⥤ (Cᵒᵖ ⥤ Type) :=
  (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type)).obj f.op

/-- The cocontinuous extension, constructed by pointwise left Kan extension. -/
noncomputable def extendPresheaf {C D : Type} [SmallCategory C] [SmallCategory D] (f : C ⥤ D) :
    (Cᵒᵖ ⥤ Type) ⥤ (Dᵒᵖ ⥤ Type) :=
  f.op.lan

theorem main : ∀ (C D : Type) [SmallCategory C] [SmallCategory D] (f : C ⥤ D),
    Nonempty (extendPresheaf f ⊣ restrictPresheaf f) ∧
      Nonempty (yoneda ⋙ extendPresheaf f ≅ f ⋙ yoneda) := by
  sorry

end OMA.S_mo_49546
