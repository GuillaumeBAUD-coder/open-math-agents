import Mathlib

/-!
# FuncoidDiagram
Open Problem Garden: https://www.openproblemgarden.org/op/a_diagram_about_funcoids_and_reloids
The other node in Figure 1 applies the lower generalized adjoint to the outer reloid map. Suprema of funcoid relations are pointwise unions.
-/

namespace OMA.S_opg_a_diagram_about_funcoids_and_reloids

open Filter Set

/-- A funcoid given by its relation on pairs of subsets. -/
structure Funcoid (A B : Type) where
  rel : Set A → Set B → Prop
  empty_left : ∀ Y, ¬ rel ∅ Y
  empty_right : ∀ X, ¬ rel X ∅
  union_left : ∀ X X' Y, rel (X ∪ X') Y ↔ rel X Y ∨ rel X' Y
  union_right : ∀ X Y Y', rel X (Y ∪ Y') ↔ rel X Y ∨ rel X Y'

/-- The outer reloid, obtained by meeting the principal reloids of
relations whose principal funcoids are above the given funcoid. -/
def outerReloid {A B : Type} (f : Funcoid A B) : Filter (A × B) :=
  Filter.generate {R | ∀ X Y, f.rel X Y → (X ×ˢ Y ∩ R).Nonempty}

/-- The top funcoid relates every pair of nonempty sets. -/
def topFuncoid (A B : Type) : Funcoid A B where
  rel X Y := X.Nonempty ∧ Y.Nonempty
  empty_left := by simp
  empty_right := by simp
  union_left := by
    intro X X' Y
    simp only [Set.union_nonempty]
    tauto
  union_right := by
    intro X Y Y'
    simp only [Set.union_nonempty]
    tauto

/-- The diagram node obtained by taking the supremum of the funcoids
whose outer reloid is below the given reloid. -/
def other {A B : Type} (r : Filter (A × B)) : Funcoid A B where
  rel X Y := ∃ f : Funcoid A B, outerReloid f ≤ r ∧ f.rel X Y
  empty_left := by
    intro Y
    rintro ⟨f, _, h⟩
    exact f.empty_left Y h
  empty_right := by
    intro X
    rintro ⟨f, _, h⟩
    exact f.empty_right X h
  union_left := by
    intro X X' Y
    constructor
    · rintro ⟨f, hf, h⟩
      exact (f.union_left _ _ _).mp h |>.elim (fun h => Or.inl ⟨f, hf, h⟩)
        (fun h => Or.inr ⟨f, hf, h⟩)
    · rintro (⟨f, hf, h⟩ | ⟨f, hf, h⟩)
      · exact ⟨f, hf, (f.union_left _ _ _).mpr (Or.inl h)⟩
      · exact ⟨f, hf, (f.union_left _ _ _).mpr (Or.inr h)⟩
  union_right := by
    intro X Y Y'
    constructor
    · rintro ⟨f, hf, h⟩
      exact (f.union_right _ _ _).mp h |>.elim (fun h => Or.inl ⟨f, hf, h⟩)
        (fun h => Or.inr ⟨f, hf, h⟩)
    · rintro (⟨f, hf, h⟩ | ⟨f, hf, h⟩)
      · exact ⟨f, hf, (f.union_right _ _ _).mpr (Or.inl h)⟩
      · exact ⟨f, hf, (f.union_right _ _ _).mpr (Or.inr h)⟩

def ClaimedOutcome : Prop :=
  ∀ (A B : Type) (r : Filter (A × B)), other r = topFuncoid A B

theorem main : ClaimedOutcome := by
  sorry

end OMA.S_opg_a_diagram_about_funcoids_and_reloids
