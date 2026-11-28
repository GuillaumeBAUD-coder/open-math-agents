import OMAStatements.S_mo_477608
import Mathlib

/-!
# The two-element antichain

The two points are both minimal and have no common cover.
Either point can occur first in a linear extension, giving two extensions.
Deleting either point or both points leaves exactly one extension.
-/

namespace OMA.S_mo_477608

/-- Two points ordered by equality. -/
inductive Point | x | y
  deriving DecidableEq

instance : Fintype Point where
  elems := {.x, .y}
  complete := fun p => by cases p <;> decide

instance : PartialOrder Point where
  le := Eq
  le_refl := Eq.refl
  le_trans := fun _ _ _ => Eq.trans
  le_antisymm := fun _ _ h _ => h
  lt := fun _ _ => False
  lt_iff_le_not_ge := by simp [eq_comm]

instance : DecidableLT Point := fun _ _ => isFalse id

/-- Bounded ranks can equivalently take values in a finite ordinal. -/
lemma countRanks (α : Type) [PartialOrder α] [Fintype α] :
    numLinExt α = Nat.card {f : α → Fin (Fintype.card α) //
      StrictMono f ∧ Function.Injective f} := by
  unfold numLinExt
  rw [Nat.card_eq_fintype_card (α := α)]
  apply Nat.card_congr
  exact {
    toFun := fun f => ⟨fun x => ⟨f.val x, f.property.2.2 x⟩,
      fun _ _ h => f.property.1 h, fun _ _ h => f.property.2.1 (congrArg Fin.val h)⟩
    invFun := fun f => ⟨fun x => (f.val x).val,
      fun _ _ h => f.property.1 h, fun _ _ h => f.property.2 (Fin.ext h),
      fun x => (f.val x).isLt⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- Enumerate bounded maps and test both conditions on pairs of points. -/
lemma enumerate (α : Type) [PartialOrder α] [Fintype α] [DecidableLT α] [DecidableEq α] :
    numLinExt α = ((Finset.univ : Finset (α → Fin (Fintype.card α))).filter
      fun f => ∀ x y, (x < y → f x < f y) ∧ (f x = f y → x = y)).card := by
  rw [countRanks, ← Fintype.card_coe]
  conv_rhs => rw [← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h x y
    exact ⟨fun hxy => h.1 hxy, fun he => h.2 he⟩
  · intro h
    exact ⟨fun {x y} => (h x y).1, fun {x y} => (h x y).2⟩

end OMA.S_mo_477608

open OMA.S_mo_477608 in
theorem OMA.solution : type_of% @OMA.S_mo_477608.main := by
  refine ⟨Point, inferInstance, inferInstance, Point.x, Point.y, by decide, ?_, ?_, ?_, ?_⟩
  · intro b h
    exact Eq.symm h
  · intro b h
    exact Eq.symm h
  · rintro ⟨z, hz, _⟩
    exact hz.1
  · simp only [enumerate]
    decide +kernel
