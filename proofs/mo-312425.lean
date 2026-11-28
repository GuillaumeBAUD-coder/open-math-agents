import OMAStatements.S_mo_312425
import Mathlib

-- Problem: Does each monotonic endofunctor on the category of sets and relations preserve conversion?
-- Upstream: formal-conjectures statements/mo-312425.lean:0 (declaration OMA.S_mo_312425.main)
-- Credit: @Mapika (the owner of the agent is credited as the solver)
-- Proof: a monotone functor preserves the adjunction id <= G;G^o, G^o;G <= id of every function graph G,
-- which forces F(G^o) = (F G)^o; every relation is G_p^o ; G_q for the projections of its tabulation.

open CategoryTheory

namespace OMAProof312425

universe u

/-- The graph of a function, as a morphism of `Rel`. -/
def gr {A B : RelCat.{u}} (f : A → B) : A ⟶ B := RelCat.Hom.ofRel (Function.graph f)

/-- The converse of the graph of a function, as a morphism of `Rel`. -/
def grInv {A B : RelCat.{u}} (f : A → B) : B ⟶ A := RelCat.Hom.ofRel (Function.graph f).inv

/-- In `Rel`, if `id ⊆ A ; B` and `B ; A ⊆ id`, then `B` is the converse of `A`. -/
theorem adj_inv {X Y : Type u} (A : SetRel X Y) (B : SetRel Y X)
    (h1 : ∀ x, ∃ y, (x, y) ∈ A ∧ (y, x) ∈ B)
    (h2 : ∀ y x y', (y, x) ∈ B → (x, y') ∈ A → y = y') : B = A.inv := by
  ext ⟨y, x⟩
  constructor
  · intro hb
    obtain ⟨y0, ha, _⟩ := h1 x
    have e := h2 y x y0 hb ha
    subst e
    exact ha
  · intro ha
    obtain ⟨y0, _, hb0⟩ := h1 x
    have e := h2 y0 x y hb0 ha
    subst e
    exact hb0

/-- A monotone endofunctor of `Rel` sends the converse of a graph to the converse of its image. -/
theorem graph_inv (F : RelCat.{u} ⥤ RelCat.{u})
    (hF : ∀ {X Y : RelCat.{u}} {R S : X ⟶ Y},
      R.rel ⊆ S.rel → (F.map R).rel ⊆ (F.map S).rel)
    {A B : RelCat.{u}} (f : A → B) :
    F.map (grInv f) = RelCat.Hom.ofRel (F.map (gr f)).rel.inv := by
  have e1 : (𝟙 A : A ⟶ A).rel ⊆ (gr f ≫ grInv f).rel := by
    rintro ⟨a, a'⟩ h
    change a = a' at h
    subst h
    exact ⟨f a, rfl, rfl⟩
  have e2 : (grInv f ≫ gr f).rel ⊆ (𝟙 B : B ⟶ B).rel := by
    rintro ⟨b, b'⟩ ⟨a, h1, h2⟩
    change f a = b at h1
    change f a = b' at h2
    change b = b'
    rw [← h1, h2]
  have f1 := hF e1
  have f2 := hF e2
  rw [F.map_id, F.map_comp] at f1 f2
  ext1
  apply adj_inv
  · intro x
    have hx := f1 (show (x, x) ∈ (𝟙 (F.obj A) : F.obj A ⟶ F.obj A).rel from rfl)
    exact hx
  · intro y x y' hb ha
    have hyy := f2 (show (y, y') ∈ (F.map (grInv f) ≫ F.map (gr f)).rel from ⟨x, hb, ha⟩)
    exact hyy

end OMAProof312425

open OMAProof312425 in
theorem OMA.solution : type_of% @OMA.S_mo_312425.main := by
  intro F hF X Y R
  -- tabulate `R` by the type of its pairs
  let T : RelCat := {pr : X × Y // pr ∈ R.rel}
  let p : T → X := fun t => (show {pr : X × Y // pr ∈ R.rel} from t).1.1
  let q : T → Y := fun t => (show {pr : X × Y // pr ∈ R.rel} from t).1.2
  have hR : R = grInv p ≫ gr q := by
    ext1
    ext ⟨x, y⟩
    constructor
    · intro h
      exact ⟨⟨(x, y), h⟩, rfl, rfl⟩
    · rintro ⟨⟨⟨x', y'⟩, h⟩, h1, h2⟩
      change x' = x at h1
      change y' = y at h2
      subst h1
      subst h2
      exact h
  have hRinv : (RelCat.Hom.ofRel R.rel.inv : Y ⟶ X) = grInv q ≫ gr p := by
    apply RelCat.Hom.ext
    ext ⟨y, x⟩
    constructor
    · intro h
      exact ⟨⟨(x, y), h⟩, rfl, rfl⟩
    · rintro ⟨⟨⟨x', y'⟩, h⟩, h1, h2⟩
      change y' = y at h1
      change x' = x at h2
      subst h1
      subst h2
      exact h
  rw [hRinv, F.map_comp, graph_inv F hF q]
  rw [hR, F.map_comp, graph_inv F hF p]
  ext1
  ext ⟨a, b⟩
  simp only [RelCat.Hom.rel_comp]
  constructor
  · rintro ⟨c, h1, h2⟩
    exact ⟨c, h2, h1⟩
  · rintro ⟨c, h1, h2⟩
    exact ⟨c, h2, h1⟩
