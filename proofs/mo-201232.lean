import OMAStatements.S_mo_201232
import Mathlib

/-!
# MO 201232: a vertex-edge incidence need not lift (the claim is false)

Statement. A pure graph is a graph with a nonempty set of edges, all edges of size 2, and no
isolated vertex. Its face poset consists of the empty face, the vertices and the edges. The claim
is that for all pure graphs P and Q and every surjective map f from the faces of P to the faces of Q
that preserves inclusion and cardinality, every incidence v subset e of Q (with |v| = 1 and |e| = 2)
lifts: there are faces x subset y of P with f x = v and f y = e.

The claim is false. Counterexample:

Source P: vertices 0, 1, 2, 3 and edges {0,1}, {2,3}. Target Q: vertices 0, 1, 2 and edges {0,1}, {1,2}.
Both are pure graphs. Define f on the faces of P by
- the empty face to the empty face;
- {0} and {1} to {0}, {2} to {1}, {3} to {2};
- {0,1} to {0,1} and {2,3} to {1,2}.

1. f is surjective: its values are the empty face and {0}, {1}, {2}, {0,1}, {1,2}, which are all faces of Q.
2. f preserves cardinality: vertices go to vertices, edges go to edges, and the empty face to itself.
3. f preserves inclusion: this is a finite check over all pairs of faces of P.
4. Take v = {1} and e = {0,1}, so v is contained in e. A lift needs a face y of P with f y = {0,1}.
   The only such face is y = {0,1}. A lift also needs x contained in {0,1} with f x = {1}. The faces
   contained in {0,1} are the empty face, {0}, {1} and {0,1}, with images the empty face, {0}, {0}
   and {0,1}. None maps to {1}. So the incidence does not lift, and the claim fails.
-/

namespace OMA.S_mo_201232

/-- The source graph P: two disjoint edges on four vertices. -/
def source : Finset (Finset (Fin 4)) := {{0,1}, {2,3}}

/-- The target graph Q: a path with two edges on three vertices. -/
def target : Finset (Finset (Fin 3)) := {{0,1}, {1,2}}

/-- The map f on faces of P (Step 1 to 3 of the header), given by its values on the empty face,
vertices and edges. -/
def imageFace (s : Finset (Fin 4)) : Finset (Fin 3) :=
  if s = ∅ then ∅ else if s.card = 2 then
    if 0 ∈ s then {0,1} else {1,2}
  else if 2 ∈ s then {1} else if 3 ∈ s then {2} else {0}

/-- The map f as a function between the face posets of P and Q. -/
def faceMap (s : Face source) : Face target :=
  ⟨imageFace s, (show ∀ t : Face source, imageFace t ∈ faces target by decide) s⟩

/-- The target incidence vertex 1 (the face {1} of Q). -/
def vertex1 : Face target := ⟨{1}, by decide⟩

/-- The target edge {0,1} of Q. -/
def edge01 : Face target := ⟨{0,1}, by decide⟩

/-- Step 0: P is a pure graph. -/
lemma source_pure : PureGraph source := by
  unfold PureGraph
  decide

/-- Step 0: Q is a pure graph. -/
lemma target_pure : PureGraph target := by
  unfold PureGraph
  decide

/-- Step 1: f is surjective onto the faces of Q. -/
lemma faceMap_surjective : Function.Surjective faceMap := by
  unfold Function.Surjective
  decide

/-- Step 3: f preserves inclusion of faces. Finite check over all pairs of faces of P. -/
lemma faceMap_monotone : ∀ x y : Face source, x.val ⊆ y.val → (faceMap x).val ⊆ (faceMap y).val := by
  decide

/-- Step 2: f preserves cardinalities of faces. Finite check over all faces of P. -/
lemma faceMap_card_preserving : ∀ x : Face source, (faceMap x).val.card = x.val.card := by
  decide

/-- Step 4: no lift of the incidence vertex1 subset edge01 exists. The finite check goes over all
pairs of faces x, y of P with x subset y and reports that none has f y = edge01 and f x = vertex1. -/
lemma no_lift : ¬ ∃ x y : Face source, x.val ⊆ y.val ∧ faceMap x = vertex1 ∧ faceMap y = edge01 := by
  decide

end OMA.S_mo_201232

open OMA.S_mo_201232 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_201232.main) := by
  intro h
  -- Apply the claim to P, Q, the map faceMap and the incidence vertex1 subset edge01.
  have lift := h 4 3 source target source_pure target_pure
    faceMap faceMap_surjective faceMap_monotone faceMap_card_preserving
    vertex1 edge01 (by decide) (by decide) (by decide)
  -- The claim would give a lift, which contradicts step 4.
  exact no_lift lift
