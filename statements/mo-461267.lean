import Mathlib

/-!
# Do vertex-maximal paths in 4-connected graphs intersect?

Source: https://mathoverflow.net/questions/461267
Credit: @zarnab222-dev

A path in a (possibly infinite) graph is vmax (vertex-maximal) if no path covers a strictly larger
set of vertices. The question: is it true that any two vmax paths intersect in any `k`-connected
graph if `k` is large enough? The affirmative claim is stated: there is a threshold `K` such that
for every `k ≥ K`, in every `k`-connected graph any two vmax paths share a vertex.

Translation choices:
* a graph is a `SimpleGraph V` on an arbitrary type `V` (finite or infinite);
* a path is a finite path, the standard meaning: a walk `p` with `p.IsPath` (no repeated vertex;
  the one-vertex walk is a path); its vertex set is `{x | x ∈ p.support}`;
* `k`-connected is the standard (Diestel) notion: more than `k` vertices, and deleting any set of
  fewer than `k` vertices leaves a connected graph; a set of fewer than `k` vertices is a `Finset`;
* two paths intersect when they have a common vertex;
* of the two questions in the post this is the first, general one. The second (is there a vertex
  on all vmax paths of any 4-connected graph) is stronger, so a refutation of this one, which
  gives two disjoint vmax paths in graphs of arbitrarily large connectivity, answers it as well.
-/

namespace OMA.S_mo_461267

/-- `G` is `k`-connected: it has more than `k` vertices and stays connected after the deletion of
any set of fewer than `k` vertices. -/
def IsKConnected {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  (k : ℕ∞) < ENat.card V ∧
    ∀ X : Finset V, X.card < k → (G.induce ((X : Set V)ᶜ)).Connected

/-- The walk `p` is a vmax path: it is a path, and no path of `G` has a vertex set strictly
containing the vertex set of `p`. -/
def IsVMax {V : Type} (G : SimpleGraph V) {a b : V} (p : G.Walk a b) : Prop :=
  p.IsPath ∧
    ∀ (c d : V) (r : G.Walk c d), r.IsPath → ¬ ({x | x ∈ p.support} ⊂ {x | x ∈ r.support})

theorem main :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ (V : Type) (G : SimpleGraph V), IsKConnected G k →
      ∀ (a b c d : V) (p : G.Walk a b) (q : G.Walk c d), IsVMax G p → IsVMax G q →
        ∃ x : V, x ∈ p.support ∧ x ∈ q.support := by
  sorry

end OMA.S_mo_461267
