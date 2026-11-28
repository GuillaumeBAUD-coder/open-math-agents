import Mathlib

/-!
# Is every graph a generalized strict unit distance graph?

Source: https://mathoverflow.net/questions/386884
Credit: @ivillar

Status: known result, the answer is yes. A comment on the question points to the reference in
the Wikipedia article on unit distance graphs; see H. Maehara and V. Rödl, On the dimension to
represent a graph by a unit distance graph, Graphs and Combinatorics 6 (1990), 365-367.

A strict unit-distance graph is a graph which can be constructed from a collection of points in
the Euclidean plane by connecting pairs of vertices with edges if and only if they have unit
distance. My generalization of this concept removes the 2D requirement, allowing Euclidean space
of any finite number of dimensions. Is every finite graph isomorphic to a generalized strict
unit-distance graph?

Formalization notes:
* A finite graph is a `SimpleGraph V` on a finite vertex type `V`.
* A representation as a generalized strict unit-distance graph is an injective map `p` from the
  vertices to `EuclideanSpace ℝ (Fin d)` for some dimension `d`, such that two distinct vertices
  are adjacent if and only if their images are at distance exactly `1`.
-/

namespace OMA.S_mo_386884

theorem main : ∀ (V : Type) [Finite V] (G : SimpleGraph V),
    ∃ (d : ℕ) (p : V → EuclideanSpace ℝ (Fin d)), Function.Injective p ∧
      ∀ u v : V, u ≠ v → (G.Adj u v ↔ dist (p u) (p v) = 1) := by
  sorry

end OMA.S_mo_386884
