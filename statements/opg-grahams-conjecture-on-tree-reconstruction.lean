import Mathlib

/-!
# Graham's conjecture on tree reconstruction

Source: https://www.openproblemgarden.org/op/grahams_conjecture_on_tree_reconstruction
Credit: @Hyvok

Informal statement (Open Problem Garden, posed by Graham; mentioned in C. Godsil and
G. Royle, Algebraic Graph Theory, GTM 207, Springer 2001, p. 18):
For every graph `G`, let `L(G)` denote the line graph of `G`. Given that `G` is a tree, can we
determine it from the integer sequence `|V(G)|, |V(L(G))|, |V(L(L(G)))|, ...`?

Formalization notes:
* The question is a yes/no question; `main` states the conjectured direction (yes): two finite
  trees whose iterated line graph sequences have the same numbers of vertices at every step
  are isomorphic. Determined means determined up to graph isomorphism.
* Trees are Mathlib's `SimpleGraph.IsTree` (connected, hence nonempty, and acyclic) on a
  `Finite` vertex type; trees are taken to be finite, as is implicit in the source (the
  sequence consists of integers).
* `L(G)` is Mathlib's `SimpleGraph.lineGraph`, whose vertex type is the edge set of `G`.
  Since each iterate lives on a different type, `iterLineGraph G k` packages the `k`-th
  iterate `L^k(G)` (with `L^0(G) = G`) together with its vertex type as a sigma type, and
  the sequence term is `Nat.card` of that vertex type. For finite `G` all iterates are finite,
  so `Nat.card` is the actual number of vertices. The index starts at `k = 0` with `|V(G)|`.
-/

namespace OMA.S_opg_grahams_conjecture_on_tree_reconstruction

/-- The `k`-th iterated line graph `L^k(G)`, packaged with its vertex type
(`L^0(G) = G`, `L^(k+1)(G) = L(L^k(G))`). -/
def iterLineGraph {V : Type} (G : SimpleGraph V) : ℕ → Σ W : Type, SimpleGraph W
  | 0 => ⟨V, G⟩
  | k + 1 => ⟨(iterLineGraph G k).2.edgeSet, (iterLineGraph G k).2.lineGraph⟩

/-- **Graham's tree reconstruction conjecture.** A finite tree is determined up to isomorphism
by the sequence `|V(G)|, |V(L(G))|, |V(L(L(G)))|, ...`. -/
theorem main :
    ∀ (V W : Type) [Finite V] [Finite W] (S : SimpleGraph V) (T : SimpleGraph W),
      S.IsTree → T.IsTree →
      (∀ k : ℕ, Nat.card (iterLineGraph S k).1 = Nat.card (iterLineGraph T k).1) →
      Nonempty (S ≃g T) := by
  sorry

end OMA.S_opg_grahams_conjecture_on_tree_reconstruction
