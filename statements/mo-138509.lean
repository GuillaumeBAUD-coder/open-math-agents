import Mathlib

/-!
# Why the number of the vertices is even?

Source: https://mathoverflow.net/questions/138509
Credit: @ivillar

Status: known result (true). The comments on the question give the proof: the hypothesis says
that the adjacency matrix is nonsingular over the field with two elements, and a symmetric
matrix with zero diagonal over that field has even rank.

Let $G$ be a graph with $n$ vertices and $V$ the vertex set. Suppose that for each non-empty
subset $W$ of $V$ there exists an element $\omega \in V$ (maybe in $W$ or not) such that the
degree of $\omega$ in $W$ is odd (that is, there are an odd number of vertices in $W$ which are
connected to $\omega$); then we can make the conclusion that $n$ is even.

Formalization notes:
* The graph is a `SimpleGraph V` on a finite vertex type, and `n = Fintype.card V`.
* The degree of `ω` in `W` is the number of `v ∈ W` adjacent to `ω`, written as the `Set.ncard`
  of `{v | v ∈ W ∧ G.Adj ω v}`.
-/

namespace OMA.S_mo_138509

theorem main : ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    (∀ W : Set V, W.Nonempty → ∃ ω : V, Odd (Set.ncard {v | v ∈ W ∧ G.Adj ω v})) →
    Even (Fintype.card V) := by
  sorry

end OMA.S_mo_138509
