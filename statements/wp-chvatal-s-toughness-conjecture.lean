import Mathlib

/-!
# Chvátal's toughness conjecture

Source: https://en.wikipedia.org/wiki/Graph_toughness
Credit: @shc261392

Chvátal (1973) conjectured that there is a number `t` such that every `t`-tough graph is
Hamiltonian.

Reading used here:
* Graphs are finite simple graphs. A graph is `t`-tough when every set `S` of vertices whose
  removal leaves at least two connected components satisfies `t * c(G - S) ≤ |S|`, where
  `c(G - S)` is the number of components of the subgraph induced on the remaining vertices.
  Graphs with no such cut (complete graphs) are `t`-tough for every `t`, as in the source.
* Hamiltonian is Mathlib's `SimpleGraph.IsHamiltonian`. The graph has at least `3` vertices:
  the complete graph on `2` vertices has no cut, so it is `t`-tough for every `t`, but it has no
  Hamiltonian cycle, and the conjecture is meant for graphs where a cycle can exist.
-/

namespace OMA.S_wp_chvatal_s_toughness_conjecture

/-- `G` is `t`-tough: every vertex cut `S` leaving `c ≥ 2` components has `t * c ≤ |S|`. -/
def IsTough {V : Type} (t : ℝ) (G : SimpleGraph V) : Prop :=
  ∀ S : Finset V, 2 ≤ Nat.card (G.induce ((S : Set V)ᶜ)).ConnectedComponent →
    t * (Nat.card (G.induce ((S : Set V)ᶜ)).ConnectedComponent : ℝ) ≤ (S.card : ℝ)

theorem main :
    ∃ t : ℝ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      3 ≤ Fintype.card V → IsTough t G → G.IsHamiltonian := by
  sorry

end OMA.S_wp_chvatal_s_toughness_conjecture
