import Mathlib

/-!
# Hamiltonian paths and cycles in vertex transitive graphs

Source: https://www.openproblemgarden.org/op/hamiltonian_paths_and_cycles_in_vertex_transitive_graphs
(L. Lovász, Combinatorial structures and their applications, Calgary 1969, Problem 11)
Credit: @k-okubo (agent: Claude Code, model claude-opus-5-5)

**Problem (Lovász).** Does every connected vertex-transitive graph have a Hamiltonian path?

No vertex-transitive graph without a Hamiltonian path is known. (Only five connected
vertex-transitive graphs without a Hamiltonian *cycle* are known: `K₂`, the Petersen graph, the
Coxeter graph, and the graphs obtained from these two by replacing every vertex with a triangle.)

The source page also records two related conjectures, which are separate problems and are not part
of `main`: Babai's conjecture that for some `ε > 0` infinitely many connected vertex-transitive
graphs have longest cycle of length `< (1 - ε)|V(G)|`, and the conjecture that every connected
Cayley graph other than `K₂` has a Hamiltonian cycle.

## Encoding

* Graphs are finite simple graphs (the source's graphs are finite: it speaks of `|V(G)|`).
* Vertex-transitive: for any two vertices `u, v` some automorphism of `G` sends `u` to `v`.
* A Hamiltonian path is a walk visiting every vertex exactly once (Mathlib's
  `SimpleGraph.Walk.IsHamiltonian`, which forces the walk to be a path).
* Mathlib's `SimpleGraph.Connected` includes nonemptiness.
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer no.
-/

namespace OMA.S_opg_hamiltonian_paths_and_cycles_in_vertex_transitive_graphs

/-- `G` is vertex-transitive: its automorphism group acts transitively on the vertices. -/
def IsVertexTransitive {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ∃ φ : G ≃g G, φ u = v

/-- **Lovász's question**, answered yes: every finite connected vertex-transitive graph has a
Hamiltonian path. -/
theorem main :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.Connected → IsVertexTransitive G →
        ∃ (u v : V) (p : G.Walk u v), p.IsHamiltonian := by
  sorry

end OMA.S_opg_hamiltonian_paths_and_cycles_in_vertex_transitive_graphs
