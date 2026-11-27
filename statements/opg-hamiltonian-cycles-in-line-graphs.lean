import Mathlib

/-!
# Hamiltonian cycles in line graphs (Thomassen's conjecture)

Source: http://www.openproblemgarden.org/op/hamiltonian_cycles_in_line_graphs
Credit: @shc261392

Conjecture (Thomassen): every 4-connected line graph is hamiltonian.

Reading used here:
* A line graph is a graph isomorphic to `H.lineGraph` for a finite simple graph `H`
  (Mathlib's `SimpleGraph.lineGraph`, on the vertex type `H.edgeSet`). Being hamiltonian is
  invariant under isomorphism, so the statement is made for `H.lineGraph` itself. (By Ryjáček,
  one may even restrict to `H` triangle-free; the conjecture is equivalent to the
  Matthews–Sumner conjecture on 4-connected claw-free graphs.)
* `k`-connected is the usual vertex connectivity: more than `k` vertices, and the graph stays
  connected after deleting any set of fewer than `k` vertices.
* Hamiltonian is Mathlib's `SimpleGraph.IsHamiltonian`.
-/

namespace OMA.S_opg_hamiltonian_cycles_in_line_graphs

/-- `G` is `k`-connected: more than `k` vertices, and removing fewer than `k` vertices leaves it
connected. -/
def IsKConnected {W : Type} [Fintype W] (k : ℕ) (G : SimpleGraph W) : Prop :=
  k < Fintype.card W ∧ ∀ S : Finset W, S.card < k → (G.induce ((S : Set W)ᶜ)).Connected

theorem main :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj],
      IsKConnected 4 H.lineGraph → H.lineGraph.IsHamiltonian := by
  sorry

end OMA.S_opg_hamiltonian_cycles_in_line_graphs
