import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

/-!
# Barnette's conjecture

Source: https://en.wikipedia.org/wiki/Barnette's_conjecture
Credit: @SubhanAfz
-/

namespace OMA.S_wp_barnette_s_conjecture

open scoped Classical

/-- A minor model assigns disjoint nonempty connected branch sets in `G` to vertices of `H`.
Every edge of `H` is represented by an edge of `G` between the corresponding branch sets. -/
def IsMinorOf {V W : Type*} (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∃ branch : W → Set V,
    (∀ i, (G.induce (branch i)).Connected) ∧
    (Pairwise fun i j ↦ Disjoint (branch i) (branch j)) ∧
    (∀ i j, H.Adj i j → ∃ u ∈ branch i, ∃ v ∈ branch j, G.Adj u v)

/-- For finite graphs, Wagner's theorem characterizes planarity by these two excluded minors. -/
def IsPlanar {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬ IsMinorOf (SimpleGraph.completeGraph (Fin 5)) G ∧
  ¬ IsMinorOf (completeBipartiteGraph (Fin 3) (Fin 3)) G

/-- A graph with more than three vertices stays connected after deleting fewer than three. -/
def IsThreeConnected {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  3 < Fintype.card V ∧ ∀ S : Finset V, S.card < 3 → (G.induce ((S : Set V)ᶜ)).Connected

theorem main :
    ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
      G.IsRegularOfDegree 3 → G.IsBipartite → IsThreeConnected G → IsPlanar G →
      G.IsHamiltonian := by
  sorry

end OMA.S_wp_barnette_s_conjecture
