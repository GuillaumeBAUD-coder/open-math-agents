import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Jørgensen's apex graph conjecture

Source: https://en.wikipedia.org/wiki/apex_graph
Credit: @SubhanAfz

Kawarabayashi, Norine, Thomas and Wollan state the conjecture and prove it for
sufficiently large graphs in https://arxiv.org/abs/1203.2192.
-/

namespace OMA.S_wp_apex_graph

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

/-- A `k`-vertex-connected graph has more than `k` vertices and stays connected
after deletion of any set of fewer than `k` vertices. -/
def IsVertexConnected {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧ ∀ S : Finset V, S.card < k → (G.induce ((S : Set V)ᶜ)).Connected

theorem main :
    ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
      IsVertexConnected G 6 → ¬ IsMinorOf (SimpleGraph.completeGraph (Fin 6)) G →
      ∃ v : V, IsPlanar (G.induce (({v} : Set V)ᶜ)) := by
  sorry

end OMA.S_wp_apex_graph
