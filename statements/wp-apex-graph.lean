import Mathlib

/-!
# Apex graph

Source: https://en.wikipedia.org/wiki/apex_graph
Credit: @Spenz90

Jorgensen's conjecture (1994): every 6-vertex-connected graph that does not
have the complete graph K6 as a minor is an apex graph.

Mathlib has no graph minors, no planarity and no vertex connectivity, so the
three notions are defined here from the standard definitions. Planarity is
defined by Kuratowski's characterization (no K5 and no K3,3 minor), which is
equivalent to the usual embedding definition.
-/

namespace OMA.S_wp_apex_graph

open SimpleGraph

/-- A graph `H` is a minor of a graph `G` if the vertices of `H` can be
represented by pairwise disjoint nonempty connected sets of vertices of `G`
(the branch sets), such that adjacent vertices of `H` have an edge of `G`
between their branch sets. -/
def IsMinor {V W : Type*} (H : SimpleGraph V) (G : SimpleGraph W) : Prop :=
  ∃ B : V → Set W,
    (∀ v, (B v).Nonempty) ∧
    (∀ v₁ v₂, v₁ ≠ v₂ → Disjoint (B v₁) (B v₂)) ∧
    (∀ v, (G.induce (B v)).Preconnected) ∧
    ∀ ⦃v₁ v₂ : V⦄, H.Adj v₁ v₂ → ∃ x ∈ B v₁, ∃ y ∈ B v₂, G.Adj x y

/-- A graph is planar if it has neither the complete graph `K5` nor the
complete bipartite graph `K3,3` as a minor (Kuratowski's theorem). -/
def IsPlanar {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬ IsMinor (completeGraph (Fin 5)) G ∧
    ¬ IsMinor (completeBipartiteGraph (Fin 3) (Fin 3)) G

/-- A graph is an apex graph if it can be made planar by the removal of a
single vertex. A planar graph is itself apex (removing any vertex keeps it
planar), and the null graph is counted as apex as well. -/
def IsApex {V : Type*} (G : SimpleGraph V) : Prop :=
  IsPlanar G ∨ ∃ v : V, IsPlanar (G.induce ({v}ᶜ : Set V))

/-- A graph is `k`-vertex-connected if it has more than `k` vertices and
removing fewer than `k` vertices leaves it connected. -/
def IsVertexConnected {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧
    ∀ S : Finset V, S.card < k → (G.induce ((S : Set V)ᶜ)).Connected

/-- Jorgensen's conjecture: every 6-vertex-connected K6-minor-free graph is
an apex graph. -/
theorem main : ∀ {V : Type*} [Fintype V] (G : SimpleGraph V),
    IsVertexConnected G 6 → ¬ IsMinor (completeGraph (Fin 6)) G → IsApex G := by
  sorry

end OMA.S_wp_apex_graph
