import Mathlib

/-!
# Vizing's conjecture on the domination number of Cartesian products of graphs

Source: https://en.wikipedia.org/wiki/Vizing's_conjecture
Credit: @joshuadc11

For any two finite simple graphs `G` and `H`,
`γ(G □ H) ≥ γ(G) * γ(H)`,
where `γ` denotes the domination number and `G □ H` (`SimpleGraph.boxProd`) is the
Cartesian product of `G` and `H`.

Formalization notes:
- A dominating set `D : Set V` of `G` satisfies `∀ v : V, v ∈ D ∨ ∃ u ∈ D, G.Adj u v`.
- `dominationNumber G` is the minimum cardinality (`Set.ncard`) of a dominating set of `G`.
- The Cartesian product of graphs is Mathlib's `SimpleGraph.boxProd`.
-/

namespace OMA.S_wp_vizing_s_conjecture_on_the_domination_number_of_cartesian_products_of_graphs

/-- A set `D` of vertices is dominating in `G` if every vertex is either in `D` or adjacent
to a vertex in `D`. -/
def IsDominating {V : Type*} (G : SimpleGraph V) (D : Set V) : Prop :=
  ∀ v : V, v ∈ D ∨ ∃ u ∈ D, G.Adj u v

/-- The domination number `γ(G)` of a finite simple graph `G`: the minimum cardinality
of a dominating set of `G`. -/
noncomputable def dominationNumber {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ D : Set V, IsDominating G D ∧ Set.ncard D = k}

theorem main :
    ∀ (V W : Type*) [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W),
      dominationNumber G * dominationNumber H ≤ dominationNumber (G.boxProd H) := by
  sorry

end OMA.S_wp_vizing_s_conjecture_on_the_domination_number_of_cartesian_products_of_graphs
