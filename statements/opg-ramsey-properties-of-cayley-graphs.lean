import Mathlib

/-!
# Ramsey properties of Cayley graphs

Source: https://www.openproblemgarden.org/op/ramsey_properties_of_cayley_graphs
Credit: @joshuadc11

Alon's conjecture: there exists a constant `c > 0` such that every finite abelian group `G`
(with `|G| ≥ 2`) has a symmetric subset `S ⊆ G` (`-S = S`, `0 ∉ S`) whose Cayley graph
`Cayley(G, S)` has neither a clique nor an independent set of size greater than `c * log |G|`.

## Encoding

* `G` is a finite `AddCommGroup` with `2 ≤ Fintype.card G` (since `log 1 = 0`, the bound
  `≤ c * log |G|` requires `|G| ≥ 2`).
* `S : Set G` satisfies `0 ∉ S` and `∀ s ∈ S, -s ∈ S`, and `cayleyGraph S` is the undirected
  Cayley graph on `G`.
* Cliques and independent sets use Mathlib's `SimpleGraph.IsClique` and `SimpleGraph.IsIndepSet`.
-/

namespace OMA.S_opg_ramsey_properties_of_cayley_graphs

/-- The undirected Cayley graph of an additive abelian group `G` with respect to `S`. -/
def cayleyGraph {G : Type} [AddCommGroup G] (S : Set G) : SimpleGraph G where
  Adj x y := x ≠ y ∧ (y - x ∈ S ∨ x - y ∈ S)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- There exists `c : ℝ` such that every finite abelian group `G` of order at least `2` admits a
symmetric subset `S` whose Cayley graph has all cliques and independent sets of size at most
`c * Real.log |G|`. -/
theorem main : ∃ c : ℝ, ∀ (G : Type) [AddCommGroup G] [Fintype G], 2 ≤ Fintype.card G →
    ∃ S : Set G, (0 : G) ∉ S ∧ (∀ s ∈ S, -s ∈ S) ∧
      (∀ K : Finset G, (cayleyGraph S).IsClique (K : Set G) →
        (K.card : ℝ) ≤ c * Real.log (Fintype.card G)) ∧
      (∀ I : Finset G, (cayleyGraph S).IsIndepSet (I : Set G) →
        (I.card : ℝ) ≤ c * Real.log (Fintype.card G)) := by
  sorry

end OMA.S_opg_ramsey_properties_of_cayley_graphs
