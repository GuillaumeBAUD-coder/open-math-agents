import Mathlib

/-!
# A generalization of Vizing's Theorem?

Source: https://www.openproblemgarden.org/op/a_generalization_of_vizings_theorem
Credit: @joshuadc11

Rosenfeld's conjecture: let `H` be a finite simple `d`-uniform hypergraph such that every set of
`d - 1` vertices is contained in at most `r` edges. Then `H` admits an `(r + d - 1)`-edge-coloring
in which any two distinct edges sharing `d - 1` vertices receive distinct colors. (For `d = 2`,
this is Vizing's theorem.)

## Encoding

* A finite simple `d`-uniform hypergraph on `V` is a `H : Finset (Finset V)` with
  `∀ e ∈ H, e.card = d`, where `1 ≤ d`.
* Every `(d - 1)`-element subset `S : Finset V` lies in at most `r` edges:
  `(H.filter fun e => S ⊆ e).card ≤ r`.
* An `(r + d - 1)`-edge-coloring is a map `c : H → Fin (r + d - 1)` such that any two distinct
  edges `e₁ e₂ : H` with `(e₁.1 ∩ e₂.1).card = d - 1` satisfy `c e₁ ≠ c e₂`.
-/

namespace OMA.S_opg_a_generalization_of_vizings_theorem

/-- Every finite simple `d`-uniform hypergraph (`d ≥ 1`) in which every `(d - 1)`-set lies in at
most `r` edges admits an `(r + d - 1)`-edge-coloring where any two distinct edges sharing `d - 1`
vertices have distinct colors. -/
theorem main : ∀ (V : Type) [Fintype V] [DecidableEq V] (d r : ℕ), 1 ≤ d →
    ∀ H : Finset (Finset V),
      (∀ e ∈ H, e.card = d) →
      (∀ S : Finset V, S.card = d - 1 → (H.filter fun e => S ⊆ e).card ≤ r) →
      ∃ c : H → Fin (r + d - 1),
        ∀ e₁ e₂ : H, e₁ ≠ e₂ → (e₁.1 ∩ e₂.1).card = d - 1 → c e₁ ≠ c e₂ := by
  sorry

end OMA.S_opg_a_generalization_of_vizings_theorem
