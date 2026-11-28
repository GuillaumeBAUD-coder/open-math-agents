import Mathlib

/-!
# Partial List Coloring

Source: https://www.openproblemgarden.org/op/partial_list_coloring
Credit: @joshuadc11

Albertson–Grossman–Haas conjecture: let `G` be a finite simple graph with `n` vertices and list
chromatic number `χ_ℓ(G)`. If `0 ≤ t ≤ χ_ℓ(G)` and each vertex of `G` is assigned a list of `t`
colors, then at least `t * n / χ_ℓ(G)` vertices of `G` can be properly colored from their lists.

## Encoding

* Colors are taken from `ℕ` (sufficient without loss of generality for any finite graph).
* `IsListColorable G k` says every `k`-list assignment `L : V → Finset ℕ` admits a proper coloring
  of `G` from `L`, and `listChromaticNumber G` is the least such `k : ℕ`.
* The bound `|S| ≥ t * n / χ_ℓ(G)` is written equivalently without division as
  `t * Fintype.card V ≤ S.card * listChromaticNumber G`.
-/

namespace OMA.S_opg_partial_list_coloring

/-- `G` is `k`-choosable (`k`-list-colorable). -/
def IsListColorable {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ L : V → Finset ℕ, (∀ v, (L v).card = k) →
    ∃ c : V → ℕ, (∀ v, c v ∈ L v) ∧ ∀ u v, G.Adj u v → c u ≠ c v

/-- The list chromatic number `χ_ℓ(G)` of a finite graph `G`. -/
noncomputable def listChromaticNumber {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | IsListColorable G k}

/-- For every finite simple graph `G`, `0 ≤ t ≤ χ_ℓ(G)`, and `t`-list assignment `L`, there is a
subset `S` of at least `t * |V| / χ_ℓ(G)` vertices that can be properly colored from `L`. -/
theorem main : ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (t : ℕ),
    t ≤ listChromaticNumber G →
    ∀ L : V → Finset ℕ, (∀ v, (L v).card = t) →
      ∃ (S : Finset V) (c : V → ℕ),
        t * Fintype.card V ≤ S.card * listChromaticNumber G ∧
        (∀ v ∈ S, c v ∈ L v) ∧
        (∀ u ∈ S, ∀ v ∈ S, G.Adj u v → c u ≠ c v) := by
  sorry

end OMA.S_opg_partial_list_coloring
