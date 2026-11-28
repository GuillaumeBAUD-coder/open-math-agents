import Mathlib

/-!
# Ryser's conjecture

Source: https://en.wikipedia.org/wiki/Ryser's_conjecture
Credit: @joshuadc11

For every `r ≥ 2` and every finite `r`-partite `r`-uniform hypergraph `H`, the minimum
transversal (vertex cover) size `τ(H)` and the maximum matching size `ν(H)` satisfy
`τ(H) ≤ (r - 1) * ν(H)`.

Formalization notes:
- An `r`-partite `r`-uniform hypergraph on a finite vertex type `V` is given by a partition
  `part : V → Fin r` and a finite set of hyperedges `E : Finset (Finset V)` such that every
  edge `e ∈ E` contains exactly one vertex from each part `i : Fin r`.
- `maxMatching E` is the maximum cardinality of a pairwise disjoint subset `M ⊆ E`.
- `minTransversal E` is the minimum cardinality of a set `T : Finset V` intersecting every
  edge `e ∈ E`.
-/

namespace OMA.S_wp_ryser_s_conjecture

/-- The maximum matching size `ν(E)` of a hypergraph `E`. -/
noncomputable def maxMatching {V : Type*} [DecidableEq V] (E : Finset (Finset V)) : ℕ :=
  sSup {k : ℕ | ∃ M : Finset (Finset V), M ⊆ E ∧
    (∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → Disjoint e₁ e₂) ∧ M.card = k}

/-- The minimum transversal (vertex cover) size `τ(E)` of a hypergraph `E`. -/
noncomputable def minTransversal {V : Type*} [DecidableEq V] (E : Finset (Finset V)) : ℕ :=
  sInf {k : ℕ | ∃ T : Finset V, (∀ e ∈ E, (e ∩ T).Nonempty) ∧ T.card = k}

theorem main :
    ∀ (r : ℕ), 2 ≤ r →
      ∀ (V : Type*) [Fintype V] [DecidableEq V]
        (part : V → Fin r) (E : Finset (Finset V)),
        (∀ e ∈ E, ∀ i : Fin r, (e.filter (fun v => part v = i)).card = 1) →
        minTransversal E ≤ (r - 1) * maxMatching E := by
  sorry

end OMA.S_wp_ryser_s_conjecture
