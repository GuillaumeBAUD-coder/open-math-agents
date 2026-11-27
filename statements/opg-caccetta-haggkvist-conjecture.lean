import Mathlib

/-!
# Caccetta-Häggkvist Conjecture

Source: https://www.openproblemgarden.org/op/caccetta_haggkvist_conjecture
Credit: @biondadave

Conjecture (Caccetta–Häggkvist, 1978): Every simple digraph of order `n` with minimum outdegree
at least `r` has a directed cycle of length at most `⌈n / r⌉`.

Conventions:
- A simple digraph is a loopless directed graph without parallel arcs. Mathlib's `Digraph V`
  has no parallel arcs by construction (an arc is a proposition `G.Adj u v`); looplessness is a
  hypothesis. Opposite arcs `u → v`, `v → u` are allowed (they form a directed cycle of length
  2), as in the standard formulation.
- The order is `n = Fintype.card V`; `r` is a positive integer, since for `r = 0` the bound
  `⌈n / r⌉` is meaningless. The digraph is nonempty (`n ≥ 1`); otherwise the out-degree
  condition holds vacuously and there is no cycle.
- The out-degree of `v` is the number of `w` with `G.Adj v w`.
- A directed cycle of length `ℓ ≥ 2` is an injective map `c : Fin ℓ → V` with an arc from `c i`
  to `c (i + 1)` for every `i`, indices taken cyclically (`finRotate ℓ`).
-/

namespace OMA.S_opg_caccetta_haggkvist_conjecture

theorem main :
    ∀ (V : Type) [Fintype V] [Nonempty V] (G : Digraph V) [DecidableRel G.Adj] (r : ℕ),
      (∀ v, ¬ G.Adj v v) → 0 < r →
      (∀ v : V, r ≤ (Finset.univ.filter (fun w => G.Adj v w)).card) →
      ∃ ℓ : ℕ, 2 ≤ ℓ ∧ ℓ ≤ ⌈(Fintype.card V : ℚ) / r⌉₊ ∧
        ∃ c : Fin ℓ → V, Function.Injective c ∧ ∀ i, G.Adj (c i) (c (finRotate ℓ i)) := by
  sorry

end OMA.S_opg_caccetta_haggkvist_conjecture
