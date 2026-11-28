import FormalConjectures.Wikipedia.LinearArboricityConjecture
import Mathlib

/-!
# Reduction: the linear arboricity conjecture for regular graphs, split into its two halves

The target `LinearArboricityConjecture.linear_arboricity_conjecture.variants.regular` is an
*equality*

  `linearArboricity G = (Δ + 2) / 2`  for a nonempty `Δ`-regular graph `G` with `Δ > 0`.

This file splits it into the two inequalities it is equivalent to:

* `H1`, the upper half `linearArboricity G ≤ (Δ + 2) / 2`: **this is the conjecture**
  (Akiyama–Exoo–Harary) restricted to regular graphs;
* `H2`, the lower half `(Δ + 2) / 2 ≤ linearArboricity G`: the counting argument the module
  docstring calls "easily seen" — `Δ / 2 < la(G)` because a nonempty linear forest on `|V|`
  vertices has at most `|V| - 1` edges, so a decomposition into `k` linear forests gives
  `|V| Δ / 2 ≤ k (|V| - 1)`, hence `k > Δ / 2`.

`main` is then `le_antisymm`: nothing else is needed. Proving `H2` closes the lower half for
every regular graph; proving `H1` closes the problem.
-/

namespace OMA.R_LinearArboricityConjecture_linear_arboricity_conjecture_variants_regular_R1

open LinearArboricityConjecture

/-- The upper half: a nonempty `Δ`-regular graph with `Δ > 0` has linear arboricity at most
`⌈(Δ + 1) / 2⌉ = (Δ + 2) / 2`. This is the linear arboricity conjecture for regular graphs. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ),
    0 < Δ → (∀ v, G.degree v = Δ) → linearArboricity G ≤ (Δ + 2) / 2

/-- The lower half: a nonempty `Δ`-regular graph with `Δ > 0` has linear arboricity at least
`(Δ + 2) / 2`. This is the edge-counting bound, and does not use the linear arboricity
conjecture. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ),
    0 < Δ → (∀ v, G.degree v = Δ) → (Δ + 2) / 2 ≤ linearArboricity G

theorem main : H1 → H2 →
    type_of% @LinearArboricityConjecture.linear_arboricity_conjecture.variants.regular := by
  intro h1 h2 V _ _ G _ Δ hΔ hreg
  exact le_antisymm (h1 (G := G) (Δ := Δ) hΔ hreg) (h2 (G := G) (Δ := Δ) hΔ hreg)

end OMA.R_LinearArboricityConjecture_linear_arboricity_conjecture_variants_regular_R1
