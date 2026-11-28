import Mathlib

/-!
# Generalised majority edge-colourings: minimum degree $k^2$ suffices

Source: P. Pękała and J. Przybyło, *On generalised majority edge-colourings of graphs*,
https://arxiv.org/abs/2309.16624 (Electron. J. Combin. 31(4), 2024)
Credit: @SulkBash

## The problem (as the source states it)

A $\frac1k$-majority $l$-edge-colouring of a graph $G$ is a colouring of its edges with $l$
colours such that for every colour $i$ and each vertex $v$ of $G$, at most $\frac1k$'th of the
edges incident with $v$ have colour $i$.
- **Conjecture.** For every integer $k \ge 2$, each graph with minimum degree $\delta \ge k^2$
  is $\frac1k$-majority $(k+1)$-edge-colourable. This would be best possible.
- **Known cases.** The case $k = 2$ was known (Bock, Kalinowski, Pardey, Pilśniak, Rautenbach,
  Woźniak), and the paper proves the conjecture for $k \le 4$.
- **Partial results.** The paper also proves it with $2k^2$, and even $(\frac74 + o(1))k^2$, in
  place of $k^2$.
- **Near-tightness.** By the paper's Observation 4, a vertex of degree $k^2 - k - 1$ already
  rules out such a colouring.

## Formalization notes

* **Graphs.** Graphs are simple graphs on `Fin n`, with decidable adjacency.
* **Colourings.** An edge colouring with `k + 1` colours is a map `c : Sym2 (Fin n) → Fin (k+1)`.
  The edge `{v, w}` gets the colour `c s(v, w)`, the same from both endpoints. Values on
  non-edges are irrelevant, because only edges at `v` are counted.
* **Majority condition.** "At most $\frac1k$'th of the edges at $v$ have colour $i$" is
  `k * #{w ∈ N(v) | c s(v, w) = i} ≤ deg v`. This is the same as the count being at most
  `deg v / k`, written without division.
* **Minimum degree.** "Minimum degree $\ge k^2$" is stated pointwise as `∀ v, k ^ 2 ≤ G.degree v`.
-/

namespace OMA.S_arxiv_2309_16624

/-- `c` is a `1/k`-majority edge-colouring of `G`: at every vertex `v`, each colour `i` is used on
at most a `1/k` fraction of the edges at `v`. -/
def IsMajorityEdgeColouring {n l : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ)
    (c : Sym2 (Fin n) → Fin l) : Prop :=
  ∀ (v : Fin n) (i : Fin l), k * ((G.neighborFinset v).filter fun w => c s(v, w) = i).card ≤ G.degree v

/-- Pękała–Przybyło conjecture: for every `k ≥ 2`, every graph of minimum degree at least `k²` has
a `1/k`-majority `(k + 1)`-edge-colouring. -/
theorem main :
    ∀ (k n : ℕ), 2 ≤ k → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v, k ^ 2 ≤ G.degree v) →
        ∃ c : Sym2 (Fin n) → Fin (k + 1), IsMajorityEdgeColouring G k c := by
  sorry

end OMA.S_arxiv_2309_16624
