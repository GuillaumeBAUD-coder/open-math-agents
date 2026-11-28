import Mathlib

/-!
# Minimum degree, edge count and clique number versus the chromatic number

Source: https://mathoverflow.net/questions/289425
Credit: @koolkao

Question (shen lixing, MathOverflow 289425, 2017; CC BY-SA 3.0). For a graph `G = (v, e)`
with `v` vertices and `e` edges, the source conjectures: if `δ(G) > n`,
`e ≤ (n - 1) v - n (n - 1) / 2` and `K_n` is not a subgraph of `G`, then `G` is `n`-colorable.
(The case `n = 4` would give the four color theorem for planar graphs of minimum degree at least
`5`.) The source also lists two weakenings of this conjecture.

`main` states the conjecture as displayed first in the source. A disproof is a graph satisfying
the three hypotheses for some `n` that is not `n`-colorable.

Translation choices:
* graphs are `SimpleGraph V` on a finite type `V`, `v = Fintype.card V` and
  `e = G.edgeFinset.card`;
* `δ(G) > n` is `n < G.degree x` for every vertex `x`;
* the edge bound is stated without division or subtraction as
  `2 e + n (n - 1) ≤ 2 (n - 1) v` (for `n ≥ 1` this is equivalent to the source's inequality over
  `ℤ`, since `n (n - 1)` is even);
* "`K_n` is not a subgraph of `G`" is `G.CliqueFree n`, and "`n` colorable" is `G.Colorable n`;
* the two weakenings listed in the source are not stated.
-/

namespace OMA.S_mo_289425

/-- If `δ(G) > n`, `e ≤ (n - 1) v - n (n - 1) / 2` and `G` has no `K_n`, then `G` is
`n`-colorable. -/
theorem main :
    ∀ (n : ℕ) (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
        [DecidableRel G.Adj],
      (∀ x, n < G.degree x) →
      2 * G.edgeFinset.card + n * (n - 1) ≤ 2 * (n - 1) * Fintype.card V →
      G.CliqueFree n →
      G.Colorable n := by
  sorry

end OMA.S_mo_289425
