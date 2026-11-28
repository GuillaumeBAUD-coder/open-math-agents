import Mathlib

/-!
# Does every triangle-free graph with maximum degree at most 6 have a 5-colouring?

Source: https://mathoverflow.net/questions/37923 (2010).
Credit: @jagraj28

The post asks the case `Δ ≤ 6` of Reed's `ω, Δ, χ` conjecture for triangle-free graphs
(`χ ≤ Δ / 2 + 2`): does every triangle-free graph with maximum degree at most `6` have chromatic
number at most `5`? (By parity this case implies the case `Δ = 5`.) Kostochka's bound
`χ ≤ 2Δ / 3 + 2` gives only `χ ≤ 6`. The post has no answer.

Formalization notes:
* Graphs are finite simple graphs: a `SimpleGraph` on a `Fintype` vertex type.
* "Triangle-free" is `G.CliqueFree 3`; "maximum degree at most 6" is `G.degree v ≤ 6` for every
  vertex `v`; "has a 5-colouring" is `G.Colorable 5`.
* The post ends with a weaker follow-up (the same question for graphs of girth at least five);
  it is implied by `main` and is not stated separately.
-/

namespace OMA.S_mo_37923

/-- Every finite triangle-free graph with maximum degree at most `6` is `5`-colourable. -/
theorem main :
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.CliqueFree 3 → (∀ v, G.degree v ≤ 6) → G.Colorable 5 := by
  sorry

end OMA.S_mo_37923
