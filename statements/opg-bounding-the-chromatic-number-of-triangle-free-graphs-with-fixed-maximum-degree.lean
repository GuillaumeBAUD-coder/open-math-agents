import Mathlib

/-!
# Bounding the chromatic number of triangle-free graphs with fixed maximum degree

Source: https://www.openproblemgarden.org/op/bounding_the_chromatic_number_of_triangle_free_graphs_with_fixed_maximum_degree
Credit: @joshuadc11

Kostochka–Reed conjecture (the triangle-free case of Reed's `ω, Δ, χ` conjecture): every finite
triangle-free simple graph with maximum degree `Δ` has chromatic number at most `⌈Δ / 2⌉ + 2`.

## Encoding

* Graphs are finite Mathlib `SimpleGraph`s; triangle-free is `G.CliqueFree 3` and maximum degree is
  `G.maxDegree`.
* For `Δ : ℕ`, `⌈Δ / 2⌉ + 2` equals `(Δ + 1) / 2 + 2` in `ℕ`.
* Chromatic number at most `k` is Mathlib's `G.Colorable k` (i.e., `Nonempty (G.Coloring (Fin k))`).
-/

namespace OMA.S_opg_bounding_the_chromatic_number_of_triangle_free_graphs_with_fixed_maximum_degree

/-- Every finite triangle-free simple graph with maximum degree `Δ` is `(⌈Δ / 2⌉ + 2)`-colorable. -/
theorem main : ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.CliqueFree 3 → G.Colorable ((G.maxDegree + 1) / 2 + 2) := by
  sorry

end OMA.S_opg_bounding_the_chromatic_number_of_triangle_free_graphs_with_fixed_maximum_degree
