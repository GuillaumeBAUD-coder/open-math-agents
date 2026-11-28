import Mathlib

/-!
# Star chromatic index of cubic graphs

Source: https://www.openproblemgarden.org/op/star_chromatic_index_of_cubic_graphs
(Z. Dvořák, B. Mohar, R. Šámal)
Credit: @ishaanzee

The star chromatic index `χ'_s(G)` of a graph `G` is the minimum number of colors needed to
properly color the edges of the graph so that no path or cycle of length four is bi-colored.

**Question.** Is it true that for every (sub)cubic graph `G`, we have `χ'_s(G) ≤ 6`?

(Dvořák, Mohar and Šámal showed `χ'_s(G) ≤ 7` for subcubic graphs.) We state the affirmative
answer.

Formalization:
* Graphs are finite simple graphs; subcubic means maximum degree at most `3` (`maxDegree`).
* An edge coloring with `6` colors is `col : Sym2 V → Fin 6` (only its values on edges matter).
* Proper: two edges `uv`, `vw` sharing the vertex `v` (with `u ≠ w`) get different colors.
* A path with four edges `v₀ v₁ v₂ v₃ v₄` (distinct vertices, consecutive ones adjacent) or a
  4-cycle `v₀ v₁ v₂ v₃ v₀` (distinct vertices, cyclically adjacent) is bi-colored in a proper
  coloring exactly when its colors alternate: the first and third edges agree and so do the
  second and fourth.
-/

namespace OMA.S_opg_star_chromatic_index_of_cubic_graphs

/-- `col` is a star edge coloring of `G`: proper, and no path or cycle with four edges of `G` is
two-colored. -/
def IsStarEdgeColoring {V : Type*} (G : SimpleGraph V) {m : ℕ} (col : Sym2 V → Fin m) : Prop :=
  (∀ v : Fin 3 → V, Function.Injective v → G.Adj (v 0) (v 1) → G.Adj (v 1) (v 2) →
    col s(v 0, v 1) ≠ col s(v 1, v 2)) ∧
  (∀ v : Fin 5 → V, Function.Injective v → (∀ i : Fin 4, G.Adj (v i.castSucc) (v i.succ)) →
    ¬ (col s(v 0, v 1) = col s(v 2, v 3) ∧ col s(v 1, v 2) = col s(v 3, v 4))) ∧
  (∀ v : Fin 4 → V, Function.Injective v → G.Adj (v 0) (v 1) → G.Adj (v 1) (v 2) →
    G.Adj (v 2) (v 3) → G.Adj (v 3) (v 0) →
    ¬ (col s(v 0, v 1) = col s(v 2, v 3) ∧ col s(v 1, v 2) = col s(v 3, v 0)))

/-- **Dvořák–Mohar–Šámal question**, affirmative form: every subcubic graph has a star edge
coloring with `6` colors. -/
theorem main : ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.maxDegree ≤ 3 → ∃ col : Sym2 V → Fin 6, IsStarEdgeColoring G col := by
  sorry

end OMA.S_opg_star_chromatic_index_of_cubic_graphs
