import Mathlib

/-!
# Odd cycle transversal in triangle-free graphs

Source: https://www.openproblemgarden.org/op/odd_cycle_transversal_in_triangle_free_graphs
Credit: @Moti1125

Conjecture (Erdős): if `G` is a simple triangle-free graph, then there is a set of at most
`n² / 25` edges whose deletion destroys every odd cycle.

Conventions:
- `n` is the number of vertices of `G`; the vertex set is `Fin n`.
- Triangle-free is `G.CliqueFree 3`.
- The bound "at most `n² / 25` edges" is the real inequality `|F| ≤ n² / 25`, written over `ℕ` as
  `25 * |F| ≤ n ^ 2`, which is equivalent.
- "Destroys every odd cycle" is stated literally: every cycle of `G.deleteEdges F` has even
  length.
- `F` is required to consist of edges of `G`. This is no restriction: deleting a non-edge does
  nothing.
- Formal Conjectures' `Erdos23.erdos_23` is the special case with `5n` vertices and bound `n²`.
-/

namespace OMA.S_opg_odd_cycle_transversal_in_triangle_free_graphs

theorem main :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.CliqueFree 3 →
      ∃ F : Finset (Sym2 (Fin n)), (F : Set (Sym2 (Fin n))) ⊆ G.edgeSet ∧
        25 * F.card ≤ n ^ 2 ∧
        ∀ (u : Fin n) (p : (G.deleteEdges (F : Set (Sym2 (Fin n)))).Walk u u),
          p.IsCycle → Even p.length := by
  sorry

end OMA.S_opg_odd_cycle_transversal_in_triangle_free_graphs
