import Mathlib

/-!
# Strong colorability

Source: https://www.openproblemgarden.org/op/strong_colorability
Credit: @ishaanzee

Let `r` be a positive integer. We say that a graph `G` is strongly `r`-colorable if for every
partition of the vertices to sets of size at most `r` there is a proper `r`-coloring of `G` in
which the vertices in each set of the partition have distinct colors.

**Conjecture** (Aharoni, Alon, Haxell). If `Δ` is the maximal degree of a graph `G`, then `G` is
strongly `2Δ`-colorable.

(Haxell proved that `G` is strongly `(3Δ - 1)`-colorable.)

Formalization: graphs are finite simple graphs and `Δ` is Mathlib's `maxDegree`. A partition of
the vertices is given by a labelling `p : V → V` (the blocks are the fibres of `p`); every block
has at most `2Δ` vertices. An `r`-coloring is `c : V → Fin r`; it is proper when adjacent
vertices get different colors, and the vertices of each block get distinct colors when `c` is
injective on each fibre of `p`.
-/

namespace OMA.S_opg_strong_colorability

/-- `G` is strongly `r`-colorable: for every partition of the vertex set into blocks of size at
most `r`, some proper `r`-coloring gives the vertices of each block distinct colors. -/
def IsStronglyColorable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (r : ℕ) :
    Prop :=
  ∀ p : V → V, (∀ b : V, (Finset.univ.filter fun v => p v = b).card ≤ r) →
    ∃ c : V → Fin r, (∀ u v, G.Adj u v → c u ≠ c v) ∧ ∀ u v, u ≠ v → p u = p v → c u ≠ c v

/-- **Aharoni–Alon–Haxell conjecture**: every finite graph of maximum degree `Δ` is strongly
`2Δ`-colorable. -/
theorem main : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    IsStronglyColorable G (2 * G.maxDegree) := by
  sorry

end OMA.S_opg_strong_colorability
