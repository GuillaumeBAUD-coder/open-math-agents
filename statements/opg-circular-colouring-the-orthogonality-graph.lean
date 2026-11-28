import Mathlib

/-!
# Circular colouring the orthogonality graph

Source: https://www.openproblemgarden.org/op/circular_colouring_the_orthogonality_graph
Credit: @manoj1978

Problem (DeVos, Ghebleh, Goddyn, Mohar, Naserasr): let `𝒪` be the graph whose vertices are the
lines through the origin in `ℝ^3`, two lines being adjacent when they are perpendicular.
Is `χ_c(𝒪) = 4`? (Known: `χ(𝒪) = 4` and `3.5 ≤ χ_c(𝒪) ≤ 4`.)

Conventions:
- Lines through the origin in `ℝ^3` are the points of the projectivization
  `Projectivization ℝ (EuclideanSpace ℝ (Fin 3))`. Two lines are perpendicular when their direction vectors
  (any representatives) have inner product zero; this does not depend on the representatives.
- `𝒪` is infinite, so the circular chromatic number is taken with the standard real-valued
  definition (X. Zhu, Circular chromatic number: a survey, Discrete Math. 229 (2001)): for a real
  `r`, a circular `r`-colouring is a map `c : V → [0, r)` with `1 ≤ |c u - c v| ≤ r - 1` for
  every edge `uv`, and `χ_c(G)` is the infimum of all `r` admitting one. For finite graphs this
  agrees with the infimum of `k / d` over `(k, d)`-colourings.
- The source asks a yes/no question; `main` states the answer yes, and a disproof would answer no.
-/

namespace OMA.S_opg_circular_colouring_the_orthogonality_graph

open SimpleGraph

/-- The orthogonality graph: lines through the origin in `ℝ^3`, adjacent when perpendicular. -/
noncomputable def orthogonalityGraph : SimpleGraph (Projectivization ℝ (EuclideanSpace ℝ (Fin 3))) :=
  SimpleGraph.fromRel fun p q => inner ℝ p.rep q.rep = 0

/-- `c` is a circular `r`-colouring of `G`: values in `[0, r)`, and adjacent vertices get values
at circular distance at least `1` on the circle of circumference `r`. -/
def IsCircularColoring {V : Type*} (G : SimpleGraph V) (r : ℝ) (c : V → ℝ) : Prop :=
  (∀ v, 0 ≤ c v ∧ c v < r) ∧
    ∀ u v, G.Adj u v → 1 ≤ |c u - c v| ∧ |c u - c v| ≤ r - 1

/-- The circular chromatic number: the infimum of all `r` for which a circular `r`-colouring
exists. -/
noncomputable def circularChromaticNumber {V : Type*} (G : SimpleGraph V) : ℝ :=
  sInf {r : ℝ | ∃ c, IsCircularColoring G r c}

/-- The circular chromatic number of the orthogonality graph of `ℝ^3` is `4`. -/
theorem main : circularChromaticNumber orthogonalityGraph = 4 := by
  sorry

end OMA.S_opg_circular_colouring_the_orthogonality_graph
