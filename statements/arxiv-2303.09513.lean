import Mathlib

/-!
# The Benda–Perles problem: no rational distance graph `G(ℚ³, d)` is 3-chromatic

Source: *A Triangle-free, 4-chromatic $\mathbb{Q}^3$ Euclidean Distance Graph Scavenger Hunt!*,
https://arxiv.org/abs/2303.09513
Credit: @SulkBash

## The problem (as the source states it)

For $d > 0$, define $G(\mathbb{Q}^3, d)$ to be the graph whose set of vertices is the rational
space $\mathbb{Q}^3$, where two vertices are adjacent if and only if they are a Euclidean distance
$d$ apart. Let $\chi(\mathbb{Q}^3, d)$ be its chromatic number.
- An open problem, originally posed by Benda and Perles in the 1970s, asks if there exists $d$
  such that $\chi(\mathbb{Q}^3, d) = 3$.
- For all distances $d$ where $\chi(\mathbb{Q}^3, d)$ has not been exactly pinned down, it is
  known that $\chi(\mathbb{Q}^3, d) \in \{3, 4\}$.
- The source conjectures that no 3-chromatic $G(\mathbb{Q}^3, d)$ exists.

## Formalization notes

* **The graph.** The vertex set is `Fin 3 → ℚ`. Distinct points `x, y` are adjacent iff
  `∑ i, (x i - y i)² = d²`, computed in `ℝ`. Since `d > 0`, this says exactly that their
  Euclidean distance is `d`. `SimpleGraph.fromRel` makes the relation symmetric and irreflexive.
* **Chromatic number.** This is Mathlib's `SimpleGraph.chromaticNumber`, valued in `ℕ∞`, which
  is `⊤` for a graph with no finite colouring. The conjecture is that it is never `3`, for any
  real `d > 0`.
* **Degenerate distances.** If `d²` is not a sum of three rational squares, the graph has no
  edges and its chromatic number is `1`. Such `d` satisfy the conjecture trivially, which matches
  the source's quantification over all `d > 0`.
-/

namespace OMA.S_arxiv_2303_09513

/-- The rational distance graph `G(ℚ³, d)`: points of `ℚ³` at Euclidean distance `d` are
adjacent. -/
def distGraph (d : ℝ) : SimpleGraph (Fin 3 → ℚ) :=
  SimpleGraph.fromRel fun x y => ∑ i, ((x i : ℝ) - (y i : ℝ)) ^ 2 = d ^ 2

/-- No `G(ℚ³, d)` is 3-chromatic. -/
theorem main : ∀ d : ℝ, 0 < d → (distGraph d).chromaticNumber ≠ 3 := by
  sorry

end OMA.S_arxiv_2303_09513
