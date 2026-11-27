import Mathlib

/-!
# Erdős Problem 132

Source: https://www.erdosproblems.com/132
Credit: @biondadave

Let `A ⊂ ℝ²` be a set of `n` points. Must there be two distances which occur at least once but
between at most `n` pairs of points? Must the number of such distances `→ ∞` as `n → ∞`?

We state the affirmative answer to the second question. It implies the first one for all large
`n`. The first question cannot be asked for every `n`: three points of an equilateral triangle
determine only one distance. Erdős believed it holds for `n ≥ 5`.

Conventions:
- `ℝ²` is `EuclideanSpace ℝ (Fin 2)`; `A` is a finite set of exactly `n` points.
- A distance `d` occurs in `A` if `d = dist a b` for distinct `a, b ∈ A`.
- The number of pairs at distance `d` counts unordered pairs `{a, b}`. Ordered pairs in
  `A.offDiag` are counted instead, so "at most `n` unordered pairs" becomes "at most `2n`
  ordered pairs".
- "The number of such distances tends to infinity": for every `K` there is `N` such that every
  `A` with `|A| = n ≥ N` has at least `K` distances that occur, each between at most `n` pairs.
-/

namespace OMA.S_erdos_132

/-- Number of ordered pairs of distinct points of `A` at distance `d`. -/
noncomputable def orderedPairsAt (A : Finset (EuclideanSpace ℝ (Fin 2))) (d : ℝ) : ℕ :=
  (A.offDiag.filter (fun p => dist p.1 p.2 = d)).card

/-- The distances occurring in `A` between at most `n` unordered pairs of points. -/
noncomputable def rareDistances (A : Finset (EuclideanSpace ℝ (Fin 2))) (n : ℕ) : Finset ℝ :=
  (A.offDiag.image (fun p => dist p.1 p.2)).filter (fun d => orderedPairsAt A d ≤ 2 * n)

theorem main :
    ∀ K : ℕ, ∃ N : ℕ, ∀ A : Finset (EuclideanSpace ℝ (Fin 2)), N ≤ A.card →
      K ≤ (rareDistances A A.card).card := by
  sorry

end OMA.S_erdos_132
