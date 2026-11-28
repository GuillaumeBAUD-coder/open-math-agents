import Mathlib

/-!
# Erdős Problem 1103

Source: https://www.erdosproblems.com/1103
Credit: @avaava791

The source asks: let `A` be an infinite sequence of integers such that every `n ∈ A + A` is
squarefree. How fast must `A` grow? Erdős notes that there are examples of exponential growth,
and believed that there is no example of polynomial growth.

Reading used here: the question how fast `A` must grow has no fixed answer, so (as the source
suggests) the statement is the conjecture of Erdős that `A` cannot grow polynomially. A sequence
grows polynomially when `a_j = O(j^K)` for some `K`; the statement says that this fails for
every `K` (taking `K` a natural number loses nothing, since `j^K ≤ j^⌈K⌉` for `j ≥ 1`).
* `A` is read as a strictly increasing sequence `a_0 < a_1 < ⋯` of natural numbers, i.e. an
  infinite set of positive integers listed in increasing order: speaking of how fast a sequence
  of integers grows presupposes that it increases to infinity. `0` cannot occur, because
  `0 + 0 = 0` is not squarefree, so the terms are positive. Starting the index at `0` rather
  than `1` does not affect `O(j^K)`.
* `A + A = {a + b : a, b ∈ A}` includes `a + a`, as usual, so `2a` is squarefree for every term
  `a` (in particular every term is odd and squarefree).
* The growth condition uses `=O[atTop]`, so it only concerns large `j`; a bound of the form
  `a_j ≤ C j^K` for all `j ≥ 1` is equivalent.

Known (from the source, not part of the statement): van Doorn and Tao (2025) proved the lower
bound `a_j > 0.24 j^{4/3}`.

Written with Claude Code (AI-assisted).
-/

namespace OMA.S_erdos_1103

open Filter Asymptotics

/-- No strictly increasing sequence of natural numbers all of whose pairwise sums (including
`a + a`) are squarefree has polynomial growth. -/
theorem main :
    ∀ A : ℕ → ℕ, StrictMono A → (∀ i j, Squarefree (A i + A j)) →
      ∀ K : ℕ, ¬ (fun j : ℕ ↦ (A j : ℝ)) =O[atTop] (fun j : ℕ ↦ (j : ℝ) ^ K) := by
  sorry

end OMA.S_erdos_1103
