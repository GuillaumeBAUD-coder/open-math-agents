import Mathlib

/-!
# Erdős Problem 612

Source: https://www.erdosproblems.com/612
Credit: @keiichisince1986-bot

Let `G` be a connected graph with `n` vertices, minimum degree `d`, and diameter `D`. Show that if
`G` contains no `K_{2r}` and `(r-1)(3r+2) ∣ d` then
  `D ≤ 2(r-1)(3r+2)/(2r^2-1) · n/d + O(1)`,
and if `G` contains no `K_{2r+1}` and `3r-1 ∣ d` then
  `D ≤ (3r-1)/r · n/d + O(1)`.

A problem of Erdős, Pach, Pollack and Tuza [EPPT89]. `main` is the conjunction of the two parts,
exactly as the source poses them.

Conventions:
- `r` ranges over the positive integers. Both coefficients are defined there
  (`2r^2-1 > 0` and `r > 0`). For `r = 1` the first part is trivial (a connected `K_2`-free graph
  is a single vertex) and the second part is the triangle-free case.
- The `O(1)` term is a constant that may depend on `r` only: for each `r` there is `C` such that
  the bound holds for every `n` and every connected graph on `n` vertices satisfying the
  hypotheses, uniformly in `n` and `d`. This is the usual reading when the main term `n/d` lets
  both `n` and `d` vary, as in the known bound `D ≤ 3n/(d+1) + O(1)` quoted on the source page.
- The vertex set is `Fin n`, `d` is `G.minDegree`, `D` is `G.diam`, and `G` contains no `K_m` is
  `G.CliqueFree m`. The quotient `n/d` is taken in `ℝ`. When `d = 0` the connected graph is a
  single vertex, `D = 0`, and Lean's `n/0 = 0` makes the bound hold trivially.

Status (from the source page, for the reviewer): Czabarka, Singgih and Székely [CSS21] gave
`K_{2r}`-free counterexamples to the first part for every `r ≥ 2`, and Cambie and Jooken [CaJo25]
gave another (`K_4`-free, `d = 16`). So the first conjunct, and hence `main`, is expected to be
false. The second part is proved for `r = 1` [EPPT89] and open for `r ≥ 2`. The source page still
lists the problem as open.
-/

namespace OMA.S_erdos_612

theorem main :
    (∀ r : ℕ, 1 ≤ r → ∃ C : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G.Connected → G.CliqueFree (2 * r) → (r - 1) * (3 * r + 2) ∣ G.minDegree →
        (G.diam : ℝ) ≤ 2 * ((r : ℝ) - 1) * (3 * (r : ℝ) + 2) / (2 * (r : ℝ) ^ 2 - 1) *
          ((n : ℝ) / (G.minDegree : ℝ)) + C) ∧
    (∀ r : ℕ, 1 ≤ r → ∃ C : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G.Connected → G.CliqueFree (2 * r + 1) → 3 * r - 1 ∣ G.minDegree →
        (G.diam : ℝ) ≤ (3 * (r : ℝ) - 1) / (r : ℝ) * ((n : ℝ) / (G.minDegree : ℝ)) + C) := by
  sorry

end OMA.S_erdos_612
