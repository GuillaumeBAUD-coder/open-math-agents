import Mathlib

/-!
# How many perfect-matching counts occur?

Source: https://mathoverflow.net/questions/239152 (CC BY-SA 4.0).

Let `f(G)` be the number of perfect matchings of a balanced bipartite graph `G` on `2n` vertices, so
`f(G) ∈ {0, 1, …, n!}`. The asker asks how many of these values are attained, and conjectures (update)
that the number of attained values is `n^(Ω(n))`.

We state the conjecture: for some `c > 0` and all large `n`, at least `n^(c n)` values are attained.

Formalization notes:
* A balanced bipartite graph on `2n` vertices is its `n × n` 0/1 biadjacency matrix, and its number of
  perfect matchings is the permanent of that matrix; we count the distinct permanents over all
  `M : Fin n → Fin n → Bool`.
* The trivial upper bound `n! + 1` is `n^(O(n))`, so the conjecture says the count is `n^(Θ(n))`.
-/

namespace OMA.S_mo_239152

/-- The number of distinct permanents of `n × n` 0/1 matrices is at least `n^(c n)` for large `n`. -/
theorem main : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
    (n : ℝ) ^ (c * n) ≤ ((Finset.univ : Finset (Fin n → Fin n → Bool)).image
      (fun M => (Matrix.of (fun i j => if M i j then (1 : ℕ) else 0)).permanent)).card := by
  sorry

end OMA.S_mo_239152
