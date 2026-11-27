import Mathlib

/-!
# Directed path of length twice the minimum outdegree

Source: https://www.openproblemgarden.org/op/directed_cycle_of_length_twice_the_minimum_outdegree
Credit: @biondadave

Conjecture (Thomassé): Every oriented graph with minimum outdegree `k` contains a directed path
of length `2k`.

This file states that conjecture. The stronger version on the same page (digraphs with minimum
outdegree `k` and directed girth `g` contain a directed path of length `(g - 1) k`) is not
stated here.

Conventions:
- An oriented graph is a finite directed graph with no loops and no pair of opposite arcs. It is
  a Mathlib `Digraph V` with `V` finite and those two hypotheses.
- The graph is nonempty, so that a path of length `0` (a single vertex) exists when `k = 0`.
- Minimum outdegree `k`: every vertex has at least `k` out-neighbours. A larger minimum only
  strengthens the hypothesis, so "at least `k`" is equivalent to "equal to `k`" here.
- A directed path of length `ℓ` has `ℓ` arcs: an injective map `P : Fin (ℓ + 1) → V` with an arc
  from `P i` to `P (i + 1)` for each `i < ℓ`.
-/

namespace OMA.S_opg_directed_cycle_of_length_twice_the_minimum_outdegree

theorem main :
    ∀ (V : Type) [Fintype V] [Nonempty V] (G : Digraph V) [DecidableRel G.Adj] (k : ℕ),
      (∀ v, ¬ G.Adj v v) → (∀ u v, G.Adj u v → ¬ G.Adj v u) →
      (∀ v : V, k ≤ (Finset.univ.filter (fun w => G.Adj v w)).card) →
      ∃ P : Fin (2 * k + 1) → V, Function.Injective P ∧
        ∀ i : Fin (2 * k), G.Adj (P i.castSucc) (P i.succ) := by
  sorry

end OMA.S_opg_directed_cycle_of_length_twice_the_minimum_outdegree
