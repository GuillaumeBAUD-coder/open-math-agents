import OMAStatements.S_wp_degree_diameter_problem
import Mathlib

/-!
# The degree-diameter maximum is attained

`OMA.S_wp_degree_diameter_problem.main` asks, for positive integers `d`, `k`, for a finite
simple graph of maximum degree at most `d` and diameter at most `k` with the maximum possible
number `n_{d,k}` of vertices (`n` in the statement is `sSup` of the set of all such vertex
counts).

The `sSup` of a set of natural numbers is the maximum of the set whenever the set is bounded
above, and is the junk value `0` when it is not (`Nat.sSup_of_not_bddAbove`).  In the second
case `0` is itself a vertex count: the graph on the empty vertex type has `0` vertices, no
vertex (so the degree condition holds vacuously) and extended diameter `0 ≤ k`.  Hence the
maximum is attained in either case; in particular no bound on `n_{d,k}` (such as the Moore
bound) has to be proved.

The positivity assumptions `0 < d`, `0 < k` are not needed.
-/

open OMA.S_wp_degree_diameter_problem

namespace OMA.WpDegreeDiameterWitness

/-- The empty graph has `0` vertices, satisfies any maximum-degree bound and has extended
diameter `0`.  So `0` is always a possible vertex count. -/
lemma zero_mem_vertexCounts (d k : ℕ) : (0 : ℕ) ∈ vertexCounts d k := by
  refine ⟨PEmpty, inferInstance, ⊥, rfl, ?_, ?_⟩
  · intro v
    exact isEmptyElim v
  · simp [SimpleGraph.ediam]

end OMA.WpDegreeDiameterWitness

open OMA.WpDegreeDiameterWitness in
theorem OMA.solution : type_of% @OMA.S_wp_degree_diameter_problem.main := by
  intro d k _ _
  show ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
    Fintype.card V = sSup (vertexCounts d k) ∧
      (∀ v, Set.ncard (G.neighborSet v) ≤ d) ∧ G.ediam ≤ (k : ℕ∞)
  by_cases hb : BddAbove (vertexCounts d k)
  · exact Nat.sSup_mem ⟨0, zero_mem_vertexCounts d k⟩ hb
  · rw [Nat.sSup_of_not_bddAbove hb]
    exact ⟨PEmpty, inferInstance, ⊥, rfl, fun v => isEmptyElim v, by simp [SimpleGraph.ediam]⟩
