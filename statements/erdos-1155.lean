import Mathlib

/-!
# Erdős Problem 1155

Source: https://www.erdosproblems.com/1155
Credit: @keiichisince1986-bot

Construct a random graph on `n` vertices in the following way: begin with the complete graph
`K_n`. At each stage, choose uniformly a random triangle in the graph and delete all the edges of
this triangle. Repeat until the graph is triangle-free.

Describe the typical parameters and structure of such a graph. In particular, if `f(n)` is the
number of edges remaining, then is it true that `𝔼 f(n) ≍ n^{3/2}` and that `f(n) ≪ n^{3/2}`
almost surely?

A problem of Bollobás and Erdős. Grable proved `ℙ(f(n) > n^{7/4+ε}) → 0`, and Bohman, Frieze and
Lubetzky [BFL15] proved `f(n) = n^{3/2+o(1)}` almost surely. Both questions below are still open.

Conventions:
- The first sentence (describe the typical parameters and structure) is open-ended. `main`
  states the two specific questions, as their conjunction.
- The process is the law `final n` of the last graph. `step G` picks a triangle of `G` (a
  3-clique, as an unordered vertex set) uniformly among the triangles of `G` and deletes its
  three edges; a triangle-free `G` stays put. `run n k` is the law after `k` steps from `K_n`
  (`⊤`). A step that changes the graph removes three edges, so the process stops after at most
  `n(n-1)/6 ≤ n^2` steps, and `final n = run n (n ^ 2)` is the law of the triangle-free graph
  where the process stops.
- `f(n)` is the number of edges of that graph. `𝔼 f(n)` is `expectedEdges n`, and
  `probEdgesLE n x` is `ℙ(f(n) ≤ x)`.
- `𝔼 f(n) ≍ n^{3/2}` is `expectedEdges =Θ[atTop] (n ↦ n^{3/2})`: both ratios bounded for large `n`.
- `f(n) ≪ n^{3/2}` almost surely is read, as is usual for random graphs (and as in [BFL15]),
  as with probability tending to `1`: there is `C > 0` with `ℙ(f(n) ≤ C n^{3/2}) → 1`.
-/

namespace OMA.S_erdos_1155

open Filter Asymptotics
open scoped Classical

/-- One step of the process: delete the edges of a uniformly random triangle of `G`, or stay at
`G` if it is triangle-free. -/
noncomputable def step {n : ℕ} (G : SimpleGraph (Fin n)) : PMF (SimpleGraph (Fin n)) :=
  if h : (G.cliqueFinset 3).Nonempty then
    (PMF.uniformOfFinset (G.cliqueFinset 3) h).map
      (fun t => G.deleteEdges (t.sym2 : Set (Sym2 (Fin n))))
  else PMF.pure G

/-- The law of the graph after `k` steps, starting from the complete graph `K_n`. -/
noncomputable def run (n : ℕ) : ℕ → PMF (SimpleGraph (Fin n))
  | 0 => PMF.pure ⊤
  | k + 1 => (run n k).bind step

/-- The law of the final triangle-free graph (the process has stopped after `n ^ 2` steps). -/
noncomputable def final (n : ℕ) : PMF (SimpleGraph (Fin n)) := run n (n ^ 2)

/-- `𝔼 f(n)`: the expected number of edges of the final graph. -/
noncomputable def expectedEdges (n : ℕ) : ℝ :=
  ∑ G : SimpleGraph (Fin n), (final n G).toReal * (G.edgeFinset.card : ℝ)

/-- `ℙ(f(n) ≤ x)`: the probability that the final graph has at most `x` edges. -/
noncomputable def probEdgesLE (n : ℕ) (x : ℝ) : ℝ :=
  ∑ G ∈ Finset.univ.filter (fun G : SimpleGraph (Fin n) => (G.edgeFinset.card : ℝ) ≤ x),
    (final n G).toReal

theorem main :
    (expectedEdges =Θ[atTop] fun n : ℕ => (n : ℝ) ^ ((3 : ℝ) / 2)) ∧
    ∃ C : ℝ, 0 < C ∧
      Tendsto (fun n : ℕ => probEdgesLE n (C * (n : ℝ) ^ ((3 : ℝ) / 2))) atTop (nhds 1) := by
  sorry

end OMA.S_erdos_1155
