import FormalConjectures.ErdosProblems.«1035»

/-!
# Reduction R1 of Erdős Problem 1035

Target (verbatim from the module): there is a constant `c > 0` such that for every `n`, every
graph `G` on `2 ^ n` vertices with minimum degree `> (1 - c) * 2 ^ n` contains the
`n`-dimensional hypercube `Q_n` (`SimpleGraph.hypercube n`). This is Erdős's question
[Er93, p. 345]; erdosproblems.com/1035 records no resolution, and the module marks it
`@[category research open]`.

This file splits the quantified domain — the pairs `(n, G)` — by the dimension `n`:

* `H1` is the region `n ≤ 1`. It is elementary and **true**, with an explicit constant
  `c = 3/4`, by a finite check: `2 ^ 0 = 1` and the single vertex of `Fin 1` has degree `0`,
  so for `n = 0` the hypothesis `0 > (1 - 3/4) * 1` is false; for `n = 1`, `2 ^ 1 = 2` and
  `(1 - 3/4) * 2 = 1/2`, so minimum degree `> 1/2` forces both degrees to be `1`, i.e. `G`
  is the complete graph on two vertices, which contains `Q_1 = K_2` as a copy. (`Q_0` is the
  one-vertex graph, contained in every graph.) So `H1` is not a renamed copy of the target:
  it is a genuine, separately provable small-dimension lemma.
* `H2` is the region `2 ≤ n`, which contains the whole asymptotic content of the problem
  (including every dimension in which the extremal number of `Q_n` is unknown), so it is
  strictly weaker than the target and remains open. Neither `H2` nor its negation is a
  published theorem in the module or on erdosproblems.com/1035.

`main` combines the two witnesses by `c := min c1 c2 > 0`: since `min c1 c2 ≤ c1` and
`min c1 c2 ≤ c2`, the hypothesis at `c = min c1 c2` is at least as strong as the hypothesis
at either `c1` or `c2`, so the appropriate region applies.
-/

namespace OMA.R_Erdos1035_erdos_1035_R1

/-- Region 1: dimensions `n ≤ 1`. True with `c = 3/4`: the case `n = 0` has no graph
satisfying the degree hypothesis, and the case `n = 1` forces `G = K_2 ⊇ Q_1`. -/
def H1 : Prop :=
  ∃ c > (0 : ℝ), ∀ n : ℕ, n ≤ 1 →
    ∀ (G : SimpleGraph (Fin (2 ^ n))) [DecidableRel G.Adj],
      (∀ v, (G.degree v : ℝ) > (1 - c) * 2 ^ n) →
        (SimpleGraph.hypercube n).IsContained G

/-- Region 2: dimensions `2 ≤ n` — the open core, containing every asymptotically relevant
dimension. Strictly weaker than the target because it restricts `n`; no known proof or
disproof. -/
def H2 : Prop :=
  ∃ c > (0 : ℝ), ∀ n : ℕ, 2 ≤ n →
    ∀ (G : SimpleGraph (Fin (2 ^ n))) [DecidableRel G.Adj],
      (∀ v, (G.degree v : ℝ) > (1 - c) * 2 ^ n) →
        (SimpleGraph.hypercube n).IsContained G

theorem main : H1 → H2 → type_of% @Erdos1035.erdos_1035 := by
  rintro ⟨c1, hc1, h1⟩ ⟨c2, hc2, h2⟩
  refine ⟨min c1 c2, lt_min hc1 hc2, ?_⟩
  intro n G _ hG
  have transfer : ∀ c : ℝ, min c1 c2 ≤ c → ∀ v, (G.degree v : ℝ) > (1 - c) * 2 ^ n := by
    intro c hc v
    have hle : (1 - c) * (2 : ℝ) ^ n ≤ (1 - min c1 c2) * (2 : ℝ) ^ n := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      linarith
    exact lt_of_le_of_lt hle (hG v)
  by_cases hn : n ≤ 1
  · exact h1 n hn G (transfer c1 (min_le_left c1 c2))
  · exact h2 n (by omega) G (transfer c2 (min_le_right c1 c2))

end OMA.R_Erdos1035_erdos_1035_R1
