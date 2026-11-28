import OMAStatements.S_opg_long_directed_cycles_in_digraph_with_minimum_in_and_out_degree

/-!
# Reduction of Jackson's conjecture on long directed cycles

Statement (`OMA.S_opg_long_directed_cycles_in_digraph_with_minimum_in_and_out_degree.main`):
every strong oriented graph whose indegree and outdegree are at least `d` contains a directed
cycle of length at least `2 * d + 1`.

Let `n` be the number of vertices.  In this file we prove the counting part that the whole
problem rests on: for an oriented graph, `indegree v + outdegree v <= n - 1` for every vertex
(the in- and out-neighbourhoods are disjoint, and neither contains `v`).  Hence
`n >= 2 * d + 1`.  This gives a sharp three-way split of the problem by the value of `n`:

* `H1` -- the tight case `n = 2 * d + 1`.  Here every vertex has total degree `n - 1`, so `G` is
  a tournament, and the claim becomes Camion's theorem (1959): a strongly connected tournament
  has a Hamiltonian directed cycle.  We also prove in this file that the degree condition forces
  the tournament property, so nothing but Camion's theorem is missing in this case.
* `H2` -- the case `n = 2 * d + 2`, where every vertex has total degree `2 * d` or `2 * d + 1`
  of the possible `2 * d + 1`, i.e. `G` is a tournament with a matching of pairs removed.
* `H3` -- the case `n >= 2 * d + 3`.

Each of `H1`, `H2`, `H3` is a strict special case of the target, so this splits the open problem
into three genuinely smaller claims, and `main` proves that they cover it.
-/

namespace OMA.R_opg_long_directed_cycles_in_digraph_with_minimum_in_and_out_degree_R1

open OMA.S_opg_long_directed_cycles_in_digraph_with_minimum_in_and_out_degree

/-- Camion's theorem: a strongly connected tournament on at least three vertices has a
Hamiltonian directed cycle. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [Nonempty V] (G : Digraph V) [DecidableRel G.Adj],
    3 ≤ Fintype.card V → IsOriented G → IsStrong G →
    (∀ u v, u ≠ v → G.Adj u v ∨ G.Adj v u) →
    HasDirectedCycleOfLength G (Fintype.card V)

/-- Jackson's conjecture in the first non-trivial case, `n = 2 * d + 2`: a strong oriented graph
on `2 * d + 2` vertices with all indegrees and outdegrees at least `d` has a directed cycle of
length at least `2 * d + 1`.  Here every vertex has total degree `2 * d` or `2 * d + 1` out of
the possible `2 * d + 1`. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [Nonempty V] (G : Digraph V) [DecidableRel G.Adj] (d : ℕ),
    1 ≤ d → IsOriented G → IsStrong G →
    (∀ v, d ≤ indegree G v ∧ d ≤ outdegree G v) →
    Fintype.card V = 2 * d + 2 →
    ∃ k, 2 * d + 1 ≤ k ∧ HasDirectedCycleOfLength G k

/-- Jackson's conjecture for `n >= 2 * d + 3` vertices. -/
def H3 : Prop :=
  ∀ (V : Type) [Fintype V] [Nonempty V] (G : Digraph V) [DecidableRel G.Adj] (d : ℕ),
    1 ≤ d → IsOriented G → IsStrong G →
    (∀ v, d ≤ indegree G v ∧ d ≤ outdegree G v) →
    2 * d + 3 ≤ Fintype.card V →
    ∃ k, 2 * d + 1 ≤ k ∧ HasDirectedCycleOfLength G k

/-! ### Counting in an oriented graph -/

/-- The in-neighbourhood and the out-neighbourhood of a vertex are disjoint in an oriented
graph: opposite arcs are forbidden. -/
lemma in_out_disjoint {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (hor : IsOriented G) (v : V) :
    Disjoint (Finset.univ.filter (fun w => G.Adj w v))
      (Finset.univ.filter (fun w => G.Adj v w)) := by
  rw [Finset.disjoint_filter]
  intro w _ hwv hvw
  exact hor v w hvw hwv

/-- The in-neighbourhood together with the out-neighbourhood of a vertex avoids the vertex
itself: an oriented graph has no loops. -/
lemma in_out_union_subset_erase {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V)
    [DecidableRel G.Adj] (hor : IsOriented G) (v : V) :
    (Finset.univ.filter (fun w => G.Adj w v)) ∪ (Finset.univ.filter (fun w => G.Adj v w))
      ⊆ Finset.univ.erase v := by
  intro w hw
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hw
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  rintro rfl
  obtain h | h := hw <;> exact hor _ _ h h

/-- The cardinality of the union of the in- and out-neighbourhoods is the sum of the indegree
and the outdegree. -/
lemma card_union_in_out {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (hor : IsOriented G) (v : V) :
    ((Finset.univ.filter (fun w => G.Adj w v)) ∪
        (Finset.univ.filter (fun w => G.Adj v w))).card
      = indegree G v + outdegree G v := by
  rw [Finset.card_union_of_disjoint (in_out_disjoint G hor v)]
  rfl

/-- In an oriented graph the total degree of a vertex is at most `n - 1`. -/
lemma indegree_add_outdegree_le {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V)
    [DecidableRel G.Adj] (hor : IsOriented G) (v : V) :
    indegree G v + outdegree G v ≤ Fintype.card V - 1 := by
  have h := Finset.card_le_card (in_out_union_subset_erase G hor v)
  rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ,
    card_union_in_out G hor v] at h
  exact h

/-- If the total degree of every vertex is at least `n - 1`, then the oriented graph is a
tournament: for every two distinct vertices there is an arc in one of the two directions. -/
lemma tournament_of_degrees {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V)
    [DecidableRel G.Adj] (d : ℕ) (hor : IsOriented G)
    (hdeg : ∀ v, d ≤ indegree G v ∧ d ≤ outdegree G v)
    (hcard : Fintype.card V = 2 * d + 1) :
    ∀ u v, u ≠ v → G.Adj u v ∨ G.Adj v u := by
  intro u v huv
  have heq : (Finset.univ.filter (fun w => G.Adj w u)) ∪
      (Finset.univ.filter (fun w => G.Adj u w)) = Finset.univ.erase u := by
    refine Finset.eq_of_subset_of_card_le (in_out_union_subset_erase G hor u) ?_
    rw [card_union_in_out G hor u, Finset.card_erase_of_mem (Finset.mem_univ u),
      Finset.card_univ, hcard]
    have h := hdeg u
    omega
  have hv : v ∈ Finset.univ.erase u := by
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact Ne.symm huv
  rw [← heq] at hv
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  rcases hv with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem main : H1 → H2 → H3 →
    type_of% @OMA.S_opg_long_directed_cycles_in_digraph_with_minimum_in_and_out_degree.main := by
  classical
  intro h1 h2 h3 V _ _ G _ d hd hor hstrong hdeg
  -- Counting: the total degree of every vertex is at least `2 * d` and at most `n - 1`.
  have hcount : 2 * d + 1 ≤ Fintype.card V := by
    have hle := indegree_add_outdegree_le G hor (Classical.arbitrary V)
    have hd' := hdeg (Classical.arbitrary V)
    omega
  rcases Nat.lt_or_ge (Fintype.card V) (2 * d + 2) with hlt | hge
  · -- The tight case: `n = 2 * d + 1`, where degrees force a tournament.
    have hcard : Fintype.card V = 2 * d + 1 := by omega
    refine ⟨Fintype.card V, by omega, ?_⟩
    exact h1 V G (by omega) hor hstrong (tournament_of_degrees G d hor hdeg hcard)
  · rcases Nat.lt_or_ge (Fintype.card V) (2 * d + 3) with hlt2 | hge2
    · -- The case `n = 2 * d + 2`.
      have hcard : Fintype.card V = 2 * d + 2 := by omega
      exact h2 V G d hd hor hstrong hdeg hcard
    · -- The case `n >= 2 * d + 3`.
      exact h3 V G d hd hor hstrong hdeg hge2

end OMA.R_opg_long_directed_cycles_in_digraph_with_minimum_in_and_out_degree_R1
