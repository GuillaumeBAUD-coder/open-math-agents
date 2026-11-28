import OMAStatements.S_opg_splitting_a_digraph_with_minimum_outdegree_constraints

/-!
# Reduction opg-splitting-a-digraph-with-minimum-outdegree-constraints.R1 of Alon's splitting
# question

Credit: @MBimrose

Target (Open Problem Garden, Alon): is there a minimum integer `f(d)` such that the vertices of any
loopless digraph with minimum outdegree at least `f(d)` can be split into two nonempty parts so that
the subgraph induced by each part has minimum outdegree at least `d`? The problem is OPEN: the
existence of `f(d)` is not known for any `d >= 2`.

Write `F(s,t)` for the least `f` such that every loopless digraph with minimum outdegree at least
`f` splits into a part with internal minimum outdegree at least `s` and a nonempty complementary
part with internal minimum outdegree at least `t`. The literature already reduces the whole
question to one sharp case:

* H1 (the open core) is `F(2,2) exists`: the case `s = t = 2`. Nothing more is known about it.
* H2 (the published reduction theorem) is `F(2,2) exists implies F(s,t) exists for all s, t`.
  This is Christoph, Petrova and Steiner, arXiv:2310.08449, Combin. Probab. Comput. 34 (2025)
  559-564: all `F(s,t)` exist as soon as `F(2,2)` exists.

Context, not needed for the reduction: `F(1,1) = 3` (Thomassen 1983, and it is tight), the lower
bound `F(d,d) >= 2d + 1` from the complete bidirected graph on `2d + 1` vertices, and Steiner's
stronger bound `F(d,d) >= 2d + (1 + o(1)) log_3 d` (J. Graph Theory, 2023).

`main` is the reduction itself: apply H2 to H1 at `s = t = d`. Neither hypothesis mentions the
target statement, so both are honest sub-problems; H2 is a published theorem, so after it is
formalised only the open case `s = t = 2` is left.
-/

namespace OMA.R_opg_splitting_a_digraph_with_minimum_outdegree_constraints_R1

/-- `F(s,t)`: the least `f` such that every loopless digraph on a finite nonempty vertex type with
minimum outdegree at least `f` splits into a nonempty set `A` whose induced subgraph has minimum
outdegree at least `s` and a nonempty complement whose induced subgraph has minimum outdegree at
least `t`. Here `F` is only used as a proposition (existence of such an `f`), so the minimality is
not encoded. -/
private def Fdef (s t : ℕ) : Prop :=
  ∃ f : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V]
    (D : Digraph V) [DecidableRel D.Adj],
    (∀ v, ¬ D.Adj v v) → (∀ v, f ≤ (Finset.univ.filter (fun w => D.Adj v w)).card) →
    ∃ A : Finset V, A.Nonempty ∧ Aᶜ.Nonempty ∧
      (∀ v ∈ A, s ≤ (A.filter (fun w => D.Adj v w)).card) ∧
      (∀ v ∈ Aᶜ, t ≤ (Aᶜ.filter (fun w => D.Adj v w)).card)

/-- H1, the open core: `F(2,2)` exists, i.e. there is a minimum outdegree that forces a split into
two parts each of internal minimum outdegree at least 2. This is the only case left open by the
literature. -/
def H1 : Prop := Fdef 2 2

/-- H2, the published reduction theorem of Christoph, Petrova and Steiner (arXiv:2310.08449,
Combin. Probab. Comput. 34 (2025) 559-564): if `F(2,2)` exists then `F(s,t)` exists for all
`s` and `t`, so the single case `s = t = 2` implies the whole conjecture. -/
def H2 : Prop := Fdef 2 2 → ∀ s t : ℕ, Fdef s t

theorem main : H1 → H2 → type_of% @OMA.S_opg_splitting_a_digraph_with_minimum_outdegree_constraints.main := by
  intro h1 h2 d
  exact h2 h1 d d

end OMA.R_opg_splitting_a_digraph_with_minimum_outdegree_constraints_R1
