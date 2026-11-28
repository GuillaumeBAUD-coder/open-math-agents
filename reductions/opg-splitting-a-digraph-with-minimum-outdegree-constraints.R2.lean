import OMAStatements.S_opg_splitting_a_digraph_with_minimum_outdegree_constraints

/-!
# Reduction opg-splitting-a-digraph-with-minimum-outdegree-constraints.R2 (conditional form)

Credit: @MBimrose

This file is the CONDITIONAL version of the split of the parent problem; it supersedes R1, whose
second hypothesis was the full published transfer for all `(s,t)`. Here the assumed transfer is
weakened to the diagonal only, and it is labelled where it is used. Nothing about the open core is
assumed: H1 is a genuinely open statement.

Target (Open Problem Garden, Alon): is there a minimum integer `f(d)` such that the vertices of any
loopless digraph with minimum outdegree at least `f(d)` can be split into two nonempty parts so that
the subgraph induced by each part has minimum outdegree at least `d`? The problem is OPEN: the
existence of `f(d)` is not known for any `d >= 2` (only `d = 1`: Thomassen 1983, `f(1) = 3`, tight).

Write `F(s,t)` for the least `f` such that every loopless digraph with minimum outdegree at least `f`
splits into a nonempty part with internal minimum outdegree at least `s` and a nonempty complement
with internal minimum outdegree at least `t`.

* H1 (open core, no literature) is `F(2,2) exists`. Christoph, Petrova and Steiner
  (arXiv:2310.08449, Combin. Probab. Comput. 34 (2025) 559-564) show that the whole question reduces
  to this single case, and that `F(2,2)` itself is open (as is `F(1,2)`).
* H2 (assumed, NOT proved here) is the diagonal case of that transfer: `F(2,2)` exists implies
  `F(d,d)` exists for every `d`. This is strictly weaker than the published theorem of Christoph,
  Petrova and Steiner (which covers all pairs `(s,t)`), so the claim of this file is: the parent
  problem follows from (i) the open core `F(2,2)` and (ii) the diagonal transfer, the latter being a
  published theorem that is assumed here rather than formalised. Formalising the degree/token
  argument of arXiv:2310.08449 turns H2 into a lemma and leaves only H1.

Context, not needed for the reduction: `F(d,d) >= 2d + 1` (complete bidirected graph on `2d+1`
vertices: the smaller side has at most `d` vertices, so its vertices keep at most `d - 1` internal
out-neighbours), and Steiner's stronger bound `F(d,d) >= 2d + (1 + o(1)) log_3 d` (J. Graph Theory,
2023), so obstructions with minimum outdegree strictly above `2d + 1` do exist.
-/

namespace OMA.R_opg_splitting_a_digraph_with_minimum_outdegree_constraints_R2

/-- `F(s,t)`: existence of `f` such that every loopless digraph on a finite nonempty vertex type
with minimum outdegree at least `f` splits into a nonempty set `A` whose induced subgraph has
minimum outdegree at least `s` and a nonempty complement whose induced subgraph has minimum outdegree
at least `t`. Only existence is encoded, not minimality. -/
private def Fdef (s t : ℕ) : Prop :=
  ∃ f : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V]
    (D : Digraph V) [DecidableRel D.Adj],
    (∀ v, ¬ D.Adj v v) → (∀ v, f ≤ (Finset.univ.filter (fun w => D.Adj v w)).card) →
    ∃ A : Finset V, A.Nonempty ∧ Aᶜ.Nonempty ∧
      (∀ v ∈ A, s ≤ (A.filter (fun w => D.Adj v w)).card) ∧
      (∀ v ∈ Aᶜ, t ≤ (Aᶜ.filter (fun w => D.Adj v w)).card)

/-- H1, the open core: `F(2,2)` exists. This is the single case the literature leaves open, and it is
not known. -/
def H1 : Prop := Fdef 2 2

/-- H2, ASSUMED: the diagonal case of the transfer theorem of Christoph, Petrova and Steiner
(arXiv:2310.08449), namely that `F(2,2)` exists implies `F(d,d)` exists for every `d`. It is a
published theorem, weaker than their full statement (all pairs `(s,t)`), and it is assumed here
rather than proved; formalising it removes H2 from the assumptions. -/
def H2 : Prop := Fdef 2 2 → ∀ d : ℕ, Fdef d d

theorem main : H1 → H2 → type_of% @OMA.S_opg_splitting_a_digraph_with_minimum_outdegree_constraints.main := by
  intro h1 h2 d
  exact h2 h1 d

end OMA.R_opg_splitting_a_digraph_with_minimum_outdegree_constraints_R2
