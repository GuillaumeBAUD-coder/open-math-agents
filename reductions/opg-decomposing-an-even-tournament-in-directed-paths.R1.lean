import OMAStatements.S_opg_decomposing_an_even_tournament_in_directed_paths

-- Reduction opg-decomposing-an-even-tournament-in-directed-paths.R1 of Decomposing an even tournament in directed paths
-- Credit: @MBimrose
-- The target asks for N = sum_v max{0, d+(v) - d-(v)} directed paths (Nat subtraction is truncated, so the
-- summand IS max{0, d+ - d-}) that partition the arcs. The split below isolates the two genuinely different
-- difficulties:
--   H1  the combinatorial core: an arc-partition of an even tournament into exactly N vertex-simple directed
--       paths exists. This is the open conjecture, but stated as a list of paths instead of a `Fin N`-indexed
--       family, i.e. with all the index bookkeeping removed from the object being built.
--   Note the `L.Nodup` clause in H1 and the matching premise in H2: the paths are listed once each. Without it
--   the bridge would be FALSE (a list holding the same path twice still satisfies "every arc lies on a unique
--   member list", since that uniqueness is over list values, but it breaks the `exists!` over path indices).
--   H2  the bridge, which is NOT open: any arc-partition of a tournament into simple directed paths whose
--       number of paths is N can be repackaged as the `Fin N`-indexed family of the target, with the
--       `exists!` property. Its content is the counting identity #paths = sum_v max{0, d+(v) - d-(v)} for an
--       arc-partition plus extraction of paths from lists.
-- Neither hypothesis mentions the value or the other hypothesis, so each can be attacked on its own.
--
-- A warning for anyone formalising the classical formulation: the standard textbook reformulation via
-- "at every vertex pair min(d+, d-) in-arcs with out-arcs so that the arc-successor digraph is acyclic" is
-- NOT equivalent to this target, because acyclicity does not make the chains vertex-simple. Counterexample
-- (n = 4, arcs a->b, b->c, c->a, x->a, x->b, c->x): pair (c,a)->(a,b) at a, (a,b)->(b,c) at b,
-- (b,c)->(c,x) at c, (c,x)->(x,a) at x. This is a saturating pairing whose successor digraph is acyclic,
-- and N = 2, but the only long chain is c,a,b,c,x,a, which repeats c and a, so it is not a directed path
-- in the sense of `IsDirectedPath` (which requires `Function.Injective`). Splitting it raises the number of
-- paths, so the acyclic-pairing statement is strictly weaker than H1 and cannot replace it.

namespace OMA.R_opg_decomposing_an_even_tournament_in_directed_paths_R1

/-- Combinatorial core: the arcs of an even tournament are partitioned by exactly
`sum_v (d+(v) - d-(v))` vertex-simple directed paths. A path is a list with at least two entries, no repeated
entry, and an arc between consecutive entries; `l.zip l.tail` is the list of its arcs. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (D : Digraph V) [DecidableRel D.Adj],
    OMA.S_opg_decomposing_an_even_tournament_in_directed_paths.IsTournament D →
    Even (Fintype.card V) →
    ∃ L : List (List V),
      L.Nodup ∧
      (∀ l ∈ L, 2 ≤ l.length ∧ l.Nodup ∧ ∀ p ∈ l.zip l.tail, D.Adj p.1 p.2) ∧
      (∀ u v : V, D.Adj u v → ∃! l : List V, l ∈ L ∧ (u, v) ∈ l.zip l.tail) ∧
      L.length = ∑ v : V, ((Finset.univ.filter (fun w => D.Adj v w)).card -
        (Finset.univ.filter (fun w => D.Adj w v)).card)

/-- Bridge: an arc-partition of a tournament into simple directed paths, counted by
`sum_v (d+(v) - d-(v))` paths, yields the exact family of paths the target asks for. This is bookkeeping, not
the conjecture: the counting identity `#paths = sum_v max{0, d+(v) - d-(v)}` holds for every such partition. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (D : Digraph V) [DecidableRel D.Adj]
    (L : List (List V)),
    L.Nodup →
    (∀ l ∈ L, 2 ≤ l.length ∧ l.Nodup ∧ ∀ p ∈ l.zip l.tail, D.Adj p.1 p.2) →
    (∀ u v : V, D.Adj u v → ∃! l : List V, l ∈ L ∧ (u, v) ∈ l.zip l.tail) →
    L.length = ∑ v : V, ((Finset.univ.filter (fun w => D.Adj v w)).card -
      (Finset.univ.filter (fun w => D.Adj w v)).card) →
    ∃ (len : Fin (∑ v : V, ((Finset.univ.filter (fun w => D.Adj v w)).card -
          (Finset.univ.filter (fun w => D.Adj w v)).card)) → ℕ)
      (path : ∀ j, Fin (len j + 1) → V),
      (∀ j, OMA.S_opg_decomposing_an_even_tournament_in_directed_paths.IsDirectedPath D (path j)) ∧
      ∀ u v, D.Adj u v → ∃! j, OMA.S_opg_decomposing_an_even_tournament_in_directed_paths.OnPath (path j) u v

/-- The tournament carries the paths, H1 and H2 only repackage them. -/
theorem main : H1 → H2 → type_of% @OMA.S_opg_decomposing_an_even_tournament_in_directed_paths.main := by
  intro h1 h2 V _ _ D _ ht he
  obtain ⟨L, hnd, hpath, honce, hcount⟩ := h1 V D ht he
  exact h2 V D L hnd hpath honce hcount

end OMA.R_opg_decomposing_an_even_tournament_in_directed_paths_R1
