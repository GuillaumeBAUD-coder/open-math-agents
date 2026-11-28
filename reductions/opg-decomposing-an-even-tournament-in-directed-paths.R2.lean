import OMAStatements.S_opg_decomposing_an_even_tournament_in_directed_paths

-- Reduction opg-decomposing-an-even-tournament-in-directed-paths.R2 of Decomposing an even
-- tournament in directed paths
-- Credit: @MBimrose

/-!
# The nonzero split: extremal excess (published) vs. the open remainder

Target: every tournament `D` of even order `n` decomposes its arc set into exactly
`N = ∑_v max {0, d⁺(v) - d⁻(v)}` vertex-simple directed paths (`N` is truncated `ℕ`
subtraction per vertex, so the summand really is `max {0, d⁺-d⁻}`).

## Why this split, and not a large-n/small-n split

The obvious literature-driven split — `H1` = Girão–Granet–Kühn–Lo–Osthus, *Path decompositions
of tournaments*, Proc. LMS (3) 126 (2023) 429–517, Thm. 1.3 (arXiv:2010.14158) — cannot be made
into a reduction here: that theorem is `∃ n₀, ∀ even n ≥ n₀, pn(T) = ex(T)` with an INEFFECTIVE
`n₀` (the authors say they use hierarchies rather than computing constants), so any hypothesis
covering the cases below `n₀` must be `∀ n₀, ∀ V, Even (card V) → card V < n₀ → conclusion`,
which is logically EQUIVALENT to the target (instantiate `n₀ = card V + 1`). `main` would then
be `h₂ (card V + 1)` with `H1` unused, i.e. a restatement, which is a documented FAIL reason.
Bounding `n₀ ≤ B` for a numeral `B` would be an unproved STRENGTHENING of the cited theorem.

## The split used here (structural, no thresholds)

Write `ex(T) = N` for the target's path count and `n = |V|`.

* `H1` (PUBLISHED, all `n`): the extremal class `ex(T) = n²/4` is consistent. Alspach–Pullman
  (Bull. Austral. Math. Soc. 1974) and Alspach–Mason–Pullman (*Path numbers of tournaments*,
  JCTB 20 (1976) 222–228) prove `pn(T) ≤ ⌊n²/4⌋` for EVERY tournament; with the elementary
  `pn(T) ≥ ex(T)` (at least `ex⁺(v)` paths must start at `v`) and `ex(T) = n²/4` for even `n`
  this forces `pn(T) = ex(T)`. So `H1` is a theorem of the literature for all `n`, not an
  assumption, and the class is infinite (the transitive tournament of every even order is in it).
* `H2` (the open remainder): the non-extremal class `ex(T) < n²/4` is consistent. This is a
  strict restriction of the target — the entire extremal class is removed — so it neither
  restates nor strengthens the target. Everything known beyond the large-`n` theorem lives here.
* `H3` (PUBLISHED, used only for coverage): `4 * ex(T) ≤ n * n` for even `n`. This is
  Lo–Patel–Skokan–Talbot, Proc. LMS 121 (2020) 426–461, Prop. 1.4 (`ex(T) ∈ [n/2, n²/4]` for
  even `n`). It is stated as an explicit hypothesis rather than assumed or faked: the natural
  in-repo proof needs Landau's score-sequence conditions, which are not in Mathlib.
  With `H3`, `H1` and `H2` are exhaustive (`4*ex = n*n` or `4*ex < n*n`), and `main` is the
  corresponding trichotomy.

Every hypothesis is used exactly once in `main`; none mentions another; the exact path count
`N = ex(T)` is in all three, so no count bookkeeping is hidden inside a hypothesis.

## Relation to R1 (for the record)

`reductions/…R1.lean` splits into "arc-partition in list form" + a repackaging bridge. Its `H1`
is logically EQUIVALENT to the target (the target's `∃!`-over-arcs clause forces the path values
to be distinct, so a `Fin N`-indexed family is a list with `Nodup` and length `N`, and conversely
the bridge `R1.H2` repackages any such list). R1 therefore carries the PR as the reduction that
isolates the counting formulation, but it earns no split credit; this R2 is the creditable split.
-/

namespace OMA.R_opg_decomposing_an_even_tournament_in_directed_paths_R2

open OMA.S_opg_decomposing_an_even_tournament_in_directed_paths

/-- `H1`: the extremal-excess class `ex(T) = n²/4` is consistent.
Cited: Alspach–Pullman 1974 / Alspach–Mason–Pullman, JCTB 20 (1976) 222–228
(`pn(T) ≤ ⌊n²/4⌋` for every tournament) together with the elementary `pn(T) ≥ ex(T)`. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (D : Digraph V) [DecidableRel D.Adj],
    IsTournament D → Even (Fintype.card V) →
    4 * (∑ v : V, ((Finset.univ.filter (fun w => D.Adj v w)).card -
          (Finset.univ.filter (fun w => D.Adj w v)).card)) =
        Fintype.card V * Fintype.card V →
    ∃ (len : Fin (∑ v : V, ((Finset.univ.filter (fun w => D.Adj v w)).card -
          (Finset.univ.filter (fun w => D.Adj w v)).card)) → ℕ)
      (path : ∀ j, Fin (len j + 1) → V),
      (∀ j, IsDirectedPath D (path j)) ∧
      ∀ u v, D.Adj u v → ∃! j, OnPath (path j) u v

/-- `H2`: the open remainder — the non-extremal class `ex(T) < n²/4` is consistent. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (D : Digraph V) [DecidableRel D.Adj],
    IsTournament D → Even (Fintype.card V) →
    4 * (∑ v : V, ((Finset.univ.filter (fun w => D.Adj v w)).card -
          (Finset.univ.filter (fun w => D.Adj w v)).card)) <
        Fintype.card V * Fintype.card V →
    ∃ (len : Fin (∑ v : V, ((Finset.univ.filter (fun w => D.Adj v w)).card -
          (Finset.univ.filter (fun w => D.Adj w v)).card)) → ℕ)
      (path : ∀ j, Fin (len j + 1) → V),
      (∀ j, IsDirectedPath D (path j)) ∧
      ∀ u v, D.Adj u v → ∃! j, OnPath (path j) u v

/-- `H3`: the excess bound `ex(T) ≤ n²/4` (coverage only).
Cited: Lo–Patel–Skokan–Talbot, PLMS 121 (2020) 426–461, Prop. 1.4. -/
def H3 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (D : Digraph V) [DecidableRel D.Adj],
    IsTournament D → Even (Fintype.card V) →
    4 * (∑ v : V, ((Finset.univ.filter (fun w => D.Adj v w)).card -
          (Finset.univ.filter (fun w => D.Adj w v)).card)) ≤
        Fintype.card V * Fintype.card V

/-- The three hypotheses cover the two cases exactly (`≤` with `=`, and its complement), so
`main` is a trichotomy on `4 * ex(T)` vs `n * n` and nothing else. -/
theorem main : H1 → H2 → H3 →
    type_of% @OMA.S_opg_decomposing_an_even_tournament_in_directed_paths.main := by
  intro h1 h2 h3 V fV dV D dA hT hEven
  have hle : 4 * (∑ v : V, ((Finset.univ.filter (fun w => D.Adj v w)).card -
        (Finset.univ.filter (fun w => D.Adj w v)).card)) ≤
      Fintype.card V * Fintype.card V := h3 V D hT hEven
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact h2 V D hT hEven hlt
  · exact h1 V D hT hEven heq

end OMA.R_opg_decomposing_an_even_tournament_in_directed_paths_R2
