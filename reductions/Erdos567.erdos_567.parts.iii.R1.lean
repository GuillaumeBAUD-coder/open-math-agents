import FormalConjectures.ErdosProblems.«567»

-- Reduction Erdos567.erdos_567.parts.iii.R1 of Erdős Problem 567 (H5) — Ramsey size linearity
-- Credit: @MBimrose
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target (erdosproblems.com/567): `H5` (`C_5` with two vertex-disjoint chords, 5 vertices,
-- 7 edges — also known as `K_4^*`, `K_4` with one edge subdivided) is *Ramsey size linear*, i.e.
-- `R(H5, H) ≤ c * |E H|` for every graph `H` without isolated vertices.
-- `IsRamseySizeLinear` quantifies over all pairs `(n, H)` on `Fin n`, and its hypothesis
-- `∀ v, 0 < H.degree v` is exactly what makes the problem about graphs with no isolated vertices.
--
-- The split is on that very hypothesis:
--   * `H1` — `H` HAS an isolated vertex (`¬ ∀ v, 0 < H.degree v`).  Then the implication in the
--     definition is vacuous, so the bound holds for *every* constant `c > 0`.  Elementary: the
--     proof is `fun c _ n H _ h => absurd h hdeg`, no graph theory at all.
--   * `H2` — every vertex of `H` has positive degree.  This is exactly the content of the
--     conjecture (Erdős–Faudree–Rousseau–Schelp), and it is where all of the difficulty lives.
--
-- Why this is honest: `H1` and `H2` partition the hypothesis space of the definition of
-- `IsRamseySizeLinear`, and `main` needs both — it takes the constant `c` of `H2` and enlarges it
-- to `max 1 c`, which is what `H1` is stated for (a vacuous bound for any constant).  After the
-- reduction no case is lost, and the remaining step `H2` is a clean statement about graphs with
-- minimum degree at least 1.
--
-- Comment on the sibling files `Erdos567.erdos_567.parts.i/.ii.R1.lean` (same shape for `Q3` and
-- `K_{3,3}`): `main` does not inspect the first graph, so it is identical; the three files are
-- separate because the catalogue's problems are separate (the known bounds for `R(H5, H)` differ
-- from those for `R(Q_3, H)` and `R(K_{3,3}, H)`).

namespace OMA.R_Erdos567_erdos_567_parts_iii_R1

open Erdos567 SimpleGraph

/-- The vacuous case: `H` has an isolated vertex, so the bound in `IsRamseySizeLinear` holds for
every constant `c > 0` (the inner implication is false in its premise). -/
def H1 : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
    ¬ (∀ v, 0 < H.degree v) → (graphRamsey (SimpleGraph.cycleGraph 5 ⊔ SimpleGraph.edge 0 2 ⊔ SimpleGraph.edge 1 3) H : ℝ) ≤ c * H.edgeSet.ncard

/-- The core: the bound `R(H5, H) ≤ c * |E H|` for graphs `H` with no isolated vertices, which is
the actual content of "`H5` is Ramsey size linear". -/
def H2 : Prop :=
  ∃ c > (0 : ℝ), ∀ (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
    (∀ v, 0 < H.degree v) → (graphRamsey (SimpleGraph.cycleGraph 5 ⊔ SimpleGraph.edge 0 2 ⊔ SimpleGraph.edge 1 3) H : ℝ) ≤ c * H.edgeSet.ncard

theorem main : H1 → H2 → type_of% @Erdos567.erdos_567.parts.iii := by
  intro h1 h2
  obtain ⟨c, hc, hle⟩ := h2
  refine ⟨max 1 c, lt_of_lt_of_le one_pos (le_max_left 1 c), ?_⟩
  intro n H hH hdeg
  by_cases hall : ∀ v, 0 < H.degree v
  · exact le_trans (hle n H hall)
      (mul_le_mul_of_nonneg_right (le_max_right 1 c) (Nat.cast_nonneg _))
  · exact h1 (max 1 c) (lt_of_lt_of_le one_pos (le_max_left 1 c)) n H hall

end OMA.R_Erdos567_erdos_567_parts_iii_R1
