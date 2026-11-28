import FormalConjectures.ErdosProblems.«126»

-- Reduction Erdos126.erdos_126.variants.isLittleO.R1 of Erdős Problem 126 — isLittleO
-- Credit: @MBimrose
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target (erdosproblems.com/126): if `f n` is the maximal number of distinct prime factors of
-- `∏_{a ≠ b ∈ A} (a + b)` over all `n`-element sets `A` (`IsMaximalAddFactorsCard`), then
-- `f n = o (n / log n)`.  Erdős–Turán proved `log n = O(f n)` and `f n = O(n / log n)` in their
-- first joint paper (the companion statement `erdos_126.variants.IsBigO`); the little-o is open.
--
-- The split is on whether `f` is bounded:
--   * `H1` — `f` is bounded above.  Then `f = o (n / log n)` for the trivial reason that the
--     right-hand side tends to infinity (`Real.isLittleO_log_id_atTop` gives `n / log n → ∞`), so a
--     bounded sequence is little-o of it.  This is the elementary region: no combinatorics, just
--     boundedness and `n / log n → ∞`.
--   * `H2` — `f` is unbounded.  This is the honest content: the whole difficulty of the problem is
--     the growth rate of `f`, and it disappears only in the bounded case.
--
-- Why this is honest: `BddAbove (Set.range f) ∨ ¬ BddAbove (Set.range f)` partitions the quantified
-- `f`, `main` is exactly that case distinction, each H states the target's conclusion on its half,
-- and the bounded half needs no number theory at all, so after the reduction only the unbounded case
-- has to be attacked.

namespace OMA.R_Erdos126_erdos_126_variants_isLittleO_R1

open Erdos126 Filter Asymptotics

/-- The elementary region: a bounded `f` is `o (n / log n)`, since `n / log n → ∞`. -/
def H1 : Prop :=
  ∀ (f : ℕ → ℕ), IsMaximalAddFactorsCard f → BddAbove (Set.range f) →
    (fun (n : ℕ) => (f n : ℝ)) =o[atTop] (fun (n : ℕ) => (n : ℝ) / Real.log n)

/-- The core: the same statement for unbounded `f`, where the growth rate carries the problem. -/
def H2 : Prop :=
  ∀ (f : ℕ → ℕ), IsMaximalAddFactorsCard f → ¬ BddAbove (Set.range f) →
    (fun (n : ℕ) => (f n : ℝ)) =o[atTop] (fun (n : ℕ) => (n : ℝ) / Real.log n)

theorem main : H1 → H2 → type_of% @Erdos126.erdos_126.variants.isLittleO := by
  intro h1 h2 f hf
  by_cases h : BddAbove (Set.range f)
  · exact h1 f hf h
  · exact h2 f hf h

end OMA.R_Erdos126_erdos_126_variants_isLittleO_R1
