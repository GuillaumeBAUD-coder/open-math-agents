import FormalConjectures.ErdosProblems.«1108»
import Mathlib

-- Reduction Erdos1108.erdos_1108.parts.i.R1 of Erdős Problem 1108 — i
-- Credit: @MBimrose
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target (erdosproblems.com/1108): for every `k ≥ 2`, `A` = the set of all finite sums of
-- DISTINCT factorials (`FactorialSums`, indices `> 0`) contains only finitely many `k`-th powers.
--
-- The split is on the value `a` of the power, uniformly in `k`, and it only separates off the two
-- smallest values:
--   * `H1` — `a ≤ 1`: the slice is contained in `{0, 1}` for every `k`, so it is finite
--     regardless of `FactorialSums` and of the equation `m ^ k = a` (which has no solution with
--     `a = 0` and `m ≠ 0`, or `a = 1` for `k ≥ 2` other than `m = 1`).  `H1` is elementary: a
--     subset of a two-element set.
--   * `H2` — `2 ≤ a`: the open core, where `m ≥ 2`, the powers are large and the finiteness of
--     the factorial sums that are `k`-th powers is the content of the problem.
--
-- `main` is the case split `a ≤ 1` / `1 < a` on a member of the set, uniformly in `k`; the set is
-- the union of the two slices and a union of finite sets is finite.  Closing `H1` and `H2` closes
-- the problem.

namespace OMA.R_Erdos1108_erdos_1108_parts_i_R1

open Erdos1108

/-- The small values `a ≤ 1`, uniformly in `k`: the slice sits inside `{0, 1}`. -/
def H1 : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    ({a : ℕ | a ∈ FactorialSums ∧ (∃ m : ℕ, m ^ k = a) ∧ a ≤ 1} : Set ℕ).Finite

/-- The open core: `2 ≤ a`. -/
def H2 : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    ({a : ℕ | a ∈ FactorialSums ∧ (∃ m : ℕ, m ^ k = a) ∧ 2 ≤ a} : Set ℕ).Finite

theorem main : H1 → H2 → type_of% @Erdos1108.erdos_1108.parts.i := by
  intro h1 h2 k hk
  refine Set.Finite.subset ((h1 k hk).union (h2 k hk)) ?_
  rintro a ⟨ha, hm⟩
  rcases le_or_gt a 1 with h | h
  · left
    exact ⟨ha, hm, h⟩
  · right
    exact ⟨ha, hm, by omega⟩

end OMA.R_Erdos1108_erdos_1108_parts_i_R1
