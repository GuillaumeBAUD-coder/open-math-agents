import FormalConjectures.ErdosProblems.«1108»
import Mathlib

-- Reduction Erdos1108.erdos_1108.parts.ii.R1 of Erdős Problem 1108 — ii
-- Credit: @MBimrose
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target (erdosproblems.com/1108): the set `A` of all finite sums of DISTINCT factorials
-- (`FactorialSums`, indices `> 0`) contains only finitely many powerful numbers.
--
-- The split is on the value `a`, and it only separates off the two smallest values:
--   * `H1` — `a ≤ 1`: this slice is contained in `{0, 1}`, so it is finite whatever
--     `FactorialSums` and `Powerful` say.  `H1` is elementary: a subset of a two-element set,
--     decided by the arithmetic of `≤ 1`.
--   * `H2` — `2 ≤ a`: the open core, where the factorial sums are genuinely large and the
--     finiteness of the powerful ones among them is the content of the problem.
--
-- `main` is the case split `a ≤ 1` / `1 < a` on a member of the set; the set is the union of the
-- two slices, and a union of finite sets is finite.  Closing `H1` and `H2` closes the problem.

namespace OMA.R_Erdos1108_erdos_1108_parts_ii_R1

open Erdos1108

/-- The small values `a ≤ 1`: this slice sits inside `{0, 1}`, hence is finite. -/
def H1 : Prop :=
  ({a : ℕ | a ∈ FactorialSums ∧ a.Powerful ∧ a ≤ 1} : Set ℕ).Finite

/-- The open core: `2 ≤ a`. -/
def H2 : Prop :=
  ({a : ℕ | a ∈ FactorialSums ∧ a.Powerful ∧ 2 ≤ a} : Set ℕ).Finite

theorem main : H1 → H2 → type_of% @Erdos1108.erdos_1108.parts.ii := by
  intro h1 h2
  refine Set.Finite.subset (h1.union h2) ?_
  rintro a ⟨ha, hp⟩
  rcases le_or_gt a 1 with h | h
  · left
    exact ⟨ha, hp, h⟩
  · right
    exact ⟨ha, hp, by omega⟩

end OMA.R_Erdos1108_erdos_1108_parts_ii_R1
