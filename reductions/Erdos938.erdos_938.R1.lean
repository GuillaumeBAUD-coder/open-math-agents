import FormalConjectures.ErdosProblems.«938»
import Mathlib

-- Reduction Erdos938.erdos_938.R1 of Erdős Problem 938
-- Credit: @MBimrose
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target (erdosproblems.com/938): only finitely many three-term arithmetic progressions are
-- made of three CONSECUTIVE powerful numbers, i.e. `P = {nth Powerful k, nth Powerful (k+1),
-- nth Powerful (k+2)}` for some `k` and `P` is an AP of length 3.
--
-- The split is on the index `k`, and it peels off the single index whose slice is a point:
--   * `H1` — `k = 0`: the slice is contained in the SINGLETON
--     `{{nth Powerful 0, nth Powerful 1, nth Powerful 2}}`, since `k = 0` pins `P` down
--     completely.  Hence it is finite; `H1` is elementary (`Set.Finite.subset` of a singleton).
--   * `H2` — `k ≠ 0`: the open core, where the progression can occur at any later index and the
--     finiteness statement is the actual content of the problem.
--
-- `main` is the case split `k = 0` / `k ≠ 0` applied to the witness of the existential: the set is
-- the union of the two slices, and a union of two finite sets is finite.  Closing `H1` and `H2`
-- closes the problem.

namespace OMA.R_Erdos938_erdos_938_R1

open Nat

/-- The `k = 0` slice: `P` is pinned to one explicit three-element set, so the slice is finite. -/
def H1 : Prop :=
  ({P : Finset ℕ | (P : Set ℕ).IsAPOfLength 3 ∧ ∃ k, k = 0 ∧
    P = {nth Powerful k, nth Powerful (k + 1), nth Powerful (k + 2)}} : Set (Finset ℕ)).Finite

/-- The open core: `k ≠ 0`. -/
def H2 : Prop :=
  ({P : Finset ℕ | (P : Set ℕ).IsAPOfLength 3 ∧ ∃ k, k ≠ 0 ∧
    P = {nth Powerful k, nth Powerful (k + 1), nth Powerful (k + 2)}} : Set (Finset ℕ)).Finite

theorem main : H1 → H2 → type_of% @Erdos938.erdos_938 := by
  intro h1 h2
  refine Set.Finite.subset (h1.union h2) ?_
  rintro P ⟨hAP, k, hP⟩
  rcases eq_or_ne k 0 with hk | hk
  · left
    exact ⟨hAP, k, hk, hP⟩
  · right
    exact ⟨hAP, k, hk, hP⟩

end OMA.R_Erdos938_erdos_938_R1
