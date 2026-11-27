import FormalConjectures.ErdosProblems.«1»

-- Reduction Erdos1.erdos_1.variants.least_N_9.R1 of Erdős Problem 1 — least N 9
-- Credit: @luciusacarr
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The least `N` with a `9`-element sum-distinct subset of `{1, …, N}` is `161`

* `H1` (attained): some `9`-element subset of `{1, …, 161}` is sum-distinct, for instance the
  Conway–Guy set `{77, 117, 137, 148, 154, 157, 159, 160, 161}`.
* `H2` (optimal): no `9`-element subset of `{1, …, 160}` is sum-distinct.  This is the exhaustive
  part (Lunnon's computation).
-/

namespace OMA.R_Erdos1_erdos_1_variants_least_N_9_R1

open Erdos1

/-- A `9`-element sum-distinct subset of `{1, …, 161}` exists. -/
def H1 : Prop :=
  ∃ A : Finset ℕ, IsSumDistinctSet A 161 ∧ A.card = 9

/-- Every `9`-element sum-distinct subset of `{1, …, N}` has `161 ≤ N`. -/
def H2 : Prop :=
  ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N → A.card = 9 → 161 ≤ N

theorem main : H1 → H2 → type_of% @Erdos1.erdos_1.variants.least_N_9 := by
  intro h1 h2
  refine ⟨h1, ?_⟩
  rintro N ⟨A, hA, hc⟩
  exact h2 N A hA hc

end OMA.R_Erdos1_erdos_1_variants_least_N_9_R1
