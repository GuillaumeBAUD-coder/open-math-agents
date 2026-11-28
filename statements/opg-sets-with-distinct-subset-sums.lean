import Mathlib

/-!
# Sets with distinct subset sums

Source: https://www.openproblemgarden.org/op/sets_with_distinct_subset_sums
Credit: @joshuadc11

Erdős conjecture: there exists a constant `c : ℝ` such that `|S| ≤ log₂(n) + c` whenever
`S ⊆ {1, 2, ..., n}` has distinct subset sums (distinct subsets of `S` have distinct sums).

## Encoding

* `S : Finset ℕ` with `S ⊆ Finset.Icc 1 n` (`1 ≤ n`).
* Distinct subset sums: for all `A ⊆ S` and `B ⊆ S`, `∑ x ∈ A, x = ∑ x ∈ B, x → A = B`.
* The bound is `(S.card : ℝ) ≤ Real.logb 2 (n : ℝ) + c`.
-/

namespace OMA.S_opg_sets_with_distinct_subset_sums

/-- A finite set of natural numbers has distinct subset sums if distinct subsets have distinct
sums. -/
def HasDistinctSubsetSums (S : Finset ℕ) : Prop :=
  ∀ A ⊆ S, ∀ B ⊆ S, (∑ x ∈ A, x) = (∑ x ∈ B, x) → A = B

/-- There exists a constant `c : ℝ` such that `|S| ≤ log₂(n) + c` for every `n ≥ 1` and every
`S ⊆ {1, ..., n}` with distinct subset sums. -/
theorem main : ∃ c : ℝ, ∀ (n : ℕ), 1 ≤ n → ∀ S : Finset ℕ,
    S ⊆ Finset.Icc 1 n → HasDistinctSubsetSums S →
    (S.card : ℝ) ≤ Real.logb 2 (n : ℝ) + c := by
  sorry

end OMA.S_opg_sets_with_distinct_subset_sums
