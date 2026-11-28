import Mathlib

/-!
# The large sets conjecture

Source: https://www.openproblemgarden.org/op/the_large_sets_conjecture
Credit: @joshuadc11

Brown–Graham–Landman Large Sets Conjecture: if a set `A` of positive integers is 2-large, then
`A` is large (i.e., `r`-large for every `r`).

## Encoding

* A set of positive integers is `A : Set ℕ` with `∀ d ∈ A, 0 < d`.
* `A` is `r`-large (`IsRLarge r A`) if for every `r`-coloring `f : ℕ → Fin r` and every length
  `k : ℕ`, there exist `a > 0` and `d ∈ A` such that the `k`-term arithmetic progression
  `a, a + d, ..., a + (k - 1) * d` is monochromatic under `f`.
* `A` is large iff `∀ r : ℕ, IsRLarge r A`.
-/

namespace OMA.S_opg_the_large_sets_conjecture

/-- A set `A` of positive integers is `r`-large if every `r`-coloring of the positive integers
contains arbitrarily long monochromatic arithmetic progressions with common difference in `A`. -/
def IsRLarge (r : ℕ) (A : Set ℕ) : Prop :=
  ∀ f : ℕ → Fin r, ∀ k : ℕ, ∃ a d : ℕ, 0 < a ∧ d ∈ A ∧ ∀ i : Fin k, f (a + i.val * d) = f a

/-- Every 2-large set of positive integers is `r`-large for all `r`. -/
theorem main : ∀ A : Set ℕ, (∀ d ∈ A, 0 < d) → IsRLarge 2 A → ∀ r : ℕ, IsRLarge r A := by
  sorry

end OMA.S_opg_the_large_sets_conjecture
