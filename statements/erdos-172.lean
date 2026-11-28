import Mathlib

/-!
# Erdős Problem 172

Source: https://www.erdosproblems.com/172
Credit: @joshuadc11

Is it true that in any finite colouring of `ℕ` there exist arbitrarily large finite `A`
such that all sums and products of distinct elements in `A` are the same colour?

Formalization notes:
- Following Erdős's convention that `ℕ = {1, 2, 3, ...}`, elements of `A` are positive integers
  (`∀ a ∈ A, 0 < a`).
- Sums and products of distinct elements in `A` are `∑ a ∈ S, a` and `∏ a ∈ S, a` as `S` ranges
  over all nonempty subsets `S ⊆ A`.
-/

namespace OMA.S_erdos_172

theorem main :
    ∀ (r : ℕ) (c : ℕ → Fin r) (m : ℕ),
      ∃ (A : Finset ℕ) (col : Fin r),
        (∀ a ∈ A, 0 < a) ∧ m ≤ A.card ∧
        ∀ S ⊆ A, S.Nonempty →
          c (∑ a ∈ S, a) = col ∧ c (∏ a ∈ S, a) = col := by
  sorry

end OMA.S_erdos_172
