import Mathlib

/-!
# Erdős Problem 327

Source: https://www.erdosproblems.com/327
Credit: @shc261392

The source: suppose `A ⊆ {1, …, N}` is such that if `a, b ∈ A` and `a ≠ b` then `a + b ∤ ab`. Can
`A` be 'substantially more' than the odd numbers? What if `a, b ∈ A` with `a ≠ b` implies
`a + b ∤ 2ab`? Must `|A| = o(N)`?

The first question ('substantially more') has no precise form in the source. This file states the
precise second question, in its affirmative form: a proof of `main` answers it yes, a proof of
`¬ main` answers it no.

Reading used here: "`|A| = o(N)`" means that the largest size of such a set `A ⊆ {1, …, N}` is
`o(N)` as `N → ∞`, i.e. for every `ε > 0`, for all large `N`, every such `A` has `|A| ≤ ε N`.
-/

namespace OMA.S_erdos_327

open Filter

theorem main :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
      (∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ (a + b) ∣ 2 * a * b) → (A.card : ℝ) ≤ ε * N := by
  sorry

end OMA.S_erdos_327
