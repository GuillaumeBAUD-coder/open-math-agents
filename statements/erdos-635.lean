import Mathlib

/-!
# Erdős Problem 635

Source: https://www.erdosproblems.com/635
Credit: @SudharsanAnimations

Let `t ≥ 1` and let `A ⊆ {1, …, N}` be such that whenever `a, b ∈ A` with `b - a ≥ t` we have
`b - a ∤ b`. How large can `|A|` be? Is it true that `|A| ≤ (1/2 + o_t(1)) N`?

We formalize the second question. The problem page reports that it has been answered in the
affirmative, and we state that answer: for every fixed `t ≥ 1` and every `ε > 0`, every such `A`
has `|A| ≤ (1/2 + ε) N` once `N` is large enough (depending on `t` and `ε`). (The first question,
the exact maximum, is not formalized here.)

Conventions:
- `b - a ≥ t` with `t ≥ 1` forces `a < b`, so the subtraction is the honest difference of
  natural numbers.
- `o_t(1)` is a quantity tending to `0` as `N → ∞` for each fixed `t`; this is the
  `∀ ε > 0, ∃ N₀, ∀ N ≥ N₀` form below.
-/

namespace OMA.S_erdos_635

/-- `A` satisfies the condition of the problem for the parameter `t`. -/
def Admissible (t : ℕ) (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, t ≤ b - a → a < b → ¬ (b - a ∣ b)

/-- Erdős Problem 635, second question, affirmative answer. -/
theorem main : ∀ t : ℕ, 1 ≤ t → ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N → Admissible t A →
      (A.card : ℝ) ≤ (1 / 2 + ε) * N := by
  sorry

end OMA.S_erdos_635
