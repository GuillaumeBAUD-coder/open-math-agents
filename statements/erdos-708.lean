import Mathlib

/-!
# Erdős Problem 708

Source: https://www.erdosproblems.com/708
Credit: @biondadave

Let `g(n)` be minimal such that for any `A ⊆ [2, ∞) ∩ ℕ` with `|A| = n` and any set `I` of
`max(A)` consecutive integers there exists some `B ⊆ I` with `|B| = g(n)` such that
`∏_{a ∈ A} a ∣ ∏_{b ∈ B} b`. Is it true that `g(n) ≤ (2 + o(1)) n`?

We state the affirmative answer to this first question; the stronger "perhaps even
`g(n) ≤ 2n`" on the source page is not stated here.

Conventions:
- `g(n) ≤ (2 + o(1)) n` is stated without defining `g` as an infimum: for every `ε > 0` and all
  sufficiently large `n`, every admissible `A` and `I` admit a suitable `B` with
  `|B| ≤ (2 + ε) n`. This is equivalent to the source statement.
- `|B| ≤ k` is used instead of `|B| = k`. For the minimal `k` the two agree, because adding
  elements of `I` to `B` preserves the divisibility (all elements of `I` are positive) and
  `|I| = max A ≥ n + 1`.
- The consecutive integers are positive: `I = {m + 1, …, m + max A}` for some `m : ℕ`. An
  interval containing `0` would make the divisibility trivial.
-/

namespace OMA.S_erdos_708

theorem main :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ A : Finset ℕ, A.card = n → (∀ a ∈ A, 2 ≤ a) →
      ∀ m : ℕ, ∃ B ⊆ Finset.Icc (m + 1) (m + A.sup id),
        (B.card : ℝ) ≤ (2 + ε) * n ∧ (∏ a ∈ A, a) ∣ ∏ b ∈ B, b := by
  sorry

end OMA.S_erdos_708
