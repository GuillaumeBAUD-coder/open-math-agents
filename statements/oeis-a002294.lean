import Mathlib

/-!
# OEIS A002294: 4-uniform words avoiding 231 and 221

Source: https://oeis.org/A002294
`A002294 n = binomial(5n, n) / (4n + 1)`. Theorem 3.6 of Defant and Kravitz,
Stack-sorting for words, counts the 4-uniform words on the alphabet `[n]` (each letter used exactly 4 times) avoiding the
patterns `231` and `221`.

Conventions. A word is `w : Fin (4n) → Fin n`. It contains `231` if there are positions
`i < j < k` with `w k < w i < w j`, and contains `221` if there are `i < j < k` with
`w k < w i = w j`. The division is exact, so `main` is stated multiplicatively.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a002294

/-- 4-uniform words on `Fin n` avoiding `231` and `221`. -/
def count (n : ℕ) : ℕ :=
  (Finset.univ.filter fun w : Fin (4 * n) → Fin n =>
    (∀ c : Fin n, (Finset.univ.filter fun i => w i = c).card = 4) ∧
    (∀ i j k : Fin (4 * n), i < j → j < k → ¬ (w k < w i ∧ w i < w j)) ∧
    (∀ i j k : Fin (4 * n), i < j → j < k → ¬ (w k < w i ∧ w i = w j))).card

theorem main :
    ∀ n : ℕ, count n * (4 * n + 1) = (5 * n).choose n := by
  sorry

end OMA.S_oeis_a002294
