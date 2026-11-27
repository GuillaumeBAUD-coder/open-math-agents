import Mathlib

/-!
# Erdős Problem 1181

Source: https://www.erdosproblems.com/1181
Credit: @joshuadc11

Let `q(n, k)` denote the least prime which does not divide `∏_{1 ≤ i ≤ k} (n + i)`.
Is it true that there exists some `c > 0` such that, for all large `n`,
`q(n, log n) < (1 - c) * (log n)^2`?

Formalization notes:
- `q n k` is defined as `sInf {p : ℕ | p.Prime ∧ ¬ p ∣ ∏ i ∈ Finset.Icc 1 k, (n + i)}`.
- In `q(n, log n)`, the upper index `log n` of `1 ≤ i ≤ log n` is interpreted as `⌊Real.log n⌋₊`.
-/

namespace OMA.S_erdos_1181

/-- The least prime which does not divide `∏_{1 ≤ i ≤ k} (n + i)`. -/
noncomputable def q (n k : ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ ¬ p ∣ ∏ i ∈ Finset.Icc 1 k, (n + i)}

theorem main :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
      (q n ⌊Real.log (n : ℝ)⌋₊ : ℝ) < (1 - c) * (Real.log (n : ℝ)) ^ 2 := by
  sorry

end OMA.S_erdos_1181
