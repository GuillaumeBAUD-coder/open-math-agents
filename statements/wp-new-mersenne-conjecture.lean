import Mathlib

/-!
# New Mersenne conjecture (Bateman–Selfridge–Wagstaff conjecture)

Source: https://en.wikipedia.org/wiki/Mersenne_conjectures#New_Mersenne_conjecture
Credit: @joshuadc11

For any odd natural number `p`, if any two of the following three conditions hold, then the
third condition also holds:
1. `p = 2^k ± 1` or `p = 4^k ± 3` for some natural number `k`,
2. `2^p - 1` is prime,
3. `(2^p + 1) / 3` is prime.

Formalization notes:
- For every odd natural number `p`, `3` divides `2^p + 1`, so natural-number division
  `(2 ^ p + 1) / 3` is exact.
- Condition 1 is written without truncated subtraction as
  `∃ k : ℕ, p + 1 = 2 ^ k ∨ p = 2 ^ k + 1 ∨ p + 3 = 4 ^ k ∨ p = 4 ^ k + 3`.
-/

namespace OMA.S_wp_new_mersenne_conjecture

/-- Condition 1 of the New Mersenne conjecture: `p = 2^k ± 1` or `p = 4^k ± 3` for some `k`. -/
def Cond1 (p : ℕ) : Prop :=
  ∃ k : ℕ, p + 1 = 2 ^ k ∨ p = 2 ^ k + 1 ∨ p + 3 = 4 ^ k ∨ p = 4 ^ k + 3

theorem main :
    ∀ p : ℕ, Odd p →
      let c1 := Cond1 p
      let c2 := (2 ^ p - 1).Prime
      let c3 := ((2 ^ p + 1) / 3).Prime
      (c1 ∧ c2 → c3) ∧ (c1 ∧ c3 → c2) ∧ (c2 ∧ c3 → c1) := by
  sorry

end OMA.S_wp_new_mersenne_conjecture
