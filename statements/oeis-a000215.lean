import Mathlib

/-!
# A000215: Fermat numbers: a(n) = 2^(2^n) + 1.

Source: https://oeis.org/A000215
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a000215

def fermat (n : ℕ) : ℕ :=
  2 ^ (2 ^ n) + 1

theorem main :
    (∀ n : ℕ, Nat.Prime (fermat n) ↔ n < 5) ∧
    (∀ n : ℕ, ¬ Nat.Prime (fermat n) →
      Nat.minFac (fermat n) < 3 * 2 ^ ((2 ^ n) / 2 - n - 2)) ∧
    (∀ n : ℕ, (∃ k : ℕ, 1 < k ∧ n = fermat k) ↔
      ((n - 1) ^ 4 - 1) ∣ (2 ^ (n - 1) - 1)) := by
  sorry

end OMA.S_oeis_a000215
