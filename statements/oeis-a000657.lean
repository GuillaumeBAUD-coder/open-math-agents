import Mathlib

/-!
# A000657: Median Euler numbers

Source: https://oeis.org/A000657
Credit: @gblacher2

Peter Bala's conjecture on eventual periodicity modulo a positive integer.
-/

namespace OMA.S_oeis_a000657

open scoped BigOperators

/-- The triangle from Oliver Seipel's recurrence in A000657. On row `n + 1`,
entry `k` is the sum of the last `k` entries of row `n`, for `k ≤ n + 1`. -/
def triangle : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | n + 1, k => ∑ j ∈ Finset.range k, triangle n (n - j)

/-- The central entries of the even rows, starting at index zero. -/
def medianEuler (n : ℕ) : ℕ := triangle (2 * n) n

/-- Following the convention for Euler's totient, the modulus is positive. -/
theorem main :
    ∀ k : ℕ, 0 < k → ∃ N p : ℕ, 0 < p ∧ p ∣ k.totient ∧
      ∀ n : ℕ, N ≤ n → Nat.ModEq k (medianEuler (n + p)) (medianEuler n) := by
  sorry

end OMA.S_oeis_a000657
