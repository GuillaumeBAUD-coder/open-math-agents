import Mathlib

/-!
# The identity for OEIS A005251

Source: https://oeis.org/A005251
Sources for the auxiliary sequences: https://oeis.org/A078065 and https://oeis.org/A005314
Credit: @Heart-galaxy

The three sequences use their listed initial values and order-three recurrences over `ℤ`.
The conjecture of Creighton Dement was proved by Sela Fried in 2025.
See https://oeis.org/A005251/a005251_2.pdf, Theorem 1.
-/

namespace OMA.S_oeis_a005251

/-- OEIS A005251, using the order-three recurrence listed in its formulas. -/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | n + 3 => 2 * a (n + 2) - a (n + 1) + a n

/-- OEIS A078065, the signed auxiliary sequence. -/
def b : ℕ → ℤ
  | 0 => 1
  | 1 => -3
  | 2 => 5
  | n + 3 => -2 * b (n + 2) - b (n + 1) - b n

/-- OEIS A005314, with its zero-based initial values. -/
def c : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | n + 3 => 2 * c (n + 2) - c (n + 1) + c n

/-- Dement's identity for A005251, A078065, and A005314. -/
theorem main : ∀ n : ℕ, a (n + 1) + |b n| = 2 * c (n + 1) := by
  sorry

end OMA.S_oeis_a005251
