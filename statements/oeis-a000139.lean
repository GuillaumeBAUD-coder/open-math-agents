import Mathlib

/-!
# A000139 — Parity and odd fibbinary numbers

Conjectured by Peter Bala in https://oeis.org/A000139.
Credit: @Ciphore

The terms of A022341 are `4 * m + 1` for fibbinary numbers `m`, whose binary
expansions have no adjacent ones (https://oeis.org/A022341 and https://oeis.org/A003714).
-/

namespace OMA.S_oeis_a000139

def a (n : ℕ) : ℕ :=
  2 * (3 * n).factorial / ((2 * n + 1).factorial * (n + 1).factorial)

theorem main : ∀ n : ℕ, Odd (a n) ↔
    ∃ m : ℕ, n = 4 * m + 1 ∧
      ∀ i : ℕ, ¬(m.testBit i = true ∧ m.testBit (i + 1) = true) := by
  sorry

end OMA.S_oeis_a000139

