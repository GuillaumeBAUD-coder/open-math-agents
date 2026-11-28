import OMAStatements.S_oeis_a163198
import Mathlib

/-! Proof for OEIS A163198: by induction on `n`. With `x = F(2n+1)`, `b = F(2n+2)` and
`y = F(2n+3) = x + b`, the step needs `(y-1)^2 (y+2) - (x-1)^2 (x+2) = 4 b^3`; the difference of the
two sides equals `3 b (x y - b^2 - 1)`, which vanishes by Cassini's identity `F(2n+1) F(2n+3) =
F(2n+2)^2 + 1` (itself proved by induction).
Credit: Sudharsan Rajendiran -/

namespace OMA.P163198
open OMA.S_oeis_a163198

lemma cassini (n : ℕ) :
    (Nat.fib (2 * n + 1) : ℚ) * Nat.fib (2 * n + 3) = (Nat.fib (2 * n + 2) : ℚ) ^ 2 + 1 := by
  induction n with
  | zero => norm_num [Nat.fib_add_two]
  | succ n ih =>
    have h3 : Nat.fib (2 * n + 3) = Nat.fib (2 * n + 1) + Nat.fib (2 * n + 2) := Nat.fib_add_two
    have h4 : Nat.fib (2 * n + 4) = Nat.fib (2 * n + 2) + Nat.fib (2 * n + 3) := Nat.fib_add_two
    have h5 : Nat.fib (2 * n + 5) = Nat.fib (2 * n + 3) + Nat.fib (2 * n + 4) := Nat.fib_add_two
    rw [show 2 * (n + 1) + 1 = 2 * n + 3 by ring, show 2 * (n + 1) + 3 = 2 * n + 5 by ring,
      show 2 * (n + 1) + 2 = 2 * n + 4 by ring, h5, h4, h3]
    rw [h3] at ih
    push_cast at ih ⊢
    linear_combination ih

lemma closed (n : ℕ) :
    (a n : ℚ) = ((Nat.fib (2 * n + 1) : ℚ) - 1) ^ 2 * ((Nat.fib (2 * n + 1) : ℚ) + 2) / 4 := by
  induction n with
  | zero => simp [a]
  | succ n ih =>
    have hs : a (n + 1) = a n + Nat.fib (2 * (n + 1)) ^ 3 := by
      unfold a
      rw [Finset.sum_Icc_succ_top (by omega)]
    have h3 : Nat.fib (2 * n + 3) = Nat.fib (2 * n + 1) + Nat.fib (2 * n + 2) := Nat.fib_add_two
    have hc := cassini n
    rw [hs, show 2 * (n + 1) + 1 = 2 * n + 3 by ring, show 2 * (n + 1) = 2 * n + 2 by ring]
    push_cast
    rw [ih]
    rw [h3] at hc ⊢
    push_cast at hc ⊢
    linear_combination (-3 / 4 * (Nat.fib (2 * n + 2) : ℚ)) * hc

end OMA.P163198

theorem OMA.solution : type_of% @OMA.S_oeis_a163198.main := OMA.P163198.closed
