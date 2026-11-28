import OMAStatements.S_oeis_a163198
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: induction on n; the step uses the Cassini identity fib(2n+1) fib(2n+3) - fib(2n+2)^2 = 1, closed by linear_combination.

namespace OMA.S_oeis_a163198

theorem cassini (n : ℕ) :
    (Nat.fib n : ℤ) * Nat.fib (n + 2) - (Nat.fib (n + 1) : ℤ) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h1 : (Nat.fib (k + 2) : ℤ) = Nat.fib k + Nat.fib (k + 1) := by
      rw [Nat.fib_add_two]; push_cast; ring
    have h2 : (Nat.fib (k + 1 + 2) : ℤ) = Nat.fib (k + 1) + Nat.fib (k + 2) := by
      rw [Nat.fib_add_two]; push_cast; ring
    rw [show k + 1 + 1 = k + 2 by ring, h2, pow_succ]
    rw [h1] at ih ⊢
    linear_combination (-1 : ℤ) * ih

/-- The stated formula a(n) = (F(2n+1)-1)^2*(F(2n+1)+2)/4, for every n ≥ 0. -/
theorem main_proof : ∀ n : ℕ,
    (a n : ℚ) = ((Nat.fib (2 * n + 1) : ℚ) - 1) ^ 2 * ((Nat.fib (2 * n + 1) : ℚ) + 2) / 4 := by
  intro n
  induction n with
  | zero => simp [a]
  | succ k ih =>
    have hc := cassini (2 * k + 1)
    have hz : (Nat.fib (2 * k + 1) : ℚ) * Nat.fib (2 * k + 3) - (Nat.fib (2 * k + 2) : ℚ) ^ 2
        = 1 := by
      have : (-1 : ℤ) ^ (2 * k + 1 + 1) = 1 := by
        rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul]; norm_num
      rw [this] at hc
      exact_mod_cast hc
    have hw : (Nat.fib (2 * k + 3) : ℚ) = Nat.fib (2 * k + 1) + Nat.fib (2 * k + 2) := by
      rw [show 2 * k + 3 = (2 * k + 1) + 2 by ring, Nat.fib_add_two]; push_cast; ring
    have hs : (a (k + 1) : ℚ) = a k + (Nat.fib (2 * k + 2) : ℚ) ^ 3 := by
      unfold a
      rw [Finset.sum_Icc_succ_top (by omega)]
      push_cast
      rw [show 2 * (k + 1) = 2 * k + 2 by ring]
    rw [hs, ih, show 2 * (k + 1) + 1 = 2 * k + 3 by ring]
    rw [hw] at hz ⊢
    linear_combination (-(3 : ℚ) / 4 * Nat.fib (2 * k + 2)) * hz


end OMA.S_oeis_a163198

theorem OMA.solution : type_of% @OMA.S_oeis_a163198.main := OMA.S_oeis_a163198.main_proof
