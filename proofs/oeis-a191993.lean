import OMAStatements.S_oeis_a191993
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a191993.main := by
  intro t
  show ((t : ℚ) + 3) * ((t : ℚ) + 3 - 3) * OMA.S_oeis_a191993.a (t + 3) -
      (7 * ((t : ℚ) + 3) ^ 2 - 23 * ((t : ℚ) + 3) + 12) * OMA.S_oeis_a191993.a (t + 2) +
      6 * (2 * ((t : ℚ) + 3) - 3) * ((t : ℚ) + 3 - 2) * OMA.S_oeis_a191993.a (t + 1) = 0
  have h1 : ((t : ℚ) + 3) * (Nat.centralBinom (t + 3) : ℚ) =
      2 * (2 * ((t : ℚ) + 2) + 1) * (Nat.centralBinom (t + 2) : ℚ) := by
    have h := Nat.succ_mul_centralBinom_succ (t + 2)
    have h' : ((t + 2 + 1 : ℕ) : ℚ) * (Nat.centralBinom (t + 2 + 1) : ℚ) =
        ((2 * (2 * (t + 2) + 1) : ℕ) : ℚ) * (Nat.centralBinom (t + 2) : ℚ) := by
      exact_mod_cast h
    push_cast at h'
    rw [show t + 3 = t + 2 + 1 from rfl]
    linarith
  have h2 : ((t : ℚ) + 2) * (Nat.centralBinom (t + 2) : ℚ) =
      2 * (2 * ((t : ℚ) + 1) + 1) * (Nat.centralBinom (t + 1) : ℚ) := by
    have h := Nat.succ_mul_centralBinom_succ (t + 1)
    have h' : ((t + 1 + 1 : ℕ) : ℚ) * (Nat.centralBinom (t + 1 + 1) : ℚ) =
        ((2 * (2 * (t + 1) + 1) : ℕ) : ℚ) * (Nat.centralBinom (t + 1) : ℚ) := by
      exact_mod_cast h
    push_cast at h'
    rw [show t + 2 = t + 1 + 1 from rfl]
    linarith
  unfold OMA.S_oeis_a191993.a
  rw [show t + 3 - 1 = t + 2 by omega, show t + 2 - 1 = t + 1 by omega,
    show t + 1 - 1 = t by omega]
  linear_combination ((t : ℚ) / 2) * h1 - (3 * ((t : ℚ) + 1) / 2) * h2
