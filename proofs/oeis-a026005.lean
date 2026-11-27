import OMAStatements.S_oeis_a026005
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

-- Credit: @erood (Lean proof with Codex)

namespace OMA.A026005Proof

open OMA.S_oeis_a026005

theorem factorial_step (n : ℕ) :
    ((n + 1).factorial : ℚ) = ((n : ℚ) + 1) * (n.factorial : ℚ) := by
  rw [Nat.factorial_succ]
  push_cast
  rfl

theorem factorial_form (n : ℕ) :
    a n = (2 * (n : ℚ) + 2) * ((4 * n + 1).factorial : ℚ) /
      ((n.factorial : ℚ) * ((3 * n + 2).factorial : ℚ)) := by
  have h := Nat.choose_mul_factorial_mul_factorial (n := 4 * n + 1) (k := n) (by omega)
  rw [show 4 * n + 1 - n = 3 * n + 1 by omega] at h
  have hh : ((4 * n + 1).choose n : ℚ) * n.factorial * (3 * n + 1).factorial =
      (4 * n + 1).factorial := by exact_mod_cast h
  unfold a
  rw [← hh, show 3 * n + 2 = (3 * n + 1) + 1 by omega, factorial_step (3 * n + 1)]
  push_cast
  field_simp
  ring

/-- Dividing successive terms of the binomial formula leaves four linear
factors in the numerator and four in the denominator. -/
theorem ratio (n : ℕ) : a (n + 1) =
    (8 * ((n : ℚ) + 2) * (2 * n + 1) * (4 * n + 3) * (4 * n + 5)) /
    (3 * ((n : ℚ) + 1) ^ 2 * (3 * n + 4) * (3 * n + 5)) * a n := by
  rw [factorial_form (n + 1), factorial_form n]
  rw [show 4 * (n + 1) + 1 = (4 * n + 1) + 1 + 1 + 1 + 1 by omega,
      show 3 * (n + 1) + 2 = (3 * n + 2) + 1 + 1 + 1 by omega]
  simp only [factorial_step]
  push_cast
  field_simp
  ring

end OMA.A026005Proof

open OMA.S_oeis_a026005 OMA.A026005Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a026005.main := by
  intro k
  dsimp only
  rw [show k + 2 = (k + 1) + 1 by omega, ratio (k + 1), ratio k]
  push_cast
  field_simp
  ring
