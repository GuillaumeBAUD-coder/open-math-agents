import OMAStatements.S_oeis_a127769
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a127769.main := by
  intro t
  simp only [OMA.S_oeis_a127769.term]
  have h1 : (4 * (t + 1) + 2).factorial = (4*t+6)*(4*t+5)*(4*t+4)*(4*t+3)*(4*t+2).factorial := by
    rw [show 4 * (t + 1) + 2 = (4*t+2) + 1 + 1 + 1 + 1 by ring]
    simp only [Nat.factorial_succ]; ring
  have h2 : (2 * (t + 1) + 3).factorial = (2*t+5)*(2*t+4)*(2*t+3).factorial := by
    rw [show 2 * (t + 1) + 3 = (2*t+3) + 1 + 1 by ring]
    simp only [Nat.factorial_succ]; ring
  have h3 : (2 * (t + 1)).factorial = (2*t+2)*(2*t+1)*(2*t).factorial := by
    rw [show 2 * (t + 1) = (2*t) + 1 + 1 by ring]
    simp only [Nat.factorial_succ]; ring
  rw [h1, h2, h3]
  have p1 : ((2*t+3).factorial : ℚ) ≠ 0 := by positivity
  have p2 : ((2*t).factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring
