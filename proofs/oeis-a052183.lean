import OMAStatements.S_oeis_a052183
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a052183.main := by
  intro t
  simp only [OMA.S_oeis_a052183.a]
  have h1 : (3 * (t + 1)).factorial = (3*t+3)*(3*t+2)*(3*t+1)*(3*t).factorial := by
    rw [show 3 * (t + 1) = 3*t + 1 + 1 + 1 by ring]; simp only [Nat.factorial_succ]; ring
  have h2 : (3 * (t + 2)).factorial =
      (3*t+6)*(3*t+5)*(3*t+4)*(3*t+3)*(3*t+2)*(3*t+1)*(3*t).factorial := by
    rw [show 3 * (t + 2) = 3*t + 1 + 1 + 1 + 1 + 1 + 1 by ring]; simp only [Nat.factorial_succ]; ring
  have h3 : (t + 1).factorial = (t+1)*t.factorial := Nat.factorial_succ t
  have h4 : (t + 2).factorial = (t+2)*(t+1)*t.factorial := by
    rw [show t + 2 = t + 1 + 1 by ring]; simp only [Nat.factorial_succ]; ring
  have h5 : (2 * (t + 1) + 1).factorial = (2*t+3)*(2*t+2)*(2*t+1).factorial := by
    rw [show 2 * (t + 1) + 1 = 2*t + 1 + 1 + 1 by ring]; simp only [Nat.factorial_succ]; ring
  have h6 : (2 * (t + 2) + 1).factorial = (2*t+5)*(2*t+4)*(2*t+3)*(2*t+2)*(2*t+1).factorial := by
    rw [show 2 * (t + 2) + 1 = 2*t + 1 + 1 + 1 + 1 + 1 by ring]; simp only [Nat.factorial_succ]; ring
  rw [h1, h2, h3, h4, h5, h6]
  have p1 : (t.factorial : ℚ) ≠ 0 := by positivity
  have p2 : ((2*t+1).factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring
