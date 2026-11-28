import OMAStatements.S_oeis_a383456
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a383456.main := by
  intro n
  have h1 : OMA.S_oeis_a383456.geodeColumn 1 n
      = OMA.S_oeis_a383456.hyperCoeff (n + 1) 1 - OMA.S_oeis_a383456.hyperCoeff (n + 2) 0 := by
    simp [OMA.S_oeis_a383456.geodeColumn]
  have e1 : 2 * n + 4 - n = n + 4 := by omega
  have e2 : 2 * (n + 1) + 3 * 1 = 2 * n + 4 + 1 := by ring
  have e3 : 1 + (n + 1) + 2 * 1 = n + 4 := by ring
  have e4 : 2 * (n + 2) + 3 * 0 = 2 * n + 4 := by ring
  have e5 : 1 + (n + 2) + 2 * 0 = n + 3 := by ring
  rw [h1, Nat.cast_choose ℚ (show n ≤ 2 * n + 4 by omega)]
  simp only [OMA.S_oeis_a383456.hyperCoeff, e1, e2, e3, e4, e5]
  have hn : (n.factorial : ℚ) ≠ 0 := by positivity
  have hm : ((2 * n + 4).factorial : ℚ) ≠ 0 := by positivity
  have f5 : ((2 * n + 4 + 1).factorial : ℚ) = (2 * (n : ℚ) + 5) * ((2 * n + 4).factorial : ℚ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have f1 : ((n + 1).factorial : ℚ) = ((n : ℚ) + 1) * (n.factorial : ℚ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have f2 : ((n + 2).factorial : ℚ) = ((n : ℚ) + 2) * ((n + 1).factorial : ℚ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have f3 : ((n + 3).factorial : ℚ) = ((n : ℚ) + 3) * ((n + 2).factorial : ℚ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have f4 : ((n + 4).factorial : ℚ) = ((n : ℚ) + 4) * ((n + 3).factorial : ℚ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [f5, f4, f3, f2, f1]
  simp only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, mul_one]
  field_simp
  ring
