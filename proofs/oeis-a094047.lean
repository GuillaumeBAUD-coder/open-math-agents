import OMAStatements.S_oeis_a094047
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a094047.main := by
  intro a _ _ _ hrec n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  have e6 := hrec (m + 6) (by omega)
  have e5 := hrec (m + 5) (by omega)
  have e4 := hrec (m + 4) (by omega)
  have i1 : m + 6 - 1 = m + 5 := by omega
  have i2 : m + 6 - 2 = m + 4 := by omega
  have i3 : m + 6 - 3 = m + 3 := by omega
  have i4 : m + 6 - 4 = m + 2 := by omega
  have j1 : m + 5 - 1 = m + 4 := by omega
  have j2 : m + 5 - 2 = m + 3 := by omega
  have j3 : m + 5 - 3 = m + 2 := by omega
  have k1 : m + 4 - 1 = m + 3 := by omega
  have k2 : m + 4 - 2 = m + 2 := by omega
  have k3 : m + 4 - 3 = m + 1 := by omega
  rw [i1, i2, i3] at e6
  rw [j1, j2, j3] at e5
  rw [k1, k2, k3] at e4
  rw [i1, i2, i3, i4]
  have g2 : (m + 2).factorial = (m + 2) * (m + 1).factorial := Nat.factorial_succ (m + 1)
  have g3 : (m + 3).factorial = (m + 3) * (m + 2).factorial := Nat.factorial_succ (m + 2)
  have f2 : ((m + 2).factorial : ℚ) = ((m : ℚ) + 2) * ((m + 1).factorial : ℚ) := by
    rw [g2]; push_cast; ring
  have f3 : ((m + 3).factorial : ℚ) = ((m : ℚ) + 3) * (((m : ℚ) + 2) * ((m + 1).factorial : ℚ)) := by
    rw [g3, g2]; push_cast; ring
  have p6 : (-1 : ℚ) ^ (m + 6) = (-1) ^ m := by rw [pow_add]; norm_num
  have p5 : (-1 : ℚ) ^ (m + 5) = -(-1) ^ m := by rw [pow_add]; norm_num
  have p4 : (-1 : ℚ) ^ (m + 4) = (-1) ^ m := by rw [pow_add]; norm_num
  rw [f3, p6] at e6
  rw [f2, p5] at e5
  rw [p4] at e4
  push_cast at e6 e5 e4 ⊢
  linear_combination e6 + ((m : ℚ) + 3) * e5 - ((m : ℚ) + 2) * e4
