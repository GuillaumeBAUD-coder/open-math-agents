import OMAStatements.S_oeis_a094047
import Mathlib

/-! A094047: Mathar's recurrence (n >= 6) follows from the defining recurrence at n, n-1, n-2:
it is h(n) + (n-3) h(n-1) + (4-n) h(n-2), after eliminating the factorial terms. -/

theorem OMA.solution : type_of% @OMA.S_oeis_a094047.main := by
  intro a _ _ _ hrec n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  have h0 := hrec (m + 6) (by omega)
  have h1 := hrec (m + 5) (by omega)
  have h2 := hrec (m + 4) (by omega)
  have e1 : m + 6 - 1 = m + 5 := by omega
  have e2 : m + 6 - 2 = m + 4 := by omega
  have e3 : m + 6 - 3 = m + 3 := by omega
  have e4 : m + 6 - 4 = m + 2 := by omega
  have f1 : m + 5 - 1 = m + 4 := by omega
  have f2 : m + 5 - 2 = m + 3 := by omega
  have f3 : m + 5 - 3 = m + 2 := by omega
  have g1 : m + 4 - 1 = m + 3 := by omega
  have g2 : m + 4 - 2 = m + 2 := by omega
  have g3 : m + 4 - 3 = m + 1 := by omega
  rw [e1, e2, e3] at h0
  rw [f1, f2, f3] at h1
  rw [g1, g2, g3] at h2
  rw [e1, e2, e3, e4]
  have k3 : ((m + 3).factorial : ℚ) = ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m + 1).factorial : ℚ) := by
    rw [show m + 3 = (m + 2) + 1 from rfl, Nat.factorial_succ, show m + 2 = (m + 1) + 1 from rfl,
      Nat.factorial_succ]
    push_cast; ring
  have k2 : ((m + 2).factorial : ℚ) = ((m : ℚ) + 2) * ((m + 1).factorial : ℚ) := by
    rw [show m + 2 = (m + 1) + 1 from rfl, Nat.factorial_succ]
    push_cast; ring
  rw [k3] at h0
  rw [k2] at h1
  have p0 : (-1 : ℚ) ^ (m + 6) = (-1) ^ m := by
    rw [pow_add]; norm_num
  have p1 : (-1 : ℚ) ^ (m + 5) = -(-1) ^ m := by
    rw [pow_add]; norm_num
  have p2 : (-1 : ℚ) ^ (m + 4) = (-1) ^ m := by
    rw [pow_add]; norm_num
  rw [p0] at h0
  rw [p1] at h1
  rw [p2] at h2
  push_cast at h0 h1 h2 ⊢
  linear_combination h0 + ((m : ℚ) + 6 - 3) * h1 + (4 - ((m : ℚ) + 6)) * h2
