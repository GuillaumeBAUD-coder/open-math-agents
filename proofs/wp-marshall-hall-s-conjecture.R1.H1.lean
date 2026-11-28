import OMAReductions.R_wp_marshall_hall_s_conjecture_R1
import Mathlib

/-! With `m = k³`, `y² - (k²)³ = (|y| - m)(|y| + m)`; if `|y| ≠ m` the first factor has absolute
value at least one and the second is at least `m`. -/

theorem OMA.solution : OMA.R_wp_marshall_hall_s_conjecture_R1.H1 := by
  intro k y hk hne
  have hm : 0 < k ^ 3 := by positivity
  have e : (k ^ 2) ^ 3 = (k ^ 3) ^ 2 := by ring
  rw [e] at hne ⊢
  have hy : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
  have ha := abs_nonneg y
  rcases lt_trichotomy |y| (k ^ 3) with h | h | h
  · rw [abs_sub_comm, abs_of_nonneg (by nlinarith)]
    nlinarith
  · exact absurd (by rw [hy, h]) hne
  · rw [abs_of_nonneg (by nlinarith)]
    nlinarith
