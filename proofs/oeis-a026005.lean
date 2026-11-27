import OMAStatements.S_oeis_a026005
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a026005.main := by
  intro k
  dsimp only
  unfold OMA.S_oeis_a026005.a
  rw [Nat.cast_choose ℚ (by omega : k + 2 ≤ 4 * (k + 2) + 1),
    Nat.cast_choose ℚ (by omega : k + 1 ≤ 4 * (k + 1) + 1), Nat.cast_choose ℚ (by omega : k ≤ 4 * k + 1)]
  rw [show 4 * (k + 2) + 1 - (k + 2) = 3 * k + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega,
    show 4 * (k + 1) + 1 - (k + 1) = 3 * k + 1 + 1 + 1 + 1 by omega,
    show 4 * k + 1 - k = 3 * k + 1 by omega,
    show 4 * (k + 2) + 1 = 4 * k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by ring,
    show 4 * (k + 1) + 1 = 4 * k + 1 + 1 + 1 + 1 + 1 by ring,
    show k + 2 = k + 1 + 1 by ring]
  simp only [Nat.factorial_succ]
  push_cast
  have h1 : ((4 * k).factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((3 * k).factorial : ℚ) ≠ 0 := by positivity
  have h3 : (k.factorial : ℚ) ≠ 0 := by positivity
  have h4 : (3 * (k : ℚ) + 2) ≠ 0 := by positivity
  have h5 : (3 * ((k : ℚ) + 1) + 2) ≠ 0 := by positivity
  have h6 : (3 * ((k : ℚ) + 1 + 1) + 2) ≠ 0 := by positivity
  have h7 : ((4 * k + 1).factorial : ℚ) ≠ 0 := by positivity
  have h8 : ((3 * k + 1).factorial : ℚ) ≠ 0 := by positivity
  field_simp
  ring
