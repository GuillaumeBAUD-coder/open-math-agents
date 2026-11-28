import OMAStatements.S_oeis_a134357
import Mathlib

open OMA.S_oeis_a134357

theorem a134357_pos (n : ℕ) : 0 < a005156 n := by
  unfold a005156
  apply Finset.prod_pos
  intro k _
  positivity

theorem OMA.solution : type_of% @OMA.S_oeis_a134357.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hne : a005156 (m + 1) ≠ 0 := (a134357_pos _).ne'
  have hs : a005156 (m + 1 + 1) = a005156 (m + 1) *
      ((((3 * m + 2 : ℕ) : ℚ) * ((6 * m + 3).factorial : ℚ) * ((2 * m + 1).factorial : ℚ)) /
      (((4 * m + 2).factorial : ℚ) * ((4 * m + 3).factorial : ℚ))) := by
    simp only [a005156, show m + 1 + 1 - 1 = m + 1 from rfl, show m + 1 - 1 = m from rfl]
    rw [Finset.prod_range_succ]
  rw [hs, mul_div_cancel_left₀ _ hne]
  have c1 : ((6 * (m + 1) - 2).choose (2 * (m + 1)) : ℚ) =
      ((6 * m + 4).factorial : ℚ) / (((2 * m + 2).factorial : ℚ) * ((4 * m + 2).factorial : ℚ)) := by
    rw [show 6 * (m + 1) - 2 = 6 * m + 4 by omega, show 2 * (m + 1) = 2 * m + 2 by ring,
      Nat.cast_choose ℚ (by omega : 2 * m + 2 ≤ 6 * m + 4),
      show 6 * m + 4 - (2 * m + 2) = 4 * m + 2 by omega]
  have c2 : ((4 * (m + 1) - 1).choose (2 * (m + 1)) : ℚ) =
      ((4 * m + 3).factorial : ℚ) / (((2 * m + 2).factorial : ℚ) * ((2 * m + 1).factorial : ℚ)) := by
    rw [show 4 * (m + 1) - 1 = 4 * m + 3 by omega, show 2 * (m + 1) = 2 * m + 2 by ring,
      Nat.cast_choose ℚ (by omega : 2 * m + 2 ≤ 4 * m + 3),
      show 4 * m + 3 - (2 * m + 2) = 2 * m + 1 by omega]
  rw [c1, c2, show 6 * m + 4 = (6 * m + 3) + 1 by ring, Nat.factorial_succ]
  have f1 : ((2 * m + 2).factorial : ℚ) ≠ 0 := by positivity
  have f2 : ((4 * m + 2).factorial : ℚ) ≠ 0 := by positivity
  have f3 : ((4 * m + 3).factorial : ℚ) ≠ 0 := by positivity
  have f4 : ((2 * m + 1).factorial : ℚ) ≠ 0 := by positivity
  field_simp
  push_cast
  ring
