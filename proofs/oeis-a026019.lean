import OMAStatements.S_oeis_a026019
import Mathlib

open OMA.S_oeis_a026019 in
theorem OMA.solution : type_of% @OMA.S_oeis_a026019.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rcases k with _ | _ | _ | j
  iterate 3 norm_num [a, Nat.choose]
  have B (n : ℕ) : (2*(n+1)*(2*n+1) * (3*n+3).choose (n+1) : ℚ) = 3*(3*n+1)*(3*n+2) * (3*n).choose n := by
    rw [Nat.cast_choose ℚ (show n+1 ≤ 3*n+3 by omega), Nat.cast_choose ℚ (show n ≤ 3*n by omega),
      show 3*n+3-(n+1) = 2*n+2 by omega, show 3*n-n = 2*n by omega]
    simp [Nat.factorial_succ]
    field_simp
    ring
  have E (m : ℕ) : (2*m+7)*(2*m+8)*(2*m+9) * a (m+3) = (m+6)*(7*m^2+48*m+83) * (3*m+9).choose (m+3) := by
    simp only [a, if_pos (Nat.le_add_left 3 m), Nat.add_sub_cancel, mul_add]
    rw [Nat.cast_choose ℚ (show m+3 ≤ 3*m+3*3 by omega), Nat.cast_choose ℚ (show m ≤ 3*m+3*3 by omega),
      show 3*m+3*3-(m+3) = 2*m+6 by omega, show 3*m+3*3-m = 2*m+6+1+1+1 by omega]
    simp only [Nat.factorial_succ]
    push_cast
    field_simp
    ring
  have E3 := E j
  have E4 := E (j+1)
  have E5 := E (j+2)
  have B3 := B (j+3)
  have B4 := B (j+4)
  simp [add_assoc, mul_add] at *
  refine mul_left_cancel₀ (show ((2*j+7)*(2*j+8)*(2*j+9)*(2*j+10)*(2*j+11)*(2*j+12)*(2*j+13) : ℚ) ≠ 0 by positivity) ?_
  linear_combination (-2*(2*j+13)*(13*j+56)*(j+6)*((2*j+7)*(2*j+8)*(2*j+9)*(2*j+10)))*E5 + ((499*(j+5)^3-7*(j+5)^2-120*(j+5)-54)*((2*j+7)*(2*j+8)*(2*j+12)*(2*j+13)))*E4 + (-3*(3*j+10)*(37*j+161)*(3*j+11)*((2*j+10)*(2*j+11)*(2*j+12)*(2*j+13)))*E3 + (j+4)*(j+6)*(j+8)*(2*j+7)*(2*j+13)*(-364*j^3-5520*j^2-27788*j-46368)*B4 + (j+5)*(j+6)*(2*j+11)*(2*j+12)*(2*j+13)*(518*j^3+5806*j^2+21598*j+26726)*B3
