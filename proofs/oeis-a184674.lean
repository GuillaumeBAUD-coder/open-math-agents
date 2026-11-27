import OMAStatements.S_oeis_a184674
import Mathlib

-- Problem: oeis-a184674
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P184674
open OMA.S_oeis_a184674

theorem sol : type_of% @OMA.S_oeis_a184674.main := by
  intro n hn
  unfold a b
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have hm : 1 ≤ m := by omega
    have e1 : ⌊(((m + m : ℕ) : ℚ) / 2 - 1 / (2 * ((m + m : ℕ) : ℚ))) ^ 2⌋ = (m : ℤ) ^ 2 - 1 := by
      rw [Int.floor_eq_iff]
      have hm' : (1 : ℚ) ≤ m := by exact_mod_cast hm
      push_cast
      constructor
      · have : ((m : ℚ) + m) / 2 - 1 / (2 * ((m : ℚ) + m)) = m - 1 / (4 * m) := by field_simp; ring
        rw [this]
        have h4 : 1 / (4 * (m : ℚ)) ≤ 1 / 4 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
        have hmt : (m : ℚ) * (1 / (4 * m)) = 1 / 4 := by field_simp
        have hp : (0 : ℚ) < 1 / (4 * m) := by positivity
        nlinarith [h4, hp, hmt]
      · have : ((m : ℚ) + m) / 2 - 1 / (2 * ((m : ℚ) + m)) = m - 1 / (4 * m) := by field_simp; ring
        rw [this]
        have hp : (0 : ℚ) < 1 / (4 * m) := by positivity
        have hmt : (m : ℚ) * (1 / (4 * m)) = 1 / 4 := by field_simp
        have h4 : 1 / (4 * (m : ℚ)) ≤ 1 / 4 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
        nlinarith [hp, hmt, h4]
    have e2 : ⌊((((m + m - 1 : ℕ) : ℚ)) ^ 2 + 6 * ((m + m - 1 : ℕ) : ℚ) + 1) / 4⌋ = (m : ℤ) ^ 2 + 2 * m - 1 := by
      rw [Int.floor_eq_iff, Nat.cast_sub (by omega)]
      push_cast
      constructor <;> nlinarith
    rw [e1, e2]; push_cast; ring
  · have hm : 1 ≤ m := by omega
    have e1 : ⌊((((2 * m + 1 : ℕ)) : ℚ) / 2 - 1 / (2 * (((2 * m + 1 : ℕ)) : ℚ))) ^ 2⌋ = (m : ℤ) ^ 2 + m - 1 := by
      rw [Int.floor_eq_iff]
      have hm' : (1 : ℚ) ≤ m := by exact_mod_cast hm
      push_cast
      have hx : ((2 * (m : ℚ) + 1) / 2 - 1 / (2 * (2 * (m : ℚ) + 1))) ^ 2
          = (m : ℚ) ^ 2 + m - 1 / 4 + 1 / (4 * (2 * (m : ℚ) + 1) ^ 2) := by field_simp; ring
      rw [hx]
      have hp : (0 : ℚ) < 1 / (4 * (2 * (m : ℚ) + 1) ^ 2) := by positivity
      have hs : 1 / (4 * (2 * (m : ℚ) + 1) ^ 2) ≤ 1 / 36 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
      constructor <;> push_cast <;> nlinarith
    have e2 : ⌊((((2 * m + 1 - 1 : ℕ) : ℚ)) ^ 2 + 6 * ((2 * m + 1 - 1 : ℕ) : ℚ) + 1) / 4⌋ = (m : ℤ) ^ 2 + 3 * m := by
      rw [Int.floor_eq_iff, show 2 * m + 1 - 1 = 2 * m by omega]
      push_cast
      constructor <;> nlinarith
    rw [e1, e2]; push_cast; ring

end OMA.P184674

theorem OMA.solution : type_of% @OMA.S_oeis_a184674.main := OMA.P184674.sol
