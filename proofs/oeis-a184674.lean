import OMAStatements.S_oeis_a184674
import Mathlib

open OMA.S_oeis_a184674

theorem OMA.solution : type_of% @OMA.S_oeis_a184674.main := by
  intro n hn
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have e1 : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
    rw [a, b, e1]
    have hb : ⌊(((2 * j + 1 : ℕ) : ℚ) ^ 2 + 6 * ((2 * j + 1 : ℕ) : ℚ) + 1) / 4⌋ = ((j:ℤ) + 1) ^ 2 + 2 * (j + 1) - 1 := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> nlinarith
    have ha : ⌊(((2 * (j + 1) : ℕ) : ℚ) / 2 - 1 / (2 * ((2 * (j + 1) : ℕ) : ℚ))) ^ 2⌋ = ((j:ℤ) + 1) ^ 2 - 1 := by
      rw [Int.floor_eq_iff]; push_cast
      have hj : (0:ℚ) ≤ j := by positivity
      have : (2 * ((j:ℚ) + 1)) / 2 - 1 / (2 * (2 * ((j:ℚ) + 1))) = (j + 1) - 1 / (4 * (j + 1)) := by
        field_simp; ring
      rw [this]
      have h1 : 0 < 1 / (4 * ((j:ℚ) + 1)) := by positivity
      have h2 : 1 / (4 * ((j:ℚ) + 1)) ≤ 1 / 4 := by
        apply div_le_div_of_nonneg_left <;> nlinarith
      have h3 : ((j:ℚ) + 1) * (1 / (4 * ((j:ℚ) + 1))) = 1 / 4 := by field_simp
      constructor <;> nlinarith
    rw [hb, ha]; push_cast; ring
  · have e1 : 2 * k + 1 - 1 = 2 * k := by omega
    have hk : 1 ≤ k := by omega
    rw [a, b, e1]
    have hb : ⌊(((2 * k : ℕ) : ℚ) ^ 2 + 6 * ((2 * k : ℕ) : ℚ) + 1) / 4⌋ = (k:ℤ) ^ 2 + 3 * k := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> nlinarith
    have ha : ⌊(((2 * k + 1 : ℕ) : ℚ) / 2 - 1 / (2 * ((2 * k + 1 : ℕ) : ℚ))) ^ 2⌋ = (k:ℤ) ^ 2 + k - 1 := by
      rw [Int.floor_eq_iff]; push_cast
      have hj : (1:ℚ) ≤ k := by exact_mod_cast hk
      set e := 1 / (2 * (2 * (k:ℚ) + 1)) with he
      have h1 : 0 < e := by positivity
      have h2 : e ≤ 1 / 6 := by
        rw [he]; apply div_le_div_of_nonneg_left <;> nlinarith
      have h3 : (2 * (k:ℚ) + 1) * e = 1 / 2 := by rw [he]; field_simp
      have h4 : ((2 * (k:ℚ) + 1) / 2 - e) ^ 2 = (k:ℚ) ^ 2 + k - 1 / 4 + e ^ 2 := by
        nlinarith
      rw [h4]
      constructor <;> nlinarith
    rw [hb, ha]; push_cast; ring
