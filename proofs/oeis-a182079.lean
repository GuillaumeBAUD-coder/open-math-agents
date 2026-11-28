import OMAStatements.S_oeis_a182079
import Mathlib

namespace A182079Proof
open OMA.S_oeis_a182079

lemma a_int (n : ℕ) : a n = ((n : ℤ) * (((n : ℤ) - 1) / 2)) / 3 := by
  unfold a
  have h1 : ⌊((n : ℚ) - 1) / 2⌋ = ((n : ℤ) - 1) / 2 := by
    have h := Rat.floor_intCast_div_natCast ((n : ℤ) - 1) 2
    push_cast at h
    exact h
  rw [h1]
  have h2 := Rat.floor_intCast_div_natCast ((n : ℤ) * (((n : ℤ) - 1) / 2)) 3
  push_cast at h2
  exact h2

lemma a_shift (n : ℕ) :
    a (n + 6) = a n + ((n : ℤ) + 2 * (((n : ℤ) - 1) / 2) + 6) := by
  rw [a_int, a_int]
  push_cast
  have hM : ((n : ℤ) + 6 - 1) / 2 = ((n : ℤ) - 1) / 2 + 3 := by omega
  rw [hM]
  have hprod : ((n : ℤ) + 6) * (((n : ℤ) - 1) / 2 + 3)
      = (n : ℤ) * (((n : ℤ) - 1) / 2) + 3 * ((n : ℤ) + 2 * (((n : ℤ) - 1) / 2) + 6) := by
    ring
  rw [hprod, Int.add_mul_ediv_left _ _ (by norm_num)]

lemma v0 : a 0 = 0 := by rw [a_int]; norm_num
lemma v1 : a 1 = 0 := by rw [a_int]; norm_num
lemma v2 : a 2 = 0 := by rw [a_int]; norm_num
lemma v3 : a 3 = 1 := by rw [a_int]; norm_num
lemma v4 : a 4 = 1 := by rw [a_int]; norm_num
lemma v5 : a 5 = 3 := by rw [a_int]; norm_num
lemma v6 : a 6 = 4 := by rw [a_int]; norm_num
lemma v7 : a 7 = 7 := by rw [a_int]; norm_num
lemma v8 : a 8 = 8 := by rw [a_int]; norm_num

end A182079Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a182079.main := by
  have e : ∀ A : PowerSeries ℤ,
      A * ((1 - PowerSeries.X) ^ 3 * (1 + PowerSeries.X) ^ 2
          * (PowerSeries.X ^ 2 - PowerSeries.X + 1) * (PowerSeries.X ^ 2 + PowerSeries.X + 1))
        = A - A * PowerSeries.X ^ 1 - A * PowerSeries.X ^ 2 + A * PowerSeries.X ^ 3
          - A * PowerSeries.X ^ 6 + A * PowerSeries.X ^ 7 + A * PowerSeries.X ^ 8
          - A * PowerSeries.X ^ 9 := by
    intro A
    ring
  have r : (PowerSeries.X ^ 3 * (PowerSeries.X ^ 4 + PowerSeries.X ^ 3 + PowerSeries.X ^ 2 + 1) :
      PowerSeries ℤ)
      = PowerSeries.X ^ 7 + PowerSeries.X ^ 6 + PowerSeries.X ^ 5 + PowerSeries.X ^ 3 := by
    ring
  rw [e, r]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow,
    PowerSeries.coeff_mk]
  rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ 9 ≤ n
    by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
  · norm_num [A182079Proof.v0]
  · norm_num [A182079Proof.v0, A182079Proof.v1]
  · norm_num [A182079Proof.v0, A182079Proof.v1, A182079Proof.v2]
  · norm_num [A182079Proof.v0, A182079Proof.v1, A182079Proof.v2, A182079Proof.v3]
  · norm_num [A182079Proof.v1, A182079Proof.v2, A182079Proof.v3, A182079Proof.v4]
  · norm_num [A182079Proof.v2, A182079Proof.v3, A182079Proof.v4, A182079Proof.v5]
  · norm_num [A182079Proof.v0, A182079Proof.v3, A182079Proof.v4, A182079Proof.v5,
      A182079Proof.v6]
  · norm_num [A182079Proof.v0, A182079Proof.v1, A182079Proof.v4, A182079Proof.v5,
      A182079Proof.v6, A182079Proof.v7]
  · norm_num [A182079Proof.v0, A182079Proof.v1, A182079Proof.v2, A182079Proof.v5,
      A182079Proof.v6, A182079Proof.v7, A182079Proof.v8]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
    have e1 : m + 9 - 1 = m + 8 := by omega
    have e2 : m + 9 - 2 = m + 7 := by omega
    have e3 : m + 9 - 3 = m + 6 := by omega
    have e6 : m + 9 - 6 = m + 3 := by omega
    have e7 : m + 9 - 7 = m + 2 := by omega
    have e8 : m + 9 - 8 = m + 1 := by omega
    have e9 : m + 9 - 9 = m := by omega
    rw [if_pos (show 1 ≤ m + 9 by omega), if_pos (show 2 ≤ m + 9 by omega),
      if_pos (show 3 ≤ m + 9 by omega), if_pos (show 6 ≤ m + 9 by omega),
      if_pos (show 7 ≤ m + 9 by omega), if_pos (show 8 ≤ m + 9 by omega),
      if_pos (show 9 ≤ m + 9 by omega), if_neg (show ¬ m + 9 = 7 by omega),
      if_neg (show ¬ m + 9 = 6 by omega), if_neg (show ¬ m + 9 = 5 by omega),
      if_neg (show ¬ m + 9 = 3 by omega), e1, e2, e3, e6, e7, e8, e9]
    have s0 := A182079Proof.a_shift m
    have s1 := A182079Proof.a_shift (m + 1)
    have s2 := A182079Proof.a_shift (m + 2)
    have s3 := A182079Proof.a_shift (m + 3)
    rw [show m + 1 + 6 = m + 7 from rfl] at s1
    rw [show m + 2 + 6 = m + 8 from rfl] at s2
    rw [show m + 3 + 6 = m + 9 from rfl] at s3
    push_cast at s0 s1 s2 s3
    omega
