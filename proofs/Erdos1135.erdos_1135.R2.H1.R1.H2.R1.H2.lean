import OMAReductions.R_Erdos1135_erdos_1135_R2_H1_R1_H2_R1
import Mathlib

-- Step Erdos1135.erdos_1135.R2.H1.R1.H2.R1.H2: hypothesis H2 of reduction Erdos1135.erdos_1135.R2.H1.R1.H2.R1
-- Credit: @Raimo33

theorem OMA.solution : OMA.R_Erdos1135_erdos_1135_R2_H1_R1_H2_R1.H2 := by
  intro n s hn hs
  rcases Nat.lt_or_ge s n with h | h
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + s := ⟨n - s, by omega⟩
    have hm : 1 ≤ m := by omega
    rw [Nat.add_sub_cancel]
    obtain ⟨N, hN⟩ : ∃ N, m + s - 2 = N := ⟨_, rfl⟩
    rw [show m + s - 2 + 2 * s = N + 2 * s by omega, hN]
    have h3 : m < 3 * N := by omega
    have hexp : (m+s)^6 = m^6 + 6*m^5*s + s^2*(15*m^4 + 20*m^3*s + 15*m^2*s^2+6*m*s^3+s^4) := by ring
    have hle : m^6 + 6*m^5*s ≤ (m+s)^6 := by rw [hexp]; exact Nat.le_add_right _ _
    have hpos : 0 < s * m^5 := by positivity
    have key : 2 * s * m^6 < 6 * m^5 * s * N := by
      have : s * m^5 * m < s * m^5 * (3 * N) := Nat.mul_lt_mul_of_pos_left h3 hpos
      nlinarith
    calc m ^ 6 * (N + 2 * s) = m^6 * N + 2 * s * m^6 := by ring
      _ < m^6 * N + 6 * m^5 * s * N := by omega
      _ = (m^6 + 6*m^5*s) * N := by ring
      _ ≤ (m+s)^6 * N := Nat.mul_le_mul_right _ hle
  · rw [Nat.sub_eq_zero_of_le h]
    simp only [zero_pow (by norm_num : 6 ≠ 0), zero_mul]
    have : 0 < n - 2 := by omega
    positivity
