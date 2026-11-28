import OMAReductions.R_Erdos687_erdos_687_parts_iii_R3_H1_R1

/-! For n ≥ C^24: if d^3 > n^2 then n^16 < d^24 = (d^8)^3 ≤ (C^8 n^5)^3 = C^24 n^15 ≤ n^16. -/

theorem OMA.solution : OMA.R_Erdos687_erdos_687_parts_iii_R3_H1_R1.H2 := by
  intro C
  filter_upwards [Filter.eventually_ge_atTop (C ^ 24)] with n hn
  intro d hd
  by_contra h
  push_neg at h
  have key : (n ^ 2) ^ 8 < (n ^ 2) ^ 8 := calc
    (n ^ 2) ^ 8 < (d ^ 3) ^ 8 := Nat.pow_lt_pow_left h (by norm_num)
    _ = (d ^ 8) ^ 3 := by ring
    _ ≤ (C ^ 8 * n ^ 5) ^ 3 := Nat.pow_le_pow_left hd 3
    _ = C ^ 24 * n ^ 15 := by ring
    _ ≤ n * n ^ 15 := Nat.mul_le_mul_right _ hn
    _ = (n ^ 2) ^ 8 := by ring
  exact lt_irrefl _ key
