import OMAStatements.S_oeis_a251743

namespace OMA.S_oeis_a251743

theorem choose_pow (n : ℕ) : Nat.choose (2 ^ (n + 1)) 2 + 2 ^ n = 2 ^ n * 2 ^ (n + 1) := by
  rw [Nat.choose_two_right]
  have h : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
  have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  rw [h, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  obtain ⟨t, ht⟩ : ∃ t, 2 ^ n = t + 1 := ⟨2 ^ n - 1, by omega⟩
  rw [ht]
  have : 2 * (t + 1) - 1 = 2 * t + 1 := by omega
  rw [this]
  ring

theorem key (n : ℕ) : 3 * a n + 5 = 3 * 2 ^ n + 2 * 4 ^ n := by
  induction n with
  | zero => simp [a]
  | succ n ih =>
    have e : a (n + 1) = a n + (2 ^ (n + 1) + Nat.choose (2 ^ (n + 1)) 2) := by
      unfold a
      rw [Finset.sum_Icc_succ_top (by omega)]
    have hc := choose_pow n
    have h1 : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by ring
    have h2 : (4 : ℕ) ^ (n + 1) = 4 * 4 ^ n := by ring
    have h3 : (4 : ℕ) ^ n = 2 ^ n * 2 ^ n := by
      rw [← mul_pow]; norm_num
    rw [e, h2]
    rw [h1] at hc ⊢
    rw [h3] at ih ⊢
    nlinarith [ih, hc]

theorem gform (n : ℕ) : (a n : ℚ) = (3 * 2 ^ n + 2 * 4 ^ n - 5) / 3 := by
  have h := key n
  have h' : (3 * a n + 5 : ℚ) = 3 * 2 ^ n + 2 * 4 ^ n := by exact_mod_cast h
  linarith

theorem zform (n : ℕ) : (3 * a n + 5 : ℤ) = 3 * 2 ^ n + 2 * 4 ^ n := by exact_mod_cast key n

theorem coeffG (m : ℕ) : PowerSeries.coeff m G = (3 * 2 ^ m + 2 * 4 ^ m - 5) / 3 := by
  unfold G
  rw [PowerSeries.coeff_mk]
  split_ifs with h
  · subst h; norm_num
  · exact gform m

end OMA.S_oeis_a251743

open OMA.S_oeis_a251743 in
theorem OMA.solution : type_of% @OMA.S_oeis_a251743.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    rw [gform]
    have : (2 : ℚ) ^ (1 + 2 * n) = 2 * 4 ^ n := by
      rw [pow_add, pow_mul]; norm_num
    rw [this]
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have e1 : m + 4 - 1 = m + 3 := by omega
    have e2 : m + 4 - 2 = m + 2 := by omega
    have e3 : m + 4 - 3 = m + 1 := by omega
    have e4 : m + 4 - 4 = m := by omega
    rw [e1, e2, e3, e4]
    have z0 := zform m
    have z1 := zform (m + 1)
    have z2 := zform (m + 2)
    have z3 := zform (m + 3)
    have z4 := zform (m + 4)
    simp only [pow_succ] at z0 z1 z2 z3 z4
    linarith
  · have h8 : (PowerSeries.C (8 : ℚ)) = 8 := map_ofNat _ 8
    have h14 : (PowerSeries.C (14 : ℚ)) = 14 := map_ofNat _ 14
    have h7 : (PowerSeries.C (7 : ℚ)) = 7 := map_ofNat _ 7
    have h3 : (PowerSeries.C (3 : ℚ)) = 3 := map_ofNat _ 3
    have hL : G * ((PowerSeries.X - 1) * (2 * PowerSeries.X - 1) * (4 * PowerSeries.X - 1))
        = PowerSeries.C 8 * (G * PowerSeries.X ^ 3) - PowerSeries.C 14 * (G * PowerSeries.X ^ 2)
          + PowerSeries.C 7 * (G * PowerSeries.X ^ 1) - G := by
      rw [h8, h14, h7]; ring
    have hR : PowerSeries.X * (8 * PowerSeries.X - 3 : PowerSeries ℚ)
        = PowerSeries.C 8 * PowerSeries.X ^ 2 - PowerSeries.C 3 * PowerSeries.X ^ 1 := by
      rw [h8, h3]; ring
    rw [hL, hR]
    ext n
    simp only [map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_X_pow, coeffG]
    rcases n with _ | _ | _ | n
    · norm_num
    · norm_num
    · norm_num
    · simp only [show ¬ (n + 1 + 1 + 1 < 3) from by omega, show n + 1 + 1 + 1 - 3 = n from by omega,
        show n + 1 + 1 + 1 - 2 = n + 1 from by omega, show n + 1 + 1 + 1 - 1 = n + 2 from by omega]
      simp [PowerSeries.coeff_C, pow_succ]
      ring
