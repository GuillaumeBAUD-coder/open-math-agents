import OMAReductions.R_AgohGiuga_agoh_giuga_variants_giuga_R3

-- Step AgohGiuga.agoh_giuga.variants.giuga.R3.H1: hypothesis H1 of reduction AgohGiuga.agoh_giuga.variants.giuga.R3
-- Credit: @JamesSlash. From q D + m = m q k + 1 and m > 1 we get D < m k; with t = m k - D this gives q t = m - 1,
-- so 1 <= t < m and D = m (k - 1) + (m - t), hence D mod m = m - t and q (m - D mod m) = q t = m - 1.

theorem OMA.solution : OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R3.H1 := by
  intro m D q k hm hq h
  have hlt : q * D < q * (m * k) := by nlinarith
  have hDK : D < m * k := Nat.lt_of_mul_lt_mul_left hlt
  obtain ⟨t, ht⟩ : ∃ t, D + t = m * k := ⟨m * k - D, by omega⟩
  have e1 : q * D + q * t = m * q * k := by rw [← mul_add, ht]; ring
  have hqt : q * t + 1 = m := by linarith
  have ht1 : 1 ≤ t := by omega
  have htm : t < m := by nlinarith
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0; simp at ht; omega
    · exact hk0
  have hD : D = (m - t) + m * (k - 1) := by
    have : m * k = m * (k - 1) + m := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega]
      ring
    omega
  have hmod : D % m = m - t := by
    rw [hD, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  rw [hmod, show m - (m - t) = t by omega]
  omega
