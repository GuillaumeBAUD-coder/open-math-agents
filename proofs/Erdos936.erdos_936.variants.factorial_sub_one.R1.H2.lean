import OMAReductions.R_Erdos936_erdos_936_variants_factorial_sub_one_R1

-- Shortens the factorial/primorial comparison by @Raimo33, adapted from the add-one case.
-- The constant-multiple limit argument also appears in PR #32702; PR #36758 was consulted.

theorem OMA.solution : OMA.R_Erdos936_erdos_936_variants_factorial_sub_one_R1.H2 := by
  intro C e
  have h := (FloorSemiring.tendsto_pow_div_factorial_atTop ((4 : ℝ) ^ e)).const_mul (C : ℝ)
  filter_upwards [h.eventually_lt_const (by simp : (C : ℝ) * 0 < 1)] with n hn
  rw [← mul_div_assoc, div_lt_one (by positivity)] at hn
  have hp := Nat.pow_le_pow_left (primorial_le_four_pow n) e
  rw [← pow_mul, mul_comm n e, pow_mul] at hp
  have hlt : C * (4 ^ e) ^ n < n.factorial := by exact_mod_cast hn
  exact (Nat.mul_le_mul_left C hp).trans_lt hlt
