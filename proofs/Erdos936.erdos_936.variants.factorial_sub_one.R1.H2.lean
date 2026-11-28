import OMAReductions.R_Erdos936_erdos_936_variants_factorial_sub_one_R1

-- Shortens the factorial/primorial comparison by @Raimo33, adapted from the add-one case.
-- Uses the natural-number bound from @sebastianbachmaier's add-one proof, PR #9084.

theorem OMA.solution : OMA.R_Erdos936_erdos_936_variants_factorial_sub_one_R1.H2 := by
  intro C e
  filter_upwards [Nat.eventually_mul_pow_lt_factorial_sub C (4 ^ e) 0] with n hn
  refine lt_of_le_of_lt ?_ hn
  rw [← pow_mul, mul_comm e n, pow_mul]
  gcongr
  exact primorial_le_four_pow n
