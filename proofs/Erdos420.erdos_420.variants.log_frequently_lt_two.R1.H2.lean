import OMAReductions.R_Erdos420_erdos_420_variants_log_frequently_lt_two_R1

/-! Monotonicity of the divisor quotient: a longer shift gives a factorial that the shorter
one divides, hence at least as many divisors. -/

theorem OMA.solution : OMA.R_Erdos420_erdos_420_variants_log_frequently_lt_two_R1.H2 := by
  intro f g n hfg
  have h0 : (0 : ℝ) < (ArithmeticFunction.sigma 0 n.factorial : ℝ) := by
    exact_mod_cast ArithmeticFunction.sigma_pos 0 _ (Nat.factorial_ne_zero n)
  unfold Erdos420.F
  apply div_le_div_of_nonneg_right _ h0.le
  simp only [ArithmeticFunction.sigma_zero_apply]
  exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd (Nat.factorial_ne_zero _)
    (Nat.factorial_dvd_factorial (Nat.add_le_add_left (Nat.floor_le_floor hfg) n)))
