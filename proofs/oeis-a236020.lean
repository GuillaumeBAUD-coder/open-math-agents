import OMAStatements.S_oeis_a236020

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a236020.main) := by
  intro h
  have h5 : (Nat.divisors 5).card = 2 ∧ ArithmeticFunction.sigma 1 5 = 6 := by
    refine ⟨by decide, ?_⟩
    rw [ArithmeticFunction.sigma_one_apply]; decide
  have h22 : (Nat.divisors 22).card = 4 ∧ ArithmeticFunction.sigma 1 22 = 36 := by
    refine ⟨by decide, ?_⟩
    rw [ArithmeticFunction.sigma_one_apply]; decide
  have := h 5 22 (by norm_num) (by norm_num) (by
    simp only [OMA.S_oeis_a236020.k, h5.1, h5.2, h22.1, h22.2, Real.logb]
    push_cast
    rw [show (36 : ℝ) = 6 ^ 2 by norm_num, show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_pow, Real.log_pow]
    have : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    field_simp)
  omega
