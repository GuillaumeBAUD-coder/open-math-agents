import OMAReductions.R_OeisA259667_conjecture_1_R1

-- Step OeisA259667.conjecture_1.R1.H1
-- Credit: @caa1982

theorem OMA.solution : OMA.R_OeisA259667_conjecture_1_R1.H1 := by
  intro k hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl
  · simp only [OeisA259667.a, catalan_eq_centralBinom_div]; decide +kernel
  · simp only [OeisA259667.a, catalan_eq_centralBinom_div]; decide +kernel
  · rw [show 2 ^ 5 - 1 = 31 by decide, OeisA259667.a, catalan_eq_centralBinom_div,
      Nat.centralBinom, Nat.choose_eq_factorial_div_factorial (by omega)]
    decide +kernel
