import OMAReductions.R_Erdos969_erdos_969_variants_evelyn_linfoot_R1_H1_R1

-- Step Erdos969.erdos_969.variants.evelyn_linfoot.R1.H1.R1.H2: hypothesis H2 of reduction Erdos969.erdos_969.variants.evelyn_linfoot.R1.H1.R1
-- Credit: @loremcdmx
-- H2 := ∀ w : ℂ, 0 < w.re → w.re < 1 → w.im ≠ 0 →   riemannZeta w = 0 → riemannZeta (1 - w) = 0

theorem OMA.solution : OMA.R_Erdos969_erdos_969_variants_evelyn_linfoot_R1_H1_R1.H2 := by
  intro w hw0 hw1 _ hz
  have h1 : ∀ n : ℕ, w ≠ -n := by
    intro n h
    have := congrArg Complex.re h
    simp at this
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have h2 : w ≠ 1 := by
    intro h
    rw [h] at hw1
    simp at hw1
  rw [riemannZeta_one_sub h1 h2, hz, mul_zero]
