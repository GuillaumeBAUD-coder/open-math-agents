import OMAReductions.R_Erdos205_erdos_205_variants_odd_counterexamples_R1

-- Step: Erdos205.erdos_205.variants.odd_counterexamples.R1.H2
-- Credit: @LordMike
-- Omega is monotone along divisibility: write b = a * c and use cardFactors_mul.

open scoped ArithmeticFunction.Omega

theorem OMA.solution : OMA.R_Erdos205_erdos_205_variants_odd_counterexamples_R1.H2 := by
  rintro a b hb ⟨c, rfl⟩
  have ha : a ≠ 0 := fun h => hb (by simp [h])
  have hc : c ≠ 0 := fun h => hb (by simp [h])
  rw [ArithmeticFunction.cardFactors_mul ha hc]
  omega
