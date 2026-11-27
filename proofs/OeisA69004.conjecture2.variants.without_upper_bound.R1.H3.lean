import OMAReductions.R_OeisA69004_conjecture2_variants_without_upper_bound_R1

-- Step OeisA69004.conjecture2.variants.without_upper_bound.R1.H3: hypothesis H3 of reduction OeisA69004.conjecture2.variants.without_upper_bound.R1
-- Credit: @Ciphore
-- H3 := Nat.primeCounting 2 = OeisA69004.a 2 ∧ Nat.primeCounting 10 = OeisA69004.a 10 ∧     5 * OeisA69004.a 12 = Nat.primeCounting 12

set_option maxRecDepth 1000000 in
theorem OMA.solution : OMA.R_OeisA69004_conjecture2_variants_without_upper_bound_R1.H3 := by
  unfold OMA.R_OeisA69004_conjecture2_variants_without_upper_bound_R1.H3
  exact ⟨by decide, by decide, by decide⟩

