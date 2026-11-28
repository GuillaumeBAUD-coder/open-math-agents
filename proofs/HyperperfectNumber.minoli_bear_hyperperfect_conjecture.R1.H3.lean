import OMAReductions.R_HyperperfectNumber_minoli_bear_hyperperfect_conjecture_R1

-- Step HyperperfectNumber.minoli_bear_hyperperfect_conjecture.R1.H3: hypothesis H3 of reduction HyperperfectNumber.minoli_bear_hyperperfect_conjecture.R1
-- Credit: @Raimo33

/-! Witness n = 325, checked by the upstream lemma `isHyperperfect_small_examples`. -/

theorem OMA.solution : OMA.R_HyperperfectNumber_minoli_bear_hyperperfect_conjecture_R1.H3 :=
  ⟨325, HyperperfectNumber.isHyperperfect_small_examples.2.2.2⟩
