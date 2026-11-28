import OMAReductions.R_HyperperfectNumber_minoli_bear_hyperperfect_conjecture_R1

/-!
Step `HyperperfectNumber.minoli_bear_hyperperfect_conjecture.R1.H2`: a 2-hyperperfect number exists.
Witness: `21`, checked by the upstream finite computation `isHyperperfect_small_examples`.
-/

theorem OMA.solution : OMA.R_HyperperfectNumber_minoli_bear_hyperperfect_conjecture_R1.H2 :=
  ⟨21, HyperperfectNumber.isHyperperfect_small_examples.2.2.1⟩
