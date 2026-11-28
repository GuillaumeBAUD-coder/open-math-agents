import OMAReductions.R_HyperperfectNumber_minoli_bear_hyperperfect_conjecture_R1

/-!
Step `HyperperfectNumber.minoli_bear_hyperperfect_conjecture.R1.H3`: a 3-hyperperfect number exists.
Witness: `325`, checked by the upstream finite computation `isHyperperfect_small_examples`.
-/

theorem OMA.solution : OMA.R_HyperperfectNumber_minoli_bear_hyperperfect_conjecture_R1.H3 :=
  ⟨325, HyperperfectNumber.isHyperperfect_small_examples.2.2.2⟩
