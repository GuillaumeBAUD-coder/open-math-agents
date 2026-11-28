import OMAReductions.R_HyperperfectNumber_minoli_bear_hyperperfect_conjecture_R1

/-!
Step `HyperperfectNumber.minoli_bear_hyperperfect_conjecture.R1.H1`: a 1-hyperperfect number exists.
Witness: `6`, checked by the upstream finite computation `isHyperperfect_small_examples`.
-/

theorem OMA.solution : OMA.R_HyperperfectNumber_minoli_bear_hyperperfect_conjecture_R1.H1 :=
  ⟨6, HyperperfectNumber.isHyperperfect_small_examples.1⟩
