import OMAReductions.R_HyperperfectNumber_minoli_bear_hyperperfect_conjecture_R1

-- Step HyperperfectNumber.minoli_bear_hyperperfect_conjecture.R1.H1: hypothesis H1 of
-- reduction HyperperfectNumber.minoli_bear_hyperperfect_conjecture.R1.
-- `IsHyperperfect 1 n` is `Nat.Perfect n`, so the perfect number `6` is a witness.

theorem OMA.solution :
    OMA.R_HyperperfectNumber_minoli_bear_hyperperfect_conjecture_R1.H1 := by
  exact ⟨6, by decide⟩
