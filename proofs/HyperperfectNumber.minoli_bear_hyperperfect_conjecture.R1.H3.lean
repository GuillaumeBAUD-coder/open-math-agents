import OMAReductions.R_HyperperfectNumber_minoli_bear_hyperperfect_conjecture_R1

-- Step HyperperfectNumber.minoli_bear_hyperperfect_conjecture.R1.H3: hypothesis H3 of
-- reduction HyperperfectNumber.minoli_bear_hyperperfect_conjecture.R1.
-- Explicit witness: `325 = 5 ^ 2 * 13` has proper divisor sum `1 + 5 + 13 + 25 + 65 = 109`, and
-- `1 + 3 * (109 - 1) = 325`, so `325` is `3`-hyperperfect.

theorem OMA.solution :
    OMA.R_HyperperfectNumber_minoli_bear_hyperperfect_conjecture_R1.H3 := by
  exact ⟨325, by decide⟩
