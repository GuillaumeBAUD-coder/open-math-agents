import OMAReductions.R_SternPrime_isSternPrime_iff_R1

-- Step SternPrime.isSternPrime_iff.R1.H2: hypothesis H2 of reduction SternPrime.isSternPrime_iff.R1
-- Credit: @Caliko06
-- H2 := ∀ q : ℕ, q ∈ ({2, 3, 17, 137, 227, 977, 1187, 1493} : Set ℕ) →     SternPrime.IsSternPrime q

theorem OMA.solution : OMA.R_SternPrime_isSternPrime_iff_R1.H2 := by
  intro q hq
  apply SternPrime.isSternPrime_known_examples q
  simpa using hq

