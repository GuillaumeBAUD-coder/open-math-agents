import OMAReductions.R_SternPrime_isSternPrime_iff_R1

-- Step SternPrime.isSternPrime_iff.R1.H2: hypothesis H2 of reduction SternPrime.isSternPrime_iff.R1
-- Credit: @anmolspace
-- Proof: the eight listed numbers are Stern primes by the upstream kernel-checked lemma
-- SternPrime.isSternPrime_known_examples; only the set-to-list membership is converted here.

theorem OMA.solution : OMA.R_SternPrime_isSternPrime_iff_R1.H2 := by
  intro q hq
  apply SternPrime.isSternPrime_known_examples q
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
