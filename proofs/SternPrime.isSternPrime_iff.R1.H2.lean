import OMAReductions.R_SternPrime_isSternPrime_iff_R1

set_option maxRecDepth 100000 in
theorem OMA.solution : OMA.R_SternPrime_isSternPrime_iff_R1.H2 := by
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact SternPrime.isSternPrime_known_examples _ (by decide)
