import OMAReductions.R_Erdos963_erdos_963_variants_positive_R1

/-! With at most one element, Nat.log 2 A.card = 0, so the empty set (which is dissociated) works. -/

theorem OMA.solution : OMA.R_Erdos963_erdos_963_variants_positive_R1.H1 := by
  intro A _ hA
  refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
  · rw [Nat.log_of_lt (by omega)]
    exact Nat.zero_le _
  · simp
