import OMAReductions.R_Erdos997_erdos_997_variants_irrational_R1_H1_R1

/-! Take the block to be the string itself: it has no bad index and k good ones. -/

theorem OMA.solution : OMA.R_Erdos997_erdos_997_variants_irrational_R1_H1_R1.H2 := by
  rintro good k hk ⟨m, hm⟩
  refine ⟨m, m + k, ?_⟩
  have h1 : (Finset.Ico m (m + k)).filter (fun i => good i = true) = Finset.Ico m (m + k) :=
    Finset.filter_true_of_mem hm
  have h2 : (Finset.Ico m (m + k)).filter (fun i => good i = false) = ∅ := by
    apply Finset.filter_false_of_mem
    intro i hi
    rw [hm i hi]
    simp
  rw [h1, h2, Finset.card_empty, Nat.card_Ico, zero_add, mul_one]
  omega
