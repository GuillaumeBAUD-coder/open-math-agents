import OMAReductions.R_Erdos436_erdos_436_variants_three_two_R1
theorem OMA.solution : OMA.R_Erdos436_erdos_436_variants_three_two_R1.H1 := fun w => by
  obtain ⟨n, h, e⟩ : ∃ n ∈ [1, 5, 6, 7, 8, 11, 12, 14, 20, 21, 25, 27, 63, 77],
      (n.primeFactorsList.map w).sum = 0 ∧ ((n + 1).primeFactorsList.map w).sum = 0 := by
    simp [Nat.primeFactorsList_ofNat]
    generalize w 2 = a, w 3 = b, w 5 = c, w 7 = d, w 11 = e, w 13 = f
    revert a b c d e f
    set_option synthInstance.maxSize 999 in decide +kernel
  exact ⟨n, Finset.mem_Icc.2 (by simp at h; omega), e⟩
