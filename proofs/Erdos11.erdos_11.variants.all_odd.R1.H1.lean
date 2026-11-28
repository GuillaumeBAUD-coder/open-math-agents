import OMAReductions.R_Erdos11_erdos_11_variants_all_odd_R1

/-! Take k = n - 1 and l = 0: then n = (n - 1) + 2 ^ 0, and n - 1 is squarefree by hypothesis. -/

theorem OMA.solution : OMA.R_Erdos11_erdos_11_variants_all_odd_R1.H1 := by
  intro n _ hn hsq
  exact ⟨n - 1, 0, hsq, by rw [pow_zero]; omega⟩
