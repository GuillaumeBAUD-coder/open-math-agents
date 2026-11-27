import OMAReductions.R_Erdos399_erdos_399_variants_sum_two_squares_R1

theorem OMA.solution : OMA.R_Erdos399_erdos_399_variants_sum_two_squares_R1.H1 := by
  have windows : ∀ k : Fin 101, 7 ≤ k.val → ∃ q : Fin 101,
      q.val.Prime ∧ q.val % 4 = 3 ∧ k.val < 2 * q.val ∧ q.val ≤ k.val := by decide +kernel
  intro n low high
  obtain ⟨q, prime, residue, twice, upper⟩ := windows ⟨n, by omega⟩ low
  exact ⟨q.val, prime, residue, twice, upper⟩
