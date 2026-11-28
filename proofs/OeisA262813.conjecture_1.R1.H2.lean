import OMAReductions.R_OeisA262813_conjecture_1_R1

theorem OMA.solution : OMA.R_OeisA262813_conjecture_1_R1.H2 := by
  have : ∀ n < 90, 0 < n → ∃ x < 5, ∃ u < 27, ∃ v < 19, 3 ≤ u ∧ 8 * n + 1 = 8 * x ^ 3 + u ^ 2 + 2 * v ^ 2 := by
    decide +kernel
  intro n h0 h
  obtain ⟨x, -, u, -, v, -, h⟩ := this n h h0
  exact ⟨x, u, v, h⟩
