import OMAReductions.R_OeisA249609_conjecture_R1

/-! Kernel decisions verify each of the five specified Pascal rows. -/

theorem OMA.solution : OMA.R_OeisA249609_conjecture_R1.H1 := by
  intro n hn
  change n ∈ ({0, 1, 2, 7, 8} : Finset ℕ) at hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide
