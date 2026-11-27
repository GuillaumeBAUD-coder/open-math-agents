import OMAReductions.R_OeisA249609_conjecture_R1

-- Step OeisA249609.conjecture.R1.H1: hypothesis H1 of reduction OeisA249609.conjecture.R1
-- Credit: @ivillar
-- H1 := for n in {0, 1, 2, 7, 8}, every binomial coefficient C(n, m) with 1 <= m <= n is odious,
-- so the search in OeisA249609.a finds nothing and returns 0.
-- Proof: a finite computation, checked by the kernel for each of the five rows.

theorem OMA.solution : OMA.R_OeisA249609_conjecture_R1.H1 := by
  unfold OMA.R_OeisA249609_conjecture_R1.H1
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
