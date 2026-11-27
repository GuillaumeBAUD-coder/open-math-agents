import OMAReductions.R_OeisA237578_conjecture_2_R1

-- Step OeisA237578.conjecture_2.R1.H1: hypothesis H1 of reduction OeisA237578.conjecture_2.R1
-- Credit: @prophetlabs
-- H1 := ∀ n : ℕ, (n = 5 ∨ n = 8 ∨ n = 13) → OeisA237578.a n = 1
-- Proof: `a n` is a finite sum over `0 < k < n` of an indicator of `(π (k * n)).Prime`, so each of
-- the three values is a closed computation, checked by the kernel with `decide`.

set_option maxRecDepth 100000 in
theorem OMA.solution : OMA.R_OeisA237578_conjecture_2_R1.H1 := by
  intro n hn
  rcases hn with rfl | rfl | rfl
  · exact OeisA237578.a_5
  · decide
  · decide
