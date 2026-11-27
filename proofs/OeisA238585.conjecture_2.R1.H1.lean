import OMAReductions.R_OeisA238585_conjecture_2_R1

-- Step OeisA238585.conjecture_2.R1.H1: hypothesis H1 of reduction OeisA238585.conjecture_2.R1
-- Credit: @hayalows
--
-- The finite direction of conjecture (i): at each of the twelve listed indices exactly one
-- prime p < n makes prime(p)^2 + (prime(n) - 1)^2 prime. Each value is a direct kernel
-- computation of the defining sum over primes, so the whole step is discharged by
-- `decide +kernel` after splitting the membership hypothesis.

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
theorem OMA.solution : OMA.R_OeisA238585_conjecture_2_R1.H1 := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide +kernel
