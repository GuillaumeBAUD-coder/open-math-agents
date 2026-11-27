import OMAReductions.R_OeisA7013_conjecture_R1
import Mathlib

-- Step OeisA7013.conjecture.R1.H1: hypothesis H1 of reduction OeisA7013.conjecture.R1
-- Credit: @ivillar. The first five Catalan-Mersenne numbers 2, 3, 7, 127 and 2^127 - 1 are prime;
-- the last one by the Lucas-Lehmer test (Mathlib's lucas_lehmer_sufficiency and its norm_num extension).

/-! The five known Catalan-Mersenne primes. -/

theorem OMA.solution : OMA.R_OeisA7013_conjecture_R1.H1 := by
  unfold OMA.R_OeisA7013_conjecture_R1.H1
  intro n hn
  interval_cases n
  · show Nat.Prime 2
    norm_num
  · show Nat.Prime 3
    norm_num
  · show Nat.Prime 7
    norm_num
  · show Nat.Prime 127
    norm_num
  · have h4 : OeisA7013.a 4 = mersenne 127 := by decide
    rw [h4]
    exact lucas_lehmer_sufficiency 127 (by norm_num) (by norm_num)
