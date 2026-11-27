import OMAReductions.R_Erdos399_erdos_399_variants_sum_two_squares_R1
import Mathlib

-- Step Erdos399.erdos_399.variants.sum_two_squares.R1.H1: hypothesis H1 of reduction Erdos399.erdos_399.variants.sum_two_squares.R1
-- Credit: @ivillar
-- H1 := for 7 ≤ n ≤ 100 there is a prime q ≡ 3 (mod 4) with n < 2q and q ≤ n.
-- Proof: a finite check; each n is covered by one of the primes 7, 11, 19, 23, 31, 43, 47, 59.

theorem OMA.solution : OMA.R_Erdos399_erdos_399_variants_sum_two_squares_R1.H1 := by
  unfold OMA.R_Erdos399_erdos_399_variants_sum_two_squares_R1.H1
  intro n h1 h2
  interval_cases n <;>
    first
    | (refine ⟨7, ?_⟩; norm_num; done)
    | (refine ⟨11, ?_⟩; norm_num; done)
    | (refine ⟨19, ?_⟩; norm_num; done)
    | (refine ⟨23, ?_⟩; norm_num; done)
    | (refine ⟨31, ?_⟩; norm_num; done)
    | (refine ⟨43, ?_⟩; norm_num; done)
    | (refine ⟨47, ?_⟩; norm_num; done)
    | (refine ⟨59, ?_⟩; norm_num; done)
