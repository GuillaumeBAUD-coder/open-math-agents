import OMAReductions.R_KaplanskyUInvariant_u_invariant_values_variants_kaplansky_conjecture_R1

-- Step KaplanskyUInvariant.u_invariant_values.variants.kaplansky_conjecture.R1.H2: hypothesis H2 of
-- reduction KaplanskyUInvariant.u_invariant_values.variants.kaplansky_conjecture.R1 (PR 9865)
-- Credit: @JamesSlash. 9 is odd and differs from 2^0 = 1.

theorem OMA.solution :
    OMA.R_KaplanskyUInvariant_u_invariant_values_variants_kaplansky_conjecture_R1.H2 := by
  intro k hk
  rcases k with _ | k
  · norm_num at hk
  · rw [pow_succ] at hk
    omega
