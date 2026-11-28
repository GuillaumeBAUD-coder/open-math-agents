import OMAReductions.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1_H1_R1

-- The prime in the required range also witnesses the excluded existential.
theorem OMA.solution : OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1_H1_R1.H2 := by
  intro n _ _ _ _ _ _ hRange _ hExcluded
  obtain ⟨p, hp, hlo, hhi, hpn⟩ := hRange
  exact (hExcluded ⟨p, hp, hhi, by omega, by omega, by omega, hpn⟩).elim
