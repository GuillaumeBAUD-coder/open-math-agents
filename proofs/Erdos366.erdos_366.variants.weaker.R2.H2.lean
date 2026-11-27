import OMAReductions.R_Erdos366_erdos_366_variants_weaker_R2

-- Step Erdos366.erdos_366.variants.weaker.R2.H2: hypothesis H2 of reduction Erdos366.erdos_366.variants.weaker.R2
-- Credit: @ishaanzee
-- Proof: a prime dividing a^3 b^4 c^5 divides a, b or c, so its cube divides a^3, b^4 or c^5.

theorem OMA.solution : OMA.R_Erdos366_erdos_366_variants_weaker_R2.H2 := by
  unfold OMA.R_Erdos366_erdos_366_variants_weaker_R2.H2
  intro a b c _ _ _ p hp
  rw [Nat.mem_primeFactors] at hp
  obtain ⟨hpp, hpd, -⟩ := hp
  have hp' := hpp.prime
  rcases hp'.dvd_mul.1 hpd with h | h
  · rcases hp'.dvd_mul.1 h with h | h
    · have ha := hp'.dvd_of_dvd_pow h
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (pow_dvd_pow_of_dvd ha 3) _) _
    · have hb := hp'.dvd_of_dvd_pow h
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left
        ((pow_dvd_pow p (by norm_num : 3 ≤ 4)).trans (pow_dvd_pow_of_dvd hb 4)) _) _
  · have hc := hp'.dvd_of_dvd_pow h
    exact Dvd.dvd.mul_left ((pow_dvd_pow p (by norm_num : 3 ≤ 5)).trans (pow_dvd_pow_of_dvd hc 5)) _
