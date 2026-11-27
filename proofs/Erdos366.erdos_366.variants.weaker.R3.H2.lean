import OMAReductions.R_Erdos366_erdos_366_variants_weaker_R3

-- Step Erdos366.erdos_366.variants.weaker.R3.H2: hypothesis H2 of reduction Erdos366.erdos_366.variants.weaker.R3
-- Credit: @JamesSlash. For p = 2: 32 divides 4 m, so 8 divides m. For an odd prime p of m: p divides D z^3,
-- hence p divides z (directly or by the local condition on D), so p^3 divides 4 m and, being odd, p^3 divides m.

theorem OMA.solution : OMA.R_Erdos366_erdos_366_variants_weaker_R3.H2 := by
  intro D z m hD hm h4 h32 hloc p hp
  obtain ⟨hpr, hpm, -⟩ := Nat.mem_primeFactors.mp hp
  by_cases h2 : p = 2
  · subst h2
    rw [← h4] at h32
    have h8 : 8 ∣ m := by omega
    norm_num
    exact h8
  · have hpDz : p ∣ D * z ^ 3 := h4 ▸ dvd_mul_of_dvd_right hpm 4
    have hpz : p ∣ z := by
      rcases (Nat.Prime.dvd_mul hpr).mp hpDz with h | h
      · exact hloc p (Nat.mem_primeFactors.mpr ⟨hpr, h, hD.ne'⟩) h2
      · exact hpr.dvd_of_dvd_pow h
    have h3 : p ^ 3 ∣ 4 * m := h4 ▸ dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hpz 3) D
    have hcop : Nat.Coprime (p ^ 3) 4 := by
      apply Nat.Coprime.pow_left
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      apply Nat.Coprime.pow_right
      exact (Nat.coprime_primes hpr Nat.prime_two).mpr h2
    exact hcop.dvd_of_dvd_mul_left h3
