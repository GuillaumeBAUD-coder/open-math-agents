import OMAReductions.R_Erdos828_erdos_828_R1

theorem OMA.solution : OMA.R_Erdos828_erdos_828_R1.H1 := by
  intro a ha
  apply Set.infinite_of_forall_exists_gt
  intro bound
  rcases ha with rfl | ⟨m, hm, hdiv, rfl⟩
  · refine ⟨2 ^ (bound + 1), ?_, ?_⟩
    · change (((2 ^ (bound + 1) : ℕ).totient : ℕ) : ℤ) ∣
        ((2 ^ (bound + 1) : ℕ) : ℤ) + 0
      rw [add_zero, Nat.totient_prime_pow_succ Nat.prime_two, show (2 : ℕ) - 1 = 1 by decide,
        mul_one]
      exact_mod_cast (pow_dvd_pow (2 : ℕ) (Nat.le_succ bound))
    · exact (Nat.lt_succ_self bound).trans (bound + 1).lt_two_pow_self
  · obtain ⟨p, hpbound, hp⟩ := Nat.exists_infinite_primes (max bound m + 1)
    have hb : bound < p := by omega
    have hmp : m < p := by omega
    have hpd : ¬ p ∣ m := fun h => (Nat.le_of_dvd hm h).not_gt hmp
    refine ⟨p * m, ?_, hb.trans_le ?_⟩
    · change (((p * m).totient : ℕ) : ℤ) ∣ ((p * m : ℕ) : ℤ) + -(m : ℤ)
      have he : ((p * m : ℕ) : ℤ) + -(m : ℤ) = (((p - 1) * m : ℕ) : ℤ) := by
        push_cast [Nat.cast_sub hp.one_lt.le]
        ring
      rw [he, Nat.totient_mul_of_prime_of_not_dvd hp hpd]
      exact_mod_cast (mul_dvd_mul (dvd_refl (p - 1)) hdiv)
    · simpa using Nat.mul_le_mul_left p (show 1 ≤ m by omega)
