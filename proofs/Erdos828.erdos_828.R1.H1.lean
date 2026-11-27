import OMAReductions.R_Erdos828_erdos_828_R1

-- Credit: @jagong-cmu

namespace E828H1

theorem h1 : ∀ a : ℤ, (a = 0 ∨ ∃ m : ℕ, 0 < m ∧ Nat.totient m ∣ m ∧ a = -(m : ℤ)) →
    Set.Infinite {n : ℕ | ((Nat.totient n : ℕ) : ℤ) ∣ (n : ℤ) + a} := by
  intro a ha
  apply Set.infinite_of_forall_exists_gt
  intro B
  rcases ha with rfl | ⟨m, hm, hdvd, rfl⟩
  · refine ⟨2 ^ (B + 1), ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq, add_zero]
      have ht : Nat.totient (2 ^ (B + 1)) = 2 ^ B := by
        rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos B)]
        simp
      rw [ht]
      exact_mod_cast (pow_dvd_pow 2 (Nat.le_succ B))
    · calc B < 2 ^ B := Nat.lt_two_pow_self
        _ < 2 ^ (B + 1) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self B)
  · obtain ⟨p, hp1, hp⟩ := Nat.exists_infinite_primes (B + m + 1)
    have hpm : ¬ p ∣ m := fun h => by
      have := Nat.le_of_dvd hm h
      omega
    have hcop : Nat.Coprime m p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm).symm
    refine ⟨m * p, ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq]
      rw [Nat.totient_mul hcop, Nat.totient_prime hp]
      have hp0 : 1 ≤ p := hp.one_lt.le
      have e : ((m * p : ℕ) : ℤ) + -(m : ℤ) = (m : ℤ) * ((p - 1 : ℕ) : ℤ) := by
        push_cast [hp0]
        ring
      rw [e]
      push_cast [hp0]
      exact mul_dvd_mul (Int.natCast_dvd_natCast.2 hdvd) dvd_rfl
    · calc B < p := by omega
        _ ≤ m * p := Nat.le_mul_of_pos_left p hm

end E828H1


theorem OMA.solution : OMA.R_Erdos828_erdos_828_R1.H1 := E828H1.h1
