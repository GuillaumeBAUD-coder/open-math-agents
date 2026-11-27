import OMAReductions.R_Erdos828_erdos_828_R1

-- Step Erdos828.erdos_828.R1.H1: hypothesis H1 of reduction Erdos828.erdos_828.R1
-- Credit: @DeepDuke
-- H1 := ∀ a : ℤ, (a = 0 ∨ ∃ m : ℕ, 0 < m ∧ Nat.totient m ∣ m ∧ a = -(m : ℤ)) →     Set.Infinite {n : ℕ | ((Nat.totient n : ℕ) : ℤ) ∣ (n : ℤ) + a}  /-- The open cases: every other integer a. -/

theorem OMA.solution : OMA.R_Erdos828_erdos_828_R1.H1 := by
  intro a ha
  rcases ha with rfl | ⟨m, hm, hdiv, rfl⟩
  · apply Set.infinite_of_forall_exists_gt
    intro b
    refine ⟨2^(b+1), ?_, ?_⟩
    · change ((2^(b+1)).totient : ℤ) ∣ (2^(b+1) : ℕ)+0
      rw [Nat.totient_prime_pow_succ Nat.prime_two]
      norm_num
      exact_mod_cast (pow_dvd_pow (2 : ℕ) (Nat.le_succ b))
    · have h : b < 2^b := Nat.lt_two_pow_self
      have hh : 2^b ≤ 2^(b+1) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
  · apply Set.infinite_of_forall_exists_gt
    intro b
    obtain ⟨p, hpgt, hp⟩ := Nat.exists_infinite_primes (b+m+1)
    have hmp : m.Coprime p := (Nat.coprime_of_lt_prime hm.ne' (by omega) hp).symm
    have hd : (m*p).totient ∣ m*p-m := by
      rw [Nat.totient_mul hmp, Nat.totient_prime hp,
        show m*p-m = m*(p-1) by rw [Nat.mul_sub]; simp]
      exact Nat.mul_dvd_mul_right hdiv (p-1)
    refine ⟨m*p, ?_, ?_⟩
    · change ((m*p).totient : ℤ) ∣ (m*p : ℕ) + -(m : ℤ)
      have hb : m ≤ m*p := Nat.le_mul_of_pos_right _ hp.pos
      have hz : ((m*p).totient : ℤ) ∣ ((m*p-m : ℕ) : ℤ) := by exact_mod_cast hd
      simpa only [Int.natCast_sub hb, Nat.cast_mul, sub_eq_add_neg] using hz
    · have hh : p ≤ m*p := Nat.le_mul_of_pos_left p hm
      omega

