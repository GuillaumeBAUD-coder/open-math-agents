import OMAReductions.R_Erdos828_erdos_828_R1

-- Step Erdos828.erdos_828.R1.H1: hypothesis H1 of reduction Erdos828.erdos_828.R1
-- Credit: @ivillar
-- H1 := ∀ a : ℤ, (a = 0 ∨ ∃ m : ℕ, 0 < m ∧ Nat.totient m ∣ m ∧ a = -(m : ℤ)) →     Set.Infinite {n : ℕ | ((Nat.totient n : ℕ) : ℤ) ∣ (n : ℤ) + a}

namespace OMA.E828H1

/-- `a = 0`: every power of two `n = 2 ^ j` (with `j ≥ 1`) has `φ n = 2 ^ (j - 1) ∣ n`. -/
lemma powers_two : Set.Infinite {n : ℕ | ((Nat.totient n : ℕ) : ℤ) ∣ (n : ℤ) + 0} := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  have h : Nat.totient (2 ^ (B + 1)) ∣ 2 ^ (B + 1) := by
    rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos B), Nat.succ_sub_one]
    exact ⟨2, by rw [pow_succ]; norm_num⟩
  have hmem : 2 ^ (B + 1) ∈ {n : ℕ | ((Nat.totient n : ℕ) : ℤ) ∣ (n : ℤ) + 0} := by
    show ((Nat.totient (2 ^ (B + 1)) : ℕ) : ℤ) ∣ ((2 ^ (B + 1) : ℕ) : ℤ) + 0
    rw [add_zero]
    exact_mod_cast h
  have h1 := hB hmem
  have h2 : B + 1 < 2 ^ (B + 1) := Nat.lt_two_pow_self
  omega

/-- `a = -m` with `φ m ∣ m`: for every prime `p > m`, `n = m p` has
`φ n = φ m (p - 1) ∣ m (p - 1) = n - m`. -/
lemma case_m (m : ℕ) (hm : 0 < m) (hdvd : Nat.totient m ∣ m) :
    Set.Infinite {n : ℕ | ((Nat.totient n : ℕ) : ℤ) ∣ (n : ℤ) + -(m : ℤ)} := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (B + m + 1)
  have hcop : Nat.Coprime m p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    have := Nat.le_of_dvd hm h
    omega
  obtain ⟨t, ht⟩ := hdvd
  have hmem : m * p ∈ {n : ℕ | ((Nat.totient n : ℕ) : ℤ) ∣ (n : ℤ) + -(m : ℤ)} := by
    show ((Nat.totient (m * p) : ℕ) : ℤ) ∣ ((m * p : ℕ) : ℤ) + -(m : ℤ)
    rw [Nat.totient_mul hcop, Nat.totient_prime hp]
    refine ⟨t, ?_⟩
    have hp1 : 1 ≤ p := hp.one_lt.le
    have ht' : (m : ℤ) = (Nat.totient m : ℤ) * t := by exact_mod_cast ht
    push_cast [Nat.cast_sub hp1]
    linear_combination ((p : ℤ) - 1) * ht'
  have h1 := hB hmem
  have h2 : p ≤ m * p := by nlinarith
  omega

end OMA.E828H1

theorem OMA.solution : OMA.R_Erdos828_erdos_828_R1.H1 := by
  unfold OMA.R_Erdos828_erdos_828_R1.H1
  rintro a (rfl | ⟨m, hm, hdvd, rfl⟩)
  · exact OMA.E828H1.powers_two
  · exact OMA.E828H1.case_m m hm hdvd
