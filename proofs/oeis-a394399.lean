import OMAStatements.S_oeis_a394399

lemma geom_mod_two {p : ℕ} (hp : p % 2 = 1) (e : ℕ) :
    (∑ i ∈ Finset.range (e + 1), p ^ i) % 2 = (e + 1) % 2 := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih, Nat.pow_mod, hp, one_pow]
    omega

lemma sq_or_twice_sq_of_sigma_odd :
    ∀ n : ℕ, Odd (ArithmeticFunction.sigma 1 n) → ∃ m : ℕ, n = m ^ 2 ∨ n = 2 * m ^ 2 := by
  intro n
  induction n using Nat.recOnPrimeCoprime with
  | zero => intro _; exact ⟨0, Or.inl (by simp)⟩
  | prime_pow p e hp =>
    intro h
    rw [ArithmeticFunction.sigma_one_apply_prime_pow hp] at h
    rcases hp.eq_two_or_odd with rfl | hpo
    · rcases Nat.even_or_odd' e with ⟨t, rfl | rfl⟩
      · exact ⟨2 ^ t, Or.inl (by ring)⟩
      · exact ⟨2 ^ t, Or.inr (by ring)⟩
    · have := geom_mod_two hpo e
      rw [Nat.odd_iff] at h
      rcases Nat.even_or_odd' e with ⟨t, rfl | rfl⟩
      · exact ⟨p ^ t, Or.inl (by ring)⟩
      · omega
  | coprime a b _ _ hab iha ihb =>
    intro h
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hab, Nat.odd_mul] at h
    obtain ⟨x, hx⟩ := iha h.1
    obtain ⟨y, hy⟩ := ihb h.2
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact ⟨x * y, Or.inl (by ring)⟩
    · exact ⟨x * y, Or.inr (by ring)⟩
    · exact ⟨x * y, Or.inr (by ring)⟩
    · exact ⟨2 * x * y, Or.inl (by ring)⟩

theorem OMA.solution : type_of% @OMA.S_oeis_a394399.main := by
  intro k ⟨hk1, hk2⟩ hg
  have hk3 : 3 ≤ k := by
    have := hk1.two_le
    omega
  -- k is even
  have hkev : k % 2 = 0 := by
    rcases hk1.eq_two_or_odd with h | h
    · have : k = 3 := by omega
      subst this; norm_num at hk2
    · omega
  -- sigma k is odd, since gcd is odd and 2 divides k
  have hsig : Odd (ArithmeticFunction.sigma 1 k) := by
    rw [Nat.odd_iff]
    by_contra hc
    have h2 : 2 ∣ Nat.gcd k (ArithmeticFunction.sigma 1 k) :=
      Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hkev) (Nat.dvd_of_mod_eq_zero (by omega))
    rw [hg] at h2
    norm_num at h2
  obtain ⟨m, hm | hm⟩ := sq_or_twice_sq_of_sigma_odd k hsig
  · exfalso
    subst hm
    have hm2 : 2 ≤ m := by
      by_contra h
      push Not at h
      interval_cases m <;> omega
    have hfac : m ^ 2 - 1 = (m - 1) * (m + 1) := by
      have : (m - 1) * (m + 1) = m ^ 2 - 1 := by
        obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        ring_nf
        omega
      exact this.symm
    rw [hfac] at hk1
    rcases Nat.prime_mul_iff.1 hk1 with ⟨_, h⟩ | ⟨_, h⟩
    · omega
    · have : m = 2 := by omega
      subst this
      rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two] at hg
      norm_num [Finset.sum_range_succ] at hg
  · exact ⟨m, hm⟩
