import OMAStatements.S_oeis_a259145

-- Problem oeis-a259145: if k^2 - phi(k) is prime then k and phi(k) are coprime.
-- Upstream: statements/oeis-a259145.lean (declaration OMA.S_oeis_a259145.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- If a prime p divides both k and phi(k), it divides the prime k^2 - phi(k), so it equals it. Then
-- k^2 - phi(k) = p <= k, and with phi(k) <= k this forces k^2 <= 2k, i.e. k <= 2. For k = 0 and k = 1 the
-- number k^2 - phi(k) is 0, not a prime, and for k = 2 the two numbers 2 and phi(2) = 1 are coprime.

theorem OMA.solution : type_of% @OMA.S_oeis_a259145.main := by
  intro k hp
  by_contra hc
  obtain ⟨p, pp, hpk, hpphi⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
  have hphi : Nat.totient k ≤ k := Nat.totient_le k
  have hk2 : p ∣ k ^ 2 := dvd_pow hpk (by norm_num)
  have hdiv : p ∣ k ^ 2 - Nat.totient k := Nat.dvd_sub hk2 hpphi
  have heq : p = k ^ 2 - Nat.totient k := (Nat.prime_dvd_prime_iff_eq pp hp).mp hdiv
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      exact (Nat.not_prime_zero (by simpa using hp)).elim
    · exact h0
  have hple : p ≤ k := Nat.le_of_dvd hkpos hpk
  have h1 : k ^ 2 - Nat.totient k ≤ k := heq ▸ hple
  have h2 : k ^ 2 ≤ 2 * k := by omega
  have hk : k ≤ 2 := by nlinarith [h2, hkpos]
  interval_cases k
  · exact Nat.not_prime_zero (by simpa using hp)
  · exact hc (by simp)
