import OMAReductions.R_Erdos1057_erdos_1057_variants_agp_infinite_R1

-- Step Erdos1057.erdos_1057.variants.agp_infinite.R1.H3: hypothesis H3 of reduction Erdos1057.erdos_1057.variants.agp_infinite.R1

/-!
Korselt's criterion, sufficiency. Let `b` be coprime to `n`. For each prime `p ∣ n` we have
`b ^ (p - 1) ≡ 1 (mod p)` and `p - 1 ∣ n - 1`, so `p ∣ b ^ (n - 1) - 1`. As `n` is squarefree it
is the product of its prime factors, and a product of distinct primes each dividing a number
divides it.
-/

theorem OMA.solution : OMA.R_Erdos1057_erdos_1057_variants_agp_infinite_R1.H3 := by
  unfold OMA.R_Erdos1057_erdos_1057_variants_agp_infinite_R1.H3
  intro n hn1 hnp hsq hk b hb hcop
  have key : ∏ p ∈ n.primeFactors, p ∣ b ^ (n - 1) - 1 := by
    apply Finset.prod_primes_dvd
    · intro p hp
      exact (Nat.prime_of_mem_primeFactors hp).prime
    · intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpn := Nat.dvd_of_mem_primeFactors hp
      obtain ⟨k, hk'⟩ := hk p hpp hpn
      have hbp : Nat.Coprime b p := (Nat.Coprime.coprime_dvd_left hpn hcop).symm
      have h1 : b ^ (p - 1) ≡ 1 [MOD p] := by
        have h0 := Nat.ModEq.pow_totient hbp
        rwa [Nat.totient_prime hpp] at h0
      have h2 : b ^ (n - 1) ≡ 1 [MOD p] := by
        rw [hk', pow_mul]
        have h0 := h1.pow k
        rwa [one_pow] at h0
      exact (Nat.modEq_iff_dvd' (Nat.one_le_pow (n - 1) b hb)).mp h2.symm
  rw [Nat.prod_primeFactors_of_squarefree hsq] at key
  exact ⟨key, hnp, hn1⟩
