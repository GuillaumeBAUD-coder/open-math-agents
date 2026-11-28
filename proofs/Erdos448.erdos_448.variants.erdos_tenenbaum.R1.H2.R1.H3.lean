import OMAReductions.R_Erdos448_erdos_448_variants_erdos_tenenbaum_R1_H2_R1

-- Step Erdos448.erdos_448.variants.erdos_tenenbaum.R1.H2.R1.H3: hypothesis H3 of reduction Erdos448.erdos_448.variants.erdos_tenenbaum.R1.H2.R1
-- Credit: @Lenqth (Claude Code, claude-opus-5-5)

/-! Split the prime factorisation of `n` by exponent: `d` collects the prime powers `p^e` with
`e ≥ 2` and `m` the primes with exponent `1`. Then `n = d * m`, `d` and `m` are coprime,
`m` is squarefree and every prime of `d` divides it at least twice. -/

theorem OMA.solution : OMA.R_Erdos448_erdos_448_variants_erdos_tenenbaum_R1_H2_R1.H3 := by
  intro n hn
  classical
  set S := n.primeFactors.filter (fun p => 2 ≤ n.factorization p) with hS
  set T := n.primeFactors.filter (fun p => ¬ 2 ≤ n.factorization p) with hT
  set d := ∏ p ∈ S, p ^ n.factorization p with hd
  set m := ∏ p ∈ T, p ^ n.factorization p with hm
  have hprime : ∀ p ∈ n.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hdpos : 0 < d := Finset.prod_pos fun p hp =>
    pow_pos (hprime p (Finset.mem_filter.mp hp).1).pos _
  have hsplit : n = d * m := by
    rw [hd, hm, hS, hT, Finset.prod_filter_mul_prod_filter_not]
    exact (Nat.prod_factorization_pow_eq_self hn.ne').symm
  have hm1 : ∀ p ∈ T, n.factorization p = 1 := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
    have := (Nat.mem_primeFactors.mp hp1)
    have : 0 < n.factorization p := Nat.Prime.factorization_pos_of_dvd this.1 hn.ne' this.2.1
    omega
  have hmeq : m = ∏ p ∈ T, p := Finset.prod_congr rfl fun p hp => by rw [hm1 p hp, pow_one]
  refine ⟨d, m, hdpos, hsplit, ?_, ?_, ?_⟩
  · -- coprime: disjoint prime supports
    rw [hd, hm]
    apply Nat.Coprime.prod_left; intro p hp
    apply Nat.Coprime.prod_right; intro q hq
    apply Nat.Coprime.pow
    have hpq : p ≠ q := by
      rintro rfl
      exact (Finset.mem_filter.mp hq).2 (Finset.mem_filter.mp hp).2
    exact (Nat.coprime_primes (hprime p (Finset.mem_filter.mp hp).1)
      (hprime q (Finset.mem_filter.mp hq).1)).mpr hpq
  · rw [hmeq]
    exact Finset.squarefree_prod_of_pairwise_isCoprime
      (fun p hp q hq hpq => (Nat.coprime_primes (hprime p (Finset.mem_filter.mp hp).1)
        (hprime q (Finset.mem_filter.mp hq).1)).mpr hpq |> Nat.coprime_iff_isRelPrime.mp)
      (fun p hp => (hprime p (Finset.mem_filter.mp hp).1).squarefree)
  · intro p hp hpd
    rw [hd] at hpd
    obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hpd
    have hqp := hprime q (Finset.mem_filter.mp hq).1
    have : p = q := (Nat.prime_dvd_prime_iff_eq hp hqp).mp (hp.dvd_of_dvd_pow hpq)
    subst this
    have h2 := (Finset.mem_filter.mp hq).2
    rw [hd]
    exact (pow_dvd_pow p h2).trans (Finset.dvd_prod_of_mem _ hq)
