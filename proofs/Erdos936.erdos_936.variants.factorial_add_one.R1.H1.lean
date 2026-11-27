import OMAReductions.R_Erdos936_erdos_936_variants_factorial_add_one_R1

-- Step Erdos936.erdos_936.variants.factorial_add_one.R1.H1: hypothesis H1 of reduction Erdos936.erdos_936.variants.factorial_add_one.R1
-- Credit: @volskew90
-- H1 := ∀ c : ℕ, 0 < c → c.Powerful → (∏ p ∈ c.primeFactors, p) ^ 2 ∣ c

theorem OMA.solution : OMA.R_Erdos936_erdos_936_variants_factorial_add_one_R1.H1 := by
  intro c hc hcp
  rw [← Finset.prod_pow]
  have key : ∀ s : Finset ℕ, s ⊆ c.primeFactors → (∏ p ∈ s, p ^ 2) ∣ c := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => simp
    | @insert p s hps ih =>
      rw [Finset.prod_insert hps]
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors (hs (Finset.mem_insert_self p s))
      refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (hcp p (hs (Finset.mem_insert_self p s)))
        (ih (fun q hq => hs (Finset.mem_insert_of_mem hq)))
      rw [Nat.coprime_pow_left_iff (by norm_num : 0 < 2), Nat.Prime.coprime_iff_not_dvd hpp]
      intro hdiv
      obtain ⟨q, hq, hqd⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hpp) (fun q => q ^ 2)).mp hdiv
      have hqp : q.Prime := Nat.prime_of_mem_primeFactors (hs (Finset.mem_insert_of_mem hq))
      have hpeq : p = q := (Nat.prime_dvd_prime_iff_eq hpp hqp).mp
        (hpp.dvd_of_dvd_pow hqd)
      exact hps (hpeq ▸ hq)
  exact key c.primeFactors Finset.Subset.rfl
