import OMAReductions.R_Erdos936_erdos_936_variants_factorial_add_one_R1

-- Step Erdos936.erdos_936.variants.factorial_add_one.R1.H1: hypothesis H1 of reduction Erdos936.erdos_936.variants.factorial_add_one.R1
-- Credit: @gabaweb
-- H1 := ∀ c : ℕ, 0 < c → c.Powerful → (∏ p ∈ c.primeFactors, p) ^ 2 ∣ c

theorem OMA.solution : OMA.R_Erdos936_erdos_936_variants_factorial_add_one_R1.H1 := by
  intro c _ hc
  rw [← Finset.prod_pow]
  have key : ∀ s ⊆ c.primeFactors, ∏ p ∈ s, p ^ 2 ∣ c := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp
    | @insert a s ha ih =>
      intro hs
      rw [Finset.prod_insert ha]
      have has : a ∈ c.primeFactors := hs (Finset.mem_insert_self a s)
      have hsub : s ⊆ c.primeFactors := fun x hx => hs (Finset.mem_insert_of_mem hx)
      refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (hc a has) (ih hsub)
      refine Nat.Coprime.prod_right fun q hq => ?_
      have hne : a ≠ q := fun h => ha (h ▸ hq)
      exact ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors has)
        (Nat.prime_of_mem_primeFactors (hsub hq))).mpr hne).pow 2 2
  exact key _ (Finset.Subset.refl _)
