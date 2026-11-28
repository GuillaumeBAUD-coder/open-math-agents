import OMAStatements.S_oeis_a130091

lemma a130091_fact_eq_one {k p : ℕ} (hp : p.Prime) (hk : k ≠ 0) (h1 : p ∣ k)
    (h2 : ¬ p ^ 2 ∣ k) : k.factorization p = 1 := by
  have a : 1 ≤ k.factorization p := (hp.pow_dvd_iff_le_factorization hk).1 (by simpa using h1)
  have b : ¬ 2 ≤ k.factorization p := fun h => h2 ((hp.pow_dvd_iff_le_factorization hk).2 h)
  omega

lemma a130091_not_inSeq {k : ℕ} (h : k % 36 = 6 ∨ k % 36 = 30) :
    ¬ OMA.S_oeis_a130091.InSeq k := by
  rintro ⟨hk, hinj⟩
  have hk0 : k ≠ 0 := hk.ne'
  have e2 : k.factorization 2 = 1 :=
    a130091_fact_eq_one Nat.prime_two hk0 (by omega) (by norm_num; omega)
  have e3 : k.factorization 3 = 1 :=
    a130091_fact_eq_one Nat.prime_three hk0 (by omega) (by norm_num; omega)
  have m2 : (2 : ℕ) ∈ (k.primeFactors : Set ℕ) := by
    simp only [Finset.mem_coe, Nat.mem_primeFactors]; exact ⟨Nat.prime_two, by omega, hk0⟩
  have m3 : (3 : ℕ) ∈ (k.primeFactors : Set ℕ) := by
    simp only [Finset.mem_coe, Nat.mem_primeFactors]; exact ⟨Nat.prime_three, by omega, hk0⟩
  have := hinj m2 m3 (e2.trans e3.symm)
  omega

theorem OMA.solution : type_of% @OMA.S_oeis_a130091.main := by
  refine ⟨fun n hn => a130091_not_inSeq (by omega), fun n => a130091_not_inSeq (by omega), ?_⟩
  rintro ⟨m, hm⟩
  by_cases h1 : m % 36 ≤ 6
  · exact a130091_not_inSeq (k := m + (6 - m % 36)) (by omega) (hm _ (by omega))
  by_cases h2 : m % 36 ≤ 30
  · exact a130091_not_inSeq (k := m + (30 - m % 36)) (by omega) (hm _ (by omega))
  · exact a130091_not_inSeq (k := m + (42 - m % 36)) (by omega) (hm _ (by omega))
