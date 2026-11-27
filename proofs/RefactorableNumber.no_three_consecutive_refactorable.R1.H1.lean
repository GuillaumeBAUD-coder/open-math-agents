import OMAReductions.R_RefactorableNumber_no_three_consecutive_refactorable_R1

-- Step RefactorableNumber.no_three_consecutive_refactorable.R1.H1: hypothesis H1 of reduction RefactorableNumber.no_three_consecutive_refactorable.R1
-- Credit: @michielkosters
-- H1 := ∀ x : ℕ, Odd x → (x ^ 2 + 1).IsRefactorable →     ∃ y : ℕ, x ^ 2 + 1 = 2 * y ^ 4  /-- Ljunggren: the only nonnegative first coordinates are 1 and 239. -/

private lemma exists_prime_mod_four_eq_three_of_mod_four_eq_three :
    ∀ n : ℕ, n % 4 = 3 → ∃ q : ℕ, Nat.Prime q ∧ q % 4 = 3 ∧ q ∣ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hn1 : 1 < n := by omega
    let q := n.minFac
    have hq_prime : Nat.Prime q := Nat.minFac_prime (by omega)
    have hq_dvd : q ∣ n := Nat.minFac_dvd n
    have hq_ne2 : q ≠ 2 := by
      intro h2
      have : 2 ∣ n := h2 ▸ hq_dvd
      omega
    have hq_odd := hq_prime.eq_two_or_odd.resolve_left hq_ne2
    have hq_mod : q % 4 = 1 ∨ q % 4 = 3 := by omega
    rcases hq_mod with h1 | h3
    · have hdiv_lt : n / q < n := Nat.div_lt_self (by omega) hq_prime.one_lt
      have hmul : q * (n / q) = n := Nat.mul_div_cancel' hq_dvd
      have hdiv_mod : (n / q) % 4 = 3 := by
        have h := congrArg (· % 4) hmul
        rw [Nat.mul_mod, h1, hn, Nat.one_mul] at h
        omega
      obtain ⟨r, hr_prime, hr_mod, hr_dvd⟩ := ih (n / q) hdiv_lt hdiv_mod
      exact ⟨r, hr_prime, hr_mod, dvd_trans hr_dvd (Nat.div_dvd_of_dvd hq_dvd)⟩
    · exact ⟨q, hq_prime, h3, hq_dvd⟩

theorem OMA.solution : OMA.R_RefactorableNumber_no_three_consecutive_refactorable_R1.H1 := by
  intro x hx_odd h_ref
  obtain ⟨k, rfl⟩ := hx_odd
  let m : ℕ := 2 * k ^ 2 + 2 * k + 1
  have hx_eq : (2 * k + 1) ^ 2 + 1 = 2 * m := by dsimp [m]; ring
  have hm_odd : Odd m := ⟨k ^ 2 + k, by dsimp [m]; ring⟩
  have hm_ne : m ≠ 0 := by dsimp [m]; omega
  have h2m_ne : 2 * m ≠ 0 := by omega
  have h2_not_mem : 2 ∉ m.primeFactors := by
    intro h
    have hd : 2 ∣ m := Nat.dvd_of_mem_primeFactors h
    obtain ⟨t, ht⟩ := hm_odd
    omega
  have hpf : (2 * m).primeFactors = insert 2 m.primeFactors := by
    rw [Nat.primeFactors_mul (by decide : (2 : ℕ) ≠ 0) hm_ne,
      Nat.Prime.primeFactors Nat.prime_two, Finset.singleton_union]
  have hfac2 : (2 * m).factorization 2 = 1 := by
    rw [Nat.factorization_mul (by decide : (2 : ℕ) ≠ 0) hm_ne, Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by obtain ⟨t, ht⟩ := hm_odd; omega)]
  have hfac_p : ∀ p ∈ m.primeFactors, (2 * m).factorization p = m.factorization p := by
    intro p hp
    have hp2 : p ≠ 2 := fun h => h2_not_mem (h ▸ hp)
    rw [Nat.factorization_mul (by decide : (2 : ℕ) ≠ 0) hm_ne, Finsupp.add_apply,
      Nat.Prime.factorization Nat.prime_two, Finsupp.single_apply, if_neg hp2.symm, Nat.zero_add]
  have hcard : (2 * m).divisors.card = 2 * m.divisors.card := by
    rw [Nat.card_divisors h2m_ne, hpf, Finset.prod_insert h2_not_mem, hfac2]
    have hprod : ∏ p ∈ m.primeFactors, ((2 * m).factorization p + 1) =
        ∏ p ∈ m.primeFactors, (m.factorization p + 1) :=
      Finset.prod_congr rfl fun p hp => by rw [hfac_p p hp]
    rw [hprod, ← Nat.card_divisors hm_ne]
  have hm_dvd : m.divisors.card ∣ m := by
    have hd2m : (2 * m).divisors.card ∣ 2 * m := by
      rw [← hx_eq]
      exact h_ref.2
    rw [hcard] at hd2m
    exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 2) hd2m
  have hcard_odd : Odd m.divisors.card := hm_odd.of_dvd_nat hm_dvd
  have h4 : ∀ p ∈ m.primeFactors, 4 ∣ m.factorization p := by
    intro p hp
    have hd_card : m.factorization p + 1 ∣ m.divisors.card := by
      rw [Nat.card_divisors hm_ne]
      exact Finset.dvd_prod_of_mem _ hp
    have heven : Even (m.factorization p) := by
      have ho := Nat.odd_iff.mp (hcard_odd.of_dvd_nat hd_card)
      exact Nat.even_iff.mpr (by omega)
    by_contra hnot4
    have hmod3 : (m.factorization p + 1) % 4 = 3 := by
      obtain ⟨t, ht⟩ := heven
      omega
    obtain ⟨q, hq_prime, hq_mod, hq_dvd_exp⟩ :=
      exists_prime_mod_four_eq_three_of_mod_four_eq_three _ hmod3
    have hq_dvd_x2 : q ∣ (2 * k + 1) ^ 2 + 1 := by
      rw [hx_eq]
      exact dvd_trans hq_dvd_exp (dvd_trans hd_card (dvd_trans hm_dvd (dvd_mul_left m 2)))
    have : Fact q.Prime := ⟨hq_prime⟩
    have hsq : IsSquare (-1 : ZMod q) := by
      obtain ⟨t, ht⟩ := hq_dvd_x2
      have h0 : (((2 * k + 1) ^ 2 + 1 : ℕ) : ZMod q) = 0 := by
        rw [ht, Nat.cast_mul, ZMod.natCast_self, zero_mul]
      push_cast at h0
      have hz : (2 * (k : ZMod q) + 1) ^ 2 = -1 := eq_neg_of_add_eq_zero_left h0
      exact ⟨2 * (k : ZMod q) + 1, by rw [← hz, sq]⟩
    have hne3 : q % 4 ≠ 3 := ZMod.exists_sq_eq_neg_one_iff.mp hsq
    exact hne3 hq_mod
  refine ⟨∏ p ∈ m.primeFactors, p ^ (m.factorization p / 4), ?_⟩
  rw [hx_eq]
  congr 1
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hm_ne, Finsupp.prod, Nat.support_factorization]
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro p hp
  rw [← pow_mul, Nat.div_mul_cancel (h4 p hp)]
