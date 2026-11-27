import OMAReductions.R_RefactorableNumber_no_three_consecutive_refactorable_R1

-- Step RefactorableNumber.no_three_consecutive_refactorable.R1.H1: hypothesis H1 of reduction RefactorableNumber.no_three_consecutive_refactorable.R1
-- Credit: @iLc0
-- Zelinsky (2002), proof of Theorem 59: for odd x, x^2 + 1 = 2m with m odd and d(m) dividing m.
-- Every prime factor of m is 1 mod 4, so every divisor of m is 1 mod 4; each exponent e of m
-- satisfies e + 1 dividing d(m), hence e is divisible by 4 and m is a fourth power.

namespace OMA.H1aux

/-- A nonzero natural number whose prime factors are all `1 mod 4` is itself `1 mod 4`. -/
lemma mod_four_eq_one_of_primeFactors {d : ℕ} (hd : d ≠ 0)
    (h : ∀ p ∈ d.primeFactors, p % 4 = 1) : d % 4 = 1 := by
  induction d using Nat.recOnMul with
  | zero => exact absurd rfl hd
  | one => rfl
  | prime p hp => exact h p (by simp [hp.primeFactors])
  | mul a b ha hb =>
    have ha0 : a ≠ 0 := left_ne_zero_of_mul hd
    have hb0 : b ≠ 0 := right_ne_zero_of_mul hd
    have h1 := ha ha0 (fun p hp => h p (by rw [Nat.primeFactors_mul ha0 hb0]; exact Finset.mem_union_left _ hp))
    have h2 := hb hb0 (fun p hp => h p (by rw [Nat.primeFactors_mul ha0 hb0]; exact Finset.mem_union_right _ hp))
    rw [Nat.mul_mod, h1, h2]

/-- If every exponent in the factorization of `m ≠ 0` is divisible by four, `m` is a fourth power. -/
lemma exists_pow_four {m : ℕ} (hm : m ≠ 0) (h : ∀ p ∈ m.primeFactors, 4 ∣ m.factorization p) :
    ∃ w : ℕ, m = w ^ 4 := by
  refine ⟨m.primeFactors.prod (fun p => p ^ (m.factorization p / 4)), ?_⟩
  rw [← Finset.prod_pow]
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hm]
  rw [Finsupp.prod]
  refine Finset.prod_congr (by simp) (fun p hp => ?_)
  rw [← pow_mul, Nat.div_mul_cancel (h p (by simpa using hp))]

end OMA.H1aux

open OMA.H1aux in
theorem OMA.solution : OMA.R_RefactorableNumber_no_three_consecutive_refactorable_R1.H1 := by
  intro x hx hr
  obtain ⟨k, rfl⟩ := hx
  set m := 2 * k ^ 2 + 2 * k + 1 with hm_def
  have hN : (2 * k + 1) ^ 2 + 1 = 2 * m := by rw [hm_def]; ring
  have hm0 : m ≠ 0 := by omega
  have hmodd : Odd m := ⟨k ^ 2 + k, by rw [hm_def]; ring⟩
  have hcop : Nat.Coprime 2 m := (Nat.coprime_two_left).mpr hmodd
  -- d(2m) = 2 d(m) divides 2m, hence d(m) ∣ m
  have hdm : m.divisors.card ∣ m := by
    have h := hr.2
    rw [hN, Nat.Coprime.card_divisors_mul hcop] at h
    have h2 : (Nat.divisors 2).card = 2 := by decide
    rw [h2] at h
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
  -- every prime factor of m is 1 mod 4
  have hsq : IsSquare (-1 : ZMod m) := by
    refine ⟨(2 * k + 1 : ℕ), ?_⟩
    have h0 : (((2 * k + 1) ^ 2 + 1 : ℕ) : ZMod m) = 0 := by
      rw [hN, ZMod.natCast_eq_zero_iff]; exact Dvd.intro_left 2 rfl
    push_cast at h0 ⊢
    linear_combination -h0
  have hp4 : ∀ p ∈ m.primeFactors, p % 4 = 1 := by
    intro p hp
    have h3 := Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one hp hsq
    have hpodd : p % 2 = 1 := by
      have : p ∣ m := Nat.dvd_of_mem_primeFactors hp
      have hpo : Odd p := hmodd.of_dvd_nat this
      exact Nat.odd_iff.mp hpo
    omega
  -- every divisor of m is 1 mod 4
  have hdiv4 : ∀ d, d ∣ m → d % 4 = 1 := by
    intro d hd
    have hd0 : d ≠ 0 := fun h => hm0 (Nat.eq_zero_of_zero_dvd (h ▸ hd))
    exact mod_four_eq_one_of_primeFactors hd0 (fun p hp =>
      hp4 p (Nat.primeFactors_mono hd hm0 hp))
  -- hence every exponent is divisible by 4
  have hexp : ∀ p ∈ m.primeFactors, 4 ∣ m.factorization p := by
    intro p hp
    have hd : m.factorization p + 1 ∣ m.divisors.card := by
      rw [Nat.card_divisors hm0]
      exact Finset.dvd_prod_of_mem _ hp
    have := hdiv4 _ (hd.trans hdm)
    omega
  obtain ⟨w, hw⟩ := exists_pow_four hm0 hexp
  exact ⟨w, by rw [hN, hw]⟩
