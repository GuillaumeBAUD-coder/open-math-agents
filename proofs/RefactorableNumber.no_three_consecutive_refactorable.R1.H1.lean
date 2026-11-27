import OMAReductions.R_RefactorableNumber_no_three_consecutive_refactorable_R1

/-! Write x²+1 = 2m with m odd. Every prime dividing m is 1 modulo 4,
since −1 is a square modulo that prime. Hence every divisor of m is 1
modulo 4, including each prime exponent plus one in the divisor count. -/

theorem OMA.solution : OMA.R_RefactorableNumber_no_three_consecutive_refactorable_R1.H1 := by
  intro x hx href
  obtain ⟨t, ht⟩ := hx
  let m := 2*(t*(t+1))+1
  have oddm : Odd m := ⟨t*(t+1), rfl⟩
  have m0 : m ≠ 0 := by dsimp [m]; omega
  have split : x^2+1 = 2*m := by rw [ht]; dsimp [m]; ring
  have tau : m.divisors.card ∣ m := by
    have h := href.2
    rw [split, oddm.coprime_two_left.card_divisors_mul, show (2 : ℕ).divisors.card = 2 by decide] at h
    exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 2) h
  have allDiv (d : ℕ) (hd : d ∣ m) : d % 4 = 1 := by
    have hd0 : d ≠ 0 := fun h => m0 (by simpa [h] using hd)
    have primes (p : ℕ) (hp : p ∈ d.primeFactors) : (p : ZMod 4) = 1 := by
      have prime := Nat.prime_of_mem_primeFactors hp
      have pd := Nat.dvd_of_mem_primeFactors hp
      have pm := pd.trans hd
      have pn : p ∣ x^2+1 := split ▸ pm.trans (dvd_mul_left m 2)
      have sq : (x : ZMod p)^2 + 1 = 0 := by
        exact_mod_cast (ZMod.natCast_eq_zero_iff _ _).mpr pn
      let : Fact p.Prime := ⟨prime⟩
      have h3 := ZMod.mod_four_ne_three_of_sq_eq_neg_one (eq_neg_of_add_eq_zero_left sq)
      have po := Nat.odd_iff.mp (oddm.of_dvd_nat pm)
      have h1 : p ≡ 1 [MOD 4] := by change p % 4 = 1; omega
      simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr h1
    have hm : (d : ZMod 4) = 1 := calc
      _ = ∏ p ∈ d.primeFactors, (p : ZMod 4) ^ d.factorization p := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 4) (Nat.prod_primeFactors_pow_factorization hd0)
      _ = 1 := Finset.prod_eq_one fun p hp => by rw [primes p hp, one_pow]
    exact (ZMod.natCast_eq_natCast_iff d 1 4).mp (by simpa using hm)
  have hexp (p : ℕ) (hp : p ∈ m.primeFactors) : m.factorization p % 4 = 0 := by
    have hd : m.factorization p + 1 ∣ m.divisors.card := by
      rw [Nat.card_divisors m0]
      exact Finset.dvd_prod_of_mem _ hp
    have := allDiv _ (hd.trans tau)
    omega
  refine ⟨∏ p ∈ m.primeFactors, p^(m.factorization p/4), ?_⟩
  rw [split, ← Finset.prod_pow]
  apply congrArg (2 * ·)
  calc
    m = _ := Nat.prod_primeFactors_pow_factorization m0
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [← pow_mul]
      congr 1
      have := hexp p hp
      omega
