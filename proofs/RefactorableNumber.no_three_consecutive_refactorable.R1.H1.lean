import OMAReductions.R_RefactorableNumber_no_three_consecutive_refactorable_R1

-- Step RefactorableNumber.no_three_consecutive_refactorable.R1.H1: hypothesis H1 of reduction RefactorableNumber.no_three_consecutive_refactorable.R1
-- Credit: @OrangeHeadz
-- H1 := ∀ x : ℕ, Odd x → (x ^ 2 + 1).IsRefactorable →     ∃ y : ℕ, x ^ 2 + 1 = 2 * y ^ 4  /-- Ljunggren: the only nonnegative first coordinates are 1 and 239. -/

/-! # An odd `x` with `x ^ 2 + 1` refactorable has `x ^ 2 + 1 = 2 * y ^ 4`

For odd `x = 2 t + 1` write `x ^ 2 + 1 = 2 * m` with `m = 2 t ^ 2 + 2 t + 1` odd. Every prime
`p` dividing `m` divides `x ^ 2 + 1`, so `-1` is a square modulo `p` and `p % 4 = 1`.
The divisor count is multiplicative, so `τ (2 m) = 2 τ (m)` and refactorability gives
`τ (m) ∣ m`. For a prime `p` dividing `m` with exponent `e`, the factor `e + 1` of `τ (m)`
divides `m`; all its prime factors are therefore `1` modulo `4`, hence so is `e + 1`, and
`4 ∣ e`. So `m` is a fourth power. -/

/-- A natural number all of whose prime factors are `1` modulo `4` is itself `1` modulo `4`. -/
lemma OMA.mod_four_of_primes (d : ℕ) (h : ∀ p : ℕ, p.Prime → p ∣ d → p % 4 = 1) :
    d % 4 = 1 := by
  induction d using Nat.recOnMul with
  | zero => exact absurd (h 2 Nat.prime_two (dvd_zero 2)) (by norm_num)
  | one => rfl
  | prime p hp => exact h p hp dvd_rfl
  | mul a b iha ihb =>
    have ha := iha (fun p hp hpa => h p hp (hpa.mul_right b))
    have hb := ihb (fun p hp hpb => h p hp (hpb.mul_left a))
    rw [Nat.mul_mod, ha, hb]

theorem OMA.solution : OMA.R_RefactorableNumber_no_three_consecutive_refactorable_R1.H1 := by
  intro x hx href
  obtain ⟨t, rfl⟩ := hx
  set m : ℕ := 2 * t ^ 2 + 2 * t + 1 with hmdef
  have hN : (2 * t + 1) ^ 2 + 1 = 2 * m := by rw [hmdef]; ring
  rw [hN] at href ⊢
  have hm0 : m ≠ 0 := by omega
  have hmodd : ¬ 2 ∣ m := by omega
  have hprime : ∀ p : ℕ, p.Prime → p ∣ m → p % 4 = 1 := by
    intro p hp hpm
    have : Fact p.Prime := Fact.mk hp
    have h0 : (((2 * t + 1) ^ 2 + 1 : ℕ) : ZMod p) = 0 := by
      rw [hN]
      exact (ZMod.natCast_eq_zero_iff _ _).2 (hpm.mul_left 2)
    have h1 : ((2 * t + 1 : ℕ) : ZMod p) ^ 2 = -1 := by
      push_cast at h0 ⊢
      linear_combination h0
    have h3 := ZMod.mod_four_ne_three_of_sq_eq_neg_one h1
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact hmodd hpm
    have h4 := hp.eq_two_or_odd
    omega
  have hτ : m.divisors.card ∣ m := by
    have hcop : Nat.Coprime 2 m := Nat.prime_two.coprime_iff_not_dvd.2 hmodd
    have h2 := href.2
    rw [hcop.card_divisors_mul, show (2 : ℕ).divisors.card = 2 by decide] at h2
    exact (Nat.mul_dvd_mul_iff_left (by norm_num)).1 h2
  have hdiv4 : ∀ p ∈ m.primeFactors, 4 ∣ m.factorization p := by
    intro p hp
    have h1 : (m.factorization p + 1) ∣ m := by
      refine dvd_trans ?_ hτ
      rw [Nat.card_divisors hm0]
      exact Finset.dvd_prod_of_mem (fun x => m.factorization x + 1) hp
    have h2 := OMA.mod_four_of_primes (m.factorization p + 1)
      (fun q hq hqd => hprime q hq (hqd.trans h1))
    omega
  refine ⟨∏ p ∈ m.primeFactors, p ^ (m.factorization p / 4), ?_⟩
  congr 1
  rw [← Finset.prod_pow]
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hm0]
  rw [Finsupp.prod, Nat.support_factorization]
  apply Finset.prod_congr rfl
  intro p hp
  rw [← pow_mul, Nat.div_mul_cancel (hdiv4 p hp)]
