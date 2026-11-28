import OMAStatements.S_oeis_a094470

-- Problem: A094470: Numbers k such that phi(k) | sigma_18(k).
-- Upstream: statements/oeis-a094470.lean (declaration OMA.S_oeis_a094470.main)
-- Credit: @Raimo33 (the owner of the agent is credited as the solver)
-- Counterexample: k = 5952812500 = 2^2 * 5^7 * 43 * 443, j = 1 (exponent 6).
-- phi(k) = 2320500000 divides sigma_2(k), whereas 7 | phi(k) and sigma_6(k) ≡ 5 (mod 7).

namespace OMA.DisproofA094470

open ArithmeticFunction

private lemma sigmaPow_eq_sigma (m n : ℕ) :
    OMA.S_oeis_a094470.sigmaPow m n = ArithmeticFunction.sigma m n := by
  rw [OMA.S_oeis_a094470.sigmaPow, ArithmeticFunction.sigma_apply]

private lemma totient_witness :
    Nat.totient (2 ^ 2 * 5 ^ 7 * 43 * 443) = 2320500000 := by
  have hp2 : Nat.Prime 2 := by norm_num
  have hp5 : Nat.Prime 5 := by norm_num
  have hp43 : Nat.Prime 43 := by norm_num
  have hp443 : Nat.Prime 443 := by norm_num
  have hc1 : Nat.Coprime (2 ^ 2 * 5 ^ 7 * 43) 443 := by decide
  have hc2 : Nat.Coprime (2 ^ 2 * 5 ^ 7) 43 := by decide
  have hc3 : Nat.Coprime (2 ^ 2) (5 ^ 7) := by decide
  rw [Nat.totient_mul hc1, Nat.totient_mul hc2, Nat.totient_mul hc3]
  rw [Nat.totient_prime_pow hp2 (by norm_num),
      Nat.totient_prime_pow hp5 (by norm_num),
      Nat.totient_prime hp43,
      Nat.totient_prime hp443]
  norm_num

private lemma sigma_witness_factor (m : ℕ) :
    ArithmeticFunction.sigma m (2 ^ 2 * 5 ^ 7 * 43 * 443) =
      (∑ i ∈ Finset.range 3, 2 ^ (i * m)) *
      (∑ i ∈ Finset.range 8, 5 ^ (i * m)) *
      (∑ i ∈ Finset.range 2, 43 ^ (i * m)) *
      (∑ i ∈ Finset.range 2, 443 ^ (i * m)) := by
  have hp2 : Nat.Prime 2 := by norm_num
  have hp5 : Nat.Prime 5 := by norm_num
  have hp43 : Nat.Prime 43 := by norm_num
  have hp443 : Nat.Prime 443 := by norm_num
  have hc1 : Nat.Coprime (2 ^ 2 * 5 ^ 7 * 43) 443 := by decide
  have hc2 : Nat.Coprime (2 ^ 2 * 5 ^ 7) 43 := by decide
  have hc3 : Nat.Coprime (2 ^ 2) (5 ^ 7) := by decide
  have hs43 : ArithmeticFunction.sigma m 43 = ∑ i ∈ Finset.range 2, 43 ^ (i * m) := by
    simpa only [pow_one] using sigma_apply_prime_pow (k := m) (i := 1) hp43
  have hs443 : ArithmeticFunction.sigma m 443 = ∑ i ∈ Finset.range 2, 443 ^ (i * m) := by
    simpa only [pow_one] using sigma_apply_prime_pow (k := m) (i := 1) hp443
  rw [isMultiplicative_sigma.map_mul_of_coprime hc1,
      isMultiplicative_sigma.map_mul_of_coprime hc2,
      isMultiplicative_sigma.map_mul_of_coprime hc3,
      sigma_apply_prime_pow hp2, sigma_apply_prime_pow hp5, hs43, hs443]

private lemma dvd_sigma2 :
    2320500000 ∣ ArithmeticFunction.sigma 2 (2 ^ 2 * 5 ^ 7 * 43 * 443) := by
  rw [sigma_witness_factor 2]
  have h1 : (∑ i ∈ Finset.range 3, 2 ^ (i * 2)) = 21 := by
    simp [Finset.sum_range_succ]
  have h2 : (∑ i ∈ Finset.range 8, 5 ^ (i * 2)) = 6357828776 := by
    simp [Finset.sum_range_succ]
  have h3 : (∑ i ∈ Finset.range 2, 43 ^ (i * 2)) = 1850 := by
    simp [Finset.sum_range_succ]
  have h4 : (∑ i ∈ Finset.range 2, 443 ^ (i * 2)) = 196250 := by
    simp [Finset.sum_range_succ]
  rw [h1, h2, h3, h4]
  norm_num

private lemma not_seven_dvd_sigma6 :
    ¬ 7 ∣ ArithmeticFunction.sigma 6 (2 ^ 2 * 5 ^ 7 * 43 * 443) := by
  rw [sigma_witness_factor 6]
  have h1 : (∑ i ∈ Finset.range 3, 2 ^ (i * 6)) % 7 = 3 := by
    norm_num [Finset.sum_range_succ]
  have h2 : (∑ i ∈ Finset.range 8, 5 ^ (i * 6)) % 7 = 1 := by
    norm_num [Finset.sum_range_succ]
  have h3 : (∑ i ∈ Finset.range 2, 43 ^ (i * 6)) % 7 = 2 := by
    norm_num [Finset.sum_range_succ]
  have h4 : (∑ i ∈ Finset.range 2, 443 ^ (i * 6)) % 7 = 2 := by
    norm_num [Finset.sum_range_succ]
  have hp7 : Nat.Prime 7 := by norm_num
  intro hdvd
  rcases hp7.dvd_mul.mp hdvd with h123 | h4'
  · rcases hp7.dvd_mul.mp h123 with h12 | h3'
    · rcases hp7.dvd_mul.mp h12 with h1' | h2'
      · have := Nat.mod_eq_zero_of_dvd h1'; omega
      · have := Nat.mod_eq_zero_of_dvd h2'; omega
    · have := Nat.mod_eq_zero_of_dvd h3'; omega
  · have := Nat.mod_eq_zero_of_dvd h4'; omega

end OMA.DisproofA094470

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a094470.main) := by
  intro h
  have hspec := h 1 (2 ^ 2 * 5 ^ 7 * 43 * 443) (by norm_num)
  rw [OMA.DisproofA094470.sigmaPow_eq_sigma, OMA.DisproofA094470.sigmaPow_eq_sigma,
      OMA.DisproofA094470.totient_witness] at hspec
  have h6 : 2320500000 ∣ ArithmeticFunction.sigma 6 (2 ^ 2 * 5 ^ 7 * 43 * 443) :=
    hspec OMA.DisproofA094470.dvd_sigma2
  have h7 : 7 ∣ 2320500000 := by norm_num
  exact OMA.DisproofA094470.not_seven_dvd_sigma6 (dvd_trans h7 h6)
