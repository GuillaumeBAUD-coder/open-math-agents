import OMAReductions.R_OeisA1599_eq_one_of_odd_of_a_R1

-- Step OeisA1599.eq_one_of_odd_of_a.R1.H1: hypothesis H1 of reduction OeisA1599.eq_one_of_odd_of_a.R1
-- Credit: @JamesSlash. For n = p^k (k >= 1), s = sigma 1 n = 1 + p + ... + p^k is 1 mod p, hence coprime
-- to p^k; so s | n * (k + 1) forces s | k + 1, but s >= p^k + 1 > k + 1.

theorem OMA.solution : OMA.R_OeisA1599_eq_one_of_odd_of_a_R1.H1 := by
  intro n hn hA
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
  obtain ⟨_, hdvd⟩ := hA
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp,
    ArithmeticFunction.sigma_zero_apply_prime_pow hp] at hdvd
  have hsplit : ∑ i ∈ Finset.range (k + 1), p ^ i = 1 + p * ∑ i ∈ Finset.range k, p ^ i := by
    rw [Finset.sum_range_succ', Finset.mul_sum]
    simp only [pow_succ, pow_zero]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hcop : Nat.Coprime (∑ i ∈ Finset.range (k + 1), p ^ i) (p ^ k) := by
    apply Nat.Coprime.pow_right
    rw [hsplit, Nat.coprime_add_mul_left_left]
    exact Nat.coprime_one_left p
  have h1 : (∑ i ∈ Finset.range (k + 1), p ^ i) ∣ k + 1 := hcop.dvd_of_dvd_mul_left hdvd
  have h2 : p ^ k + 1 ≤ ∑ i ∈ Finset.range (k + 1), p ^ i := by
    rw [Finset.sum_range_succ]
    have : 1 ≤ ∑ i ∈ Finset.range k, p ^ i := by
      have h0 : (0 : ℕ) ∈ Finset.range k := Finset.mem_range.mpr hk
      calc 1 = p ^ 0 := by simp
        _ ≤ ∑ i ∈ Finset.range k, p ^ i :=
          Finset.single_le_sum (f := fun i => p ^ i) (fun _ _ => Nat.zero_le _) h0
    omega
  have h3 : k < p ^ k := Nat.lt_pow_self hp.one_lt
  have h4 := Nat.le_of_dvd (by omega) h1
  omega
