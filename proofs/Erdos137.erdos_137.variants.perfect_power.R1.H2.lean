import OMAReductions.R_Erdos137_erdos_137_variants_perfect_power_R1

-- Credit: @sturdy4days
-- Bertrand gives a prime above half the upper endpoint. With no prime
-- at or above k in the interval, this prime is itself one of the factors
-- and none of the other factors is divisible by it.
theorem OMA.solution : OMA.R_Erdos137_erdos_137_variants_perfect_power_R1.H2 := by
  intro k n hk hNoPrime
  obtain ⟨p, hp, hpAboveHalf, hpAtMostDoubleHalf⟩ :=
    Nat.exists_prime_lt_and_le_two_mul ((n + k) / 2) (by omega)
  have hpUpper : p ≤ n + k := by omega
  have hpLarge : n + k < 2 * p := by omega
  have hpBelowK : p < k := by
    by_contra! hkp
    exact hNoPrime ⟨p, hkp, hpUpper, hp⟩
  have hpMem : p ∈ Finset.Ioc n (n + k) := Finset.mem_Ioc.mpr ⟨by omega, hpUpper⟩
  refine ⟨p, hp, ?_⟩
  have hNonzero : ∀ m ∈ Finset.Ioc n (n + k), m ≠ 0 := by
    intro m hm
    have hmLower := (Finset.mem_Ioc.mp hm).1
    omega
  rw [Nat.factorization_prod_apply (g := fun m => m) hNonzero]
  have hOtherFactors : ∀ m ∈ Finset.Ioc n (n + k), m ≠ p → m.factorization p = 0 := by
    intro m hm hmp
    apply Nat.factorization_eq_zero_of_not_dvd
    obtain ⟨hmLower, hmUpper⟩ := Finset.mem_Ioc.mp hm
    rintro ⟨t, hmt⟩
    have htNonzero : t ≠ 0 := by
      intro htZero
      simp only [htZero, Nat.mul_zero] at hmt
      omega
    have htLess : t < 2 := by
      by_contra! htAtLeast
      have hmAtLeast : p * 2 ≤ p * t := Nat.mul_le_mul_left p htAtLeast
      omega
    have htOne : t = 1 := by omega
    exact hmp (by simpa only [htOne, Nat.mul_one] using hmt)
  rw [Finset.sum_eq_single_of_mem p hpMem hOtherFactors]
  simp [hp.factorization]
