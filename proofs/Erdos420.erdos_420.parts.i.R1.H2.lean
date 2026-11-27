import OMAReductions.R_Erdos420_erdos_420_parts_i_R1

-- Step Erdos420.erdos_420.parts.i.R1.H2: hypothesis H2 of reduction Erdos420.erdos_420.parts.i.R1
-- Credit: @smurali12
-- H2 := ∀ a b p s : ℕ, p.Prime → 0 < s → s < p → a < s * p → s * p ≤ b →     (s + 1) * (σ 0 a.factorial) ≤ s * (σ 0 b.factorial)

open scoped ArithmeticFunction.sigma

theorem OMA.solution : OMA.R_Erdos420_erdos_420_parts_i_R1.H2 := by
  intro a b p s hp _hs hsp ha hb
  have hba : a ≤ b := by omega
  have ha0 : a.factorial ≠ 0 := Nat.factorial_ne_zero a
  have hb0 : b.factorial ≠ 0 := Nat.factorial_ne_zero b
  have hdvd : a.factorial ∣ b.factorial := Nat.factorial_dvd_factorial hba
  have hle_fac : ∀ q : ℕ, a.factorial.factorization q ≤ b.factorial.factorization q :=
    (Nat.factorization_le_iff_dvd ha0 hb0).mpr hdvd
  have hsub : a.factorial.primeFactors ⊆ b.factorial.primeFactors := by
    intro q hq
    obtain ⟨hq_prime, hq_dvd, _⟩ := Nat.mem_primeFactors.mp hq
    exact Nat.mem_primeFactors.mpr ⟨hq_prime, dvd_trans hq_dvd hdvd, hb0⟩
  have hp_dvd_b : p ∣ b.factorial := Nat.dvd_factorial hp.pos (by nlinarith)
  have hpS : p ∈ b.factorial.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hp_dvd_b, hb0⟩
  have hsig_a :
      σ 0 a.factorial = ∏ q ∈ b.factorial.primeFactors, (a.factorial.factorization q + 1) := by
    rw [ArithmeticFunction.sigma_zero_apply, Nat.card_divisors ha0]
    refine Finset.prod_subset hsub ?_
    intro q _ hq_not
    have hq0 : a.factorial.factorization q = 0 :=
      Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization])
    simp [hq0]
  have hsig_b :
      σ 0 b.factorial = ∏ q ∈ b.factorial.primeFactors, (b.factorial.factorization q + 1) := by
    rw [ArithmeticFunction.sigma_zero_apply, Nat.card_divisors hb0]
  have ha_p : a.factorial.factorization p + 1 ≤ s := by
    have hlog : Nat.log p a < 2 := Nat.log_lt_of_lt_pow' (by decide) (by nlinarith)
    rw [Nat.factorization_factorial hp hlog]
    have hIco : Finset.Ico 1 2 = {1} := by decide
    rw [hIco, Finset.sum_singleton, pow_one]
    have hdiv : a / p < s := Nat.div_lt_of_lt_mul (by linarith)
    omega
  have hb_p : s + 1 ≤ b.factorial.factorization p + 1 := by
    have hps : (p * s).factorial ∣ b.factorial := Nat.factorial_dvd_factorial (by linarith)
    have hps_le := (Nat.factorization_le_iff_dvd (Nat.factorial_ne_zero (p * s)) hb0).mpr hps p
    rw [Nat.factorization_factorial_mul hp] at hps_le
    omega
  rw [hsig_a, hsig_b]
  rw [← Finset.mul_prod_erase b.factorial.primeFactors (fun q => a.factorial.factorization q + 1) hpS]
  rw [← Finset.mul_prod_erase b.factorial.primeFactors (fun q => b.factorial.factorization q + 1) hpS]
  have hrest :
      ∏ q ∈ b.factorial.primeFactors.erase p, (a.factorial.factorization q + 1) ≤
      ∏ q ∈ b.factorial.primeFactors.erase p, (b.factorial.factorization q + 1) := by
    apply Finset.prod_le_prod'
    intro q _
    exact Nat.add_le_add_right (hle_fac q) 1
  have hmain :
      (s + 1) * (a.factorial.factorization p + 1) ≤
      s * (b.factorial.factorization p + 1) := by
    nlinarith
  calc
    (s + 1) * ((a.factorial.factorization p + 1) *
        ∏ q ∈ b.factorial.primeFactors.erase p, (a.factorial.factorization q + 1))
      = ((s + 1) * (a.factorial.factorization p + 1)) *
        ∏ q ∈ b.factorial.primeFactors.erase p, (a.factorial.factorization q + 1) := by ring
    _ ≤ (s * (b.factorial.factorization p + 1)) *
        ∏ q ∈ b.factorial.primeFactors.erase p, (b.factorial.factorization q + 1) :=
      Nat.mul_le_mul hmain hrest
    _ = s * ((b.factorial.factorization p + 1) *
        ∏ q ∈ b.factorial.primeFactors.erase p, (b.factorial.factorization q + 1)) := by ring

