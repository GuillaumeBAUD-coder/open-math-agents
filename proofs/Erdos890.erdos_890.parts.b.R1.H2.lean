import OMAReductions.R_Erdos890_erdos_890_parts_b_R1
/-! Uniform control of prime factors above a variable power of log n.
The product estimate is adapted from @mucoucah’s in-repository proof of
Erdos890.erdos_890.variants.omega_limsup at a634340ede671933fd26c40e756591ba34559e9c. -/
open Filter Finset Real
private lemma log_large_prime_product (n : ℕ) (hn : n ≠ 0) (y : ℝ) (hy : 1 < y) :
    (((n.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ y)).card : ℕ) : ℝ) * log y ≤ log n := by
  classical
  have hprod : ∏ p ∈ n.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ y), p ≤ n := by
    apply Nat.le_of_dvd (Nat.pos_of_ne_zero hn)
    exact (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)).trans
      (Nat.prod_primeFactors_dvd n)
  have hpow : y ^ (n.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ y)).card ≤ (n : ℝ) := by
    calc y ^ (n.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ y)).card
        = ∏ _p ∈ n.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ y), y := by simp
      _ ≤ ∏ p ∈ n.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ y), (p : ℝ) := by
          apply Finset.prod_le_prod
          · intro i _; linarith
          · intro i hi
            rw [Finset.mem_filter] at hi
            exact (not_le.mp hi.2).le
      _ = ((∏ p ∈ n.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ y), p : ℕ) : ℝ) := by
          push_cast; rfl
      _ ≤ n := by exact_mod_cast hprod
  have h := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow] at h
  exact h
theorem OMA.solution : OMA.R_Erdos890_erdos_890_parts_b_R1.H2 := by
  classical
  intro k hk ε hε
  obtain ⟨B, hB⟩ := exists_nat_gt ((2 * k : ℝ) / ε + 1)
  have hBreal : 0 < (B : ℝ) := by
    have : 0 ≤ (2 * k : ℝ) / ε := by positivity
    linarith
  have hBnat : 0 < B := by exact_mod_cast hBreal
  refine ⟨B, by omega, ?_⟩
  have ht : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_gt_atTop (1 : ℝ)), eventually_ge_atTop k] with n hL hnk
  have hn : 2 ≤ n := by omega
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlpos : 0 < log (n : ℝ) := by linarith
  have hy : 1 < (log n) ^ B := one_lt_pow₀ hL hBnat.ne'
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑ _i ∈ range k, (2 / (B : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := mem_range.mp hi
      have hprod := log_large_prime_product (n+i) (by omega) ((log n)^B) hy
      rw [Real.log_pow] at hprod
      have hni : (n + i : ℝ) ≤ (n : ℝ)^2 := by
        have hin : (i : ℝ) ≤ n := by exact_mod_cast (show i ≤ n by omega)
        nlinarith [mul_nonneg (by linarith : 0 ≤ (n : ℝ) - 2) (by positivity : 0 ≤ (n : ℝ))]
      have hl := Real.log_le_log (by positivity : (0 : ℝ) < (n+i : ℝ)) hni
      rw [Real.log_pow] at hl
      push_cast at hprod hl
      apply (le_div_iff₀ hBreal).2
      rw [mul_assoc, div_mul_eq_mul_div, ← mul_div_assoc, div_le_iff₀ hlpos]
      nlinarith [hprod.trans hl]
    _ = (2 * (k : ℝ)) / B := by simp; ring
    _ ≤ ε := (div_le_iff₀ hBreal).2 (by
      have hlt : 2 * (k : ℝ) / ε ≤ B := by linarith
      linarith [(div_le_iff₀ hε).mp hlt])
