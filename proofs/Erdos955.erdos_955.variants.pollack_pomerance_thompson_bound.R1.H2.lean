import OMAReductions.R_Erdos955_erdos_955_variants_pollack_pomerance_thompson_bound_R1

-- Step Erdos955.erdos_955.variants.pollack_pomerance_thompson_bound.R1.H2: hypothesis H2 of reduction Erdos955.erdos_955.variants.pollack_pomerance_thompson_bound.R1
-- Credit: @aqron7
-- H2 := ∀ n : ℕ, 1 ≤ n → (ArithmeticFunction.sigma 1 n : ℝ) ≤ n * (1 + Real.log n)

/-! `σ(n) = ∑_{d ∣ n} n / d ≤ n ∑_{d ≤ n} 1 / d = n H_n ≤ n (1 + log n)`. -/

theorem OMA.solution : OMA.R_Erdos955_erdos_955_variants_pollack_pomerance_thompson_bound_R1.H2 := by
  intro n hn
  have h1 : (ArithmeticFunction.sigma 1 n : ℝ) = ∑ d ∈ n.divisors, (n : ℝ) / d := by
    rw [ArithmeticFunction.sigma_one_apply, ← Nat.sum_div_divisors n (fun d => d)]
    push_cast
    apply Finset.sum_congr rfl
    intro d hd
    have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
    have hd0 : (d : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
    rw [Nat.cast_div hdn hd0]
  have h2 : ∑ d ∈ n.divisors, (n : ℝ) / d ≤ ∑ d ∈ Finset.Icc 1 n, (n : ℝ) / d := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd
      exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, Nat.divisor_le hd⟩
    · intro d _ _; positivity
  have h3 : ∑ d ∈ Finset.Icc 1 n, (n : ℝ) / d = n * (harmonic n : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _; push_cast; ring
  have h4 : (harmonic n : ℝ) ≤ 1 + Real.log n := harmonic_le_one_add_log n
  rw [h1]
  calc _ ≤ _ := h2
    _ = _ := h3
    _ ≤ _ := by gcongr
