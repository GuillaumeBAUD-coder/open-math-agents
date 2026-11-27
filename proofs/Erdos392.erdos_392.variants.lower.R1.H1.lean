import OMAReductions.R_Erdos392_erdos_392_variants_lower_R1

open scoped Nat

theorem OMA.solution : OMA.R_Erdos392_erdos_392_variants_lower_R1.H1 := by
  intro n hn t a hprod hle
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hlog : 0 < Real.log n := Real.log_pos hn1
  -- n! ≤ n ^ (t+1)
  have h1 : (n)! ≤ n ^ (t + 1) := by
    rw [hprod]
    calc ∏ i, a i ≤ ∏ _i : Fin (t + 1), n := Finset.prod_le_prod' (fun i _ => hle i)
      _ = n ^ (t + 1) := by simp
  have h1' : ((n)! : ℝ) ≤ (n : ℝ) ^ (t + 1) := by exact_mod_cast h1
  -- n^n / n! ≤ e^n
  have h2 : (n : ℝ) ^ n / (n)! ≤ Real.exp n := Real.pow_div_factorial_le_exp (n : ℝ) hn0.le n
  have hfact : (0 : ℝ) < (n)! := by exact_mod_cast Nat.factorial_pos n
  have h3 : (n : ℝ) ^ n ≤ Real.exp n * (n : ℝ) ^ (t + 1) := by
    rw [div_le_iff₀ hfact] at h2
    calc (n : ℝ) ^ n ≤ Real.exp n * (n)! := h2
      _ ≤ Real.exp n * (n : ℝ) ^ (t + 1) := by gcongr
  have h4 : Real.log ((n : ℝ) ^ n) ≤ Real.log (Real.exp n * (n : ℝ) ^ (t + 1)) :=
    Real.log_le_log (by positivity) h3
  rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp, Real.log_pow,
    Real.log_pow] at h4
  have h5 : (n : ℝ) / Real.log n = (n : ℝ) * (Real.log n)⁻¹ := div_eq_mul_inv _ _
  rw [sub_le_iff_le_add]
  have h6 : (n : ℝ) * Real.log n ≤ ((t : ℝ) + 1 + n / Real.log n) * Real.log n := by
    have : (n : ℝ) / Real.log n * Real.log n = n := div_mul_cancel₀ _ hlog.ne'
    push_cast at h4
    nlinarith
  exact le_of_mul_le_mul_right h6 hlog
