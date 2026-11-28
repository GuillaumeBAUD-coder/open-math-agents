import OMAReductions.R_wpc_local_smoothing_conjecture_R1_H1_R1_H2_R1

theorem OMA.solution : OMA.R_wpc_local_smoothing_conjecture_R1_H1_R1_H2_R1.H3 := by
  intro A ε hε d
  set r : ℝ := (2:ℝ)⁻¹ ^ ε with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hε
  have hrn : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg hr0]
  have hg : Summable (fun j : ℕ => r ^ j) := summable_geometric_of_lt_one hr0 hr1
  have hp : Summable (fun j : ℕ => (j:ℝ) ^ A * r ^ j) := summable_pow_mul_geometric_of_norm_lt_one A hrn
  have hl2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) ((hg.add hp).mul_left (2^A))
  · have : 0 ≤ 1 + Real.log (1 / d j) := by
      simp only [d, one_div, inv_pow, inv_inv]
      have := Real.log_nonneg (one_le_pow₀ (show (1:ℝ) ≤ 2 by norm_num) (n := j))
      linarith
    positivity
  · have e1 : d j ^ ε = r ^ j := by
      simp only [d, hr]
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), mul_comm]
    have e2 : Real.log (1 / d j) = j * Real.log 2 := by
      simp only [d, one_div, inv_pow, inv_inv, Real.log_pow]
    rw [e1, e2]
    have hj : (0:ℝ) ≤ j := by positivity
    have h1 : 1 + (j:ℝ) * Real.log 2 ≤ 1 + j := by nlinarith
    have h2 : (1 + (j:ℝ))^A ≤ 2^A * (1 + (j:ℝ)^A) := by
      rcases le_total (j:ℝ) 1 with h | h
      · calc (1 + (j:ℝ))^A ≤ 2^A := pow_le_pow_left₀ (by positivity) (by linarith) A
          _ ≤ 2^A * (1 + (j:ℝ)^A) := by
            have : (0:ℝ) ≤ (j:ℝ)^A := by positivity
            nlinarith [show (0:ℝ) < 2^A by positivity]
      · calc (1 + (j:ℝ))^A ≤ (2 * j)^A := pow_le_pow_left₀ (by positivity) (by linarith) A
          _ = 2^A * (j:ℝ)^A := mul_pow _ _ _
          _ ≤ 2^A * (1 + (j:ℝ)^A) := by
            nlinarith [show (0:ℝ) < 2^A by positivity]
    have h3 : (1 + (j:ℝ) * Real.log 2)^A ≤ (1 + (j:ℝ))^A :=
      pow_le_pow_left₀ (by positivity) h1 A
    have hrj : 0 ≤ r ^ j := by positivity
    calc r ^ j * (1 + (j:ℝ) * Real.log 2)^A ≤ r ^ j * (2^A * (1 + (j:ℝ)^A)) :=
          mul_le_mul_of_nonneg_left (h3.trans h2) hrj
      _ = 2^A * (r ^ j + (j:ℝ)^A * r^j) := by ring
