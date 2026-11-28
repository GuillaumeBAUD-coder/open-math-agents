import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1

-- Step Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R1.H2: hypothesis H2 of reduction Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R1
-- Credit: @mburv
-- H2 := ∀ c η : ℝ, 0 < c → 0 < η →     Summable (fun j : ℕ ↦ Real.exp (-c * (Real.log (Real.log ((4 : ℝ) ^ j))) ^ (1 + η)))

open Filter Topology

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1.H2 := by
  intro c η hc hη
  -- (log j)^η → ∞
  have hlog : Tendsto (fun j : ℕ => Real.log (j : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun j : ℕ => Real.log (j : ℝ) ^ η) atTop atTop :=
    (tendsto_rpow_atTop hη).comp hlog
  have hsum : Summable (fun j : ℕ => ((j : ℝ) ^ (2 : ℕ))⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by norm_num)
  refine Summable.of_norm_bounded_eventually_nat hsum ?_
  filter_upwards [hpow.eventually_ge_atTop (2 / c), hlog.eventually_ge_atTop 1,
    eventually_ge_atTop 1] with j hj hl1 hj1
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj1
  have hlog4 : (1 : ℝ) < Real.log 4 := by
    have := Real.exp_one_lt_d9
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    linarith
  -- log (4^j) = j * log 4 ≥ j
  have hL : (j : ℝ) ≤ Real.log ((4 : ℝ) ^ j) := by
    rw [Real.log_pow]
    nlinarith
  -- log log (4^j) ≥ log j
  have hLL : Real.log (j : ℝ) ≤ Real.log (Real.log ((4 : ℝ) ^ j)) :=
    Real.log_le_log hjpos hL
  set x := Real.log (Real.log ((4 : ℝ) ^ j)) with hx
  set y := Real.log (j : ℝ) with hy
  have hy0 : 0 ≤ y := by linarith
  have hxy : y ^ (1 + η) ≤ x ^ (1 + η) := Real.rpow_le_rpow hy0 hLL (by linarith)
  have hsplit : y ^ (1 + η) = y * y ^ η := by
    rw [Real.rpow_add' hy0 (by linarith), Real.rpow_one]
  -- c * y^(1+η) ≥ 2 y
  have hkey : 2 * y ≤ c * x ^ (1 + η) := by
    have h1 : 2 ≤ c * y ^ η := by
      have := mul_le_mul_of_nonneg_left hj hc.le
      rwa [mul_div_cancel₀ _ hc.ne'] at this
    have h2 : 2 * y ≤ c * (y * y ^ η) := by nlinarith
    calc 2 * y ≤ c * (y * y ^ η) := h2
      _ = c * y ^ (1 + η) := by rw [hsplit]
      _ ≤ c * x ^ (1 + η) := mul_le_mul_of_nonneg_left hxy hc.le
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hexp : Real.exp (-c * x ^ (1 + η)) ≤ Real.exp (-(2 * y)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hjy : Real.exp (-(2 * y)) = ((j : ℝ) ^ (2 : ℕ))⁻¹ := by
    rw [Real.exp_neg, show 2 * y = Real.log ((j : ℝ) ^ (2 : ℕ)) by
      rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]
  rw [← hjy]
  exact hexp
