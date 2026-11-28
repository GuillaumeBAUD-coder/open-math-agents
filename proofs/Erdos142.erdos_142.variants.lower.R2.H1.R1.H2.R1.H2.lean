import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1

/-! The series on powers of four converges by eventual comparison with the inverse squares. -/

-- Step Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R1.H2: hypothesis H2 of reduction Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R1
-- Credit: @PianothShaveck
-- H2 := ∀ c η : ℝ, 0 < c → 0 < η →     Summable (fun j : ℕ ↦ Real.exp (-c * (Real.log (Real.log ((4 : ℝ) ^ j))) ^ (1 + η)))

open Filter Real

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1.H2 := by
  intro c η hc hη
  have hlog : Tendsto (fun j : ℕ ↦ log (j : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hgrowth : Tendsto (fun j : ℕ ↦ (log (j : ℝ)) ^ η) atTop atTop :=
    (tendsto_rpow_atTop hη).comp hlog
  refine Summable.of_norm_bounded_eventually_nat
    (Real.summable_nat_rpow.mpr (show (-2 : ℝ) < -1 by norm_num)) ?_
  filter_upwards [hgrowth.eventually_ge_atTop (2 / c), eventually_gt_atTop 1] with j hηj hj
  have hj' : (1 : ℝ) < j := by exact_mod_cast hj
  have hL := log_pos hj'
  have h4 : 1 ≤ log 4 := (le_log_iff_exp_le (by norm_num)).mpr (by linarith [exp_one_lt_three])
  have hbase : log (j : ℝ) ≤ log (log ((4 : ℝ) ^ j)) := by
    rw [Real.log_pow]
    exact log_le_log (by positivity) (le_mul_of_one_le_right (by positivity) h4)
  have hcoeff : 2 ≤ (log (j : ℝ)) ^ η * c := (div_le_iff₀ hc).mp hηj
  have hbound : 2 * log (j : ℝ) ≤ c * (log (log ((4 : ℝ) ^ j))) ^ (1 + η) := calc
    2 * log (j : ℝ) ≤ ((log (j : ℝ)) ^ η * c) * log (j : ℝ) :=
      mul_le_mul_of_nonneg_right hcoeff hL.le
    _ = c * (log (j : ℝ)) ^ (1 + η) := by rw [rpow_add hL, rpow_one]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (rpow_le_rpow hL.le hbase (by positivity)) hc.le
  rw [Real.norm_of_nonneg (by positivity), rpow_def_of_pos (by positivity : 0 < (j : ℝ))]
  apply Real.exp_le_exp.mpr
  linarith
