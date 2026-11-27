import OMAReductions.R_Erdos976_erdos_976_variants_erdos_R1

-- Step Erdos976.erdos_976.variants.erdos.R1.H2
-- Credit: @caa1982

open Filter Asymptotics

theorem OMA.solution : OMA.R_Erdos976_erdos_976_variants_erdos_R1.H2 := by
  intro c hc
  refine Asymptotics.IsBigO.of_bound 1 ?_
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog2 : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hlo : (fun u : ℝ => Real.log u) =o[atTop] (fun u : ℝ => u ^ (c / 2)) :=
    isLittleO_log_rpow_atTop (by positivity)
  have hbound : ∀ᶠ n : ℕ in atTop,
      ‖Real.log (Real.log (n : ℝ))‖ ≤ 1 * ‖(Real.log (n : ℝ)) ^ (c / 2)‖ :=
    hlog.eventually (hlo.bound one_pos)
  filter_upwards [hlog.eventually_gt_atTop 1, hlog2.eventually_gt_atTop 1, hbound] with n h1 h2 hb
  have hu_pos : 0 < Real.log (n : ℝ) := by linarith
  have hlu_pos : 0 < Real.log (Real.log (n : ℝ)) := by linarith
  have hlhs_nonneg : 0 ≤ (n : ℝ) * (Real.log (n : ℝ)) ^ Real.log (Real.log (Real.log (n : ℝ))) :=
    mul_nonneg (Nat.cast_nonneg n) (Real.rpow_nonneg hu_pos.le _)
  have hrhs_nonneg : 0 ≤ (n : ℝ) * Real.exp ((Real.log (n : ℝ)) ^ c) :=
    mul_nonneg (Nat.cast_nonneg n) (Real.exp_pos _).le
  rw [Real.norm_of_nonneg hlhs_nonneg, Real.norm_of_nonneg hrhs_nonneg, one_mul]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
  rw [Real.rpow_def_of_pos hu_pos]
  apply Real.exp_le_exp.mpr
  rw [Real.norm_of_nonneg hlu_pos.le, Real.norm_of_nonneg (Real.rpow_nonneg hu_pos.le _), one_mul] at hb
  have hll_le : Real.log (Real.log (Real.log (n : ℝ))) ≤ Real.log (Real.log (n : ℝ)) := by
    linarith [Real.log_le_sub_one_of_pos hlu_pos]
  have hsq : Real.log (Real.log (n : ℝ)) * Real.log (Real.log (Real.log (n : ℝ))) ≤
      ((Real.log (n : ℝ)) ^ (c / 2)) ^ 2 := by
    calc Real.log (Real.log (n : ℝ)) * Real.log (Real.log (Real.log (n : ℝ)))
        ≤ Real.log (Real.log (n : ℝ)) * Real.log (Real.log (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hll_le hlu_pos.le
      _ ≤ (Real.log (n : ℝ)) ^ (c / 2) * (Real.log (n : ℝ)) ^ (c / 2) :=
          mul_le_mul hb hb hlu_pos.le (Real.rpow_nonneg hu_pos.le _)
      _ = ((Real.log (n : ℝ)) ^ (c / 2)) ^ 2 := by ring
  have hrpow : ((Real.log (n : ℝ)) ^ (c / 2)) ^ 2 = (Real.log (n : ℝ)) ^ c := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu_pos.le]
    congr 1
    push_cast
    ring
  linarith
