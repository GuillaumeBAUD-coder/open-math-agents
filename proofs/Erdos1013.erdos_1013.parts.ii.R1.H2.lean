import OMAReductions.R_Erdos1013_erdos_1013_parts_ii_R1

/-!
# Proof of `Erdos1013.erdos_1013.parts.ii.R1.H2`

For any `c > 0`, the ratio `(c * (k + 1)^2 * log (k + 1)) / (c * k^2 * log k)` tends to `1` as
`k → ∞`, since for `k ≥ 2` it factors as `(1 + 1 / k)^2 * (1 + log (1 + 1 / k) / log k)`.
-/

open Filter

theorem OMA.solution : OMA.R_Erdos1013_erdos_1013_parts_ii_R1.H2 := by
  intro c hc
  have hinv : Tendsto (fun k : ℕ => (1 : ℝ) / (k : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hstep : Tendsto (fun k : ℕ => (1 : ℝ) + 1 / (k : ℝ)) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hinv
  have hsq : Tendsto (fun k : ℕ => ((1 : ℝ) + 1 / (k : ℝ)) ^ 2) atTop (nhds 1) := by
    simpa using hstep.pow 2
  have hlog_step : Tendsto (fun k : ℕ => Real.log ((1 : ℝ) + 1 / (k : ℝ))) atTop (nhds 0) := by
    simpa [Function.comp_def] using (Real.continuousAt_log one_ne_zero).tendsto.comp hstep
  have hlog_inv : Tendsto (fun k : ℕ => (Real.log (k : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlog_quot :
      Tendsto (fun k : ℕ => (1 : ℝ) + Real.log ((1 : ℝ) + 1 / (k : ℝ)) / Real.log (k : ℝ))
        atTop (nhds 1) := by
    have hmul : Tendsto (fun k : ℕ => Real.log ((1 : ℝ) + 1 / (k : ℝ)) / Real.log (k : ℝ))
        atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using hlog_step.mul hlog_inv
    simpa using tendsto_const_nhds.add hmul
  have hprod :
      Tendsto (fun k : ℕ =>
        ((1 : ℝ) + 1 / (k : ℝ)) ^ 2 *
          ((1 : ℝ) + Real.log ((1 : ℝ) + 1 / (k : ℝ)) / Real.log (k : ℝ)))
        atTop (nhds 1) := by
    simpa using hsq.mul hlog_quot
  refine hprod.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 1] with k hk
  have hk1 : (1 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  have hk0 : (k : ℝ) ≠ 0 := ne_of_gt hkpos
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hlogk : Real.log (k : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hkpos (ne_of_gt hk1)
  have hstep_pos : (0 : ℝ) < 1 + 1 / (k : ℝ) := by positivity
  have hk1_eq : ((k + 1 : ℕ) : ℝ) = (k : ℝ) * (1 + 1 / (k : ℝ)) := by
    push_cast
    field_simp
  have hlog_eq : Real.log ((k + 1 : ℕ) : ℝ) = Real.log (k : ℝ) + Real.log (1 + 1 / (k : ℝ)) := by
    rw [hk1_eq, Real.log_mul hk0 (ne_of_gt hstep_pos)]
  rw [hlog_eq, hk1_eq]
  field_simp
