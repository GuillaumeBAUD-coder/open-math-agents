import OMAReductions.R_Erdos1081_erdos_1081_R1

/-!
# Step H2 of reduction Erdos1081.erdos_1081.R1 (Erdős Problem 1081)

Written with Claude Code (AI-assisted).
Reduction Erdos1081.erdos_1081.R1 is by @JaviSoto.

Paper proof. Put `y = log x`, which tends to infinity with `x`. Since `(log y) ^ C = o(y ^ a)`
for every real `C` and every `a > 0`, the quotient `(log y) ^ C / y ^ a` tends to `0`, and it is
positive for `y > 1`. Hence its inverse `y ^ a / (log y) ^ C` tends to infinity.
Elementary (standard growth comparison); no source used.
-/

-- Step Erdos1081.erdos_1081.R1.H2: hypothesis H2 of that reduction
-- Credit: @timlantin

theorem OMA.solution : OMA.R_Erdos1081_erdos_1081_R1.H2 := by
  intro a C ha
  have h0 : Filter.Tendsto (fun y : ℝ => Real.log y ^ C / y ^ a) Filter.atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop C ha).tendsto_div_nhds_zero
  have hpos : ∀ᶠ y : ℝ in Filter.atTop, Real.log y ^ C / y ^ a ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with y hy
    exact div_pos (Real.rpow_pos_of_pos (Real.log_pos hy) C)
      (Real.rpow_pos_of_pos (by linarith) a)
  have h1 : Filter.Tendsto (fun y : ℝ => (Real.log y ^ C / y ^ a)⁻¹) Filter.atTop Filter.atTop :=
    tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨h0, hpos⟩)
  have h2 := h1.comp Real.tendsto_log_atTop
  refine h2.congr (fun x => ?_)
  simp only [Function.comp_apply, inv_div]
