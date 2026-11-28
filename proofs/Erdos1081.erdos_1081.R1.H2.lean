import OMAReductions.R_Erdos1081_erdos_1081_R1

/-! With y = log x → ∞ it suffices that y^a / (log y)^C → ∞. Its reciprocal (log y)^C / y^a
tends to 0 by `isLittleO_log_rpow_rpow_atTop` and is eventually positive. -/

open Filter Topology in
theorem OMA.solution : OMA.R_Erdos1081_erdos_1081_R1.H2 := by
  intro a C ha
  have h0 : Tendsto (fun y : ℝ => Real.log y ^ C / y ^ a) atTop (𝓝 0) :=
    (isLittleO_log_rpow_rpow_atTop C ha).tendsto_div_nhds_zero
  have hpos : ∀ᶠ y : ℝ in atTop, Real.log y ^ C / y ^ a ∈ Set.Ioi 0 := by
    filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0, eventually_gt_atTop 0]
      with y h1 h2
    exact div_pos (Real.rpow_pos_of_pos h1 C) (Real.rpow_pos_of_pos h2 a)
  have h1 : Tendsto (fun y : ℝ => Real.log y ^ C / y ^ a) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨h0, hpos⟩
  have h2 : Tendsto (fun y : ℝ => y ^ a / Real.log y ^ C) atTop atTop := by
    refine (tendsto_inv_nhdsGT_zero.comp h1).congr ?_
    intro y
    simp only [Function.comp_apply, inv_div]
  exact h2.comp Real.tendsto_log_atTop
