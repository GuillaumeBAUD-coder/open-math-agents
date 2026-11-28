import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3

open Filter Real Asymptotics
open scoped Topology

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3.H2 := by
  intro A C c ε hA hC hc hε
  have hLog : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratioLog : Tendsto (fun L : ℝ => log L / L ^ ε) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop hε).tendsto_div_nhds_zero
  have hratioConst : Tendsto (fun L : ℝ => log C / L ^ ε) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_rpow_atTop hε)
  have hcomb0 : Tendsto (fun L : ℝ => log C / L ^ ε + A * (log L / L ^ ε)) atTop (𝓝 0) := by
    simpa using hratioConst.add (hratioLog.const_mul A)
  have hcomb : Tendsto (fun L : ℝ => (log C + A * log L) / L ^ ε) atTop (𝓝 0) := by
    convert hcomb0 using 1
    ext L
    ring_nf
  have hEv := (hcomb.comp hLog).eventually (eventually_lt_nhds hc)
  filter_upwards [hEv, hLog.eventually (eventually_gt_atTop (1 : ℝ))] with N hrat hLgt
  let L : ℝ := log (N : ℝ)
  change (log C + A * log L) / L ^ ε < c at hrat
  have hLpos : 0 < L := lt_trans zero_lt_one hLgt
  have hpowpos : 0 < L ^ ε := Real.rpow_pos_of_pos hLpos ε
  have hApowpos : 0 < L ^ A := Real.rpow_pos_of_pos hLpos A
  have hsum : log C + A * log L < c * L ^ ε := by
    exact (div_lt_iff₀ hpowpos).mp hrat
  have hLeq : L ^ A = exp (A * log L) := by
    rw [Real.rpow_def_of_pos hLpos]
    congr 1
    ring
  have hCeq : C = exp (log C) := (Real.exp_log hC).symm
  have hexp : C * L ^ A ≤ exp (c * L ^ ε) := by
    rw [hCeq, hLeq, ← Real.exp_add]
    exact Real.exp_le_exp.mpr hsum.le
  have hmul : (C * exp (-c * L ^ ε)) * L ^ A ≤ 1 := by
    calc
      (C * exp (-c * L ^ ε)) * L ^ A = (C * L ^ A) * exp (-c * L ^ ε) := by ring
      _ ≤ exp (c * L ^ ε) * exp (-c * L ^ ε) :=
        mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; ring_nf; simp
  change C * exp (-c * L ^ ε) ≤ 1 / L ^ A
  exact (le_div_iff₀ hApowpos).mpr hmul
