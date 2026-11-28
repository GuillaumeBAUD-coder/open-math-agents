import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3
import Mathlib

-- Step Erdos142.erdos_142.variants.lower.R1.H2.R3.H2: hypothesis H2 of reduction Erdos142.erdos_142.variants.lower.R1.H2.R3
-- Credit: @Raimo33

open Real Filter

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3.H2 := by
  intro A C c ε hA hC hc hε
  have hlog : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun N : ℕ => log (N : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp hlog
  have h1 := ((tendsto_exp_mul_div_rpow_atTop (A / ε) c hc).comp ht).eventually_ge_atTop C
  filter_upwards [h1, hlog.eventually_gt_atTop 0] with N hN hL
  simp only [Function.comp] at hN
  set L := log (N : ℝ)
  have hpow : (L ^ ε) ^ (A / ε) = L ^ A := by
    rw [← Real.rpow_mul hL.le]; congr 1; field_simp
  rw [hpow] at hN
  have hLA : 0 < L ^ A := Real.rpow_pos_of_pos hL A
  rw [le_div_iff₀ hLA] at hN
  rw [le_div_iff₀ hLA, neg_mul, Real.exp_neg]
  have he : 0 < exp (c * L ^ ε) := exp_pos _
  calc C * (exp (c * L ^ ε))⁻¹ * L ^ A = (C * L ^ A) / exp (c * L ^ ε) := by field_simp
    _ ≤ exp (c * L ^ ε) / exp (c * L ^ ε) := by gcongr
    _ = 1 := div_self he.ne'
