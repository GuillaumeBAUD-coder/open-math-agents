import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R1
import Mathlib

open Filter Topology

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- log log 2^m = log m + log log 2, and (log m + K)^eta tends to infinity, so eventually
-- c (log log 2^m)^(1+eta) is at least 2 log m and the term is at most 1/m^2.

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R1.H2 := by
  unfold OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R1.H2
  intro c η hc hη
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K := Real.log (Real.log 2) with hK
  have hLeq : ∀ m : ℕ, 1 ≤ m → Real.log (Real.log ((2 : ℝ) ^ m)) = Real.log m + K := by
    intro m hm
    have hm' : (0:ℝ) < m := by exact_mod_cast hm
    rw [Real.log_pow, Real.log_mul hm'.ne' hlog2.ne']
  have hlogm : Tendsto (fun m : ℕ => Real.log (m:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hL : Tendsto (fun m : ℕ => Real.log (m:ℝ) + K) atTop atTop :=
    tendsto_atTop_add_const_right _ K hlogm
  have hLη : Tendsto (fun m : ℕ => (Real.log (m:ℝ) + K) ^ η) atTop atTop :=
    (tendsto_rpow_atTop hη).comp hL
  have e1 := hLη.eventually_ge_atTop (4 / c)
  have e2 := hlogm.eventually_ge_atTop (-2 * K)
  have e3 := hlogm.eventually_ge_atTop 0
  have e4 := eventually_ge_atTop (1 : ℕ)
  refine Summable.of_norm_bounded_eventually_nat (Real.summable_nat_pow_inv.mpr one_lt_two) ?_
  filter_upwards [e1, e2, e3, e4] with m h1 h2 h3 h4

  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hLeq m h4]
  have hm' : (0:ℝ) < m := by exact_mod_cast h4
  have hA : (1/2) * Real.log m ≤ Real.log m + K := by linarith
  have hA0 : 0 ≤ Real.log m + K := by linarith
  have hpow : (Real.log m + K) ^ (1 + η) = (Real.log m + K) * (Real.log m + K) ^ η := by
    rw [Real.rpow_add' hA0 (by positivity), Real.rpow_one]
  have hB : ((1/2) * Real.log m) * (4 / c) ≤ (Real.log m + K) * (Real.log m + K) ^ η :=
    mul_le_mul hA h1 (by positivity) hA0
  have hC : 2 * Real.log m ≤ c * (Real.log m + K) ^ (1 + η) := by
    rw [hpow]
    have : c * (((1/2) * Real.log m) * (4 / c)) = 2 * Real.log m := by
      field_simp; ring
    rw [← this]
    exact mul_le_mul_of_nonneg_left hB hc.le
  have hE : Real.exp (2 * Real.log m) = (m:ℝ) ^ 2 := by
    rw [show (2:ℝ) * Real.log m = Real.log ((m:ℝ) ^ 2) by rw [Real.log_pow]; norm_num,
      Real.exp_log (by positivity)]
  calc Real.exp (-c * (Real.log m + K) ^ (1 + η)) ≤ Real.exp (-(2 * Real.log m)) := by
        apply Real.exp_le_exp.mpr; linarith
    _ = ((m:ℝ) ^ 2)⁻¹ := by rw [Real.exp_neg, hE]
