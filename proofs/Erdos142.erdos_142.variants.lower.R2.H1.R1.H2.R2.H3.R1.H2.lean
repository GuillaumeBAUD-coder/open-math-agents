import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R1
import Mathlib

/-!
Step H2 of the reduction Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R2.H3.R1: the saving exp(-c (log log 2^m)^(1+eta)) is summable in m.

Since log (2^m) = m log 2, put L = log (m log 2) = log m + log log 2. For large m we have
L^eta >= 4 / c and log m <= 2 L, so c L^(1+eta) >= 4 L >= 2 log m and the term is at most
1 / m^2. Comparison with the convergent series of 1 / m^2.
-/

open Filter

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R1.H2 := by
  intro c η hc hη
  have hs : Summable (fun m : ℕ => (1 : ℝ) / (m : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  refine hs.of_norm_bounded_eventually_nat ?_
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL : Tendsto (fun m : ℕ => Real.log ((m : ℝ) * Real.log 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.atTop_mul_const hl2)
  have hP : Tendsto (fun m : ℕ => Real.log ((m : ℝ) * Real.log 2) ^ η) atTop atTop :=
    (tendsto_rpow_atTop hη).comp hL
  have hlogm : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop 0, hP.eventually_ge_atTop (4 / c),
    hlogm.eventually_ge_atTop (-2 * Real.log (Real.log 2)), hL.eventually_gt_atTop 0]
    with m hm hp hlm hLpos
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have key : Real.log ((2 : ℝ) ^ m) = (m : ℝ) * Real.log 2 := Real.log_pow _ _
  rw [key, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hLeq : Real.log ((m : ℝ) * Real.log 2) = Real.log m + Real.log (Real.log 2) :=
    Real.log_mul hm'.ne' hl2.ne'
  have h1 : Real.log m ≤ 2 * Real.log ((m : ℝ) * Real.log 2) := by rw [hLeq]; linarith
  have h2 : 4 * Real.log ((m : ℝ) * Real.log 2) ≤ c * Real.log ((m : ℝ) * Real.log 2) ^ (1 + η) := by
    rw [Real.rpow_add hLpos, Real.rpow_one]
    have h4 := (div_le_iff₀ hc).mp hp
    nlinarith [mul_le_mul_of_nonneg_right h4 hLpos.le]
  have h3 : Real.exp (-c * Real.log ((m : ℝ) * Real.log 2) ^ (1 + η)) ≤
      Real.exp (-(2 * Real.log m)) := Real.exp_le_exp.mpr (by linarith)
  refine h3.trans (le_of_eq ?_)
  rw [Real.exp_neg, show (2 : ℝ) * Real.log m = Real.log ((m : ℝ) ^ 2) by
    rw [Real.log_pow]; norm_num, Real.exp_log (by positivity), one_div]
