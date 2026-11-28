import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1
import Mathlib.Analysis.PSeries

-- Credit: @ChristFollower873461
-- uses note #175650 (inverse-square comparison); retain log b for general bases.
open Filter Real

lemma OMA.summable_loglog_geometric {b c η : ℝ}
    (hb : 1 < b) (hc : 0 < c) (hη : 0 < η) :
    Summable (fun j : ℕ ↦ exp (-c * (log (log (b ^ j))) ^ (1 + η))) := by
  let L (j : ℕ) := log (log (b ^ j))
  have hL : Tendsto L atTop atTop :=
    tendsto_log_atTop.comp (tendsto_log_atTop.comp (tendsto_pow_atTop_atTop_of_one_lt hb))
  have growth := (tendsto_rpow_atTop hη).comp hL
  have majorant := (Real.summable_nat_pow_inv.mpr (by decide : 1 < (2 : ℕ))).mul_left
    (((log b) ^ 2)⁻¹)
  refine Summable.of_norm_bounded_eventually_nat majorant ?_
  filter_upwards [growth.eventually_ge_atTop (2 / c), hL.eventually_gt_atTop 0,
    eventually_gt_atTop (0 : ℕ)] with j hlarge hpos hj
  change 2 / c ≤ L j ^ η at hlarge
  have hcoef : 2 ≤ L j ^ η * c := (div_le_iff₀ hc).mp hlarge
  have hdecay : 2 * L j ≤ c * L j ^ (1 + η) := by
    rw [add_comm, rpow_add_one hpos.ne']
    nlinarith [mul_le_mul_of_nonneg_right hcoef hpos.le]
  have harg : 0 < (j : ℝ) * log b := mul_pos (by exact_mod_cast hj) (log_pos hb)
  rw [Real.norm_of_nonneg (exp_pos _).le]
  calc
    exp (-c * L j ^ (1 + η)) ≤ exp (-(2 * L j)) := exp_le_exp.mpr (by linarith)
    _ = (((j : ℝ) * log b) ^ 2)⁻¹ := by
      rw [exp_neg]
      unfold L
      have hs : log (((j : ℝ) * log b) ^ 2) = 2 * log ((j : ℝ) * log b) := by
        simpa using Real.log_pow ((j : ℝ) * log b) 2
      rw [Real.log_pow b j, ← hs, exp_log (sq_pos_of_pos harg)]
    _ = _ := by simp [mul_pow, mul_comm]

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1.H2 := by
  intro c η hc hη
  exact OMA.summable_loglog_geometric (by norm_num) hc hη
