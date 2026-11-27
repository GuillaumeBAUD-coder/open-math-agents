import OMAReductions.R_LatinSquare_growthRateZn_R1
import Mathlib

-- Step LatinSquare.growthRateZn.R1.H2: hypothesis H2 of reduction LatinSquare.growthRateZn.R1
-- Credit: @ivillar

/-!
# The logarithmic form of Stirling's formula used for the Latin-square growth rate

Mathlib's `Stirling.log_stirlingSeq_formula` gives
`log n! = log (stirlingSeq n) + log (2 n) / 2 + n (log n - 1)`, and `stirlingSeq n → √π`. Hence
`(log n! - (n - 1) log n) / n = log (stirlingSeq n) / n + (log 2 / 2) / n + (3 / 2) (log n / n) - 1`
tends to `-1`.
-/

namespace LatinSquareStirlingStep

open Real Filter
open scoped Topology

theorem stirling_log : Tendsto (fun n : ℕ ↦ (log (n.factorial : ℝ) -
  ((n : ℝ)-1)*log n) / n) atTop (𝓝 (-1)) := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hpi : (√π : ℝ) ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hlog : Tendsto (fun n : ℕ => log (Stirling.stirlingSeq n)) atTop (𝓝 (log (√π))) :=
    (Real.continuousAt_log hpi).tendsto.comp Stirling.tendsto_stirlingSeq_sqrt_pi
  have h1 : Tendsto (fun n : ℕ => log (Stirling.stirlingSeq n) / (n : ℝ)) atTop (𝓝 0) :=
    hlog.div_atTop hcast
  have h2 : Tendsto (fun n : ℕ => log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp hcast
  have h3 : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hg : Tendsto (fun n : ℕ => log (Stirling.stirlingSeq n) / (n : ℝ) +
      (1 / 2 * log 2) * (1 / (n : ℝ)) + 3 / 2 * (log (n : ℝ) / (n : ℝ)) - 1) atTop
      (𝓝 (0 + (1 / 2 * log 2) * 0 + 3 / 2 * 0 - 1)) :=
    ((h1.add (h3.const_mul _)).add (h2.const_mul _)).sub_const 1
  have hlim : (0 + (1 / 2 * log 2) * 0 + 3 / 2 * 0 - 1 : ℝ) = -1 := by ring
  rw [hlim] at hg
  refine hg.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hf := Stirling.log_stirlingSeq_formula n
  rw [Real.log_mul (by norm_num) hn0.ne', Real.log_div hn0.ne' (Real.exp_pos 1).ne',
    Real.log_exp] at hf
  rw [eq_div_iff hn0.ne']
  have hfact : log (n.factorial : ℝ) = log (Stirling.stirlingSeq n) +
      1 / 2 * (log 2 + log (n : ℝ)) + (n : ℝ) * (log (n : ℝ) - 1) := by linarith
  rw [hfact]
  field_simp
  ring

end LatinSquareStirlingStep

theorem OMA.solution : OMA.R_LatinSquare_growthRateZn_R1.H2 :=
  LatinSquareStirlingStep.stirling_log
