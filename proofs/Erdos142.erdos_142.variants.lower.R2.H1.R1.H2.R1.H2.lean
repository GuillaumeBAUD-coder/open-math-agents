import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter Real

-- The double-logarithmic exponential is eventually at most j^(-2).
-- Step H2 of Yevhen Diachenko’s reduction #29901.
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1.H2 := by
  intro c η hc hη
  have h4 : 1 ≤ log (4 : ℝ) := by
    rw [log_four_eq]
    linarith [log_two_gt_d9]
  have hseq : Tendsto (fun j : ℕ ↦ log (log ((4 : ℝ) ^ j))) atTop atTop := by
    simpa only [log_pow, Function.comp_def] using
      tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.atTop_mul_const (lt_of_lt_of_le zero_lt_one h4))
  have hgrowth := ((tendsto_rpow_atTop hη).comp hseq).const_mul_atTop hc
  have hbound : ∀ᶠ j : ℕ in atTop,
      exp (-c * log (log ((4 : ℝ) ^ j)) ^ (1 + η)) ≤ (j : ℝ) ^ (-2 : ℝ) := by
    filter_upwards [hgrowth.eventually_ge_atTop 2, hseq.eventually_gt_atTop 0,
      eventually_ge_atTop (1 : ℕ)] with j hg hx hj
    change 2 ≤ c * log (log ((4 : ℝ) ^ j)) ^ η at hg
    have hjpos : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have hl : log (j : ℝ) ≤ log (log ((4 : ℝ) ^ j)) := by
      rw [log_pow]
      exact log_le_log hjpos (le_mul_of_one_le_right hjpos.le h4)
    have hm := mul_le_mul_of_nonneg_left hg hx.le
    rw [Real.rpow_add hx, Real.rpow_one]
    calc
      exp (-c * (log (log ((4 : ℝ) ^ j)) * log (log ((4 : ℝ) ^ j)) ^ η))
          ≤ exp (log (j : ℝ) * (-2)) := by
        apply exp_le_exp.mpr
        nlinarith only [hm, hl]
      _ = (j : ℝ) ^ (-2 : ℝ) := (rpow_def_of_pos hjpos _).symm
  obtain ⟨J, hJ⟩ := eventually_atTop.1 hbound
  have hsum : Summable (fun j : ℕ ↦ (j : ℝ) ^ (-2 : ℝ)) :=
    summable_nat_rpow.mpr (by norm_num)
  apply (summable_nat_add_iff J).mp
  exact Summable.of_nonneg_of_le (fun j ↦ (exp_pos _).le)
    (fun j ↦ hJ (j + J) (by omega)) ((summable_nat_add_iff J).mpr hsum)
