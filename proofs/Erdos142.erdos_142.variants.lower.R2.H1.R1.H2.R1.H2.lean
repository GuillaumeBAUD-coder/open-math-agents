import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds


/-! Step H2: the saving exp(-c (log log 4^j)^(1+eta)) is summable.
For j at least 2, log log 4^j is at least log j (log 4 > 1), and eventually (log j)^eta is at least 2/c,
so the term is at most exp(-2 log j) = 1/j^2, which is summable. -/
open Filter

namespace OMA.H2_erdos142

theorem summable_saving : ∀ c η : ℝ, 0 < c → 0 < η →
    Summable (fun j : ℕ ↦ Real.exp (-c * (Real.log (Real.log ((4 : ℝ) ^ j))) ^ (1 + η))) := by
  intro c η hc hη
  have hg : Summable (fun j : ℕ ↦ 1 / (j : ℝ) ^ 2) := Real.summable_one_div_nat_pow.mpr (by norm_num)
  refine Summable.of_norm_bounded_eventually_nat hg ?_
  have ht : Tendsto (fun j : ℕ ↦ (Real.log j) ^ η) atTop atTop :=
    (tendsto_rpow_atTop hη).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [ht.eventually_ge_atTop (2 / c), eventually_ge_atTop 2] with j hj hj2
  have hj1 : (1 : ℝ) < j := by exact_mod_cast (by omega : 1 < j)
  have hjpos : (0 : ℝ) < j := by linarith
  have hlogj : 0 < Real.log j := Real.log_pos hj1
  have hlog4 : 1 < Real.log 4 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have hL : Real.log j ≤ Real.log (Real.log ((4 : ℝ) ^ j)) := by
    apply Real.log_le_log hjpos
    rw [Real.log_pow]
    nlinarith
  have hpow : Real.log j * (2 / c) ≤ (Real.log (Real.log ((4 : ℝ) ^ j))) ^ (1 + η) := by
    calc Real.log j * (2 / c) ≤ Real.log j * (Real.log j) ^ η :=
          mul_le_mul_of_nonneg_left hj hlogj.le
      _ = (Real.log j) ^ (1 + η) := by rw [Real.rpow_add hlogj, Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow hlogj.le hL (by linarith)
  have h2 : -c * (Real.log (Real.log ((4 : ℝ) ^ j))) ^ (1 + η) ≤ -(2 * Real.log j) := by
    have hm := mul_le_mul_of_nonneg_left hpow hc.le
    have e : c * (Real.log j * (2 / c)) = 2 * Real.log j := by field_simp
    linarith
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-c * (Real.log (Real.log ((4 : ℝ) ^ j))) ^ (1 + η))
      ≤ Real.exp (-(2 * Real.log j)) := Real.exp_le_exp.mpr h2
    _ = 1 / (j : ℝ) ^ 2 := by
      rw [show 2 * Real.log j = Real.log ((j : ℝ) ^ 2) by rw [Real.log_pow]; norm_num,
        Real.exp_neg, Real.exp_log (by positivity), one_div]

end OMA.H2_erdos142

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1.H2 :=
  OMA.H2_erdos142.summable_saving
