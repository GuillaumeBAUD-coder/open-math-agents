import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds

-- Step Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R1.H2
-- Credit: @Luckylamb666

open Filter

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1.H2 := by
  intro c η hc hη
  have hlog4_gt1 : (1 : ℝ) < Real.log 4 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 4)]
    linarith [Real.exp_one_lt_d9]
  have hlog4_pos : 0 < Real.log 4 := by linarith
  let B : ℝ := (2 / c) ^ (1 / η)
  let N0 : ℕ := Nat.ceil (Real.exp B) + 2
  have hsum : Summable (fun j : ℕ => (1 : ℝ) / ((j : ℝ) ^ (2 : ℕ))) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  refine Summable.of_norm_bounded_eventually_nat hsum ?_
  filter_upwards [eventually_ge_atTop N0] with j hj
  have hj2 : (2 : ℝ) ≤ (j : ℝ) := by
    have : 2 ≤ j := by omega
    exact_mod_cast this
  have hj_pos : (0 : ℝ) < (j : ℝ) := by linarith
  have hj_ge_exp : Real.exp B ≤ (j : ℝ) := by
    have h1 : Real.exp B ≤ (Nat.ceil (Real.exp B) : ℝ) := Nat.le_ceil _
    have h2 : Nat.ceil (Real.exp B) ≤ j := by omega
    have h3 : (Nat.ceil (Real.exp B) : ℝ) ≤ (j : ℝ) := by exact_mod_cast h2
    linarith
  have hlogj_ge_B : B ≤ Real.log (j : ℝ) := by
    have h1 := Real.log_le_log (Real.exp_pos B) hj_ge_exp
    rwa [Real.log_exp] at h1
  have hlogj_pos : 0 < Real.log (j : ℝ) := Real.log_pos (by linarith)
  have hB_pos : 0 < B := Real.rpow_pos_of_pos (by positivity) _
  have hlogj_eta : 2 / c ≤ (Real.log (j : ℝ)) ^ η := by
    have h1 : B ^ η ≤ (Real.log (j : ℝ)) ^ η :=
      Real.rpow_le_rpow (le_of_lt hB_pos) hlogj_ge_B (le_of_lt hη)
    have h2 : B ^ η = 2 / c := by
      dsimp only [B]
      rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2 / c), one_div_mul_cancel (ne_of_gt hη),
        Real.rpow_one]
    linarith
  have hxj_ge : Real.log (j : ℝ) ≤ Real.log (Real.log ((4 : ℝ) ^ j)) := by
    rw [Real.log_pow]
    have hmul : (j : ℝ) ≤ (j : ℝ) * Real.log 4 := by nlinarith
    exact Real.log_le_log hj_pos hmul
  have hpow_ge : (Real.log (j : ℝ)) ^ (1 + η) ≤ (Real.log (Real.log ((4 : ℝ) ^ j))) ^ (1 + η) :=
    Real.rpow_le_rpow (le_of_lt hlogj_pos) hxj_ge (by linarith)
  have h1eta : (Real.log (j : ℝ)) ^ (1 + η) = Real.log (j : ℝ) * (Real.log (j : ℝ)) ^ η := by
    rw [Real.rpow_add hlogj_pos, Real.rpow_one]
  have hmain_ineq : 2 * Real.log (j : ℝ) ≤ c * (Real.log (Real.log ((4 : ℝ) ^ j))) ^ (1 + η) := by
    have hmul : 2 ≤ c * (Real.log (j : ℝ)) ^ η := by
      have := mul_le_mul_of_nonneg_left hlogj_eta (le_of_lt hc)
      rwa [mul_div_cancel₀ _ (ne_of_gt hc)] at this
    have hstep1 : 2 * Real.log (j : ℝ) ≤ c * (Real.log (j : ℝ)) ^ (1 + η) := by
      rw [h1eta]
      nlinarith
    nlinarith
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hexp_eq : Real.exp (-(2 * Real.log (j : ℝ))) = (1 : ℝ) / ((j : ℝ) ^ (2 : ℕ)) := by
    rw [Real.exp_neg, mul_comm 2, Real.exp_mul, Real.exp_log hj_pos, Real.rpow_two, one_div]
  rw [← hexp_eq]
  apply Real.exp_le_exp.mpr
  linarith
