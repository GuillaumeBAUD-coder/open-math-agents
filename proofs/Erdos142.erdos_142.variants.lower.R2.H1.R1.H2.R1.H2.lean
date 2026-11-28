import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1

-- Step Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R1.H2: hypothesis H2 of reduction Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R1
-- Credit: @thatoneguy006
-- H2 := ∀ c η : ℝ, 0 < c → 0 < η →     Summable (fun j : ℕ ↦ Real.exp (-c * (Real.log (Real.log ((4 : ℝ) ^ j))) ^ (1 + η)))

/-!
Since log (log (4 ^ j)) = log (j * log 4) ≥ log j and (log j) ^ η → ∞, eventually
c * (log log 4 ^ j) ^ (1 + η) ≥ 2 * log j, so each term is at most j ^ (-2), which is summable.
-/

namespace OMAStepE142H2

open Filter Real

theorem e142_step_summable : ∀ c η : ℝ, 0 < c → 0 < η →
    Summable (fun j : ℕ ↦ Real.exp (-c * (Real.log (Real.log ((4 : ℝ) ^ j))) ^ (1 + η))) := by
  intro c η hc hη
  have hlog4 : 1 < Real.log 4 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  -- (log j)^η eventually exceeds 2/c
  have hev : ∀ᶠ j : ℕ in atTop, 2 / c ≤ (Real.log (j : ℝ)) ^ η :=
    ((tendsto_rpow_atTop hη).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually_ge_atTop (2 / c)
  have hsum : Summable (fun j : ℕ ↦ (j : ℝ) ^ (-2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  refine Summable.of_norm_bounded_eventually_nat hsum ?_
  filter_upwards [hev, eventually_ge_atTop 3] with j hj hj3
  have hjpos : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hj1 : (1 : ℝ) < j := by exact_mod_cast (show 1 < j by omega)
  have hlogj : 0 < Real.log (j : ℝ) := Real.log_pos hj1
  set L := Real.log (Real.log ((4 : ℝ) ^ j)) with hL
  have hLeq : L = Real.log ((j : ℝ) * Real.log 4) := by rw [hL, Real.log_pow]
  have hLge : Real.log (j : ℝ) ≤ L := by
    rw [hLeq]
    exact Real.log_le_log hjpos (by nlinarith)
  have hLpos : 0 < L := lt_of_lt_of_le hlogj hLge
  have hLη : 2 / c ≤ L ^ η :=
    le_trans hj (Real.rpow_le_rpow hlogj.le hLge hη.le)
  have hsplit : L ^ (1 + η) = L * L ^ η := by
    rw [Real.rpow_add hLpos, Real.rpow_one]
  have key : 2 * Real.log (j : ℝ) ≤ c * L ^ (1 + η) := by
    rw [hsplit]
    have h2 : 2 ≤ c * L ^ η := by
      have := mul_le_mul_of_nonneg_left hLη hc.le
      rwa [mul_div_cancel₀ _ hc.ne'] at this
    nlinarith
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.rpow_def_of_pos hjpos]
  apply Real.exp_le_exp.mpr
  linarith

end OMAStepE142H2

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1.H2 :=
  OMAStepE142H2.e142_step_summable
