import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R1
import Mathlib

namespace OMA.Helpers

open Filter

/-- The iterated logarithm along dyadic scales tends to infinity. -/
lemma e142dyad_loglog_tendsto :
    Tendsto (fun m : ℕ => Real.log (Real.log ((2 : ℝ) ^ m))) atTop atTop := by
  have hlin : Tendsto (fun m : ℕ => (m : ℝ) * Real.log 2) atTop atTop :=
    Tendsto.atTop_mul_const (Real.log_pos (by norm_num)) tendsto_natCast_atTop_atTop
  refine (Real.tendsto_log_atTop.comp hlin).congr ?_
  intro m
  simp [Function.comp, Real.log_pow]

/-- Comparison of `log m` with the dyadic iterated logarithm. -/
lemma e142dyad_log_le (m : ℕ) (hm : 1 ≤ m) :
    Real.log (m : ℝ) ≤ Real.log (Real.log ((2 : ℝ) ^ m)) + 1 := by
  have hl2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; norm_num at this ⊢; linarith
  have hm0 : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  rw [Real.log_pow]
  have hhalf : (m : ℝ) / 2 ≤ (m : ℝ) * Real.log 2 := by nlinarith
  have hA : Real.log ((m : ℝ) / 2) ≤ Real.log ((m : ℝ) * Real.log 2) :=
    Real.log_le_log (div_pos hm0 two_pos) hhalf
  rw [Real.log_div (by positivity) (by norm_num)] at hA
  have hl2' : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; norm_num at this ⊢; linarith
  linarith

end OMA.Helpers

open Filter in
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R1.H2 := by
  intro c η hc hη
  have hT := OMA.Helpers.e142dyad_loglog_tendsto
  have hTη : Tendsto (fun m : ℕ => Real.log (Real.log ((2 : ℝ) ^ m)) ^ η) atTop atTop :=
    (tendsto_rpow_atTop hη).comp hT
  have hg : Summable (fun m : ℕ => ((m : ℝ) ^ 2)⁻¹) := Real.summable_nat_pow_inv.mpr (by norm_num)
  refine Summable.of_norm_bounded_eventually_nat hg ?_
  filter_upwards [hT.eventually_ge_atTop 1, hTη.eventually_ge_atTop (4 / c),
    eventually_ge_atTop 1] with m hX hXη hm
  set X := Real.log (Real.log ((2 : ℝ) ^ m)) with hXdef
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  have hlog := OMA.Helpers.e142dyad_log_le m hm
  rw [← hXdef] at hlog
  have hm0 : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hX0 : 0 < X := by linarith
  have hsplit : X ^ (1 + η) = X * X ^ η := by
    rw [Real.rpow_add hX0, Real.rpow_one]
  have hcX : 4 ≤ c * X ^ η := by
    have := mul_le_mul_of_nonneg_left hXη hc.le
    rwa [mul_div_cancel₀ _ hc.ne'] at this
  have hkey : 2 * Real.log (m : ℝ) ≤ c * X ^ (1 + η) := by
    rw [hsplit]
    nlinarith
  have hexp : Real.exp (-c * X ^ (1 + η)) ≤ Real.exp (-(2 * Real.log (m : ℝ))) :=
    Real.exp_le_exp.mpr (by linarith)
  calc Real.exp (-c * X ^ (1 + η)) ≤ Real.exp (-(2 * Real.log (m : ℝ))) := hexp
    _ = ((m : ℝ) ^ 2)⁻¹ := by
      rw [Real.exp_neg, two_mul, Real.exp_add, Real.exp_log hm0, sq]
