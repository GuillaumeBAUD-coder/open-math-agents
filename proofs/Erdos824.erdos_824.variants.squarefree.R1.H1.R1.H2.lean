import OMAReductions.R_Erdos824_erdos_824_variants_squarefree_R1_H1_R1
import Mathlib

/-! Both the higher prime powers and the contribution below the prime cutoff
are smaller than the target power of y. -/

open Filter Real

namespace E824PrimePowerError

theorem main : ∀ η : ℝ, 0 < η → ∃ e : ℝ, 0 < e ∧ ∀ᶠ y : ℝ in atTop,
    Chebyshev.psi (5*y) - Chebyshev.theta (5*y) + y^(1-η) * log (5*y) < y^(1-e) := by
  intro η hη
  let e : ℝ := min (η/2) (1/4)
  have he : 0 < e := lt_min (by positivity) (by norm_num)
  have heη : e < η := (min_le_left _ _).trans_lt (by linarith)
  have he₂ : e < 1/2 := (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨e,he,?_⟩
  obtain ⟨C,hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hs := (tendsto_rpow_atTop (sub_pos.mpr he₂)).eventually_ge_atTop (3*C*sqrt 5)
  have hconst := (tendsto_rpow_atTop (sub_pos.mpr heη)).eventually_ge_atTop (6*log 5)
  have hlog := (isLittleO_log_rpow_atTop (sub_pos.mpr heη)).def (by norm_num : (0:ℝ) < 1/6)
  filter_upwards [hs,hconst,hlog,eventually_ge_atTop (1:ℝ)] with y hs hc hl hy
  have hy' : 0 < y := zero_lt_one.trans_le hy
  have hpow : 0 < y^(1-e) := rpow_pos_of_pos hy' _
  have hfirst : Chebyshev.psi (5*y) - Chebyshev.theta (5*y) ≤ y^(1-e)/3 := by
    apply (hC (5*y)).trans
    rw [sqrt_mul (by norm_num : (0:ℝ) ≤ 5), sqrt_eq_rpow y]
    have hmul := mul_le_mul_of_nonneg_right hs (rpow_nonneg hy'.le (1/2:ℝ))
    rw [← rpow_add hy', show (1/2-e : ℝ) + 1/2 = 1-e by ring] at hmul
    nlinarith only [hmul]
  have hlog' : log y ≤ (1/6 : ℝ) * y^(η-e) := by
    simpa only [norm_eq_abs, abs_of_nonneg (log_nonneg hy), abs_of_nonneg (rpow_nonneg hy'.le _)]
      using hl
  have hsecond : y^(1-η) * log (5*y) ≤ y^(1-e)/3 := by
    rw [log_mul (by norm_num : (5:ℝ) ≠ 0) hy'.ne']
    have hsum : log 5 + log y ≤ y^(η-e)/3 := by linarith only [hc,hlog']
    calc
      _ ≤ y^(1-η) * (y^(η-e)/3) := mul_le_mul_of_nonneg_left hsum (rpow_nonneg hy'.le _)
      _ = _ := by rw [← mul_div_assoc, ← rpow_add hy']; congr 2 <;> ring
  linarith only [hfirst,hsecond,hpow]

end E824PrimePowerError

theorem OMA.solution : OMA.R_Erdos824_erdos_824_variants_squarefree_R1_H1_R1.H2 :=
  E824PrimePowerError.main