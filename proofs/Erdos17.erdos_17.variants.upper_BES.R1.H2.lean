import OMAReductions.R_Erdos17_erdos_17_variants_upper_BES_R1
import Mathlib

/-! With `L = log log x`, eventually `L ≥ A / c`, so `c L² ≥ A L` and
`exp (-c L²) ≤ exp (-A L) = (log x)^(-A)`. -/

open Filter Asymptotics

theorem OMA.solution : OMA.R_Erdos17_erdos_17_variants_upper_BES_R1.H2 := by
  intro A hA c hc
  apply IsBigO.of_bound 1
  have hL : Tendsto (fun x : ℕ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hL.eventually_ge_atTop (A / c), hL.eventually_gt_atTop 0] with x hx hx0
  have hlog0 : 0 ≤ Real.log (x : ℝ) := Real.log_natCast_nonneg x
  have hlogx : 0 < Real.log (x : ℝ) := by
    rcases hlog0.lt_or_eq with h | h
    · exact h
    · rw [← h, Real.log_zero] at hx0
      exact absurd hx0 (lt_irrefl 0)
  have hxpos : (0 : ℝ) < x := by
    rcases (Nat.cast_nonneg x : (0 : ℝ) ≤ x).lt_or_eq with h | h
    · exact h
    · rw [← h, Real.log_zero] at hlogx
      exact absurd hlogx (lt_irrefl 0)
  set L := Real.log (Real.log (x : ℝ)) with hLdef
  have hAL : A ≤ c * L := by
    rw [div_le_iff₀ hc] at hx
    linarith
  have hcL : A * L ≤ c * L ^ 2 := by nlinarith
  have h1 : Real.exp (-c * L ^ 2) ≤ Real.exp (-(A * L)) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-(A * L)) = (Real.log (x : ℝ) ^ A)⁻¹ := by
    rw [Real.exp_neg, Real.rpow_def_of_pos hlogx, ← hLdef, mul_comm]
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul,
    div_eq_mul_inv, ← h2]
  exact mul_le_mul_of_nonneg_left h1 hxpos.le
