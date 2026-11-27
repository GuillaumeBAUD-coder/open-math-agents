import OMAReductions.R_Erdos976_erdos_976_variants_erdos_R1
import Mathlib

-- Step Erdos976.erdos_976.variants.erdos.R1.H2: hypothesis H2 of reduction Erdos976.erdos_976.variants.erdos.R1
-- Credit: @ivillar

/-!
# `(log n) ^ (log log log n)` is dominated by `exp ((log n) ^ c)`

With `y = log (log n)` we have `(log n) ^ (log y) = exp (y * log y)` and
`(log n) ^ c = exp (c * y)`. For large `y`, `y * log y ≤ y ^ 2 ≤ exp (c * y)`.
-/

namespace Erdos976CompareStep

open Filter Asymptotics

theorem compare : ∀ c > (0 : ℝ),
    (fun n : ℕ ↦ (n : ℝ) * Real.log n ^ Real.log (Real.log (Real.log n))) =O[atTop]
    (fun n : ℕ ↦ (n : ℝ) * Real.exp (Real.log n ^ c)) := by
  intro c hc
  have hx : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hy : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hx
  have hexp := (isLittleO_pow_exp_pos_mul_atTop 2 hc).bound (show (0 : ℝ) < 1 by norm_num)
  refine IsBigO.of_bound 1 ?_
  filter_upwards [hy.eventually hexp, hy.eventually (eventually_ge_atTop 1),
    hx.eventually (eventually_gt_atTop 1)] with n h1 h2 h3
  have hx0 : 0 < Real.log (n : ℝ) := by linarith
  have hy0 : 0 < Real.log (Real.log (n : ℝ)) := by linarith
  rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (Real.exp_pos _).le, one_mul] at h1
  have hlogy : Real.log (Real.log (Real.log (n : ℝ))) ≤ Real.log (Real.log (n : ℝ)) := by
    have := Real.log_le_sub_one_of_pos hy0
    linarith
  have hkey : Real.log (Real.log (n : ℝ)) * Real.log (Real.log (Real.log (n : ℝ))) ≤
      Real.exp (Real.log (Real.log (n : ℝ)) * c) := by
    calc Real.log (Real.log (n : ℝ)) * Real.log (Real.log (Real.log (n : ℝ)))
        ≤ Real.log (Real.log (n : ℝ)) * Real.log (Real.log (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hlogy hy0.le
      _ = Real.log (Real.log (n : ℝ)) ^ 2 := (sq _).symm
      _ ≤ Real.exp (c * Real.log (Real.log (n : ℝ))) := h1
      _ = Real.exp (Real.log (Real.log (n : ℝ)) * c) := by rw [mul_comm]
  have hpow : Real.log (n : ℝ) ^ Real.log (Real.log (Real.log (n : ℝ))) ≤
      Real.exp (Real.log (n : ℝ) ^ c) := by
    rw [Real.rpow_def_of_pos hx0, Real.rpow_def_of_pos hx0]
    exact Real.exp_le_exp.mpr hkey
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [Real.norm_of_nonneg (mul_nonneg hn0 (Real.rpow_nonneg hx0.le _)),
    Real.norm_of_nonneg (mul_nonneg hn0 (Real.exp_pos _).le), one_mul]
  exact mul_le_mul_of_nonneg_left hpow hn0

end Erdos976CompareStep

theorem OMA.solution : OMA.R_Erdos976_erdos_976_variants_erdos_R1.H2 :=
  Erdos976CompareStep.compare
