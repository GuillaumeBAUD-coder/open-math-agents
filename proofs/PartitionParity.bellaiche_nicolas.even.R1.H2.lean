import OMAReductions.R_PartitionParity_bellaiche_nicolas_even_R1
import Mathlib

open Real
-- Step PartitionParity.bellaiche_nicolas.even.R1.H2: hypothesis H2 of reduction PartitionParity.bellaiche_nicolas.even.R1
-- Credit: @ivillar (original proof).
-- Strategy. For X >= e both sides are nonnegative and sqrt X log log X <= (1/c) F X.

open Filter Asymptotics in
theorem OMA.solution : OMA.R_PartitionParity_bellaiche_nicolas_even_R1.H2 := by
  intro c F hc hF
  apply IsBigO.of_bound (1 / c)
  filter_upwards [eventually_ge_atTop (exp 1)] with X hX
  have hX1 : 1 < X := lt_of_lt_of_le (by simp [one_lt_exp_iff]) hX
  have hlog : 1 ≤ log X := by
    rw [← log_exp 1]
    exact log_le_log (exp_pos 1) hX
  have hll : 0 ≤ log (log X) := log_nonneg hlog
  have hval : 0 ≤ sqrt X * log (log X) := mul_nonneg (sqrt_nonneg X) hll
  have hb := hF X hX1
  have hFX : 0 ≤ F X := le_trans (by rw [mul_assoc]; exact mul_nonneg hc.le hval) hb
  rw [norm_of_nonneg hval, norm_of_nonneg hFX]
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc]
  linarith
