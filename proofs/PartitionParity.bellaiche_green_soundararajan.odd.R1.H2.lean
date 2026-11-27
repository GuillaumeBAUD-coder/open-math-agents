import OMAReductions.R_PartitionParity_bellaiche_green_soundararajan_odd_R1
import Mathlib

-- Step PartitionParity.bellaiche_green_soundararajan.odd.R1.H2: hypothesis H2 of reduction PartitionParity.bellaiche_green_soundararajan.odd.R1
-- Credit: @ivillar (original proof).
-- Strategy. For X >= exp(e), log log X >= 1, so sqrt X / log log X <= sqrt X.

open Filter Asymptotics in
theorem OMA.solution : OMA.R_PartitionParity_bellaiche_green_soundararajan_odd_R1.H2 := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop (Real.exp (Real.exp 1))] with X hX
  have hlog : Real.exp 1 ≤ Real.log X := by
    rw [← Real.log_exp (Real.exp 1)]
    exact Real.log_le_log (Real.exp_pos _) hX
  have hll : 1 ≤ Real.log (Real.log X) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hlog
  have hs := Real.sqrt_nonneg X
  have hq : 0 ≤ Real.sqrt X / Real.log (Real.log X) := div_nonneg hs (by linarith)
  rw [Real.norm_of_nonneg hq, Real.norm_of_nonneg hs, one_mul]
  exact div_le_self hs hll
