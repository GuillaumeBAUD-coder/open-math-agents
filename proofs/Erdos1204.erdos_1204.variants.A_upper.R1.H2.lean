import OMAReductions.R_Erdos1204_erdos_1204_variants_A_upper_R1
import Mathlib.NumberTheory.Chebyshev

/-! Chebyshev's upper bound implies the primes have density zero. -/

open Filter Real

theorem OMA.solution : OMA.R_Erdos1204_erdos_1204_variants_A_upper_R1.H2 := by
  intro δ hδ
  have hcast := tendsto_natCast_atTop_atTop (R := ℝ)
  filter_upwards [hcast.eventually (Chebyshev.eventually_primeCounting_le (ε := 1) zero_lt_one),
    (tendsto_log_atTop.comp hcast).eventually_ge_atTop ((log 4 + 1)/δ),
    eventually_ge_atTop 2] with k hk hlog hk2
  simp only [Nat.floor_natCast] at hk
  apply hk.trans
  have hl : 0 < log (k : ℝ) := log_pos (by exact_mod_cast (show 1 < k by omega))
  apply (div_le_iff₀ hl).mpr
  have hcoef := (div_le_iff₀ hδ).mp hlog
  simpa [Function.comp_apply, mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg (α := ℝ) k)
