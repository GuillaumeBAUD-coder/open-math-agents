import OMAReductions.R_Erdos375_erdos_375_variants_bounded_gap_R1
import Mathlib.NumberTheory.Chebyshev

open Filter Real

theorem OMA.solution : OMA.R_Erdos375_erdos_375_variants_bounded_gap_R1.H2 := by
  intro c hc
  have hlog : Tendsto (fun k : ℕ => log (k : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
    [tendsto_natCast_atTop_atTop.eventually
      (Chebyshev.eventually_primeCounting_le (show (0 : ℝ) < 1 by norm_num)),
     hlog.eventually_gt_atTop ((log 4 + 1) / c),
     eventually_ge_atTop (2 : ℕ)] with k hcount hlarge hk
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hpos : 0 < log (k : ℝ) := log_pos (by linarith)
  have hscale : log 4 + 1 < c * log (k : ℝ) := by
    simpa only [mul_comm c] using (div_lt_iff₀ hc).mp hlarge
  rw [Nat.primesBelow_card_eq_primeCounting', ← Nat.primeCounting_eq_primeCounting'_succ]
  rw [Nat.floor_natCast] at hcount
  refine hcount.trans_lt ((div_lt_iff₀ hpos).mpr ?_)
  simpa only [mul_assoc, mul_comm (k : ℝ), mul_left_comm] using
    mul_lt_mul_of_pos_right hscale (show (0 : ℝ) < k by linarith)
