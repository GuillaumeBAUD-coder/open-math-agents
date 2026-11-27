import OMAReductions.R_Erdos375_erdos_375_variants_bounded_gap_R1
import Mathlib.NumberTheory.Chebyshev

open Filter

/-- Chebyshev's estimate implies that the prime count is sublinear. -/
theorem OMA.solution : OMA.R_Erdos375_erdos_375_variants_bounded_gap_R1.H2 := by
  intro c hc
  let A := Real.log 4 + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hCast : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hLog : Tendsto (fun k : ℕ => Real.log (k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hCast
  filter_upwards [hCast.eventually (Chebyshev.eventually_primeCounting_le
      (show (0 : ℝ) < 1 by norm_num)),
    hLog.eventually_gt_atTop (A / c), eventually_ge_atTop (1 : ℕ)] with k hcount hlarge hk
  have hK : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hLogPos : 0 < Real.log (k : ℝ) :=
    (div_pos hA hc).trans hlarge
  have hRatio : A < c * Real.log (k : ℝ) := by
    simpa [mul_comm] using (div_lt_iff₀ hc).mp hlarge
  have hBound : ((Nat.primeCounting k : ℕ) : ℝ) ≤ A * (k : ℝ) / Real.log (k : ℝ) := by
    simpa [A] using hcount
  rw [Nat.primesBelow_card_eq_primeCounting']
  change (Nat.primeCounting k : ℝ) < _
  exact hBound.trans_lt <| (div_lt_iff₀ hLogPos).mpr <| by
    simpa only [mul_right_comm, mul_comm (Real.log (k : ℝ))] using
      mul_lt_mul_of_pos_right hRatio hK
