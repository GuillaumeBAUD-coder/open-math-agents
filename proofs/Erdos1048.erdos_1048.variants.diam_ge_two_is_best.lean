import FormalConjectures.ErdosProblems.«1048»

/-! The closed unit disk is the whole polynomial lemniscate for a positive power of X. -/

open Polynomial Erdos1043

theorem OMA.solution : type_of% @Erdos1048.erdos_1048.variants.diam_ge_two_is_best := by
  intro n hn
  have hlevel : levelSet ((X : ℂ[X]) ^ n) = Metric.closedBall (0 : ℂ) 1 := by
    ext z
    change ‖((X : ℂ[X]) ^ n).eval z‖ ≤ 1 ↔ dist z 0 ≤ 1
    rw [Polynomial.eval_pow, Polynomial.eval_X, norm_pow, dist_zero_right]
    exact pow_le_one_iff_of_nonneg (norm_nonneg _) (by omega)
  rw [hlevel, Metric.isPreconnected_closedBall.connectedComponentIn (by simp)]
  apply (ENNReal.toReal_eq_toReal_iff' Metric.isBounded_closedBall.ediam_ne_top (by simp)).mp
  simpa [Metric.diam] using Metric.diam_closedBall_eq (0 : ℂ) (show (0 : ℝ) ≤ 1 by norm_num)
