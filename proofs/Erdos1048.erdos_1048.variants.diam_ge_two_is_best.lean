import FormalConjectures.ErdosProblems.«1048»

-- Shorter proof of the previously merged result: use the exact diameter
-- of a normed-space closed ball instead of reproving its two inequalities.
open Polynomial Erdos1043

theorem OMA.solution : type_of% @Erdos1048.erdos_1048.variants.diam_ge_two_is_best := by
  intro n hn
  have hlevel : levelSet ((X : ℂ[X]) ^ n) = Metric.closedBall (0 : ℂ) 1 := by
    ext z
    change ‖((X : ℂ[X]) ^ n).eval z‖ ≤ 1 ↔ dist z 0 ≤ 1
    rw [Polynomial.eval_pow, Polynomial.eval_X, norm_pow, dist_zero_right]
    exact pow_le_one_iff_of_nonneg (norm_nonneg _) (by omega)
  rw [hlevel, Metric.isPreconnected_closedBall.connectedComponentIn (by simp)]
  rw [← ENNReal.ofReal_toReal (Metric.isBounded_closedBall.ediam_ne_top)]
  change ENNReal.ofReal (Metric.diam (Metric.closedBall (0 : ℂ) 1)) = 2
  rw [Metric.diam_closedBall_eq _ (by norm_num)]
  norm_num

-- Original proof from the upstream repository, last author @Genbox.
