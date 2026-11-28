import FormalConjectures.ErdosProblems.«1048»

/-! For positive `n`, the level set of `X ^ n` is the closed unit disk,
which is preconnected and has diameter two. This follows the proofs by
Genbox (PR #13) and VestigeClub (PR #10863). -/

open Polynomial Erdos1043

theorem OMA.solution : type_of% @Erdos1048.erdos_1048.variants.diam_ge_two_is_best := by
  intro n hn
  have hn' : n ≠ 0 := by omega
  have hlevel : levelSet ((X : ℂ[X]) ^ n) = Metric.closedBall (0 : ℂ) 1 := by
    ext z
    simp only [levelSet, Set.mem_ofPred_eq, eval_pow, eval_X, norm_pow, Metric.mem_closedBall,
      dist_zero_right, pow_le_one_iff_of_nonneg (norm_nonneg _) hn']
  rw [hlevel, Metric.isPreconnected_closedBall.connectedComponentIn (by simp)]
  rw [← ENNReal.ofReal_toReal Metric.isBounded_closedBall.ediam_ne_top, ← Metric.diam]
  norm_num [Metric.diam_closedBall_eq]
