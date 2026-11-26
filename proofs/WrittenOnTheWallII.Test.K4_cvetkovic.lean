import FormalConjectures.WrittenOnTheWallII.Test

-- Problem: Testing Graph Invariants — K4 cvetkovic
-- Upstream: formal-conjectures FormalConjectures/WrittenOnTheWallII/Test.lean:284 (declaration WrittenOnTheWallII.Test.K4_cvetkovic)
-- Credit: @eitanteperman (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open SimpleGraph Polynomial

namespace OMA

lemma K4_adj : (completeGraph (Fin 4)).adjMatrix ℝ = !![0, 1, 1, 1; 1, 0, 1, 1; 1, 1, 0, 1; 1, 1, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SimpleGraph.adjMatrix_apply]

set_option maxRecDepth 10000 in
lemma K4_charpoly :
    ((completeGraph (Fin 4)).adjMatrix ℝ).charpoly = (X - C 3) * (X - C (-1)) ^ 3 := by
  rw [K4_adj, Matrix.charpoly, Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.det_fin_three]
  simp [Matrix.submatrix_apply, Fin.succAbove, Fin.lt_def]
  have h3 : (C 3 : ℝ[X]) = 3 := map_ofNat C 3
  rw [h3]
  ring

lemma K4_roots : ((completeGraph (Fin 4)).adjMatrix ℝ).charpoly.roots = {3} + 3 • {-1} := by
  rw [K4_charpoly, roots_mul, roots_X_sub_C, roots_pow, roots_X_sub_C]
  exact mul_ne_zero (X_sub_C_ne_zero 3) (pow_ne_zero 3 (X_sub_C_ne_zero (-1)))

end OMA

theorem OMA.solution : type_of% @WrittenOnTheWallII.Test.K4_cvetkovic := by
  unfold cvetkovic
  simp only [WrittenOnTheWallII.Test.K4, OMA.K4_roots]
  have e1 : Multiset.countP (fun x : ℝ => 0 = x) {-1} = 0 := by
    rw [Multiset.countP_eq_zero]; norm_num
  have e2 : Multiset.countP (fun x : ℝ => 0 < x) {-1} = 0 := by
    rw [Multiset.countP_eq_zero]; norm_num
  have e3 : Multiset.countP (fun x : ℝ => x < 0) {-1} = 1 := by
    rw [Multiset.countP_eq_card_filter, Multiset.filter_singleton]; norm_num
  simp [Multiset.countP_nsmul]
  rw [e1, e2, e3]
  norm_num
