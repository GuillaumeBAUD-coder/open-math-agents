import FormalConjectures.WrittenOnTheWallII.Test

open SimpleGraph Matrix Polynomial WrittenOnTheWallII.Test

theorem OMA.solution : type_of% @WrittenOnTheWallII.Test.house_cvetkovic := by
  classical
  let A := HouseGraph.adjMatrix ℝ
  have hA : A = !![0,1,0,1,0; 1,0,1,0,0; 0,1,0,1,1; 1,0,1,0,1; 0,0,1,1,0] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [A, adjMatrix_apply, HouseGraph, fromEdgeSet_adj, Sym2.eq_iff, Fin.ext_iff]
  have hroot {t b c d e : ℝ} (h0 : t = b + d) (h1 : t * b = 1 + c) (h2 : t * c = b + d + e)
      (h3 : t * d = c + 1 + e) (h4 : t * e = c + d) : A.charpoly.eval t = 0 := by
    rw [Matrix.eval_charpoly, ← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨![1, b, c, d, e], fun h => by have := congrFun h (0 : Fin 5); norm_num at this, ?_⟩
    rw [Matrix.sub_mulVec, sub_eq_zero, hA]; ext i
    fin_cases i <;>
      norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.scalar, Matrix.diagonal] <;>
      linarith
  let f (t : ℝ) := t ^ 3 - 2 * t ^ 2 - 2 * t + 2
  have hf : Continuous f := by fun_prop
  have hfr {t : ℝ} (h : f t = 0) : A.charpoly.eval t = 0 := by
    apply hroot (b := 1) (c := t - 1) (d := t - 1) (e := t * (t - 2)) <;>
      dsimp [f] at h <;> nlinarith
  obtain ⟨a, ha, za⟩ := intermediate_value_Icc (show (-3 / 2 : ℝ) ≤ -1 by norm_num)
    hf.continuousOn (show (0 : ℝ) ∈ Set.Icc (f (-3 / 2)) (f (-1)) by norm_num [f])
  obtain ⟨b, hb, zb⟩ := intermediate_value_Icc' (show (1 / 2 : ℝ) ≤ 1 by norm_num)
    hf.continuousOn (show (0 : ℝ) ∈ Set.Icc (f 1) (f (1 / 2)) by norm_num [f])
  obtain ⟨c, hc, zc⟩ := intermediate_value_Icc (show (2 : ℝ) ≤ 3 by norm_num)
    hf.continuousOn (show (0 : ℝ) ∈ Set.Icc (f 2) (f 3) by norm_num [f])
  have z0 : A.charpoly.eval 0 = 0 := by
    apply hroot (b := -1) (c := -1) (d := 1) (e := 0) <;> norm_num
  have zm : A.charpoly.eval (-2) = 0 := by
    apply hroot (b := -1) (c := 1) (d := -1) (e := 0) <;> norm_num
  let R : Multiset ℝ := (-2) ::ₘ a ::ₘ 0 ::ₘ b ::ₘ c ::ₘ 0
  have nd : R.Nodup := by
    simp [R, Multiset.nodup_cons, not_or]; (repeat' constructor) <;>
      linarith [ha.1, ha.2, hb.1, hb.2, hc.1, hc.2]
  have rs : A.charpoly.roots = R :=
    Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero (S := ⟨R, nd⟩)
      (fun x hx => by
        rcases (by simpa [R] using hx) with rfl | rfl | rfl | rfl | rfl
        exacts [zm, hfr za, z0, hfr zb, hfr zc])
      (by rw [Matrix.charpoly_natDegree_eq_dim]; simp [R, Finset.card]) A.charpoly_monic.ne_zero
  change A.charpoly.roots.countP (fun x => 0 = x) +
    min (A.charpoly.roots.countP (fun x => 0 < x)) (A.charpoly.roots.countP (fun x => 0 > x)) = 3
  rw [rs]
  have ha' : a < 0 := by linarith [ha.2]
  have hb' : 0 < b := by linarith [hb.1]
  have hc' : 0 < c := by linarith [hc.1]
  simp only [R, Multiset.countP_cons, Multiset.countP_zero]
  norm_num [ha', hb', hc', ha'.not_gt, hb'.not_gt, hc'.not_gt, ha'.ne', hb'.ne, hc'.ne]
