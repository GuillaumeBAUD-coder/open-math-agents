import FormalConjectures.WrittenOnTheWallII.Test

/-! # The signs and multiplicities of the house graph spectrum -/
-- Credit: @steveDOTdigital

namespace OMA.House

open SimpleGraph Matrix Polynomial WrittenOnTheWallII.Test

private abbrev A := HouseGraph.adjMatrix ℝ

private lemma matrix_eq : A = !![0,1,0,1,0; 1,0,1,0,0; 0,1,0,1,1;
    1,0,1,0,1; 0,0,1,1,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A, adjMatrix_apply, HouseGraph, fromEdgeSet_adj, Sym2.eq_iff, Fin.ext_iff]

-- All eigenvectors used below have first coordinate 1.
private theorem root {t b c d e : ℝ}
    (h0 : t = b+d) (h1 : t*b = 1+c) (h2 : t*c = b+d+e)
    (h3 : t*d = c+1+e) (h4 : t*e = c+d) : A.charpoly.eval t = 0 := by
  rw [Matrix.eval_charpoly, ← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨![1,b,c,d,e], ?_, ?_⟩
  · intro h
    have := congrFun h (0 : Fin 5)
    norm_num at this
  · rw [Matrix.sub_mulVec, sub_eq_zero, matrix_eq]
    ext i
    fin_cases i <;>
      norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.scalar, Matrix.diagonal] <;>
      linarith

private def cubic (t : ℝ) := t^3 - 2*t^2 - 2*t + 2

private lemma cubic_root {t : ℝ} (h : cubic t = 0) : A.charpoly.eval t = 0 := by
  apply root (b := 1) (c := t-1) (d := t-1) (e := t*(t-2)) <;>
    unfold cubic at h <;> nlinarith

private theorem signs : cvetkovic HouseGraph = 3 := by
  classical
  have cont : Continuous cubic := by unfold cubic; fun_prop
  obtain ⟨a, ha, za⟩ := intermediate_value_Icc (show (-3/2 : ℝ) ≤ -1 by norm_num)
    cont.continuousOn (show (0 : ℝ) ∈ Set.Icc (cubic (-3/2)) (cubic (-1)) by norm_num [cubic])
  obtain ⟨b, hb, zb⟩ := intermediate_value_Icc' (show (1/2 : ℝ) ≤ 1 by norm_num)
    cont.continuousOn (show (0 : ℝ) ∈ Set.Icc (cubic 1) (cubic (1/2)) by norm_num [cubic])
  obtain ⟨c, hc, zc⟩ := intermediate_value_Icc (show (2 : ℝ) ≤ 3 by norm_num)
    cont.continuousOn (show (0 : ℝ) ∈ Set.Icc (cubic 2) (cubic 3) by norm_num [cubic])
  obtain ⟨al,au⟩ := ha
  obtain ⟨bl,bu⟩ := hb
  obtain ⟨cl,cu⟩ := hc
  have z0 : A.charpoly.eval 0 = 0 := by
    apply root (b := -1) (c := -1) (d := 1) (e := 0) <;> norm_num
  have zm : A.charpoly.eval (-2) = 0 := by
    apply root (b := -1) (c := 1) (d := -1) (e := 0) <;> norm_num
  let roots : Multiset ℝ := (-2) ::ₘ a ::ₘ 0 ::ₘ b ::ₘ c ::ₘ 0
  have nd : roots.Nodup := by
    simp [roots, Multiset.nodup_cons, not_or] <;> (repeat' constructor) <;> linarith
  let s : Finset ℝ := ⟨roots, nd⟩
  have rs : A.charpoly.roots = s.val := by
    apply Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
    · intro x hx
      change x ∈ roots at hx
      simp [roots] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      exacts [zm, cubic_root za, z0, cubic_root zb, cubic_root zc]
    · rw [Matrix.charpoly_natDegree_eq_dim]
      simp [s, roots, Finset.card]
    · exact A.charpoly_monic.ne_zero
  change A.charpoly.roots.countP (fun x => 0 = x) +
    min (A.charpoly.roots.countP (fun x => 0 < x)) (A.charpoly.roots.countP (fun x => 0 > x)) = 3
  rw [rs]
  have ha : a < 0 := by linarith
  have hb : 0 < b := by linarith
  have hc : 0 < c := by linarith
  simp only [s, roots, Multiset.countP_cons, Multiset.countP_zero]
  norm_num [ha, hb, hc, ha.not_gt, hb.not_gt, hc.not_gt, ha.ne', hb.ne, hc.ne]

end OMA.House

theorem OMA.solution : type_of% @WrittenOnTheWallII.Test.house_cvetkovic := OMA.House.signs
