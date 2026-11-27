import FormalConjectures.Wikipedia.BorsukConjecture

/-! # Eight smaller sets in four dimensions

Eight signed coordinate centres cover the small-circumradius regime.
For an intermediate radius it suffices to partition a compact set into eight cells
with no diametral pair, provided the cells are closed. At large radius it is enough
for five open balls of radius less than half the diameter to meet every diametral pair.
The use of open balls makes their leftover set compact.

The thresholds refer to the radius divided by the original diameter. The large-radius
strategy follows Logan R. Chalmers, arXiv:2611.17375. The eight-centre estimate below
uses the largest absolute coordinate in four dimensions. Credit: @Deldor14.
-/
namespace OMA.R_Borsuk_borsuk_conjecture_four_eight_parts_R1

open Metric Bornology Borsuk
open scoped EuclideanGeometry

private theorem four_axis (x : EuclideanSpace ℝ (Fin 4)) :
    ∃ i, ‖x‖ ≤ 2 * |x i| := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin 4 => |x i|) Finset.univ_nonempty
  have hsq : ‖x‖ ^ 2 ≤ 4 * |x i| ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      ∑ j, (x j)^2 ≤ ∑ _j : Fin 4, |x i| ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        rw [← sq_abs (x j)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hi j hj) 2
      _ = _ := by simp
  exact ⟨i, by nlinarith [norm_nonneg x, abs_nonneg (x i)]⟩

private theorem near_axis (x : EuclideanSpace ℝ (Fin 4)) (R : ℝ) (hR : ‖x‖ ≤ R) :
    ∃ i : Fin 4, ∃ a : Fin 2,
      ‖x - EuclideanSpace.single i (if a = 0 then R / 2 else -(R / 2))‖ ≤ (13/15 : ℝ)*R := by
  obtain ⟨i, hi⟩ := four_axis x
  have hpos : 0 ≤ R := (norm_nonneg x).trans hR
  have half : 0 ≤ (R - ‖x‖) * (R/2 + ‖x‖) := mul_nonneg (by linarith) (by positivity)
  have prod := mul_le_mul_of_nonneg_left hi hpos
  by_cases h : 0 ≤ x i
  · refine ⟨i, 0, ?_⟩
    change ‖x - EuclideanSpace.single i (R/2)‖ ≤ (13/15 : ℝ)*R
    rw [abs_of_nonneg h] at prod
    have sq := norm_sub_sq_real x (EuclideanSpace.single i (R/2))
    rw [EuclideanSpace.inner_single_right] at sq
    simp [Real.norm_eq_abs, abs_of_nonneg hpos] at sq
    nlinarith [sq_nonneg R, norm_nonneg (x - EuclideanSpace.single i (R/2))]
  · refine ⟨i, 1, ?_⟩
    change ‖x - EuclideanSpace.single i (-(R/2))‖ ≤ (13/15 : ℝ)*R
    rw [abs_of_neg (lt_of_not_ge h)] at prod
    have sq := norm_sub_sq_real x (EuclideanSpace.single i (-(R/2)))
    rw [EuclideanSpace.inner_single_right] at sq
    simp [Real.norm_eq_abs, abs_of_nonneg hpos] at sq
    nlinarith [sq_nonneg R, norm_nonneg (x - EuclideanSpace.single i (-(R/2)))]

private theorem ofReal_diam' {K : Set (EuclideanSpace ℝ (Fin 4))} (hb : IsBounded K) :
    ENNReal.ofReal (diam K) = ediam K :=
  ENNReal.ofReal_toReal (isBounded_iff_ediam_ne_top.mp hb)

private theorem ball_bound (c : EuclideanSpace ℝ (Fin 4)) (r : ℝ) :
    ediam (closedBall c r) ≤ ENNReal.ofReal (2*r) := by
  apply ediam_le_of_forall_dist_le
  intro x hx y hy
  exact (dist_triangle_right x y c).trans (by linarith [mem_closedBall.mp hx, mem_closedBall.mp hy])

private theorem small_case {K : Set (EuclideanSpace ℝ (Fin 4))} (hb : IsBounded K)
    (hnt : K.Nontrivial) {c : EuclideanSpace ℝ (Fin 4)}
    (hc : ∀ x ∈ K, dist x c ≤ (4/7 : ℝ)*diam K) : HasBorsukCover 8 K := by
  classical
  let R := (4/7 : ℝ) * diam K
  let center (i : Fin 4 × Fin 2) := c +
    EuclideanSpace.single i.1 (if i.2 = 0 then R/2 else -(R/2))
  let e : Fin 4 × Fin 2 ≃ Fin 8 := finProdFinEquiv
  refine ⟨fun j => closedBall (center (e.symm j)) ((13/15 : ℝ)*R), ?_, ?_⟩
  · intro x hx
    obtain ⟨i, a, hz⟩ := near_axis (x-c) R (by simpa [dist_eq_norm] using hc x hx)
    apply Set.mem_iUnion.mpr
    refine ⟨e (i,a), ?_⟩
    rw [e.symm_apply_apply]
    change dist x (c + _) ≤ _
    rw [dist_eq_norm, ← sub_sub]
    exact hz
  · intro j
    apply (ball_bound _ _).trans_lt
    rw [← ofReal_diam' hb]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).2 (by
      dsimp [R]
      linarith [diam_pos hnt hb])

private theorem compact_strict {K T : Set (EuclideanSpace ℝ (Fin 4))}
    (hK : IsCompact K) (hnt : K.Nontrivial) (hT : IsCompact T) (hsub : T ⊆ K)
    (hnod : ∀ x ∈ T, ∀ y ∈ T, dist x y ≠ diam K) : ediam T < ediam K := by
  rcases T.eq_empty_or_nonempty with rfl | hne
  · simpa using ediam_pos_iff.mpr hnt
  obtain ⟨⟨x,y⟩, hxy, hmax⟩ := (hT.prod hT).exists_isMaxOn (hne.prod hne)
    (continuous_fst.dist continuous_snd).continuousOn
  have ltD := (dist_le_diam_of_mem hK.isBounded (hsub hxy.1) (hsub hxy.2)).lt_of_ne
    (hnod x hxy.1 y hxy.2)
  have hb : ediam T ≤ ENNReal.ofReal (dist x y) := by
    apply ediam_le_of_forall_dist_le
    intro a ha b hb
    exact (isMaxOn_iff.mp hmax) (a,b) ⟨ha,hb⟩
  apply hb.trans_lt
  rw [← ofReal_diam' hK.isBounded]
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).2 ltD

private theorem eight_of_seven_and_one {K : Set (EuclideanSpace ℝ (Fin 4))}
    (A : Fin 7 → Set (EuclideanSpace ℝ (Fin 4))) (T : Set (EuclideanSpace ℝ (Fin 4)))
    (hA : ∀ i, ediam (A i) < ediam K) (hT : ediam T < ediam K)
    (hall : ∀ x ∈ K, x ∈ T ∨ ∃ i, x ∈ A i) : HasBorsukCover 8 K := by
  classical
  refine ⟨Fin.cons T A, ?_, ?_⟩
  · intro x hx
    apply Set.mem_iUnion.mpr
    rcases hall x hx with h | ⟨i, hi⟩
    · exact ⟨0, by simpa using h⟩
    · exact ⟨i.succ, by simpa using hi⟩
  · exact Fin.cases (by simpa using hT) fun i => by simpa using hA i

private theorem large_case {K : Set (EuclideanSpace ℝ (Fin 4))}
    (hK : IsCompact K) (hnt : K.Nontrivial)
    {c : Fin 5 → EuclideanSpace ℝ (Fin 4)} {r : ℝ} (hr : 0 < r) (hrD : 2*r < diam K)
    (hit : ∀ x ∈ K, ∀ y ∈ K, dist x y = diam K →
      ∃ i, x ∈ ball (c i) r ∨ y ∈ ball (c i) r) : HasBorsukCover 8 K := by
  classical
  let U := ⋃ i, ball (c i) r
  let T := K \ U
  have hcomp : IsCompact T := hK.diff (isOpen_iUnion fun _ => isOpen_ball)
  have hT : ediam T < ediam K := by
    apply compact_strict hK hnt hcomp Set.sdiff_subset
    intro x hx y hy hd
    obtain ⟨i, hi⟩ := hit x hx.1 y hy.1 hd
    rcases hi with hi | hi
    · exact hx.2 (Set.mem_iUnion.mpr ⟨i,hi⟩)
    · exact hy.2 (Set.mem_iUnion.mpr ⟨i,hi⟩)
  let A (j : Fin 7) := if h : j.val < 5 then ball (c ⟨j.val,h⟩) r else ∅
  apply eight_of_seven_and_one A T _ hT
  · intro x hx
    by_cases hu : x ∈ U
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hu
      right
      exact ⟨⟨i.val, by have := i.isLt; omega⟩, by simpa [A, i.isLt] using hi⟩
    · exact Or.inl ⟨hx,hu⟩
  · intro j
    dsimp only [A]
    split
    · apply (ediam_mono ball_subset_closedBall).trans_lt
      apply (ball_bound _ _).trans_lt
      rw [← ofReal_diam' hK.isBounded]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).2 hrD
    · simpa using ediam_pos_iff.mpr hnt

def H1 : Prop :=
  ∀ K : Set (EuclideanSpace ℝ (Fin 4)), IsCompact K → K.Nontrivial →
    (∀ c, ∃ x ∈ K, (4 / 7 : ℝ) * diam K < dist x c) →
    (∃ c, ∀ x ∈ K, dist x c ≤ (627 / 1000 : ℝ) * diam K) →
    ∃ C : Fin 8 → Set (EuclideanSpace ℝ (Fin 4)), (∀ i, IsClosed (C i)) ∧
      K ⊆ ⋃ i, C i ∧
      ∀ i, ∀ x ∈ K ∩ C i, ∀ y ∈ K ∩ C i, dist x y ≠ diam K

def H2 : Prop :=
  ∀ K : Set (EuclideanSpace ℝ (Fin 4)), IsCompact K → K.Nontrivial →
    (∀ c, ∃ x ∈ K, (627 / 1000 : ℝ) * diam K < dist x c) →
    ∃ (c : Fin 5 → EuclideanSpace ℝ (Fin 4)) (r : ℝ), 0 < r ∧ 2*r < diam K ∧
      ∀ x ∈ K, ∀ y ∈ K, dist x y = diam K →
        ∃ i, x ∈ ball (c i) r ∨ y ∈ ball (c i) r

theorem main : H1 → H2 → type_of% @Borsuk.borsuk_conjecture.four.eight_parts := by
  classical
  intro middle large s hs hnt
  let K := closure s
  have hK : IsCompact K := hs.isCompact_closure
  have hntK : K.Nontrivial := hnt.mono subset_closure
  suffices cov : HasBorsukCover 8 K by
    obtain ⟨C, hC, hsmall⟩ := cov
    exact ⟨C, subset_closure.trans hC, fun i => by simpa [K, ediam_closure] using hsmall i⟩
  by_cases small : ∃ c, ∀ x ∈ K, dist x c ≤ (4/7 : ℝ)*diam K
  · obtain ⟨c, hc⟩ := small
    exact small_case hK.isBounded hntK hc
  push Not at small
  by_cases mid : ∃ c, ∀ x ∈ K, dist x c ≤ (627/1000 : ℝ)*diam K
  · obtain ⟨C, hclosed, hcover, hdist⟩ := middle K hK hntK small mid
    refine ⟨fun j => K ∩ C j, ?_, fun j => compact_strict hK hntK
      (hK.inter_right (hclosed j)) Set.inter_subset_left (hdist j)⟩
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hx)
    exact Set.mem_iUnion.mpr ⟨i,hx,hi⟩
  · push Not at mid
    obtain ⟨c,r,hr,hrD,hit⟩ := large K hK hntK mid
    exact large_case hK hntK hr hrD hit

end OMA.R_Borsuk_borsuk_conjecture_four_eight_parts_R1
