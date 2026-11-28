import OMAStatements.S_mo_283370

open OMA.S_mo_283370 MeasureTheory Set Metric

namespace OMA.MO283370Proof

private abbrev E := EuclideanSpace ℝ (Fin 2)

private noncomputable def axis (i : Fin 2) (r : ℝ) : E := EuclideanSpace.single i r

private noncomputable def coordinate (x : E) : ℝ := inner ℝ (axis 0 1) x

private lemma coordinate_axis (i : Fin 2) (r : ℝ) :
    coordinate (axis i r) = if i = 0 then r else 0 := by
  unfold coordinate axis
  rw [EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]
  by_cases h : i = 0
  · simp [h]
  · simp [h, Ne.symm h]

private lemma coordinate_add (x y : E) : coordinate (x + y) = coordinate x + coordinate y := by
  simp [coordinate, inner_add_right]

private lemma coordinate_continuous : Continuous coordinate :=
  continuous_const.inner continuous_id

private lemma axis_norm (i : Fin 2) (r : ℝ) : ‖axis i r‖ = |r| :=
  EuclideanSpace.norm_single i r

private def body : Set E := closedBall 0 1 ∩ {x | coordinate x ≤ 1 / 4}

private lemma body_closed : IsClosed body :=
  isClosed_closedBall.inter (isClosed_le coordinate_continuous continuous_const)

private lemma body_compact : IsCompact body :=
  (isCompact_closedBall (0 : E) 1).of_isClosed_subset body_closed inter_subset_left

private lemma body_convex : Convex ℝ body := by
  apply (convex_closedBall (0 : E) 1).inter
  refine convex_halfSpace_le (𝕜 := ℝ) (f := coordinate) ⟨?_, ?_⟩ _
  · exact coordinate_add
  · intro c x
    simp [coordinate, inner_smul_right]

private lemma body_origin_interior : (0 : E) ∈ interior body := by
  have ho : IsOpen (ball (0 : E) 1 ∩ {x | coordinate x < 1 / 4}) :=
    isOpen_ball.inter (isOpen_lt coordinate_continuous continuous_const)
  have hsub : ball (0 : E) 1 ∩ {x | coordinate x < 1 / 4} ⊆ body :=
    fun x hx => ⟨ball_subset_closedBall hx.1,
      show coordinate x ≤ 1 / 4 from le_of_lt (show coordinate x < 1 / 4 from hx.2)⟩
  apply interior_maximal hsub ho
  constructor
  · simp
  · change coordinate (0 : E) < 1 / 4
    norm_num [coordinate]

private lemma vertical_mem (r : ℝ) (hr : |r| ≤ 1) : axis 1 r ∈ body := by
  constructor
  · simpa [Metric.mem_closedBall, dist_zero_right, axis_norm] using hr
  · change coordinate (axis 1 r) ≤ 1 / 4
    rw [coordinate_axis, if_neg (by decide : (1 : Fin 2) ≠ 0)]
    norm_num

private lemma body_diam : 2 ≤ diam body := by
  have h := dist_le_diam_of_mem body_compact.isBounded
    (vertical_mem 1 (by norm_num)) (vertical_mem (-1) (by norm_num))
  change dist (EuclideanSpace.single 1 (1 : ℝ) : E) (EuclideanSpace.single 1 (-1)) ≤ diam body at h
  rw [EuclideanSpace.dist_single_same] at h
  norm_num [Real.dist_eq] at h
  exact h

private lemma flat_point_not_interior :
    axis 0 (1 / 4) ∉ interior body := by
  intro h
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior _ h
  let q := axis 0 (1 / 4) + axis 0 (ε / 2)
  have hdist : dist q (axis 0 (1 / 4)) = ε / 2 := by
    change dist (axis 0 (1 / 4) + axis 0 (ε / 2)) (axis 0 (1 / 4)) = _
    rw [dist_eq_norm, add_sub_cancel_left, axis_norm, abs_of_pos (by positivity)]
  have hq : q ∈ body := interior_subset (hball (by rw [mem_ball, hdist]; linarith))
  have hle : coordinate q ≤ 1 / 4 := hq.2
  dsimp only [q] at hle
  rw [coordinate_add, coordinate_axis, coordinate_axis, if_pos rfl, if_pos rfl] at hle
  linarith

private lemma body_not_ball (z : E) (r : ℝ) : body ≠ closedBall z r := by
  intro he
  let m := axis 0 (1 / 4)
  let v := axis 1 (1 / 2)
  have hnormm : ‖m‖ = 1 / 4 := by dsimp [m]; rw [axis_norm]; norm_num
  have hnormv : ‖v‖ = 1 / 2 := by dsimp [v]; rw [axis_norm]; norm_num
  have hcm : coordinate m = 1 / 4 := by simp [m, coordinate_axis]
  have hcv : coordinate v = 0 := by simp [v, coordinate_axis, show (1 : Fin 2) ≠ 0 by decide]
  have hp : m + v ∈ body := by
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right]
      have h := norm_add_le m v
      linarith
    · change coordinate (m + v) ≤ 1 / 4
      rw [coordinate_add, hcm, hcv, add_zero]
  have hn : m + (-v) ∈ body := by
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right]
      have h := norm_add_le m (-v)
      rw [norm_neg] at h
      linarith
    · have hz : coordinate (-v) = -coordinate v := by simp [coordinate]
      change coordinate (m + (-v)) ≤ 1 / 4
      rw [coordinate_add, hz, hcv, hcm, neg_zero, add_zero]
  have hne : m + v ≠ m + (-v) := by
    intro h
    have hv : v = -v := add_left_cancel h
    have hc : v 1 = (-v) 1 := congrArg (fun x : E => x 1) hv
    dsimp only [v, axis] at hc
    norm_num [EuclideanSpace.single_apply] at hc
  have hstrict : StrictConvex ℝ body := he.symm ▸ strictConvex_closedBall ℝ z r
  have hm : midpoint ℝ (m + v) (m + (-v)) = m := by
    rw [midpoint_eq_smul_add, invOf_eq_inv]
    module
  have hmi : m ∈ interior body := hm ▸ hstrict.openSegment_subset hp hn hne
    (midpoint_mem_openSegment (𝕜 := ℝ) _ _)
  exact flat_point_not_interior hmi

end OMA.MO283370Proof

open OMA.MO283370Proof in
/-- Every properly intersecting plank of width 3/2 contains zero, since its
boundary projections are in [-1,1]. A clipped unit disk and the unit mass at
zero therefore meet the premise, while the flat boundary excludes a disk. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_283370.main) := by
  intro h
  have horigin : (0 : E) ∈ body := interior_subset body_origin_interior
  have hinvar : ∃ c, ∀ (u : E) (a : ℝ), ‖u‖ = 1 →
      ProperlyMeets body u a (3 / 2) → (Measure.dirac (0 : E)) (plank u a (3 / 2) ∩ body) = c := by
    refine ⟨1, fun u a hu hmeet => ?_⟩
    rcases hmeet with ⟨⟨x, hx, hxa⟩, ⟨y, hy, hya⟩⟩
    have hbound (t : E) (ht : t ∈ body) : |inner ℝ u t| ≤ 1 := by
      have hnorm : ‖t‖ ≤ 1 := by
        have hp : t ∈ closedBall (0 : E) 1 := ht.1
        simpa [mem_closedBall, dist_zero_right] using hp
      calc
        _ ≤ ‖u‖ * ‖t‖ := abs_real_inner_le_norm u t
        _ ≤ 1 := by simpa only [hu, one_mul] using hnorm
    have hl := (abs_le.mp (hbound x hx)).1
    have hr := (abs_le.mp (hbound y hy)).2
    rw [hxa] at hl
    rw [hya] at hr
    apply Measure.dirac_apply_of_mem
    refine ⟨?_, horigin⟩
    change a ≤ inner ℝ u 0 ∧ inner ℝ u 0 ≤ a + 3 / 2
    simp only [inner_zero_right]
    constructor <;> linarith
  obtain ⟨z, r, he⟩ := h body body_convex body_compact ⟨0, body_origin_interior⟩
    (3 / 2) (by norm_num) (by have hh := body_diam; linarith)
    (Measure.dirac (0 : E)) inferInstance Measure.dirac_ne_zero
    (by rw [Measure.dirac_apply]; simp [horigin]) hinvar
  exact body_not_ball z r he
