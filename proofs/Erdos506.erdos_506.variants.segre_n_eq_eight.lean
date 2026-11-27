import FormalConjectures.ErdosProblems.«506»
import Mathlib

/-! Proof of Erdos506.erdos_506.variants.segre_n_eq_eight using 7 points on the unit circle
(including 3 antipodal pairs) plus the origin, which determines at most 19 < 21 circles. -/

open EuclideanGeometry Finset Set

namespace OMA_Erdos506_Segre

private abbrev Pt := EuclideanSpace ℝ (Fin 2)

private noncomputable def mkPt (x y : ℝ) : Pt := !₂[x, y]

private lemma mkPt_eq_iff (x1 y1 x2 y2 : ℝ) :
    mkPt x1 y1 = mkPt x2 y2 ↔ x1 = x2 ∧ y1 = y2 := by
  constructor
  · intro h
    have h0 : (mkPt x1 y1) 0 = (mkPt x2 y2) 0 := congrArg (fun z : Pt => z 0) h
    have h1 : (mkPt x1 y1) 1 = (mkPt x2 y2) 1 := congrArg (fun z : Pt => z 1) h
    exact ⟨by simpa [mkPt] using h0, by simpa [mkPt] using h1⟩
  · rintro ⟨rfl, rfl⟩; rfl

private lemma dist_sq_mkPt (p q : Pt) :
    dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
  simp only [Real.dist_eq, sq_abs]

private lemma mem_sphere_sq {s : Sphere Pt} {p : Pt} (hp : p ∈ s) :
    (p 0 - s.center 0) ^ 2 + (p 1 - s.center 1) ^ 2 = s.radius ^ 2 := by
  rw [← dist_sq_mkPt, EuclideanGeometry.mem_sphere.mp hp]

private lemma sphere_eq_of_three_noncollinear {s1 s2 : Sphere Pt} {a b c : Pt}
    (ha1 : a ∈ s1) (hb1 : b ∈ s1) (hc1 : c ∈ s1)
    (ha2 : a ∈ s2) (hb2 : b ∈ s2) (hc2 : c ∈ s2)
    (hdet : (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0) ≠ 0) :
    s1 = s2 := by
  have h1a := mem_sphere_sq ha1
  have h1b := mem_sphere_sq hb1
  have h1c := mem_sphere_sq hc1
  have h2a := mem_sphere_sq ha2
  have h2b := mem_sphere_sq hb2
  have h2c := mem_sphere_sq hc2
  -- Subtracting gives 2*(b-a)·(c1 - c2) = 0 and 2*(c-a)·(c1 - c2) = 0
  have eq1 : (b 0 - a 0) * (s1.center 0 - s2.center 0) + (b 1 - a 1) * (s1.center 1 - s2.center 1) = 0 := by
    linarith
  have eq2 : (c 0 - a 0) * (s1.center 0 - s2.center 0) + (c 1 - a 1) * (s1.center 1 - s2.center 1) = 0 := by
    linarith
  have hx : s1.center 0 = s2.center 0 := by
    have hmul : ((b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)) * (s1.center 0 - s2.center 0) = 0 := by
      linear_combination (c 1 - a 1) * eq1 - (b 1 - a 1) * eq2
    have := (mul_eq_zero.mp hmul).resolve_left hdet
    linarith
  have hy : s1.center 1 = s2.center 1 := by
    have hmul : ((b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)) * (s1.center 1 - s2.center 1) = 0 := by
      linear_combination -(c 0 - a 0) * eq1 + (b 0 - a 0) * eq2
    have := (mul_eq_zero.mp hmul).resolve_left hdet
    linarith
  have hcenter : s1.center = s2.center := by
    ext i; fin_cases i
    · exact hx
    · exact hy
  have hrad : s1.radius = s2.radius := by
    have h1 := EuclideanGeometry.mem_sphere.mp ha1
    have h2 := EuclideanGeometry.mem_sphere.mp ha2
    rw [hcenter] at h1
    rw [← h1, h2]
  cases s1; cases s2; simp only at hcenter hrad; subst hcenter hrad; rfl

private lemma no_sphere_through_origin_antipodal {s : Sphere Pt} {p : Pt}
    (hp : p ≠ mkPt 0 0) (h0 : mkPt 0 0 ∈ s) (h1 : p ∈ s) (h2 : -p ∈ s) : False := by
  have e0 := mem_sphere_sq h0
  have e1 := mem_sphere_sq h1
  have e2 := mem_sphere_sq h2
  simp only [mkPt, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at e0
  have hneg0 : (-p) 0 = -(p 0) := rfl
  have hneg1 : (-p) 1 = -(p 1) := rfl
  rw [hneg0, hneg1] at e2
  have hsq : p 0 ^ 2 + p 1 ^ 2 = 0 := by linarith
  have hp0 : p 0 = 0 := by nlinarith
  have hp1 : p 1 = 0 := by nlinarith
  apply hp
  ext i; fin_cases i
  · simpa [mkPt] using hp0
  · simpa [mkPt] using hp1

private noncomputable def unitSphere : Sphere Pt := ⟨mkPt 0 0, 1⟩

private lemma mem_unitSphere_of_sq {p : Pt} (h : p 0 ^ 2 + p 1 ^ 2 = 1) : p ∈ unitSphere := by
  rw [EuclideanGeometry.mem_sphere, EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp only [unitSphere, mkPt, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Real.dist_eq, sub_zero, sq_abs]
  rw [h, Real.sqrt_one]

/-- Three distinct points on the unit circle are never collinear (determinant ≠ 0). -/
private lemma unitCircle_three_det_ne_zero {a b c : Pt}
    (ha : a 0 ^ 2 + a 1 ^ 2 = 1) (hb : b 0 ^ 2 + b 1 ^ 2 = 1) (hc : c 0 ^ 2 + c 1 ^ 2 = 1)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0) ≠ 0 := by
  intro hdet
  -- If collinear, a, b, c lie on a line L: u·x = d. Intersecting L with x^2+y^2=1 gives at most 2 points!
  -- Let u = (b 1 - a 1, -(b 0 - a 0)) ≠ 0. Then (b-a) = t*(...) -> param p(s) = a + s*(b - a)
  have hba : (b 0 - a 0) ^ 2 + (b 1 - a 1) ^ 2 ≠ 0 := by
    intro h0
    have h00 : b 0 - a 0 = 0 := by nlinarith
    have h01 : b 1 - a 1 = 0 := by nlinarith
    apply hab; ext i; fin_cases i
    · change a 0 = b 0; linarith
    · change a 1 = b 1; linarith
  -- Since (b0-a0)(c1-a1) = (b1-a1)(c0-a0), let t = ((c0-a0)(b0-a0) + (c1-a1)(b1-a1)) / ((b0-a0)^2 + (b1-a1)^2)
  set D := (b 0 - a 0) ^ 2 + (b 1 - a 1) ^ 2
  set t := ((c 0 - a 0) * (b 0 - a 0) + (c 1 - a 1) * (b 1 - a 1)) / D
  have hc0 : c 0 - a 0 = t * (b 0 - a 0) := by
    dsimp only [t]; field_simp [hba]
    linear_combination -(b 1 - a 1) * hdet
  have hc1 : c 1 - a 1 = t * (b 1 - a 1) := by
    dsimp only [t]; field_simp [hba]
    linear_combination (b 0 - a 0) * hdet
  -- Plug c = a + t*(b - a) into c0^2 + c1^2 = 1, using a0^2+a1^2=1 and b0^2+b1^2=1:
  -- 0 = (c0^2+c1^2 - 1) - t*(b0^2+b1^2 - 1) - (1-t)*(a0^2+a1^2 - 1) = t*(t-1)*D!
  have hquad : t * (t - 1) * D = 0 := by
    have h1 : (a 0 + t * (b 0 - a 0)) ^ 2 + (a 1 + t * (b 1 - a 1)) ^ 2 = 1 := by
      rw [← hc0, ← hc1]; ring_nf; linarith
    linear_combination h1 - t * hb - (1 - t) * ha
  rcases mul_eq_zero.mp ((mul_eq_zero.mp hquad).resolve_right hba) with ht0 | ht1
  · rw [ht0, zero_mul] at hc0 hc1
    apply hac; ext i; fin_cases i
    · change a 0 = c 0; linarith
    · change a 1 = c 1; linarith
  · have ht : t = 1 := by linarith
    rw [ht, one_mul] at hc0 hc1
    apply hbc; ext i; fin_cases i
    · change b 0 = c 0; linarith
    · change b 1 = c 1; linarith

/-- Origin and two non-antipodal distinct points on the unit circle are non-collinear. -/
private lemma origin_unitCircle_det_ne_zero {a b : Pt}
    (ha : a 0 ^ 2 + a 1 ^ 2 = 1) (hb : b 0 ^ 2 + b 1 ^ 2 = 1)
    (hab : a ≠ b) (hanti : a ≠ -b) :
    (a 0 - (mkPt 0 0) 0) * (b 1 - (mkPt 0 0) 1) - (a 1 - (mkPt 0 0) 1) * (b 0 - (mkPt 0 0) 0) ≠ 0 := by
  simp only [mkPt, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, sub_zero]
  intro hdet
  have h1 : (a 0 * b 0 + a 1 * b 1) ^ 2 = 1 := by
    linear_combination (b 0 ^ 2 + b 1 ^ 2) * ha + hb - (a 0 * b 1 - a 1 * b 0) * hdet
  have hsq : (a 0 * b 0 + a 1 * b 1 - 1) * (a 0 * b 0 + a 1 * b 1 + 1) = 0 := by linarith
  rcases mul_eq_zero.mp hsq with hpos | hneg
  · have hsum : (a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2 = 0 := by linarith
    apply hab; ext i; fin_cases i
    · change a 0 = b 0; nlinarith
    · change a 1 = b 1; nlinarith
  · have hsum : (a 0 + b 0) ^ 2 + (a 1 + b 1) ^ 2 = 0 := by linarith
    apply hanti; ext i; fin_cases i
    · change a 0 = -(b 0); nlinarith
    · change a 1 = -(b 1); nlinarith

-- The 8 points: 7 on the unit circle + origin
private noncomputable def p0 : Pt := mkPt 0 0
private noncomputable def p1 : Pt := mkPt 1 0
private noncomputable def p2 : Pt := mkPt (-1) 0
private noncomputable def p3 : Pt := mkPt 0 1
private noncomputable def p4 : Pt := mkPt 0 (-1)
private noncomputable def p5 : Pt := mkPt (3 / 5) (4 / 5)
private noncomputable def p6 : Pt := mkPt (-3 / 5) (-4 / 5)
private noncomputable def p7 : Pt := mkPt (4 / 5) (3 / 5)

private noncomputable def C7 : Finset Pt := {p1, p2, p3, p4, p5, p6, p7}
private noncomputable def P8 : Finset Pt := insert p0 C7

private lemma C7_on_unit : ∀ p ∈ C7, p 0 ^ 2 + p 1 ^ 2 = 1 := by
  intro p hp
  simp only [C7, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [p1, p2, p3, p4, p5, p6, p7, mkPt, PiLp.toLp_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] <;> norm_num

private lemma P8_card : P8.card = 8 := by
  simp only [P8, C7]
  repeat rw [Finset.card_insert_of_notMem]
  · simp
  all_goals
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    repeat' constructor
    all_goals
      intro h
      have h0 := congrArg (fun z : Pt => z 0) h
      have h1 := congrArg (fun z : Pt => z 1) h
      simp only [p0, p1, p2, p3, p4, p5, p6, p7, mkPt, PiLp.toLp_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one] at h0 h1
      linarith

private lemma C7_card : C7.card = 7 := by
  have hp0 : p0 ∉ C7 := by
    intro h
    have hsq := C7_on_unit p0 h
    simp only [p0, mkPt, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at hsq
    norm_num at hsq
  have h8 := P8_card
  rw [P8, Finset.card_insert_of_notMem hp0] at h8
  omega

end OMA_Erdos506_Segre

theorem OMA.solution : type_of% @Erdos506.erdos_506.variants.segre_n_eq_eight := by
  classical
  refine ⟨OMA_Erdos506_Segre.P8, OMA_Erdos506_Segre.P8_card, ?_, ?_, ?_⟩
  · -- Not collinear: p0, p1, p3 are not collinear
    intro hcol
    have h0 : OMA_Erdos506_Segre.p0 ∈ (OMA_Erdos506_Segre.P8 : Set OMA_Erdos506_Segre.Pt) := by
      simp [OMA_Erdos506_Segre.P8]
    have h1 : OMA_Erdos506_Segre.p1 ∈ (OMA_Erdos506_Segre.P8 : Set OMA_Erdos506_Segre.Pt) := by
      simp [OMA_Erdos506_Segre.P8, OMA_Erdos506_Segre.C7]
    have h3 : OMA_Erdos506_Segre.p3 ∈ (OMA_Erdos506_Segre.P8 : Set OMA_Erdos506_Segre.Pt) := by
      simp [OMA_Erdos506_Segre.P8, OMA_Erdos506_Segre.C7]
    have hsub := hcol.subset (show ({OMA_Erdos506_Segre.p0, OMA_Erdos506_Segre.p1, OMA_Erdos506_Segre.p3} : Set _) ⊆ _ by
      intro x hx; rcases hx with rfl | rfl | rfl <;> assumption)
    rw [collinear_iff_exists_forall_eq_smul_vadd] at hsub
    rcases hsub with ⟨q, v, hq⟩
    obtain ⟨t0, ht0⟩ := hq OMA_Erdos506_Segre.p0 (by simp)
    obtain ⟨t1, ht1⟩ := hq OMA_Erdos506_Segre.p1 (by simp)
    obtain ⟨t3, ht3⟩ := hq OMA_Erdos506_Segre.p3 (by simp)
    have e00 := congrArg (fun z : OMA_Erdos506_Segre.Pt => z 0) ht0
    have e01 := congrArg (fun z : OMA_Erdos506_Segre.Pt => z 1) ht0
    have e10 := congrArg (fun z : OMA_Erdos506_Segre.Pt => z 0) ht1
    have e11 := congrArg (fun z : OMA_Erdos506_Segre.Pt => z 1) ht1
    have e30 := congrArg (fun z : OMA_Erdos506_Segre.Pt => z 0) ht3
    have e31 := congrArg (fun z : OMA_Erdos506_Segre.Pt => z 1) ht3
    simp only [OMA_Erdos506_Segre.p0, OMA_Erdos506_Segre.p1, OMA_Erdos506_Segre.p3,
      OMA_Erdos506_Segre.mkPt, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at e00 e01 e10 e11 e30 e31
    have hv1 : (t1 - t0) * v 0 = 1 := by linarith
    have hv2 : (t1 - t0) * v 1 = 0 := by linarith
    have hv3 : (t3 - t0) * v 0 = 0 := by linarith
    have hv4 : (t3 - t0) * v 1 = 1 := by linarith
    have hdet : ((t1 - t0) * v 0) * ((t3 - t0) * v 1) = ((t1 - t0) * v 1) * ((t3 - t0) * v 0) := by ring
    rw [hv1, hv2, hv3, hv4] at hdet
    norm_num at hdet
  · -- Not cospherical: p0, p1, p2 cannot lie on any common sphere
    rintro ⟨c, r, hc⟩
    have h0 : OMA_Erdos506_Segre.p0 ∈ (⟨c, r⟩ : Sphere OMA_Erdos506_Segre.Pt) := hc _ (by simp [OMA_Erdos506_Segre.P8])
    have h1 : OMA_Erdos506_Segre.p1 ∈ (⟨c, r⟩ : Sphere OMA_Erdos506_Segre.Pt) := hc _ (by simp [OMA_Erdos506_Segre.P8, OMA_Erdos506_Segre.C7])
    have h2 : OMA_Erdos506_Segre.p2 ∈ (⟨c, r⟩ : Sphere OMA_Erdos506_Segre.Pt) := hc _ (by simp [OMA_Erdos506_Segre.P8, OMA_Erdos506_Segre.C7])
    have hp2 : OMA_Erdos506_Segre.p2 = -OMA_Erdos506_Segre.p1 := by
      ext i; fin_cases i <;>
        simp [OMA_Erdos506_Segre.p1, OMA_Erdos506_Segre.p2, OMA_Erdos506_Segre.mkPt]
    have hp1ne : OMA_Erdos506_Segre.p1 ≠ OMA_Erdos506_Segre.p0 := by
      intro h; have := congrArg (fun z : OMA_Erdos506_Segre.Pt => z 0) h
      simp [OMA_Erdos506_Segre.p0, OMA_Erdos506_Segre.p1, OMA_Erdos506_Segre.mkPt] at this
    rw [hp2] at h2
    exact OMA_Erdos506_Segre.no_sphere_through_origin_antipodal hp1ne h0 h1 h2
  · -- numCircles P8 ≤ 19 < 21 = C(7, 2)
    unfold Erdos506.numCircles
    -- Define the finite set of candidate spheres: unitSphere plus circumspheres of (p0, a, b) for non-antipodal {a, b} ⊆ C7
    let pairs : Finset (Sym2 OMA_Erdos506_Segre.Pt) :=
      (OMA_Erdos506_Segre.C7.offDiag.image (fun q : OMA_Erdos506_Segre.Pt × OMA_Erdos506_Segre.Pt => s(q.1, q.2))).filter
        (fun e => e ≠ s(OMA_Erdos506_Segre.p1, OMA_Erdos506_Segre.p2) ∧
                  e ≠ s(OMA_Erdos506_Segre.p3, OMA_Erdos506_Segre.p4) ∧
                  e ≠ s(OMA_Erdos506_Segre.p5, OMA_Erdos506_Segre.p6))
    have hpairs_card : pairs.card ≤ 18 := by
      have htot : (OMA_Erdos506_Segre.C7.offDiag.image (fun q : OMA_Erdos506_Segre.Pt × OMA_Erdos506_Segre.Pt => s(q.1, q.2))).card = 21 := by
        have hfn : (fun q : OMA_Erdos506_Segre.Pt × OMA_Erdos506_Segre.Pt => s(q.1, q.2)) = Function.uncurry Sym2.mk := rfl
        rw [hfn, Sym2.card_image_offDiag, OMA_Erdos506_Segre.C7_card]; decide
      let bad3 : Finset (Sym2 OMA_Erdos506_Segre.Pt) :=
        {s(OMA_Erdos506_Segre.p1, OMA_Erdos506_Segre.p2),
         s(OMA_Erdos506_Segre.p3, OMA_Erdos506_Segre.p4),
         s(OMA_Erdos506_Segre.p5, OMA_Erdos506_Segre.p6)}
      have hbad3_sub : bad3 ⊆ OMA_Erdos506_Segre.C7.offDiag.image (fun q => s(q.1, q.2)) := by
        intro e he
        simp only [bad3, Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl
        · refine Finset.mem_image.mpr ⟨(OMA_Erdos506_Segre.p1, OMA_Erdos506_Segre.p2), Finset.mem_offDiag.mpr ⟨?_, ?_, ?_⟩, rfl⟩
          · simp [OMA_Erdos506_Segre.C7]
          · simp [OMA_Erdos506_Segre.C7]
          · intro h; have := congrArg (fun z : OMA_Erdos506_Segre.Pt => z 0) h; simp [OMA_Erdos506_Segre.p1, OMA_Erdos506_Segre.p2, OMA_Erdos506_Segre.mkPt] at this; norm_num at this
        · refine Finset.mem_image.mpr ⟨(OMA_Erdos506_Segre.p3, OMA_Erdos506_Segre.p4), Finset.mem_offDiag.mpr ⟨?_, ?_, ?_⟩, rfl⟩
          · simp [OMA_Erdos506_Segre.C7]
          · simp [OMA_Erdos506_Segre.C7]
          · intro h; have := congrArg (fun z : OMA_Erdos506_Segre.Pt => z 1) h; simp [OMA_Erdos506_Segre.p3, OMA_Erdos506_Segre.p4, OMA_Erdos506_Segre.mkPt] at this; norm_num at this
        · refine Finset.mem_image.mpr ⟨(OMA_Erdos506_Segre.p5, OMA_Erdos506_Segre.p6), Finset.mem_offDiag.mpr ⟨?_, ?_, ?_⟩, rfl⟩
          · simp [OMA_Erdos506_Segre.C7]
          · simp [OMA_Erdos506_Segre.C7]
          · intro h; have := congrArg (fun z : OMA_Erdos506_Segre.Pt => z 0) h; simp [OMA_Erdos506_Segre.p5, OMA_Erdos506_Segre.p6, OMA_Erdos506_Segre.mkPt] at this; norm_num at this
      have hbad3_card : bad3.card = 3 := by
        simp only [bad3]
        repeat rw [Finset.card_insert_of_notMem]
        · simp
        all_goals
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or, Sym2.eq_iff]
          repeat' constructor
          all_goals
            rintro ⟨h, _⟩
            have h0 := congrArg (fun z : OMA_Erdos506_Segre.Pt => z 0) h
            have h1 := congrArg (fun z : OMA_Erdos506_Segre.Pt => z 1) h
            simp only [OMA_Erdos506_Segre.p1, OMA_Erdos506_Segre.p3,
              OMA_Erdos506_Segre.p4, OMA_Erdos506_Segre.p5, OMA_Erdos506_Segre.p6,
              OMA_Erdos506_Segre.mkPt, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
              Matrix.cons_val_fin_one] at h0 h1
            linarith
      have hsub_sdiff : pairs ⊆ (OMA_Erdos506_Segre.C7.offDiag.image (fun q => s(q.1, q.2))) \ bad3 := by
        intro e he
        simp only [pairs, Finset.mem_filter] at he
        exact Finset.mem_sdiff.mpr ⟨he.1, by simp [bad3, he.2]⟩
      calc pairs.card
          ≤ ((OMA_Erdos506_Segre.C7.offDiag.image (fun q => s(q.1, q.2))) \ bad3).card := Finset.card_le_card hsub_sdiff
        _ = 21 - 3 := by rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hbad3_sub, htot, hbad3_card]
        _ = 18 := rfl
    -- Map every circle s in S_circ into Option pairs: none if s = unitSphere, else some s(a, b)
    let Scirc : Set (Sphere OMA_Erdos506_Segre.Pt) :=
      {s | 3 ≤ {p ∈ (OMA_Erdos506_Segre.P8 : Set OMA_Erdos506_Segre.Pt) | p ∈ s}.ncard}
    have hmap : ∀ s ∈ Scirc, s = OMA_Erdos506_Segre.unitSphere ∨
        ∃ e ∈ pairs, OMA_Erdos506_Segre.p0 ∈ s ∧ ∀ p ∈ e, p ∈ s := by
      intro s hs
      have hfin : {p ∈ (OMA_Erdos506_Segre.P8 : Set OMA_Erdos506_Segre.Pt) | p ∈ s}.Finite :=
        OMA_Erdos506_Segre.P8.finite_toSet.subset (fun _ h => h.1)
      set F : Finset OMA_Erdos506_Segre.Pt := OMA_Erdos506_Segre.P8.filter (fun p => p ∈ s)
      have hFcard : 3 ≤ F.card := by
        have hEq : (F : Set OMA_Erdos506_Segre.Pt) = {p ∈ (OMA_Erdos506_Segre.P8 : Set OMA_Erdos506_Segre.Pt) | p ∈ s} := by
          ext p; simp [F]
        have h3 : 3 ≤ {p ∈ (OMA_Erdos506_Segre.P8 : Set OMA_Erdos506_Segre.Pt) | p ∈ s}.ncard := hs
        rw [← hEq, Set.ncard_coe_finset] at h3; exact h3
      -- Split F into F ∩ C7 and {p0}
      set FC : Finset OMA_Erdos506_Segre.Pt := F.filter (fun p => p ∈ OMA_Erdos506_Segre.C7)
      by_cases hFC3 : 3 ≤ FC.card
      · left
        obtain ⟨T, hTsub, hT3⟩ := Finset.exists_subset_card_eq hFC3
        rw [Finset.card_eq_three] at hT3
        rcases hT3 with ⟨a, b, c, hab, hac, hbc, rfl⟩
        have haF : a ∈ FC := hTsub (by simp)
        have hbF : b ∈ FC := hTsub (by simp)
        have hcF : c ∈ FC := hTsub (by simp)
        have haC := (Finset.mem_filter.mp haF).2
        have hbC := (Finset.mem_filter.mp hbF).2
        have hcC := (Finset.mem_filter.mp hcF).2
        have haS := (Finset.mem_filter.mp (Finset.mem_filter.mp haF).1).2
        have hbS := (Finset.mem_filter.mp (Finset.mem_filter.mp hbF).1).2
        have hcS := (Finset.mem_filter.mp (Finset.mem_filter.mp hcF).1).2
        exact OMA_Erdos506_Segre.sphere_eq_of_three_noncollinear haS hbS hcS
          (OMA_Erdos506_Segre.mem_unitSphere_of_sq (OMA_Erdos506_Segre.C7_on_unit a haC))
          (OMA_Erdos506_Segre.mem_unitSphere_of_sq (OMA_Erdos506_Segre.C7_on_unit b hbC))
          (OMA_Erdos506_Segre.mem_unitSphere_of_sq (OMA_Erdos506_Segre.C7_on_unit c hcC))
          (OMA_Erdos506_Segre.unitCircle_three_det_ne_zero
            (OMA_Erdos506_Segre.C7_on_unit a haC) (OMA_Erdos506_Segre.C7_on_unit b hbC)
            (OMA_Erdos506_Segre.C7_on_unit c hcC) hab hac hbc)
      · right
        have hp0F : OMA_Erdos506_Segre.p0 ∈ F := by
          by_contra hp0n
          have hsub : F ⊆ FC := by
            intro p hp
            refine Finset.mem_filter.mpr ⟨hp, ?_⟩
            have hP := (Finset.mem_filter.mp hp).1
            rw [OMA_Erdos506_Segre.P8, Finset.mem_insert] at hP
            exact hP.resolve_left (fun heq => hp0n (heq ▸ hp))
          have := Finset.card_le_card hsub; omega
        have hp0s : OMA_Erdos506_Segre.p0 ∈ s := (Finset.mem_filter.mp hp0F).2
        have hFC2 : 2 ≤ FC.card := by
          have hsub : F ⊆ insert OMA_Erdos506_Segre.p0 FC := by
            intro p hp
            have hP := (Finset.mem_filter.mp hp).1
            rw [OMA_Erdos506_Segre.P8, Finset.mem_insert] at hP
            rcases hP with rfl | hC
            · exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hp, hC⟩)
          have hle := Finset.card_le_card hsub
          have hins := Finset.card_insert_le OMA_Erdos506_Segre.p0 FC
          omega
        obtain ⟨T, hTsub, hT2⟩ := Finset.exists_subset_card_eq hFC2
        rw [Finset.card_eq_two] at hT2
        rcases hT2 with ⟨a, b, hab, rfl⟩
        have haF : a ∈ FC := hTsub (by simp)
        have hbF : b ∈ FC := hTsub (by simp)
        have haC := (Finset.mem_filter.mp haF).2
        have hbC := (Finset.mem_filter.mp hbF).2
        have haS := (Finset.mem_filter.mp (Finset.mem_filter.mp haF).1).2
        have hbS := (Finset.mem_filter.mp (Finset.mem_filter.mp hbF).1).2
        have hnot_anti : ∀ p q : OMA_Erdos506_Segre.Pt, p ≠ OMA_Erdos506_Segre.p0 → q = -p →
            s(a, b) ≠ s(p, q) := by
          intro p q hpne hqp heq
          rw [Sym2.eq_iff] at heq
          rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact OMA_Erdos506_Segre.no_sphere_through_origin_antipodal hpne hp0s haS (hqp ▸ hbS)
          · exact OMA_Erdos506_Segre.no_sphere_through_origin_antipodal hpne hp0s hbS (hqp ▸ haS)
        refine ⟨s(a, b), Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨(a, b), Finset.mem_offDiag.mpr ⟨haC, hbC, hab⟩, rfl⟩,
          ⟨hnot_anti OMA_Erdos506_Segre.p1 OMA_Erdos506_Segre.p2 (by intro h; have := congrArg (fun z : OMA_Erdos506_Segre.Pt => z 0) h; simp [OMA_Erdos506_Segre.p0, OMA_Erdos506_Segre.p1, OMA_Erdos506_Segre.mkPt] at this)
            (by ext i; fin_cases i <;> simp [OMA_Erdos506_Segre.p1, OMA_Erdos506_Segre.p2, OMA_Erdos506_Segre.mkPt]),
           hnot_anti OMA_Erdos506_Segre.p3 OMA_Erdos506_Segre.p4 (by intro h; have := congrArg (fun z : OMA_Erdos506_Segre.Pt => z 1) h; simp [OMA_Erdos506_Segre.p0, OMA_Erdos506_Segre.p3, OMA_Erdos506_Segre.mkPt] at this)
            (by ext i; fin_cases i <;> simp [OMA_Erdos506_Segre.p3, OMA_Erdos506_Segre.p4, OMA_Erdos506_Segre.mkPt]),
           hnot_anti OMA_Erdos506_Segre.p5 OMA_Erdos506_Segre.p6 (by intro h; have := congrArg (fun z : OMA_Erdos506_Segre.Pt => z 0) h; simp [OMA_Erdos506_Segre.p0, OMA_Erdos506_Segre.p5, OMA_Erdos506_Segre.mkPt] at this)
            (by ext i; fin_cases i <;> simp [OMA_Erdos506_Segre.p5, OMA_Erdos506_Segre.p6, OMA_Erdos506_Segre.mkPt] <;> ring)⟩⟩,
          hp0s, fun p hp => by
            rw [Sym2.mem_iff] at hp; rcases hp with rfl | rfl <;> assumption⟩
    -- Build an injective map from Scirc to Option {e // e ∈ pairs}
    have hcard_le : Scirc.ncard ≤ 1 + pairs.card := by
      -- Every e ∈ pairs determines AT MOST ONE sphere through p0 and e!
      have huniq : ∀ e ∈ pairs, ∀ s1 s2 : Sphere OMA_Erdos506_Segre.Pt,
          OMA_Erdos506_Segre.p0 ∈ s1 → (∀ p ∈ e, p ∈ s1) →
          OMA_Erdos506_Segre.p0 ∈ s2 → (∀ p ∈ e, p ∈ s2) → s1 = s2 := by
        intro e he s1 s2 h01 he1 h02 he2
        simp only [pairs, Finset.mem_filter, Finset.mem_image, Finset.mem_offDiag] at he
        rcases he with ⟨⟨⟨a, b⟩, ⟨haC, hbC, hab⟩, rfl⟩, hne12, hne34, hne56⟩
        have hanti : a ≠ -b := by
          intro heq
          -- Check all pairs of points in C7 with a = -b: only {p1,p2}, {p3,p4}, {p5,p6}!
          have hpair : s(a, b) = s(OMA_Erdos506_Segre.p1, OMA_Erdos506_Segre.p2) ∨
                       s(a, b) = s(OMA_Erdos506_Segre.p3, OMA_Erdos506_Segre.p4) ∨
                       s(a, b) = s(OMA_Erdos506_Segre.p5, OMA_Erdos506_Segre.p6) := by
            have h0 : a 0 = -(b 0) := congrArg (fun z : OMA_Erdos506_Segre.Pt => z 0) heq
            have h1 : a 1 = -(b 1) := congrArg (fun z : OMA_Erdos506_Segre.Pt => z 1) heq
            simp only [OMA_Erdos506_Segre.C7, Finset.mem_insert, Finset.mem_singleton] at haC hbC
            rcases haC with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
              rcases hbC with rfl | rfl | rfl | rfl | rfl | rfl | rfl
            all_goals
              first
              | exact Or.inl rfl
              | exact Or.inl Sym2.eq_swap
              | exact Or.inr (Or.inl rfl)
              | exact Or.inr (Or.inl Sym2.eq_swap)
              | exact Or.inr (Or.inr rfl)
              | exact Or.inr (Or.inr Sym2.eq_swap)
              | (exfalso
                 simp only [OMA_Erdos506_Segre.p1, OMA_Erdos506_Segre.p2, OMA_Erdos506_Segre.p3,
                   OMA_Erdos506_Segre.p4, OMA_Erdos506_Segre.p5, OMA_Erdos506_Segre.p6,
                   OMA_Erdos506_Segre.p7, OMA_Erdos506_Segre.mkPt, PiLp.toLp_apply,
                   Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h0 h1
                 linarith)
          rcases hpair with h | h | h
          · exact hne12 h
          · exact hne34 h
          · exact hne56 h
        exact OMA_Erdos506_Segre.sphere_eq_of_three_noncollinear
          h01 (he1 a (by simp)) (he1 b (by simp))
          h02 (he2 a (by simp)) (he2 b (by simp))
          (OMA_Erdos506_Segre.origin_unitCircle_det_ne_zero
            (OMA_Erdos506_Segre.C7_on_unit a haC) (OMA_Erdos506_Segre.C7_on_unit b hbC) hab hanti)
      -- Embed Scirc into insert none (pairs.image some)
      let f : Sphere OMA_Erdos506_Segre.Pt → Option (Sym2 OMA_Erdos506_Segre.Pt) :=
        fun s => if h : s ∈ Scirc ∧ s ≠ OMA_Erdos506_Segre.unitSphere then
          some ((hmap s h.1).resolve_left h.2).choose
        else none
      have hf_mem : ∀ s ∈ Scirc, f s ∈ insert (none : Option (Sym2 OMA_Erdos506_Segre.Pt)) (pairs.image some) := by
        intro s hs
        by_cases hu : s = OMA_Erdos506_Segre.unitSphere
        · simp [f, hu]
        · have hcond : s ∈ Scirc ∧ s ≠ OMA_Erdos506_Segre.unitSphere := ⟨hs, hu⟩
          simp only [f, dif_pos hcond]
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem some ((hmap s hs).resolve_left hu).choose_spec.1)
      have hf_inj : Set.InjOn f Scirc := by
        intro s1 hs1 s2 hs2 heq
        by_cases hu1 : s1 = OMA_Erdos506_Segre.unitSphere <;> by_cases hu2 : s2 = OMA_Erdos506_Segre.unitSphere
        · rw [hu1, hu2]
        · have h2 : s2 ∈ Scirc ∧ s2 ≠ OMA_Erdos506_Segre.unitSphere := ⟨hs2, hu2⟩
          simp only [f, hu1, ne_eq, not_true_eq_false, and_false, ↓reduceDIte, dif_pos h2] at heq
          exact absurd heq (by simp)
        · have h1 : s1 ∈ Scirc ∧ s1 ≠ OMA_Erdos506_Segre.unitSphere := ⟨hs1, hu1⟩
          simp only [f, hu2, ne_eq, not_true_eq_false, and_false, ↓reduceDIte, dif_pos h1] at heq
          exact absurd heq (by simp)
        · have h1 : s1 ∈ Scirc ∧ s1 ≠ OMA_Erdos506_Segre.unitSphere := ⟨hs1, hu1⟩
          have h2 : s2 ∈ Scirc ∧ s2 ≠ OMA_Erdos506_Segre.unitSphere := ⟨hs2, hu2⟩
          simp only [f, dif_pos h1, dif_pos h2, Option.some.injEq] at heq
          have spec1 := ((hmap s1 hs1).resolve_left hu1).choose_spec
          have spec2 := ((hmap s2 hs2).resolve_left hu2).choose_spec
          rw [← heq] at spec2
          exact huniq _ spec1.1 s1 s2 spec1.2.1 spec1.2.2 spec2.2.1 spec2.2.2
      have hfinS : Scirc.Finite :=
        Set.Finite.of_finite_image (Finset.finite_toSet _ |>.subset (fun y hy => by
          rcases hy with ⟨s, hs, rfl⟩; exact hf_mem s hs)) hf_inj
      calc Scirc.ncard
          = (f '' Scirc).ncard := hf_inj.ncard_image.symm
        _ ≤ ((insert (none : Option (Sym2 OMA_Erdos506_Segre.Pt)) (pairs.image some) : Finset _) : Set _).ncard :=
            Set.ncard_le_ncard (fun y hy => by rcases hy with ⟨s, hs, rfl⟩; exact hf_mem s hs) (Finset.finite_toSet _)
        _ = (insert (none : Option (Sym2 OMA_Erdos506_Segre.Pt)) (pairs.image some)).card :=
            Set.ncard_coe_finset _
        _ ≤ 1 + (pairs.image some).card := by
            have := Finset.card_insert_le (none : Option (Sym2 OMA_Erdos506_Segre.Pt)) (pairs.image some)
            omega
        _ ≤ 1 + pairs.card := Nat.add_le_add_left Finset.card_image_le 1
    have h21 : (8 - 1).choose 2 = 21 := by decide
    change Scirc.ncard < (8 - 1).choose 2
    omega
