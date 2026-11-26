import FormalConjectures.ErdosProblems.«668»

/-!
# Proof of Erdős Problem 668 (Four Points)

We prove that for `n = 4` there is, up to congruence, a unique 4-point set in `ℝ²` maximizing the
number of unit distances, namely the unit rhombus `R0 = {p2, p0, p1, p3}` formed by two unit
equilateral triangles joined along `p0 p1`:
1. `R0` has 4 points and `5 ≤ unitDistNum R0 ≤ maxUnitDistances 4`.
2. Any 4-point set `S` with `5 ≤ unitDistNum S` has at most one non-unit pair, so an explicit
   rigid motion sends `R0` onto `S`.
3. `unitDistNum` is invariant under isometries `ℝ² ≃ᵢ ℝ²`, so every 4-point set satisfies
   `unitDistNum S ≤ unitDistNum R0`, yielding `unitDistNum R0 = maxUnitDistances 4` and the
   exact characterization `unitDistNum B = maxUnitDistances 4 ↔ ∃ f : ℝ² ≃ᵢ ℝ², f '' R0 = B`.
-/

-- Problem: Erdős Problem 668 — four points
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/668.lean:84 (declaration Erdos668.erdos_668.variants.four_points)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace Erdos668FourPointsProof

open Erdos668 Erdos90
open scoped EuclideanGeometry

private noncomputable def mkPt (x y : ℝ) : ℝ² :=
  WithLp.toLp 2 ![x, y]

private lemma mkPt_zero (x y : ℝ) : mkPt x y 0 = x := rfl
private lemma mkPt_one (x y : ℝ) : mkPt x y 1 = y := rfl

private lemma dist_sq_eq (a b : ℝ²) :
    dist a b ^ 2 = (a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
  simp [Real.dist_eq]

private lemma dist_eq_one_iff (a b : ℝ²) :
    dist a b = 1 ↔ (a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2 = 1 := by
  constructor
  · intro h
    rw [← dist_sq_eq, h, one_pow]
  · intro h
    have hsq : dist a b ^ 2 = 1 ^ 2 := by rw [dist_sq_eq, h, one_pow]
    nlinarith [dist_nonneg (x := a) (y := b)]

private lemma dist_sym2_out (a b : ℝ²) :
    dist (s(a, b)).out.1 (s(a, b)).out.2 = dist a b := by
  have h : s((s(a, b)).out.1, (s(a, b)).out.2) = s(a, b) := Quot.out_eq s(a, b)
  rw [Sym2.eq_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, dist_comm]

private noncomputable def p0 : ℝ² := mkPt 0 0
private noncomputable def p1 : ℝ² := mkPt 1 0
private noncomputable def p2 : ℝ² := mkPt (1 / 2) (Real.sqrt 3 / 2)
private noncomputable def p3 : ℝ² := mkPt (1 / 2) (-(Real.sqrt 3 / 2))
private noncomputable def R0 : Finset ℝ² := {p0, p1, p2, p3}

private lemma sqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)

private lemma p0_ne_p1 : p0 ≠ p1 := by
  intro h; have := congr_arg (fun q : ℝ² => q 0) h; simp [p0, p1, mkPt_zero] at this

private lemma p0_ne_p2 : p0 ≠ p2 := by
  intro h; have := congr_arg (fun q : ℝ² => q 0) h; simp [p0, p2, mkPt_zero] at this

private lemma p0_ne_p3 : p0 ≠ p3 := by
  intro h; have := congr_arg (fun q : ℝ² => q 0) h; simp [p0, p3, mkPt_zero] at this

private lemma p1_ne_p2 : p1 ≠ p2 := by
  intro h; have := congr_arg (fun q : ℝ² => q 0) h; simp [p1, p2, mkPt_zero] at this

private lemma p1_ne_p3 : p1 ≠ p3 := by
  intro h; have := congr_arg (fun q : ℝ² => q 0) h; simp [p1, p3, mkPt_zero] at this

private lemma p2_ne_p3 : p2 ≠ p3 := by
  intro h
  have h1 := congr_arg (fun q : ℝ² => q 1) h
  simp only [p2, p3, mkPt_one] at h1
  linarith [sqrt3_pos]

private lemma dist_p0_p1 : dist p0 p1 = 1 := by
  rw [dist_eq_one_iff]; simp [p0, p1, mkPt_zero, mkPt_one]

private lemma dist_p0_p2 : dist p0 p2 = 1 := by
  rw [dist_eq_one_iff]
  simp only [p0, p2, mkPt_zero, mkPt_one]
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  nlinarith

private lemma dist_p0_p3 : dist p0 p3 = 1 := by
  rw [dist_eq_one_iff]
  simp only [p0, p3, mkPt_zero, mkPt_one]
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  nlinarith

private lemma dist_p1_p2 : dist p1 p2 = 1 := by
  rw [dist_eq_one_iff]
  simp only [p1, p2, mkPt_zero, mkPt_one]
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  nlinarith

private lemma dist_p1_p3 : dist p1 p3 = 1 := by
  rw [dist_eq_one_iff]
  simp only [p1, p3, mkPt_zero, mkPt_one]
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  nlinarith

private lemma card_R0 : R0.card = 4 := by
  simp [R0, p0_ne_p1, p0_ne_p2, p0_ne_p3, p1_ne_p2, p1_ne_p3, p2_ne_p3]

private lemma five_le_unitDistNum_R0 : 5 ≤ unitDistNum R0 := by
  classical
  let E : Finset (Sym2 ℝ²) := {s(p0, p1), s(p0, p2), s(p0, p3), s(p1, p2), s(p1, p3)}
  have hE_card : E.card = 5 := by
    simp [E, p0_ne_p1, p0_ne_p2, p0_ne_p3, p1_ne_p2, p1_ne_p3, p2_ne_p3,
      p0_ne_p1.symm, p0_ne_p2.symm, p1_ne_p2.symm, p1_ne_p3.symm, p2_ne_p3.symm]
  have hE_sub : E ⊆ R0.sym2.filter (fun p => dist p.out.1 p.out.2 = 1) := by
    intro e he
    simp only [E, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl <;>
      refine Finset.mem_filter.mpr ⟨Finset.mk_mem_sym2_iff.mpr ?_, ?_⟩
    · exact ⟨by simp [R0], by simp [R0]⟩
    · rw [dist_sym2_out, dist_p0_p1]
    · exact ⟨by simp [R0], by simp [R0]⟩
    · rw [dist_sym2_out, dist_p0_p2]
    · exact ⟨by simp [R0], by simp [R0]⟩
    · rw [dist_sym2_out, dist_p0_p3]
    · exact ⟨by simp [R0], by simp [R0]⟩
    · rw [dist_sym2_out, dist_p1_p2]
    · exact ⟨by simp [R0], by simp [R0]⟩
    · rw [dist_sym2_out, dist_p1_p3]
  calc
    5 = E.card := hE_card.symm
    _ ≤ (R0.sym2.filter (fun p => dist p.out.1 p.out.2 = 1)).card := Finset.card_le_card hE_sub
    _ = unitDistNum R0 := rfl

private lemma five_le_maxUnitDistances_four : 5 ≤ maxUnitDistances 4 := by
  exact le_trans five_le_unitDistNum_R0
    (le_csSup (unitDistanceCounts_BddAbove 4) ⟨R0, card_R0, rfl⟩)

private noncomputable def rigidMotion (u v : ℝ²) (huv : dist u v = 1) : ℝ² ≃ᵢ ℝ² :=
  let c : ℝ := v 0 - u 0
  let d : ℝ := v 1 - u 1
  have hcd : c ^ 2 + d ^ 2 = 1 := by
    have h := (dist_eq_one_iff u v).mp huv
    dsimp only [c, d]
    linarith
  { toFun := fun q => mkPt (u 0 + c * q 0 - d * q 1) (u 1 + d * q 0 + c * q 1)
    invFun := fun r => mkPt (c * (r 0 - u 0) + d * (r 1 - u 1))
      (-d * (r 0 - u 0) + c * (r 1 - u 1))
    left_inv := fun q => by
      ext i
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, mkPt_zero, mkPt_one]
        linear_combination (q 0) * hcd
      · simp only [Fin.mk_one, Fin.isValue, mkPt_zero, mkPt_one]
        linear_combination (q 1) * hcd
    right_inv := fun r => by
      ext i
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, mkPt_zero, mkPt_one]
        linear_combination (r 0 - u 0) * hcd
      · simp only [Fin.mk_one, Fin.isValue, mkPt_zero, mkPt_one]
        linear_combination (r 1 - u 1) * hcd
    isometry_toFun := isometry_iff_dist_eq.mpr fun p q => by
      have hsq : dist (mkPt (u 0 + c * p 0 - d * p 1) (u 1 + d * p 0 + c * p 1))
          (mkPt (u 0 + c * q 0 - d * q 1) (u 1 + d * q 0 + c * q 1)) ^ 2 = dist p q ^ 2 := by
        rw [dist_sq_eq, dist_sq_eq]
        simp only [mkPt_zero, mkPt_one]
        linear_combination ((p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2) * hcd
      nlinarith [dist_nonneg (x := mkPt (u 0 + c * p 0 - d * p 1) (u 1 + d * p 0 + c * p 1))
          (y := mkPt (u 0 + c * q 0 - d * q 1) (u 1 + d * q 0 + c * q 1)),
        dist_nonneg (x := p) (y := q)] }

private lemma rigidMotion_p0 (u v : ℝ²) (huv : dist u v = 1) :
    rigidMotion u v huv p0 = u := by
  ext i
  fin_cases i <;> simp [rigidMotion, p0, mkPt_zero, mkPt_one]

private lemma rigidMotion_p1 (u v : ℝ²) (huv : dist u v = 1) :
    rigidMotion u v huv p1 = v := by
  ext i
  fin_cases i <;> simp [rigidMotion, p1, mkPt_zero, mkPt_one]

private lemma eq_p2_or_p3_of_dist_p0_p1 {q : ℝ²} (h0 : dist q p0 = 1) (h1 : dist q p1 = 1) :
    q = p2 ∨ q = p3 := by
  have h0' := (dist_eq_one_iff q p0).mp h0
  have h1' := (dist_eq_one_iff q p1).mp h1
  simp only [p0, p1, mkPt_zero, mkPt_one, sub_zero] at h0' h1'
  have hq0 : q 0 = 1 / 2 := by linarith
  have hq1_sq : q 1 ^ 2 = (Real.sqrt 3 / 2) ^ 2 := by
    have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hq1_sq with hq1 | hq1
  · left
    ext i
    fin_cases i
    · simpa [p2, mkPt_zero] using hq0
    · simpa [p2, mkPt_one] using hq1
  · right
    ext i
    fin_cases i
    · simpa [p3, mkPt_zero] using hq0
    · simpa [p3, mkPt_one] using hq1

private lemma exists_isometry_of_rhombus {u v s t : ℝ²} (hst : s ≠ t)
    (huv : dist u v = 1) (hus : dist u s = 1) (hut : dist u t = 1)
    (hvs : dist v s = 1) (hvt : dist v t = 1) :
    ∃ f : ℝ² ≃ᵢ ℝ², f '' (R0 : Set ℝ²) = ({u, v, s, t} : Set ℝ²) := by
  let f : ℝ² ≃ᵢ ℝ² := rigidMotion u v huv
  have hf0 : f p0 = u := rigidMotion_p0 u v huv
  have hf1 : f p1 = v := rigidMotion_p1 u v huv
  let s' : ℝ² := f.symm s
  let t' : ℝ² := f.symm t
  have hs0 : dist s' p0 = 1 := by
    have := f.dist_eq s' p0
    simp only [s', f.apply_symm_apply, hf0] at this
    rw [← this, dist_comm, hus]
  have hs1 : dist s' p1 = 1 := by
    have := f.dist_eq s' p1
    simp only [s', f.apply_symm_apply, hf1] at this
    rw [← this, dist_comm, hvs]
  have ht0 : dist t' p0 = 1 := by
    have := f.dist_eq t' p0
    simp only [t', f.apply_symm_apply, hf0] at this
    rw [← this, dist_comm, hut]
  have ht1 : dist t' p1 = 1 := by
    have := f.dist_eq t' p1
    simp only [t', f.apply_symm_apply, hf1] at this
    rw [← this, dist_comm, hvt]
  have hst' : s' ≠ t' := fun h => hst (f.symm.injective h)
  have hs_cases := eq_p2_or_p3_of_dist_p0_p1 hs0 hs1
  have ht_cases := eq_p2_or_p3_of_dist_p0_p1 ht0 ht1
  refine ⟨f, ?_⟩
  have hR0_coe : (R0 : Set ℝ²) = {p0, p1, p2, p3} := by simp [R0]
  rw [hR0_coe]
  rcases hs_cases with hs2 | hs3 <;> rcases ht_cases with ht2 | ht3
  · exact absurd (hs2.trans ht2.symm) hst'
  · have hfp2 : f p2 = s := by rw [← hs2]; exact f.apply_symm_apply s
    have hfp3 : f p3 = t := by rw [← ht3]; exact f.apply_symm_apply t
    simp [Set.image_insert_eq, hf0, hf1, hfp2, hfp3]
  · have hfp2 : f p2 = t := by rw [← ht2]; exact f.apply_symm_apply t
    have hfp3 : f p3 = s := by rw [← hs3]; exact f.apply_symm_apply s
    simp only [Set.image_insert_eq, Set.image_singleton, hf0, hf1, hfp2, hfp3]
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor <;> (rintro (rfl | rfl | rfl | rfl) <;> simp)
  · exact absurd (hs3.trans ht3.symm) hst'

private lemma exists_rhombus_labeling (S : Finset ℝ²)
    (hcard : S.card = 4) (hdist : 5 ≤ unitDistNum S) :
    ∃ u v s t : ℝ², s ≠ t ∧
      dist u v = 1 ∧ dist u s = 1 ∧ dist u t = 1 ∧ dist v s = 1 ∧ dist v t = 1 ∧
      (S : Set ℝ²) = {u, v, s, t} := by
  classical
  have h4 : ∃ w x y z : ℝ², w ≠ x ∧ w ≠ y ∧ w ≠ z ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      S = {w, x, y, z} := by
    rcases Finset.card_eq_succ.mp hcard with ⟨w, S1, hw1, rfl, h1⟩
    rcases Finset.card_eq_succ.mp h1 with ⟨x, S2, hx2, rfl, h2⟩
    rcases Finset.card_eq_succ.mp h2 with ⟨y, S3, hy3, rfl, h3⟩
    rcases Finset.card_eq_one.mp h3 with ⟨z, rfl⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw1 hx2 hy3
    exact ⟨w, x, y, z, hw1.1, hw1.2.1, hw1.2.2, hx2.1, hx2.2, hy3, rfl⟩
  rcases h4 with ⟨w, x, y, z, hwx, hwy, hwz, hxy, hxz, hyz, rfl⟩
  let pairs : Finset (Sym2 ℝ²) :=
    {s(w, x), s(w, y), s(w, z), s(x, y), s(x, z), s(y, z)}
  have hm1 : s(w, x) ∈ pairs := Finset.mem_insert_self _ _
  have hm2 : s(w, y) ∈ pairs := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hm3 : s(w, z) ∈ pairs :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hm4 : s(x, y) ∈ pairs :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_insert_self _ _)))
  have hm5 : s(x, z) ∈ pairs :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))
  have hm6 : s(y, z) ∈ pairs :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))))
  have hpairs_card : pairs.card ≤ 6 := by
    dsimp only [pairs]
    have h1 := Finset.card_insert_le s(w, x) {s(w, y), s(w, z), s(x, y), s(x, z), s(y, z)}
    have h2 := Finset.card_insert_le s(w, y) {s(w, z), s(x, y), s(x, z), s(y, z)}
    have h3 := Finset.card_insert_le s(w, z) {s(x, y), s(x, z), s(y, z)}
    have h4 := Finset.card_insert_le s(x, y) {s(x, z), s(y, z)}
    have h5 := Finset.card_insert_le s(x, z) {s(y, z)}
    have h6 := Finset.card_singleton s(y, z)
    omega
  have hunit_sub : ({w, x, y, z} : Finset ℝ²).sym2.filter (fun p => dist p.out.1 p.out.2 = 1) ⊆
      pairs.filter (fun p => dist p.out.1 p.out.2 = 1) := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hmem, hdp⟩
    refine Finset.mem_filter.mpr ⟨?_, hdp⟩
    revert hmem hdp
    refine Sym2.ind (fun a b hab hdab => ?_) p
    rw [dist_sym2_out] at hdab
    have hne : a ≠ b := by
      intro h; subst h; simp at hdab
    rw [Finset.mk_mem_sym2_iff] at hab
    simp only [Finset.mem_insert, Finset.mem_singleton] at hab
    rcases hab with ⟨rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl⟩
    · exact absurd rfl hne
    · exact hm1
    · exact hm2
    · exact hm3
    · rw [Sym2.eq_swap]; exact hm1
    · exact absurd rfl hne
    · exact hm4
    · exact hm5
    · rw [Sym2.eq_swap]; exact hm2
    · rw [Sym2.eq_swap]; exact hm4
    · exact absurd rfl hne
    · exact hm6
    · rw [Sym2.eq_swap]; exact hm3
    · rw [Sym2.eq_swap]; exact hm5
    · rw [Sym2.eq_swap]; exact hm6
    · exact absurd rfl hne
  have hgood_ge : 5 ≤ (pairs.filter (fun p => dist p.out.1 p.out.2 = 1)).card :=
    le_trans hdist (Finset.card_le_card hunit_sub)
  have hbad_le : (pairs.filter (fun p => ¬ dist p.out.1 p.out.2 = 1)).card ≤ 1 := by
    have hdisj : Disjoint (pairs.filter (fun p => dist p.out.1 p.out.2 = 1))
        (pairs.filter (fun p => ¬ dist p.out.1 p.out.2 = 1)) :=
      Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1
    have hunion : pairs.filter (fun p => dist p.out.1 p.out.2 = 1) ∪
        pairs.filter (fun p => ¬ dist p.out.1 p.out.2 = 1) = pairs := by
      ext r
      simp only [Finset.mem_union, Finset.mem_filter]
      exact ⟨fun h => h.elim And.left And.left,
        fun h => (em (dist r.out.1 r.out.2 = 1)).imp (And.intro h) (And.intro h)⟩
    have hsum : (pairs.filter (fun p => dist p.out.1 p.out.2 = 1)).card +
        (pairs.filter (fun p => ¬ dist p.out.1 p.out.2 = 1)).card = pairs.card := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    omega
  have hnot_two : ∀ p q : Sym2 ℝ², p ∈ pairs → q ∈ pairs → p ≠ q →
      dist p.out.1 p.out.2 = 1 ∨ dist q.out.1 q.out.2 = 1 := by
    intro p q hp hq hpq
    by_contra hboth
    push Not at hboth
    have hsub : ({p, q} : Finset (Sym2 ℝ²)) ⊆
        pairs.filter (fun r => ¬ dist r.out.1 r.out.2 = 1) := by
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hp, hboth.1⟩
      · exact Finset.mem_filter.mpr ⟨hq, hboth.2⟩
    have h2 : 2 ≤ (pairs.filter (fun r => ¬ dist r.out.1 r.out.2 = 1)).card := by
      calc
        2 = ({p, q} : Finset (Sym2 ℝ²)).card := by simp [hpq]
        _ ≤ _ := Finset.card_le_card hsub
    omega
  have hpair_or : ∀ a b c d : ℝ², s(a, b) ∈ pairs → s(c, d) ∈ pairs → s(a, b) ≠ s(c, d) →
      dist a b = 1 ∨ dist c d = 1 := by
    intro a b c d hab hcd hne
    simpa [dist_sym2_out] using hnot_two s(a, b) s(c, d) hab hcd hne
  have hsym_ne : ∀ {a b c d : ℝ²}, (a ≠ c ∨ b ≠ d) → (a ≠ d ∨ b ≠ c) → s(a, b) ≠ s(c, d) := by
    intro a b c d h1 h2 heq
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases h1 with h | h <;> exact h rfl
    · rcases h2 with h | h <;> exact h rfl
  by_cases h1 : dist w x = 1
  · by_cases h2 : dist w y = 1
    · by_cases h3 : dist w z = 1
      · by_cases h4 : dist x y = 1
        · by_cases h5 : dist x z = 1
          · exact ⟨w, x, y, z, hyz, h1, h2, h3, h4, h5, by simp⟩
          · have h6 : dist y z = 1 := (hpair_or x z y z hm5 hm6
              (hsym_ne (Or.inl hxy) (Or.inl hxz))).resolve_left h5
            exact ⟨w, y, x, z, hxz, h2, h1, h3, by rwa [dist_comm], h6, by
              ext q; simp only [Finset.coe_insert, Finset.coe_singleton,
                Set.mem_insert_iff, Set.mem_singleton_iff]
              constructor <;> (rintro (rfl | rfl | rfl | rfl) <;> simp)⟩
        · have h5 : dist x z = 1 := (hpair_or x y x z hm4 hm5
            (hsym_ne (Or.inr hyz) (Or.inl hxz))).resolve_left h4
          have h6 : dist y z = 1 := (hpair_or x y y z hm4 hm6
            (hsym_ne (Or.inl hxy) (Or.inl hxz))).resolve_left h4
          exact ⟨w, z, x, y, hxy, h3, h1, h2, by rwa [dist_comm], by rwa [dist_comm], by
            ext q; simp only [Finset.coe_insert, Finset.coe_singleton,
              Set.mem_insert_iff, Set.mem_singleton_iff]
            constructor <;> (rintro (rfl | rfl | rfl | rfl) <;> simp)⟩
      · have h4 : dist x y = 1 := (hpair_or w z x y hm3 hm4
          (hsym_ne (Or.inl hwx) (Or.inl hwy))).resolve_left h3
        have h5 : dist x z = 1 := (hpair_or w z x z hm3 hm5
          (hsym_ne (Or.inl hwx) (Or.inl hwz))).resolve_left h3
        have h6 : dist y z = 1 := (hpair_or w z y z hm3 hm6
          (hsym_ne (Or.inl hwy) (Or.inl hwz))).resolve_left h3
        exact ⟨x, y, w, z, hwz, h4, by rwa [dist_comm], h5, by rwa [dist_comm], h6, by
          ext q; simp only [Finset.coe_insert, Finset.coe_singleton,
            Set.mem_insert_iff, Set.mem_singleton_iff]
          constructor <;> (rintro (rfl | rfl | rfl | rfl) <;> simp)⟩
    · have h3 : dist w z = 1 := (hpair_or w y w z hm2 hm3
        (hsym_ne (Or.inr hyz) (Or.inl hwz))).resolve_left h2
      have h4 : dist x y = 1 := (hpair_or w y x y hm2 hm4
        (hsym_ne (Or.inl hwx) (Or.inl hwy))).resolve_left h2
      have h5 : dist x z = 1 := (hpair_or w y x z hm2 hm5
        (hsym_ne (Or.inl hwx) (Or.inl hwz))).resolve_left h2
      have h6 : dist y z = 1 := (hpair_or w y y z hm2 hm6
        (hsym_ne (Or.inl hwy) (Or.inl hwz))).resolve_left h2
      exact ⟨x, z, w, y, hwy, h5, by rwa [dist_comm], h4, by rwa [dist_comm], by rwa [dist_comm], by
        ext q; simp only [Finset.coe_insert, Finset.coe_singleton,
          Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor <;> (rintro (rfl | rfl | rfl | rfl) <;> simp)⟩
  · have h2 : dist w y = 1 := (hpair_or w x w y hm1 hm2
      (hsym_ne (Or.inr hxy) (Or.inl hwy))).resolve_left h1
    have h3 : dist w z = 1 := (hpair_or w x w z hm1 hm3
      (hsym_ne (Or.inr hxz) (Or.inl hwz))).resolve_left h1
    have h4 : dist x y = 1 := (hpair_or w x x y hm1 hm4
      (hsym_ne (Or.inl hwx) (Or.inl hwy))).resolve_left h1
    have h5 : dist x z = 1 := (hpair_or w x x z hm1 hm5
      (hsym_ne (Or.inl hwx) (Or.inl hwz))).resolve_left h1
    have h6 : dist y z = 1 := (hpair_or w x y z hm1 hm6
      (hsym_ne (Or.inl hwy) (Or.inl hwz))).resolve_left h1
    exact ⟨y, z, w, x, hwx, h6, by rwa [dist_comm], by rwa [dist_comm],
      by rwa [dist_comm], by rwa [dist_comm], by
      ext q; simp only [Finset.coe_insert, Finset.coe_singleton,
        Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor <;> (rintro (rfl | rfl | rfl | rfl) <;> simp)⟩

private lemma exists_isometry_from_R0 (S : Finset ℝ²)
    (hcard : S.card = 4) (hdist : 5 ≤ unitDistNum S) :
    ∃ f : ℝ² ≃ᵢ ℝ², f '' (R0 : Set ℝ²) = (S : Set ℝ²) := by
  rcases exists_rhombus_labeling S hcard hdist with
    ⟨u, v, s, t, hst, huv, hus, hut, hvs, hvt, hS⟩
  rcases exists_isometry_of_rhombus hst huv hus hut hvs hvt with ⟨f, hf⟩
  exact ⟨f, hf.trans hS.symm⟩

private lemma unitDistNum_eq_of_isometry (f : ℝ² ≃ᵢ ℝ²) {A B : Finset ℝ²}
    (hAB : f '' (A : Set ℝ²) = (B : Set ℝ²)) : unitDistNum B = unitDistNum A := by
  classical
  have hBeq : B = A.image f := by
    apply Finset.coe_injective
    rw [Finset.coe_image, hAB]
  subst hBeq
  have hfilt :
      (A.image f).sym2.filter (fun p => dist p.out.1 p.out.2 = 1) =
        (A.sym2.filter (fun p => dist p.out.1 p.out.2 = 1)).image (Sym2.map f) := by
    ext e
    refine Sym2.ind (fun x y => ?_) e
    simp only [Finset.mem_filter, Finset.mk_mem_sym2_iff, Finset.mem_image, dist_sym2_out]
    constructor
    · rintro ⟨⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩, hdist⟩
      refine ⟨s(a, b), ⟨Finset.mk_mem_sym2_iff.mpr ⟨ha, hb⟩, ?_⟩, rfl⟩
      rw [dist_sym2_out, ← f.dist_eq a b, hdist]
    · rintro ⟨e', ⟨he', hdist⟩, hmap⟩
      revert hmap he' hdist
      refine Sym2.ind (fun a b hmap hab hdab => ?_) e'
      rw [Finset.mk_mem_sym2_iff] at hab
      rw [dist_sym2_out] at hdab
      simp only [Sym2.map_mk] at hmap
      rw [Sym2.eq_iff] at hmap
      rcases hmap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨⟨⟨a, hab.1, rfl⟩, ⟨b, hab.2, rfl⟩⟩, by rw [f.dist_eq, hdab]⟩
      · exact ⟨⟨⟨b, hab.2, rfl⟩, ⟨a, hab.1, rfl⟩⟩, by rw [f.dist_eq, dist_comm, hdab]⟩
  change ((A.image f).sym2.filter (fun p => dist p.out.1 p.out.2 = 1)).card =
    (A.sym2.filter (fun p => dist p.out.1 p.out.2 = 1)).card
  rw [hfilt, Finset.card_image_of_injective _ (Sym2.map.injective f.injective)]

private lemma unitDistNum_R0_eq_maxUnitDistances_four :
    unitDistNum R0 = maxUnitDistances 4 := by
  apply le_antisymm
  · exact le_csSup (unitDistanceCounts_BddAbove 4) ⟨R0, card_R0, rfl⟩
  · refine csSup_le ⟨unitDistNum R0, R0, card_R0, rfl⟩ ?_
    rintro _ ⟨S, hScard, rfl⟩
    by_cases h5 : 5 ≤ unitDistNum S
    · rcases exists_isometry_from_R0 S hScard h5 with ⟨f, hf⟩
      rw [unitDistNum_eq_of_isometry f hf]
    · have hlt : unitDistNum S ≤ 5 := by omega
      exact le_trans hlt five_le_unitDistNum_R0

end Erdos668FourPointsProof

open Erdos668 Erdos90 Erdos668FourPointsProof
open scoped EuclideanGeometry

theorem OMA.solution : type_of% @Erdos668.erdos_668.variants.four_points := by
  refine ⟨p2, p0, p1, p3, by rw [dist_comm]; exact dist_p0_p2,
    by rw [dist_comm]; exact dist_p1_p2, dist_p0_p1, dist_p0_p3, dist_p1_p3, ?_, ?_⟩
  · have hEq : ({p2, p0, p1, p3} : Finset ℝ²) = R0 := by
      ext q
      simp [R0]
      tauto
    rw [hEq, card_R0]
  · intro B hBcard
    have hSetEq : ({p2, p0, p1, p3} : Set ℝ²) = (R0 : Set ℝ²) := by
      ext q
      simp [R0]
      tauto
    rw [hSetEq]
    constructor
    · intro hBmax
      have h5 : 5 ≤ unitDistNum B := hBmax ▸ five_le_maxUnitDistances_four
      exact exists_isometry_from_R0 B hBcard h5
    · rintro ⟨f, hf⟩
      rw [unitDistNum_eq_of_isometry f hf, unitDistNum_R0_eq_maxUnitDistances_four]
