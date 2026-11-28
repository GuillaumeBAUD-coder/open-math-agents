import OMAReductions.R_Erdos103_erdos_103_variants_two_le_R1_H2_R1_H2_R1
import Mathlib

/-!
# Support-line bounds for planar diameter minimisers

If there are finitely many congruence classes of minimisers, a supporting line
meets each minimiser in sites at pairwise distances less than two. For diameter
greater than two the squared distance is at most four minus the squared
reciprocal diameter.

The proof first uses one-site replacements to show that the feasible region is
covered by unit disks, even with one site omitted. On a supporting segment of
length at least two, this covering forces a blocker closer to the line than a
shallowest blocker. For the quantitative bound, a point just outside the
midpoint of the segment lies within the diameter constraint. Two sites covering
this point would be less than one unit apart.
-/

namespace OMA.SupportBoundsProof

namespace Replacements

open EuclideanGeometry Filter Finset Erdos103 InnerProductSpace
open scoped Classical ENNReal Topology

/-- Strictly opening every constraint incident to p produces a minimiser with a free point. -/
private theorem replacement_optimal {n : ℕ} {A : Finset ℝ²} {p z : ℝ²}
    (hA : IsMinimiser n A) (hp : p ∈ A)
    (hDistances : ∀ q ∈ A.erase p, 1 < dist z q ∧ dist z q < Metric.diam (A : Set ℝ²)) :
    IsMinimiser n (insert z (A.erase p)) := by
  classical
  let C := A.erase p
  have hzC : z ∉ C := by
    intro hz
    have h := (hDistances z hz).1
    rw [dist_self] at h
    linarith
  have old {x : ℝ²} (hx : x ∈ C) : x ∈ A := mem_of_mem_erase hx
  let B := insert z C
  have hSep : B ∈ separatedSets n := by
    refine ⟨?_, ?_⟩
    · change (insert z (A.erase p)).card = n
      rw [card_insert_of_notMem hzC, card_erase_add_one hp, hA.1.1]
    · intro x hx y hy hxy
      change x ∈ B at hx
      change y ∈ B at hy
      have sep (u : ℝ²) (hu : u ∈ C) : (1 : ℝ≥0∞) ≤ edist z u := by
        rw [edist_dist, ← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff dist_nonneg]
        exact (hDistances u hu).1.le
      rcases mem_insert.mp hx with ex | hx
      · subst x
        rcases mem_insert.mp hy with ey | hy
        · exact (hxy ey.symm).elim
        · exact sep y hy
      · rcases mem_insert.mp hy with ey | hy
        · subst y
          change (1 : ℝ≥0∞) ≤ edist x z
          rw [edist_comm]
          exact sep x hx
        · exact hA.1.2 (old hx) (old hy) hxy
  have hDiam : Metric.diam (B : Set ℝ²) ≤ Metric.diam (A : Set ℝ²) := by
    apply Metric.diam_le_of_forall_dist_le Metric.diam_nonneg
    intro x hx y hy
    change x ∈ B at hx
    change y ∈ B at hy
    rcases mem_insert.mp hx with ex | hx
    · subst x
      rcases mem_insert.mp hy with ey | hy
      · rw [ey, dist_self]
        exact Metric.diam_nonneg
      · exact (hDistances y hy).2.le
    · rcases mem_insert.mp hy with ey | hy
      · rw [ey, dist_comm]
        exact (hDistances x hx).2.le
      · exact Metric.dist_le_diam_of_mem A.finite_toSet.isBounded (old hx) (old hy)
  exact ⟨hSep, fun X hX => hDiam.trans (hA.2 hX)⟩

/-- The finite-family escape criterion gives infinitely many congruence classes
in the upstream definition of the counting function. -/
private theorem infinite_count_of_escape {n : ℕ}
    (escape : ∀ F : Finset (Finset ℝ²), ∃ B, IsMinimiser n B ∧ ∀ C ∈ F, ¬Congruent C B) :
    Erdos103.h n = ⊤ := by
  classical
  have symm {A B : Finset ℝ²} : Congruent A B → Congruent B A := by
    rintro ⟨e, he⟩
    refine ⟨e.symm, ?_⟩
    rw [← he, Set.image_image]
    simp
  have fam (k : ℕ) : ∃ F : Finset (Finset ℝ²), F.card = k ∧
      (∀ C ∈ F, IsMinimiser n C) ∧
      (∀ B ∈ F, ∀ C ∈ F, B ≠ C → ¬ Congruent B C) := by
    induction k with
    | zero => exact ⟨∅, by simp⟩
    | succ k ih =>
      obtain ⟨F,hk,hm,hn⟩ := ih
      obtain ⟨B,hB,hnew⟩ := escape F
      have hBF : B ∉ F := fun h => hnew B h ⟨IsometryEquiv.refl _, Set.image_id _⟩
      refine ⟨insert B F, by simp [hBF,hk], ?_, ?_⟩
      · intro C hC
        rcases mem_insert.mp hC with rfl | h
        · exact hB
        · exact hm C h
      · intro C hC D hD hne
        rcases mem_insert.mp hC with e | h
        · subst C
          rcases mem_insert.mp hD with e | hD
          · exact (hne e.symm).elim
          · exact fun h => hnew D hD (symm h)
        · rcases mem_insert.mp hD with e | hD
          · subst D
            exact hnew C h
          · exact hn C h D hD hne
  apply top_unique
  rw [← ENat.iSup_natCast]
  apply iSup_le
  intro k
  obtain ⟨F,hk,hm,hn⟩ := fam k
  rw [← hk]
  exact le_iSup_of_le F (le_iSup_of_le ⟨hm,hn⟩ le_rfl)

/-- A strictly feasible replacement can be moved through an interval of
distances to a retained site. That interval avoids any finite list of
distances, and hence any finite family of congruence classes. -/
private theorem infinite_of_strict_replacement {A : Finset ℝ²} {n : ℕ} {a z : ℝ²}
    (hA : IsMinimiser n A) (hn : 5 ≤ n) (ha : a ∈ A)
    (hlower : ∀ q ∈ A.erase a, 1 < dist z q)
    (hupper : ∀ q ∈ A.erase a, dist z q < Metric.diam (A : Set ℝ²)) : h n = ⊤ := by
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (show 0 < (A.erase a).card by
    rw [Finset.card_erase_of_mem ha, hA.1.1]
    omega)
  have hwPos : 0 < dist z w := zero_lt_one.trans (hlower w hw)
  let p (t : ℝ) := w + (1 + t) • (z - w)
  have hp0 : p 0 = z := by simp [p]
  have hd (q : ℝ²) : Continuous (fun t : ℝ => dist (p t) q) := by
    dsimp [p]
    fun_prop
  have near (q : ℝ²) (hq : q ∈ A.erase a) :
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        1 < dist (p t) q ∧ dist (p t) q < Metric.diam (A : Set ℝ²) := by
    have hzero : 1 < dist (p 0) q ∧ dist (p 0) q < Metric.diam (A : Set ℝ²) := by
      simpa only [hp0] using And.intro (hlower q hq) (hupper q hq)
    exact (((hd q).tendsto 0).eventually (Ioo_mem_nhds hzero.1 hzero.2)).filter_mono
      nhdsWithin_le_nhds
  have avoid (s : ℝ) : ∀ᶠ t in 𝓝[>] (0 : ℝ), dist (p t) w ≠ s := by
    by_cases hsw : dist z w = s
    · filter_upwards [self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ))] with t ht
      change 0 < t at ht
      have hdist : dist (p t) w = (1 + t) * dist z w := by
        rw [dist_eq_norm, show p t - w = (1 + t) • (z - w) by dsimp [p]; abel,
          norm_smul, Real.norm_of_nonneg (by linarith), ← dist_eq_norm]
      rw [← hsw, hdist]
      have := mul_pos ht hwPos
      nlinarith only [this]
    · have hzero : dist (p 0) w ≠ s := by simpa only [hp0] using hsw
      exact ((hd w).continuousAt.eventually_ne hzero).filter_mono nhdsWithin_le_nhds
  apply infinite_count_of_escape
  intro F
  let S := F.biUnion fun C => (C ×ˢ C).image fun e => dist e.1 e.2
  obtain ⟨t, ht, hS⟩ := (((A.erase a).eventually_all.2 near).and
    (S.eventually_all.2 fun s _ => avoid s)).exists
  let B := insert (p t) (A.erase a)
  refine ⟨B, replacement_optimal hA ha ht, ?_⟩
  rintro C hC ⟨e, he⟩
  have pre {x : ℝ²} (hx : x ∈ B) : ∃ y ∈ C, e y = x := by
    change x ∈ (B : Set ℝ²) at hx
    rwa [← he] at hx
  obtain ⟨x, hx, hxz⟩ := pre (mem_insert_self _ _)
  obtain ⟨y, hy, hyw⟩ := pre (mem_insert_of_mem hw)
  apply hS (dist x y)
  · exact mem_biUnion.mpr ⟨C, hC, mem_image.mpr ⟨(x, y), mem_product.mpr ⟨hx, hy⟩, rfl⟩⟩
  · rw [← hxz, ← hyw, e.isometry.dist_eq]

/-- At strict diameter slack, pushing in a direction that weakly opens every
unit contact makes all the inequalities for a replacement strict. -/
private theorem infinite_of_outward_replacement {A : Finset ℝ²} {n : ℕ} {a z u : ℝ²}
    (hA : IsMinimiser n A) (hn : 5 ≤ n) (ha : a ∈ A) (hu : ‖u‖ = 1)
    (hlower : ∀ q ∈ A.erase a, 1 ≤ dist z q)
    (hside : ∀ q ∈ A.erase a, dist z q = 1 → 0 ≤ inner ℝ (z - q) u)
    (hupper : ∀ q ∈ A.erase a, dist z q < Metric.diam (A : Set ℝ²)) : h n = ⊤ := by
  let p (t : ℝ) := z + t • u
  have near (q : ℝ²) (hq : q ∈ A.erase a) :
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        1 < dist (p t) q ∧ dist (p t) q < Metric.diam (A : Set ℝ²) := by
    have hc : Continuous (fun t : ℝ => dist (p t) q) := by dsimp [p]; fun_prop
    have htop : dist (p 0) q < Metric.diam (A : Set ℝ²) := by simpa [p] using hupper q hq
    refine Filter.Eventually.and ?_ (((hc.tendsto 0).eventually (Iio_mem_nhds htop)).filter_mono
      nhdsWithin_le_nhds)
    by_cases hUnit : dist z q = 1
    · filter_upwards [self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ))] with t ht
      change 0 < t at ht
      apply (sq_lt_sq₀ zero_le_one dist_nonneg).1
      have hform : dist (p t) q ^ 2 = dist z q ^ 2 + 2 * t * inner ℝ (z - q) u + t ^ 2 := by
        rw [dist_eq_norm, dist_eq_norm, show p t - q = (z - q) + t • u by dsimp [p]; abel,
          norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, hu,
          mul_one, sq_abs]
        ring
      rw [hform, hUnit]
      nlinarith only [mul_nonneg ht.le (hside q hq hUnit), sq_pos_of_pos ht]
    · have hstrict : 1 < dist (p 0) q := by
        simpa [p] using lt_of_le_of_ne (hlower q hq) (Ne.symm hUnit)
      exact ((hc.tendsto 0).eventually (Ioi_mem_nhds hstrict)).filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ht⟩ := ((A.erase a).eventually_all.2 near).exists
  exact infinite_of_strict_replacement hA hn ha (fun q hq => (ht q hq).1) (fun q hq => (ht q hq).2)

/-- Replacing one site by a point beyond unit distance of every retained site
forces infinitely many optimal congruence classes, even with weak diameter bounds. -/
private theorem infinite_of_clear_replacement {A : Finset ℝ²} {n : ℕ} {a z : ℝ²}
    (hA : IsMinimiser n A) (hn : 5 ≤ n) (ha : a ∈ A)
    (hlower : ∀ q ∈ A.erase a, 1 < dist z q)
    (hupper : ∀ q ∈ A.erase a, dist z q ≤ Metric.diam (A : Set ℝ²)) : h n = ⊤ := by
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (show 0 < (A.erase a).card by
    rw [Finset.card_erase_of_mem ha, hA.1.1]
    omega)
  have hzw : z ≠ w := by
    intro he
    have hd := hlower w hw
    norm_num [he, dist_self] at hd
  let p (t : ℝ) := AffineMap.lineMap z w t
  have hnear (q : ℝ²) (hq : q ∈ A.erase a) :
      ∀ᶠ t in 𝓝[>] (0 : ℝ), 1 < dist (p t) q := by
    have hc : Continuous (fun t : ℝ => dist (p t) q) := by
      simp only [p, AffineMap.lineMap_apply_module]
      fun_prop
    have hzero : 1 < dist (p 0) q := by simpa [p] using hlower q hq
    exact ((hc.tendsto 0).eventually (Ioi_mem_nhds hzero)).filter_mono nhdsWithin_le_nhds
  have htime : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t < 1 := by
    have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ), t < 1 := Iio_mem_nhds (by norm_num)
    filter_upwards [self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)),
      hsmall.filter_mono nhdsWithin_le_nhds] with t ht ht'
    exact ⟨ht, ht'⟩
  obtain ⟨t, ht, hdist⟩ := (htime.and ((A.erase a).eventually_all.2 hnear)).exists
  have hstrict (q : ℝ²) (hq : q ∈ A.erase a) : dist (p t) q < Metric.diam (A : Set ℝ²) := by
    have hzBall := Metric.mem_closedBall.mpr (hupper q hq)
    have hwBall := Metric.mem_closedBall.mpr (Metric.dist_le_diam_of_mem A.finite_toSet.isBounded
      (mem_of_mem_erase hw) (mem_of_mem_erase hq))
    exact Metric.mem_ball.mp (openSegment_subset_ball_of_ne hzBall hwBall hzw
      (lineMap_mem_openSegment ℝ z w ht))
  exact infinite_of_strict_replacement hA hn ha hdist hstrict

/-- The closed diameter-ball intersection of the retained sites is covered by
their closed unit balls, after any one site is erased. -/
private theorem unit_cover_after_erase {A : Finset ℝ²} {n : ℕ} {a z : ℝ²}
    (hA : IsMinimiser n A) (hn : 5 ≤ n) (hfin : h n ≠ ⊤) (ha : a ∈ A)
    (hupper : ∀ q ∈ A.erase a, dist z q ≤ Metric.diam (A : Set ℝ²)) :
    ∃ q ∈ A.erase a, dist z q ≤ 1 := by
  by_contra hcover
  exact hfin (infinite_of_clear_replacement hA hn ha
    (fun q hq => lt_of_not_ge fun hd => hcover ⟨q, hq, hd⟩) hupper)

/-- Every point in the closed diameter-ball intersection of a minimiser lies
in the closed unit balls of two distinct sites, including when it is a site. -/
private theorem two_unit_cover {A : Finset ℝ²} {n : ℕ} {z : ℝ²}
    (hA : IsMinimiser n A) (hn : 5 ≤ n) (hfin : h n ≠ ⊤)
    (hupper : ∀ q ∈ A, dist z q ≤ Metric.diam (A : Set ℝ²)) :
    ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ dist z a ≤ 1 ∧ dist z b ≤ 1 := by
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < A.card by rw [hA.1.1]; omega)
  obtain ⟨a, ha, hza⟩ := unit_cover_after_erase hA hn hfin hp
    (fun q hq => hupper q (mem_of_mem_erase hq))
  obtain ⟨b, hb, hzb⟩ := unit_cover_after_erase hA hn hfin (mem_of_mem_erase ha)
    (fun q hq => hupper q (mem_of_mem_erase hq))
  exact ⟨a, mem_of_mem_erase ha, b, mem_of_mem_erase hb, (mem_erase.mp hb).1.symm, hza, hzb⟩

/-- A site strictly between two other sites has diameter slack. If it is a
projection maximum among its unit neighbours, it can move outward. -/
private theorem infinite_of_blocked_between {A : Finset ℝ²} {n : ℕ} (hA : IsMinimiser n A)
    (hn : 5 ≤ n) {p a b v : ℝ²} (hp : p ∈ A) (ha : a ∈ A) (hb : b ∈ A)
    (hab : a ≠ b) (hbetween : p ∈ openSegment ℝ a b) (hv : ‖v‖ = 1)
    (hmax : ∀ y ∈ A, dist p y = 1 → inner ℝ y v ≤ inner ℝ p v) : h n = ⊤ := by
  apply infinite_of_outward_replacement hA hn hp hv
  · intro q hq
    have hl := hA.1.2 hp (mem_of_mem_erase hq) (mem_erase.mp hq).1.symm
    change (1 : ℝ≥0∞) ≤ edist p q at hl
    rwa [edist_dist, ← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff dist_nonneg] at hl
  · intro q hq hUnit
    rw [inner_sub_left]
    exact sub_nonneg.mpr (hmax q (mem_of_mem_erase hq) hUnit)
  · intro q hq
    have hbound (z : ℝ²) (hz : z ∈ A) : z ∈ Metric.closedBall q (Metric.diam (A : Set ℝ²)) :=
      Metric.mem_closedBall.mpr
        (Metric.dist_le_diam_of_mem A.finite_toSet.isBounded hz (mem_of_mem_erase hq))
    exact Metric.mem_ball.mp (openSegment_subset_ball_of_ne (hbound a ha) (hbound b hb)
      hab hbetween)

/-- Above a supporting line all distances grow. If a point on the line has
strict diameter slack, its open unit disk contains a retained site after any
one site is erased. -/
private theorem strictly_covered_after_erase {n : ℕ} {A : Finset ℝ²} (hA : IsMinimiser n A)
    (hn : 5 ≤ n) (hfin : h n ≠ ⊤) {a z u : ℝ²} (ha : a ∈ A) (hu : ‖u‖ = 1)
    (hs : ∀ q ∈ A, inner ℝ q u ≤ inner ℝ z u)
    (hd : ∀ q ∈ A, dist z q < Metric.diam (A : Set ℝ²)) :
    ∃ q ∈ A.erase a, dist z q < 1 := by
  by_contra! hNoCover
  apply hfin (infinite_of_outward_replacement hA hn ha hu hNoCover ?_ ?_)
  · intro q hq _
    rw [inner_sub_left]
    exact sub_nonneg.mpr (hs q (mem_of_mem_erase hq))
  · exact fun q hq => hd q (mem_of_mem_erase hq)

end Replacements

namespace SupportFrame

open EuclideanGeometry InnerProductSpace Erdos103

/-- Centre the horizontal coordinate at the segment midpoint and measure depth
along the inward normal. -/
private theorem coordinates (a b u : ℝ²) (hne : a ≠ b) (hu : ‖u‖ = 1)
    (hline : inner ℝ b u = inner ℝ a u) :
    ∃ (x d : ℝ² → ℝ) (z : ℝ → ℝ²),
      (∀ p q, dist p q ^ 2 = (x p - x q) ^ 2 + (d p - d q) ^ 2) ∧
      (∀ p, d p = inner ℝ a u - inner ℝ p u) ∧
      (∀ t, x (z t) = t ∧ d (z t) = 0) ∧
      (∀ t, |t| < dist a b / 2 → z t ∈ openSegment ℝ a b) := by
  let L := dist a b
  have hL : 0 < L := dist_pos.mpr hne
  let e := L⁻¹ • (b - a)
  have he : ‖e‖ = 1 := by
    dsimp [e]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hL.le), ← dist_eq_norm,
      dist_comm b a]
    exact inv_mul_cancel₀ hL.ne'
  have heu : inner ℝ e u = 0 := by
    dsimp [e]
    rw [real_inner_smul_left, inner_sub_left, hline, sub_self, mul_zero]
  let v : Fin 2 → ℝ² := ![e, u]
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    have hue : inner ℝ u e = 0 := (real_inner_comm e u).trans heu
    intro i
    fin_cases i <;> intro j <;> fin_cases j <;>
      simp [v, he, hu, heu, hue]
  have hcard : Fintype.card (Fin 2) = Module.finrank ℝ ℝ² := by simp
  let B := basisOfOrthonormalOfCardEqFinrank hv hcard
  have hB : (B : Fin 2 → ℝ²) = v := coe_basisOfOrthonormalOfCardEqFinrank hv hcard
  let E := B.toOrthonormalBasis (hB ▸ hv)
  have hE : (E : Fin 2 → ℝ²) = v :=
    (Module.Basis.coe_toOrthonormalBasis _ _).trans hB
  let m := a + (1 / 2 : ℝ) • (b - a)
  let x := fun p : ℝ² => inner ℝ (p - m) e
  let d := fun p : ℝ² => inner ℝ a u - inner ℝ p u
  let z := fun t : ℝ => m + t • e
  refine ⟨x, d, z, ?_, fun _ => rfl, ?_, ?_⟩
  · intro p q
    have hnorm := E.sum_sq_inner_left (p - q)
    rw [hE, Fin.sum_univ_two] at hnorm
    dsimp [v] at hnorm
    dsimp [x, d]
    rw [dist_eq_norm, ← hnorm]
    simp only [inner_sub_left]
    ring
  · intro t
    constructor
    · dsimp [x, z]
      rw [add_comm m, add_sub_cancel_right, real_inner_smul_left,
        real_inner_self_eq_norm_sq, he]
      ring
    · have hm : inner ℝ m u = inner ℝ a u := by
        dsimp [m]
        rw [inner_add_left, real_inner_smul_left, inner_sub_left, hline]
        ring
      dsimp [d, z]
      rw [inner_add_left, hm, real_inner_smul_left, heu]
      ring
  · intro t ht
    have hparam : 1 / 2 + t / L ∈ Set.Ioo (0 : ℝ) 1 := by
      change |t| < L / 2 at ht
      rcases abs_lt.mp ht with ⟨hlo, hhi⟩
      constructor
      · linarith [(lt_div_iff₀ hL).mpr (show -(1 / 2 : ℝ) * L < t by linarith)]
      · linarith [(div_lt_iff₀ hL).mpr (show t < (1 / 2 : ℝ) * L by linarith)]
    have hz : z t = AffineMap.lineMap a b (1 / 2 + t / L) := by
      dsimp [z, m, e]
      rw [AffineMap.lineMap_apply_module', smul_smul, add_smul, div_eq_mul_inv]
      abel
    rw [hz]
    exact lineMap_mem_openSegment ℝ a b hparam

end SupportFrame

namespace UnitIntervals

private theorem strictConcaveOn_unitSemicircle :
    StrictConcaveOn ℝ (Set.Icc (-1) 1) (fun x => Real.sqrt (1 - x ^ 2)) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  let X := Real.sqrt (1 - x ^ 2)
  let Y := Real.sqrt (1 - y ^ 2)
  change a * X + b * Y < Real.sqrt (1 - (a * x + b * y) ^ 2)
  have on_semicircle (z : ℝ) (hz : z ∈ Set.Icc (-1) 1) :
      Real.sqrt (1 - z ^ 2) ^ 2 + z ^ 2 = 1 := by
    have hleft : 0 ≤ 1 - z := sub_nonneg.mpr hz.2
    have hright : 0 ≤ 1 + z := by linarith [hz.1]
    rw [Real.sq_sqrt (by nlinarith [mul_nonneg hleft hright])]
    ring
  have hX : X ^ 2 + x ^ 2 = 1 := on_semicircle x hx
  have hY : Y ^ 2 + y ^ 2 = 1 := on_semicircle y hy
  -- The convex combination of two distinct unit vectors has norm strictly below one.
  have hmix : (a * X + b * Y) ^ 2 + (a * x + b * y) ^ 2 +
      a * b * ((X - Y) ^ 2 + (x - y) ^ 2) = 1 := by
    linear_combination (a * (a + b)) * hX + (b * (a + b)) * hY + (a + b + 1) * hab
  have hdeficit : 0 < a * b * ((X - Y) ^ 2 + (x - y) ^ 2) :=
    mul_pos (mul_pos ha hb) (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero
      (sub_ne_zero.mpr hxy)))
  exact Real.lt_sqrt_of_sq_lt (by linarith only [hmix, hdeficit])

/-- If shifting both abscissae left by `d` does not increase their combined
semicircle height, their sum is at most `d`. -/
private theorem sum_le_of_semicircle_le {d e f : ℝ} (hd : 0 < d)
    (he : e ∈ Set.Icc (-1) 1) (hf : f ∈ Set.Icc (-1) 1)
    (h : Real.sqrt (1 - (d - e) ^ 2) + Real.sqrt (1 - (d - f) ^ 2) ≤
      Real.sqrt (1 - e ^ 2) + Real.sqrt (1 - f ^ 2)) : e + f ≤ d := by
  by_contra! hsum
  have hpositive : 0 < e + f := hd.trans hsum
  let t := d / (e + f)
  have ht₀ : 0 < t := div_pos hd hpositive
  have ht₁ : t < 1 := (div_lt_one hpositive).2 hsum
  have hmul : t * (e + f) = d := div_mul_cancel₀ _ hpositive.ne'
  have hnege : -e ∈ Set.Icc (-1) 1 := ⟨by linarith [he.2], by linarith [he.1]⟩
  have hnegf : -f ∈ Set.Icc (-1) 1 := ⟨by linarith [hf.2], by linarith [hf.1]⟩
  have hex : e ≠ -f := by intro h'; linarith
  have hfx : f ≠ -e := by intro h'; linarith
  have ht' : 0 < 1 - t := sub_pos.mpr ht₁
  have htadd : 1 - t + t = 1 := sub_add_cancel _ _
  -- The shifted pair is a strict convex combination of `(e, f)` and `(-f, -e)`.
  have hleft := strictConcaveOn_unitSemicircle.2 he hnegf hex ht' ht₀ htadd
  have hright := strictConcaveOn_unitSemicircle.2 hf hnege hfx ht' ht₀ htadd
  have hx : (1 - t) * e + t * -f = e - d := by linear_combination -hmul
  have hy : (1 - t) * f + t * -e = f - d := by linear_combination -hmul
  simp only [smul_eq_mul, neg_sq, hx, hy, show (e - d) ^ 2 = (d - e) ^ 2 by ring,
    show (f - d) ^ 2 = (d - f) ^ 2 by ring] at hleft hright
  linarith only [h, hleft, hright]

private theorem blocker_right_of_shift {t u d e δ : ℝ} (hd : 0 < d) (he : 0 ≤ e)
    (hshift : 0 < δ) (hgeometry : (1 - δ)^2 + d^2 ≤ 1)
    (hstrict : (1 - δ)^2 + d^2 < 1 ∨ (t + δ - u)^2 + e^2 < 1)
    (hsep : 1 ≤ (t - u)^2 + (d - e)^2)
    (hcover : (t + δ - u)^2 + e^2 ≤ 1) : t < u := by
  by_contra! hwrong
  have hx : 0 ≤ t - u := sub_nonneg.mpr hwrong
  have hxshift : 0 ≤ t + δ - u := by linarith only [hx, hshift]
  have hxgrowth : (t - u)^2 < (t + δ - u)^2 :=
    (sq_lt_sq₀ hx hxshift).2 (by linarith only [hshift])
  have hshallow : e < d := by
    by_contra! hdeep
    have hvert : (e - d)^2 ≤ e^2 :=
      (sq_le_sq₀ (sub_nonneg.mpr hdeep) he).2 (sub_le_self _ hd.le)
    nlinarith only [hsep, hcover, hxgrowth, hvert]
  have hdepth : (d - e)^2 ≤ d^2 :=
    pow_le_pow_left₀ (sub_nonneg.mpr hshallow.le) (by linarith only [he]) 2
  rcases hstrict with hgeometry' | hraised
  · have hxbound : t + δ - u ≤ 1 :=
      (sq_le_sq₀ hxshift zero_le_one).1 (by nlinarith only [hcover, sq_nonneg e])
    have hxcap : (t - u)^2 ≤ (1 - δ)^2 :=
      pow_le_pow_left₀ hx (by linarith only [hxbound]) 2
    linarith only [hsep, hxcap, hdepth, hgeometry']
  · have hxbound : t + δ - u < 1 :=
      (sq_lt_sq₀ hxshift zero_le_one).1 (by nlinarith only [hraised, sq_nonneg e])
    have hxcap : (t - u)^2 < (1 - δ)^2 :=
      pow_lt_pow_left₀ (by linarith only [hxbound]) hx two_ne_zero
    linarith only [hsep, hxcap, hdepth, hgeometry]

/-- At offset `1 - √(1 - d²)`, strict unit-ball coverage forces the blocker
to lie to the right of `p`. -/
private theorem blocker_right_of_sharp_step {t u d e : ℝ} (hd : 0 < d) (hdmax : d < 1)
    (he : 0 ≤ e) (hsep : 1 ≤ (t - u)^2 + (d - e)^2)
    (hcover : (t + (1 - Real.sqrt (1 - d^2)) - u)^2 + e^2 < 1) : t < u := by
  have hdsq : d^2 < 1 := by
    simpa using (sq_lt_sq₀ hd.le (zero_le_one : (0 : ℝ) ≤ 1)).2 hdmax
  have hradicand : 0 ≤ 1 - d^2 := sub_nonneg.mpr hdsq.le
  have hshift : 0 < 1 - Real.sqrt (1 - d^2) := by
    rw [sub_pos]
    exact (Real.sqrt_lt hradicand zero_le_one).2 (by nlinarith only [sq_pos_of_pos hd])
  have hgeometry : (1 - (1 - Real.sqrt (1 - d^2)))^2 + d^2 ≤ 1 := by
    rw [sub_sub_cancel, Real.sq_sqrt hradicand]
    linarith
  exact blocker_right_of_shift hd he hshift hgeometry (Or.inr hcover) hsep hcover.le

/-- Reflection gives the sharp leftward bound. -/
private theorem blocker_left_of_sharp_step {t u d e : ℝ} (hd : 0 < d) (hdmax : d < 1)
    (he : 0 ≤ e) (hsep : 1 ≤ (t - u)^2 + (d - e)^2)
    (hcover : (t - (1 - Real.sqrt (1 - d^2)) - u)^2 + e^2 < 1) : u < t := by
  have hright := blocker_right_of_sharp_step (t := -t) (u := -u) hd hdmax he
    (by nlinarith only [hsep]) (by nlinarith only [hcover])
  linarith only [hright]

private noncomputable def radius (d : ℝ) : ℝ := Real.sqrt (1 - d ^ 2)

/-- The distance from the interval centre to either test point. -/
private noncomputable def offset (d : ℝ) : ℝ := 1 - Real.sqrt (1 - d ^ 2)

private theorem covers_iff {s t d : ℝ} :
    (s - t) ^ 2 + d ^ 2 < 1 ↔ t - radius d < s ∧ s < t + radius d := by
  have h : (s - t) ^ 2 + d ^ 2 < 1 ↔ |s - t| < radius d := by
    rw [radius, Real.lt_sqrt (abs_nonneg _), sq_abs]
    constructor <;> intro h <;> linarith only [h]
  rw [h, abs_lt]
  constructor <;> intro hs <;> constructor <;> linarith only [hs.1, hs.2]

private theorem depth_lt_one {a d : ℝ} (h : a ^ 2 + d ^ 2 < 1) : d < 1 := by
  nlinarith only [h, sq_nonneg a, sq_nonneg (d - 1)]

/-- Both test points and their interval belong to the open unit interval if the
chosen disk covers zero strictly. -/
private theorem test_interval_subset {t d : ℝ} (hp : t ^ 2 + d ^ 2 < 1) :
    Set.Icc (t - offset d) (t + offset d) ⊆ Set.Ioo (-1) 1 := by
  have hzero := (covers_iff (s := 0) (t := t) (d := d)).mp
    (by simpa only [zero_sub, neg_sq] using hp)
  intro s hs
  change t - offset d ≤ s ∧ s ≤ t + offset d at hs
  change -1 < s ∧ s < 1
  unfold offset at hs
  unfold radius at hzero
  constructor <;> linarith only [hs.1, hs.2, hzero.1, hzero.2]

/-- Two overlapping disks on opposite sides of a disk covering zero force a
shallower disk to cover zero too. -/
private theorem shallower_of_overlap {t d u e v f z : ℝ} (hd : 0 < d) (he : 0 ≤ e) (hf : 0 ≤ f)
    (hleft : u < t) (hright : t < v) (hp : t ^ 2 + d ^ 2 < 1)
    (hsepq : 1 ≤ (u - t) ^ 2 + (e - d) ^ 2)
    (hsepr : 1 ≤ (v - t) ^ 2 + (f - d) ^ 2)
    (hq : (z - u) ^ 2 + e ^ 2 < 1) (hr : (z - v) ^ 2 + f ^ 2 < 1) :
    (e < d ∧ u ^ 2 + e ^ 2 < 1) ∨ (f < d ∧ v ^ 2 + f ^ 2 < 1) := by
  have hqz := covers_iff.mp hq
  have hrz := covers_iff.mp hr
  have hpz := (covers_iff (s := 0) (t := t) (d := d)).mp
    (by simpa only [zero_sub, neg_sq] using hp)
  have hlowq : radius (d - e) ≤ t - u := Real.sqrt_le_iff.mpr
    ⟨by linarith only [hleft], by nlinarith only [hsepq]⟩
  have hlowr : radius (d - f) ≤ v - t := Real.sqrt_le_iff.mpr
    ⟨by linarith only [hright], by nlinarith only [hsepr]⟩
  have hgap : radius (d - e) + radius (d - f) < radius e + radius f := by
    linarith only [hlowq, hlowr, hqz.2, hrz.1]
  have hsum := sum_le_of_semicircle_le hd
    (show e ∈ Set.Icc (-1) 1 from ⟨by linarith only [he], (depth_lt_one hq).le⟩)
    (show f ∈ Set.Icc (-1) 1 from ⟨by linarith only [hf], (depth_lt_one hr).le⟩) hgap.le
  have hlt : e + f < d := by
    apply lt_of_le_of_ne hsum
    intro heq
    have hde : d - e = f := by linarith only [heq]
    have hdf : d - f = e := by linarith only [heq]
    rw [hde, hdf, add_comm (radius f) (radius e)] at hgap
    exact (lt_irrefl _) hgap
  have hle : e < d := by linarith only [hlt, hf]
  have hlf : f < d := by linarith only [hlt, he]
  have wider {a : ℝ} (ha : 0 ≤ a) (had : a < d) : radius d < radius a := by
    apply Real.sqrt_lt_sqrt
    · linarith only [hp, sq_nonneg t]
    · have hprod := mul_pos (sub_pos.mpr had) (show 0 < d + a by linarith only [ha, hd])
      nlinarith only [hprod]
  -- One of the two intervals contains zero, according to the sign of the overlap point.
  by_cases hz : z ≤ 0
  · right
    refine ⟨hlf, ?_⟩
    simpa only [zero_sub, neg_sq] using (covers_iff (s := 0) (t := v) (d := f)).mpr
      ⟨by linarith only [hrz.1, hz], by linarith only [hpz.2, hright, wider hf hlf]⟩
  · left
    refine ⟨hle, ?_⟩
    simpa only [zero_sub, neg_sq] using (covers_iff (s := 0) (t := u) (d := e)).mpr
      ⟨by linarith only [hpz.1, hleft, wider he hle], by linarith only [hqz.2, le_of_not_ge hz]⟩

/-- A disk of minimum depth `d > 0` among those strictly covering zero cannot have
its whole test interval strictly covered by other disks separated from it. -/
private theorem no_cover_at_min_depth {ι : Type*} (A : Finset ι) (x depth : ι → ℝ) {p : ι}
    (hp : p ∈ A) (hdepth : ∀ i ∈ A, 0 ≤ depth i) (hpdepth : 0 < depth p)
    (hsep : ∀ i ∈ A, i ≠ p → 1 ≤ (x i - x p) ^ 2 + (depth i - depth p) ^ 2)
    (hmin : ∀ i ∈ A, (x i) ^ 2 + (depth i) ^ 2 < 1 → depth p ≤ depth i)
    (hcenter : (x p) ^ 2 + (depth p) ^ 2 < 1)
    (hcover : ∀ s ∈ Set.Icc (x p - offset (depth p)) (x p + offset (depth p)),
      ∃ i ∈ A, i ≠ p ∧ (s - x i) ^ 2 + (depth i) ^ 2 < 1) : False := by
  let lo := x p - offset (depth p)
  let hi := x p + offset (depth p)
  let cov (i : ι) : Set ℝ := {s | (s - x i) ^ 2 + (depth i) ^ 2 < 1}
  let L := ⋃ (i : ι) (_ : i ∈ A ∧ x i < x p), cov i
  let R := ⋃ (i : ι) (_ : i ∈ A ∧ x p < x i), cov i
  have hp_lt_one := depth_lt_one hcenter
  have horder : lo ≤ hi := by
    have hoff : 0 ≤ offset (depth p) := by
      exact sub_nonneg.mpr (Real.sqrt_le_iff.mpr ⟨zero_le_one, by nlinarith [sq_nonneg (depth p)]⟩)
    dsimp [lo, hi]
    linarith only [hoff]
  have hopen (i : ι) : IsOpen (cov i) := by
    convert isOpen_Ioo (a := x i - radius (depth i)) (b := x i + radius (depth i)) using 1
    ext s
    exact covers_iff
  have hL : IsOpen L := isOpen_iUnion fun i => isOpen_iUnion fun _ => hopen i
  have hR : IsOpen R := isOpen_iUnion fun i => isOpen_iUnion fun _ => hopen i
  have hcover' : Set.Icc lo hi ⊆ L ∪ R := by
    intro s hs
    obtain ⟨i, hiA, hip, hcov⟩ := hcover s hs
    rcases lt_trichotomy (x i) (x p) with hleft | heq | hright
    · exact Or.inl (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨⟨hiA, hleft⟩, hcov⟩⟩)
    · have hi_lt_one := depth_lt_one hcov
      have hdiff := (abs_lt).2 (show -1 < depth i - depth p ∧ depth i - depth p < 1 by
        constructor <;> linarith only [hp_lt_one, hi_lt_one, hdepth i hiA, hdepth p hp])
      have hsq := (sq_lt_sq₀ (abs_nonneg _) (zero_le_one : (0 : ℝ) ≤ 1)).2 hdiff
      have hi_sep := hsep i hiA hip
      rw [heq, sub_self, zero_pow two_ne_zero, zero_add] at hi_sep
      rw [sq_abs, one_pow] at hsq
      exact False.elim ((not_lt_of_ge hi_sep) hsq)
    · exact Or.inr (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨⟨hiA, hright⟩, hcov⟩⟩)
  have hLmeet : (Set.Icc lo hi ∩ L).Nonempty := by
    have hlo := Set.left_mem_Icc.mpr horder
    obtain ⟨i, hiA, hip, hcov⟩ := hcover lo hlo
    have hli := blocker_left_of_sharp_step (t := x p) (u := x i)
      hpdepth hp_lt_one (hdepth i hiA)
      (by nlinarith only [hsep i hiA hip]) (by simpa only [lo, offset] using hcov)
    exact ⟨lo, hlo, Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨⟨hiA, hli⟩, hcov⟩⟩⟩
  have hRmeet : (Set.Icc lo hi ∩ R).Nonempty := by
    have hhi := Set.right_mem_Icc.mpr horder
    obtain ⟨i, hiA, hip, hcov⟩ := hcover hi hhi
    have hri := blocker_right_of_sharp_step (t := x p) (u := x i)
      hpdepth hp_lt_one (hdepth i hiA)
      (by nlinarith only [hsep i hiA hip]) (by simpa only [hi, offset] using hcov)
    exact ⟨hi, hhi, Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨⟨hiA, hri⟩, hcov⟩⟩⟩
  -- A connected interval covered by the two open unions meets their intersection.
  obtain ⟨z, _, hzL, hzR⟩ := isPreconnected_Icc L R hL hR hcover' hLmeet hRmeet
  obtain ⟨q, ⟨hq, hqleft⟩, hqcov⟩ := Set.mem_iUnion.1 (show z ∈ L from hzL) |>.imp
    (fun _ h => Set.mem_iUnion.1 h)
  obtain ⟨r, ⟨hr, hrright⟩, hrcov⟩ := Set.mem_iUnion.1 (show z ∈ R from hzR) |>.imp
    (fun _ h => Set.mem_iUnion.1 h)
  have hqp : q ≠ p := fun heq => (lt_irrefl (x p)) (heq ▸ hqleft)
  have hrp : r ≠ p := fun heq => (lt_irrefl (x p)) (heq ▸ hrright)
  rcases shallower_of_overlap hpdepth (hdepth q hq) (hdepth r hr) hqleft hrright hcenter
    (hsep q hq hqp) (hsep r hr hrp) hqcov hrcov with ⟨hqlt, hq0⟩ | ⟨hrlt, hr0⟩
  · exact (not_lt_of_ge (hmin q hq hq0)) hqlt
  · exact (not_lt_of_ge (hmin r hr hr0)) hrlt

end UnitIntervals

namespace SupportingSegments

open EuclideanGeometry Finset Erdos103 InnerProductSpace
open scoped Classical ENNReal

/-- Every pair of sites on a common supporting line is strictly less than two units
apart in a minimiser having only finitely many optimal congruence classes. -/
private theorem dist_lt_two_on_support {n : ℕ} {A : Finset ℝ²} (hA : IsMinimiser n A)
    (hn : 5 ≤ n) (hfin : h n ≠ ⊤) {a b u : ℝ²} (ha : a ∈ A) (hb : b ∈ A)
    (hu : ‖u‖ = 1) (hs : ∀ q ∈ A, inner ℝ q u ≤ inner ℝ a u)
    (hl : inner ℝ b u = inner ℝ a u) : dist a b < 2 := by
  by_contra! hlong
  have hab : a ≠ b := by rintro rfl; norm_num at hlong
  obtain ⟨x, d, z, heuc, hdepth, haxis, hseg⟩ :=
    SupportFrame.coordinates a b u hab hu hl
  have hnonneg (q : ℝ²) (hq : q ∈ A) : 0 ≤ d q := by
    rw [hdepth]
    exact sub_nonneg.mpr (hs q hq)
  have axis_cover (t : ℝ) (ht : |t| < 1) (p : ℝ²) (hp : p ∈ A) :
      ∃ q ∈ A, q ≠ p ∧ (t - x q)^2 + (d q)^2 < 1 := by
    have hseg' := hseg t (by linarith)
    have hz : inner ℝ (z t) u = inner ℝ a u := by
      linarith [(haxis t).2, hdepth (z t)]
    have hball (q : ℝ²) (hq : q ∈ A) : dist (z t) q < Metric.diam (A : Set ℝ²) := by
      have bound (r : ℝ²) (hr : r ∈ A) : r ∈ Metric.closedBall q (Metric.diam (A : Set ℝ²)) :=
        Metric.mem_closedBall.mpr (Metric.dist_le_diam_of_mem A.finite_toSet.isBounded hr hq)
      exact Metric.mem_ball.mp (openSegment_subset_ball_of_ne (bound a ha) (bound b hb) hab hseg')
    obtain ⟨q,hq,hd⟩ := Replacements.strictly_covered_after_erase hA hn hfin hp hu
      (fun r hr => hz.symm ▸ hs r hr) hball
    refine ⟨q,mem_of_mem_erase hq,(mem_erase.mp hq).1,?_⟩
    simpa only [heuc, (haxis t).1, (haxis t).2, zero_sub, neg_sq, one_pow] using
      (pow_lt_pow_left₀ hd dist_nonneg (by decide : (2 : ℕ) ≠ 0))
  let S := A.filter (fun q => (x q)^2 + (d q)^2 < 1)
  have hS : S.Nonempty := by
    obtain ⟨q,hq,_,h⟩ := axis_cover 0 (by norm_num) a ha
    exact ⟨q, mem_filter.mpr ⟨hq,by simpa using h⟩⟩
  obtain ⟨p,hpS,hmin⟩ := S.exists_min_image d hS
  obtain ⟨hp,hcenter⟩ := mem_filter.mp hpS
  have hpos : 0 < d p := by
    refine lt_of_le_of_ne (hnonneg p hp) ?_
    intro he
    have hpz : z (x p) = p := by
      apply dist_eq_zero.mp
      have hdist := heuc (z (x p)) p
      rw [(haxis _).1, (haxis _).2, ← he] at hdist
      simpa using hdist
    have hx : |x p| < 1 := abs_lt.mpr ⟨by nlinarith [sq_nonneg (x p + 1), sq_nonneg (d p)],
      by nlinarith [sq_nonneg (x p - 1), sq_nonneg (d p)]⟩
    have hbet := hseg (x p) (by linarith)
    rw [hpz] at hbet
    apply hfin
    apply Replacements.infinite_of_blocked_between hA hn hp ha hb hab hbet hu
    intro y hy _
    have := hdepth p
    linarith [hs y hy]
  have hsep (i : ℝ²) (hi : i ∈ A) (hip : i ≠ p) :
      1 ≤ (x i - x p)^2 + (d i - d p)^2 := by
    have h := hA.1.2 hi hp hip
    change (1 : ℝ≥0∞) ≤ edist i p at h
    rw [edist_dist, ← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff dist_nonneg] at h
    simpa only [one_pow, heuc] using (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) h 2)
  apply UnitIntervals.no_cover_at_min_depth A x d hp hnonneg hpos hsep
    (fun i hi h => hmin i (mem_filter.mpr ⟨hi,h⟩)) hcenter
  intro s hs'
  have hin := UnitIntervals.test_interval_subset hcenter hs'
  exact axis_cover s (abs_lt.mpr hin) p hp

private theorem sector_coordinates {r h t d : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1)
    (hh : 0 < h) (hd : 0 ≤ d) (hcover : t ^ 2 + (d + h) ^ 2 ≤ 1)
    (hanchor : 1 ≤ (r - |t|) ^ 2 + d ^ 2) : t ^ 2 + d ^ 2 < 1 ∧ 3 * t ^ 2 ≤ d ^ 2 := by
  have hstrict : t ^ 2 + d ^ 2 < 1 := by
    nlinarith only [hcover, mul_nonneg hd hh.le, sq_pos_of_pos hh]
  have hhorizontal : 2 * |t| < r := by
    by_contra! h
    nlinarith only [hstrict, hanchor, sq_abs t, mul_nonneg hr.le (sub_nonneg.mpr h)]
  have hleft : 0 ≤ r - |t| := by linarith
  have hright : 0 ≤ 1 - |t| := by linarith
  have hsquare : (r - |t|) ^ 2 ≤ (1 - |t|) ^ 2 :=
    (sq_le_sq₀ hleft hright).2 (by linarith)
  have hspan : 0 ≤ 1 - 2 * |t| := by linarith
  refine ⟨hstrict, ?_⟩
  nlinarith only [hanchor, hsquare, sq_abs t, mul_nonneg (abs_nonneg t) hspan]

private theorem dist_sq_lt_one_of_sector {t d s e : ℝ} (hd : 0 ≤ d) (he : 0 ≤ e)
    (ht : t ^ 2 + d ^ 2 < 1) (hs : s ^ 2 + e ^ 2 < 1)
    (hdt : 3 * t ^ 2 ≤ d ^ 2) (hes : 3 * s ^ 2 ≤ e ^ 2) :
    (t - s) ^ 2 + (d - e) ^ 2 < 1 := by
  let R := Real.sqrt (t ^ 2 + d ^ 2)
  let S := Real.sqrt (s ^ 2 + e ^ 2)
  have hR : R ^ 2 = t ^ 2 + d ^ 2 := Real.sq_sqrt (by positivity)
  have hS : S ^ 2 = s ^ 2 + e ^ 2 := Real.sq_sqrt (by positivity)
  have hR₀ : 0 ≤ R := Real.sqrt_nonneg _
  have hS₀ : 0 ≤ S := Real.sqrt_nonneg _
  have htR : 2 * |t| ≤ R :=
    (sq_le_sq₀ (by positivity) hR₀).1 (by nlinarith only [hR, hdt, sq_abs t])
  have hsS : 2 * |s| ≤ S :=
    (sq_le_sq₀ (by positivity) hS₀).1 (by nlinarith only [hS, hes, sq_abs s])
  have hts : 4 * (-(t * s)) ≤ R * S := by
    calc
      4 * (-(t * s)) ≤ 4 * |t * s| := by linarith only [neg_le_abs (t * s)]
      _ = (2 * |t|) * (2 * |s|) := by rw [abs_mul]; ring
      _ ≤ R * S := mul_le_mul htR hsS (by positivity) hR₀
  have hde : 3 * (R * S) ≤ 4 * (d * e) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).1
    have hleft : 3 * R ^ 2 ≤ 4 * d ^ 2 := by nlinarith only [hR, hdt]
    have hright : 3 * S ^ 2 ≤ 4 * e ^ 2 := by nlinarith only [hS, hes]
    have hmul := mul_le_mul hleft hright (by positivity : 0 ≤ 3 * S ^ 2)
      (by positivity : 0 ≤ 4 * d ^ 2)
    nlinarith only [hmul]
  have hbound : (t-s) ^ 2 + (d-e) ^ 2 ≤ R ^ 2 + S ^ 2 - R * S := by
    nlinarith only [hR, hS, hts, hde]
  rcases le_total R S with h | h
  · nlinarith only [hbound, hS, hs, mul_nonneg hR₀ (sub_nonneg.mpr h)]
  · nlinarith only [hbound, hR, ht, mul_nonneg hS₀ (sub_nonneg.mpr h)]

/-- Two sites below an edge of length `2 * r ≤ 2`, each separated from its
    nearer endpoint and covering the lifted midpoint, cannot be unit-separated. -/
private theorem dist_sq_lt_one_of_midpoint_covers {r h t d s e : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1)
    (hh : 0 < h) (hd : 0 ≤ d) (he : 0 ≤ e)
    (ht : t ^ 2 + (d + h) ^ 2 ≤ 1) (hs : s ^ 2 + (e + h) ^ 2 ≤ 1)
    (ht_anchor : 1 ≤ (r - |t|) ^ 2 + d ^ 2) (hs_anchor : 1 ≤ (r - |s|) ^ 2 + e ^ 2) :
    (t - s) ^ 2 + (d - e) ^ 2 < 1 := by
  obtain ⟨ht', hdt⟩ := sector_coordinates hr hr₁ hh hd ht ht_anchor
  obtain ⟨hs', hes⟩ := sector_coordinates hr hr₁ hh he hs hs_anchor
  exact dist_sq_lt_one_of_sector hd he ht' hs' hdt hes

/-- A common supporting line cannot carry two sites at squared separation
    greater than `4 - (diam A)⁻¹ ^ 2` when the optimal classes are finite. -/
private theorem dist_sq_add_inv_diam_sq_le_four_on_support {n : ℕ} {A : Finset ℝ²}
    (hA : IsMinimiser n A) (hn : 5 ≤ n) (hfin : h n ≠ ⊤)
    (hlarge : 2 < Metric.diam (A : Set ℝ²)) {a b u : ℝ²}
    (ha : a ∈ A) (hb : b ∈ A) (hu : ‖u‖ = 1)
    (hs : ∀ q ∈ A, inner ℝ q u ≤ inner ℝ a u) (hl : inner ℝ b u = inner ℝ a u) :
    dist a b ^ 2 + ((Metric.diam (A : Set ℝ²))⁻¹) ^ 2 ≤ 4 := by
  let D := Metric.diam (A : Set ℝ²)
  have hD : 2 < D := hlarge
  have hD₀ : 0 < D := by linarith
  change dist a b ^ 2 + (D⁻¹) ^ 2 ≤ 4
  by_contra! habove
  have hinv : 0 ≤ D⁻¹ := inv_nonneg.mpr hD₀.le
  have hinv₁ : D⁻¹ ≤ 1 := by rw [inv_le_one₀ hD₀]; linarith
  have hab : a ≠ b := by
    intro he
    rw [he, dist_self] at habove
    have h := (sq_le_sq₀ hinv zero_le_one).2 hinv₁
    nlinarith only [habove, h]
  let r := dist a b / 2
  let height := 1 / (2 * D)
  have hr : 0 < r := div_pos (dist_pos.mpr hab) (by norm_num)
  have hr₁ : r ≤ 1 := by
    have h := dist_lt_two_on_support hA hn hfin ha hb hu hs hl
    change dist a b / 2 ≤ 1
    linarith
  have hh : 0 < height := by dsimp [height]; positivity
  have hprod : 2 * D * height = 1 := by dsimp [height]; field_simp
  have hdouble : 2 * height = D⁻¹ := by dsimp [height]; field_simp
  have hclear : 1 < r ^ 2 + height ^ 2 := by
    rw [← hdouble] at habove
    dsimp only [r]
    nlinarith only [habove]
  have hDheight : 0 ≤ D - height := by linarith [hdouble, hinv₁]
  let m := midpoint ℝ a b
  let z := m + height • u
  have hzm : dist z m = height := by
    rw [dist_eq_norm, show z - m = height • u by dsimp [z]; abel, norm_smul,
      Real.norm_of_nonneg hh.le, hu, mul_one]
  have hupper (w : ℝ²) (hw : w ∈ A) : dist z w ≤ D := by
    have haD := Metric.dist_le_diam_of_mem A.finite_toSet.isBounded hw ha
    have hbD := Metric.dist_le_diam_of_mem A.finite_toSet.isBounded hw hb
    have haDs := (sq_le_sq₀ dist_nonneg hD₀.le).2 haD
    have hbDs := (sq_le_sq₀ dist_nonneg hD₀.le).2 hbD
    have hmid := dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq w a b
    change dist w a ^ 2 + dist w b ^ 2 = 2 * (dist w m ^ 2 + r ^ 2) at hmid
    have hmw : dist m w ≤ D - height := by
      rw [dist_comm m w]
      apply (sq_le_sq₀ dist_nonneg hDheight).1
      nlinarith only [haDs, hbDs, hmid, hclear, hprod]
    linarith [dist_triangle z m w, hzm]
  obtain ⟨x, d, _, heuc, hdepth, _, _⟩ := SupportFrame.coordinates a b u hab hu hl
  have hmp : inner ℝ m u = inner ℝ a u := by
    dsimp only [m]
    rw [midpoint_eq_smul_add, real_inner_smul_left, inner_add_left, hl, invOf_eq_inv]
    ring
  have hda : d a = 0 := by rw [hdepth, sub_self]
  have hdb : d b = 0 := by rw [hdepth, hl, sub_self]
  have hdm : d m = 0 := by rw [hdepth, hmp, sub_self]
  have hdz : d z = -height := by
    rw [hdepth]
    dsimp only [z]
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hu, hmp]
    ring
  have hxz : x z = x m := by
    have hz := heuc z m
    rw [hzm, hdz, hdm] at hz
    have hzero : (x z - x m) ^ 2 = 0 := by nlinarith only [hz]
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hzero)
  have hma : dist m a = r := by
    dsimp only [m]
    rw [dist_midpoint_left, Real.norm_two]
    dsimp [r]
    ring
  have hmb : dist m b = r := by
    dsimp only [m]
    rw [dist_midpoint_right, Real.norm_two]
    dsimp [r]
    ring
  have hxa : (x a - x m) ^ 2 = r ^ 2 := by
    have h := heuc m a
    rw [hma, hda, hdm] at h
    nlinarith only [h]
  have hxb : (x b - x m) ^ 2 = r ^ 2 := by
    have h := heuc m b
    rw [hmb, hdb, hdm] at h
    nlinarith only [h]
  have hxab : (x a - x b) ^ 2 = (2 * r) ^ 2 := by
    have h := heuc a b
    rw [hda, hdb] at h
    dsimp only [r]
    nlinarith only [h]
  have hsides : (x a = x m + r ∧ x b = x m - r) ∨
      (x a = x m - r ∧ x b = x m + r) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hxa with ha' | ha' <;>
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hxb with hb' | hb'
    · have hsame : x a = x b := by linarith only [ha', hb']
      rw [hsame, sub_self] at hxab
      nlinarith only [hxab, sq_pos_of_pos hr]
    · exact Or.inl ⟨by linarith only [ha'], by linarith only [hb']⟩
    · exact Or.inr ⟨by linarith only [ha'], by linarith only [hb']⟩
    · have hsame : x a = x b := by linarith only [ha', hb']
      rw [hsame, sub_self] at hxab
      nlinarith only [hxab, sq_pos_of_pos hr]
  have hza : 1 < dist z a := by
    apply (sq_lt_sq₀ zero_le_one dist_nonneg).1
    rw [heuc, hxz, hdz, hda]
    nlinarith only [hclear, hxa]
  have hzb : 1 < dist z b := by
    apply (sq_lt_sq₀ zero_le_one dist_nonneg).1
    rw [heuc, hxz, hdz, hdb]
    nlinarith only [hclear, hxb]
  have hsep (v w : ℝ²) (hv : v ∈ A) (hw : w ∈ A) (hne : v ≠ w) :
      1 ≤ dist v w ^ 2 := by
    have h := hA.1.2 hv hw hne
    change (1 : ℝ≥0∞) ≤ edist v w at h
    rw [edist_dist, ← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff dist_nonneg] at h
    simpa only [one_pow] using (sq_le_sq₀ zero_le_one dist_nonneg).2 h
  have hnear (w : ℝ²) (hw : w ∈ A) (hwa : w ≠ a) (hwb : w ≠ b) :
      1 ≤ (r - |x w - x m|) ^ 2 + (d w) ^ 2 := by
    have h1 := hsep w a hw ha hwa
    have h2 := hsep w b hw hb hwb
    rw [heuc, hda, sub_zero] at h1
    rw [heuc, hdb, sub_zero] at h2
    rcases le_total 0 (x w - x m) with hx | hx
    · rw [abs_of_nonneg hx]
      rcases hsides with ⟨hpos, _⟩ | ⟨_, hpos⟩
      · rw [hpos] at h1
        nlinarith only [h1]
      · rw [hpos] at h2
        nlinarith only [h2]
    · rw [abs_of_nonpos hx]
      rcases hsides with ⟨_, hneg⟩ | ⟨hneg, _⟩
      · rw [hneg] at h2
        nlinarith only [h2]
      · rw [hneg] at h1
        nlinarith only [h1]
  have hcover (w : ℝ²) (hw : dist z w ≤ 1) :
      (x w - x m) ^ 2 + (d w + height) ^ 2 ≤ 1 := by
    have h := (sq_le_sq₀ dist_nonneg zero_le_one).2 hw
    rw [heuc, hxz, hdz] at h
    nlinarith only [h]
  have hd₀ (w : ℝ²) (hw : w ∈ A) : 0 ≤ d w := by
    rw [hdepth]
    exact sub_nonneg.mpr (hs w hw)
  obtain ⟨p, hp, q, hq, hpq, hzp, hzq⟩ := Replacements.two_unit_cover hA hn hfin hupper
  have hp_a : p ≠ a := fun he => hza.not_ge (he ▸ hzp)
  have hp_b : p ≠ b := fun he => hzb.not_ge (he ▸ hzp)
  have hq_a : q ≠ a := fun he => hza.not_ge (he ▸ hzq)
  have hq_b : q ≠ b := fun he => hzb.not_ge (he ▸ hzq)
  have hshort := dist_sq_lt_one_of_midpoint_covers hr hr₁ hh (hd₀ p hp) (hd₀ q hq)
    (hcover p hzp) (hcover q hzq) (hnear p hp hp_a hp_b) (hnear q hq hq_a hq_b)
  have hunit := hsep p q hp hq hpq
  rw [heuc] at hunit
  nlinarith only [hshort, hunit]

end SupportingSegments

end OMA.SupportBoundsProof

/-- The support-line bound required by the reduction of the rigid jump case. -/
theorem OMA.solution : OMA.R_Erdos103_erdos_103_variants_two_le_R1_H2_R1_H2_R1.H1 := by
  intro n A hn hA hFinite a ha b hb u hu hSupport hLine
  refine ⟨OMA.SupportBoundsProof.SupportingSegments.dist_lt_two_on_support
    hA hn hFinite ha hb hu hSupport hLine, ?_⟩
  intro hLarge
  exact OMA.SupportBoundsProof.SupportingSegments.dist_sq_add_inv_diam_sq_le_four_on_support
    hA hn hFinite hLarge ha hb hu hSupport hLine
