import FormalConjectures.ErdosProblems.«633»
import Mathlib.Analysis.Real.Cardinality
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Geometry.Euclidean.Similarity

/-!
# Generic Triangle Simili-Cuttability Characterization (Erdős Problem 633)

We prove that there exists a triangle `T` in `ℝ²` which is simili-cuttable into `n` mutually
similar triangles if and only if `n ∉ {0, 2, 3, 5}` (Soifer 2009):
1. Positive direction (`n ∉ {0, 2, 3, 5} → IsSimiliCuttable n T`): adapted from the merged proof
   of `Erdos633.IsSimiliCuttable.of_ne_zero_two_three_five` (credit: @TheWaler).
2. Impossibility direction (`¬ IsSimiliCuttable n T` for `n ∈ {2, 3, 5}`): construct a triangle `T`
   whose angles are `ℤ`-linearly independent; prove angular measure conservation for any
   simili-cutting via barycentric coordinates and Lebesgue measure on circular arcs; transfer
   `ℤ`-linear independence to the piece angles; deduce unique corner triangles with vertices
   strictly on the open edges of `T`; classify non-corner vertex degrees as `3` or `6` to obtain
   `#E + 2 #I = n - 1` with `#E ≥ 3` (ruling out `n = 2, 3`); and eliminate `n = 5` by showing
   two distinct corner vertices on one edge force two remaining pieces to share a boundary edge
   (contradicting interior disjointness), while coinciding corner vertices force a 4th edge vertex
   of degree `3` into only `2` remaining pieces.
-/

namespace Erdos633SimiliCuttableProof

open Affine
open scoped EuclideanGeometry Similar NNReal

private def vec3 (x y z : ℝ) : Fin 3 → ℝ
  | 0 => x
  | 1 => y
  | 2 => z

private lemma affineCombination_eq_imp (T : Triangle ℝ ℝ²) {w₁ w₂ : Fin 3 → ℝ}
    (hw₁ : ∑ i, w₁ i = 1) (hw₂ : ∑ i, w₂ i = 1)
    (h : Finset.univ.affineCombination ℝ T.points w₁ =
      Finset.univ.affineCombination ℝ T.points w₂) : w₁ = w₂ := by
  have hind := T.independent.indicator_eq_of_affineCombination_eq
    Finset.univ Finset.univ w₁ w₂ hw₁ hw₂ h
  simpa using hind

private noncomputable def homothetyMap (s : ℝ) (c : ℝ²) : ℝ² →ᵃ[ℝ] ℝ² where
  toFun x := s • x + c
  linear := s • LinearMap.id
  map_vadd' p v := by
    change s • (v + p) + c = s • v + (s • p + c)
    rw [smul_add, add_assoc]

private lemma homothetyMap_injective {s : ℝ} (hs : s ≠ 0) (c : ℝ²) :
    Function.Injective (homothetyMap s c) := by
  intro x y h
  change s • x + c = s • y + c at h
  exact smul_right_injective ℝ² hs (add_right_cancel h)

private noncomputable def subTri (T : Triangle ℝ ℝ²) (s : ℝ) (hs : s ≠ 0)
    (a : Fin 3 → ℝ) : Triangle ℝ ℝ² :=
  T.map (homothetyMap s (∑ i : Fin 3, a i • T.points i)) (homothetyMap_injective hs _)

private lemma subTri_similar (T : Triangle ℝ ℝ²) {s : ℝ} (hs : s ≠ 0) (a : Fin 3 → ℝ) :
    (subTri T s hs a).points ∼ T.points := by
  refine ⟨⟨|s|, abs_nonneg s⟩, ?_, fun i j => ?_⟩
  · intro h
    have h0 : |s| = 0 := congrArg NNReal.toReal h
    exact hs (abs_eq_zero.mp h0)
  · simp only [subTri, Simplex.map_points, Function.comp_apply, homothetyMap, AffineMap.coe_mk]
    rw [edist_dist, edist_dist]
    have hd : dist (s • T.points i + ∑ k : Fin 3, a k • T.points k)
        (s • T.points j + ∑ k : Fin 3, a k • T.points k) =
        |s| * dist (T.points i) (T.points j) := by
      rw [dist_add_right, dist_smul₀, Real.norm_eq_abs]
    rw [hd, ENNReal.ofReal_mul (abs_nonneg s), ENNReal.ofReal_eq_coe_nnreal (abs_nonneg s)]
    rfl

private lemma subTri_affineCombination (T : Triangle ℝ ℝ²) {s : ℝ} (hs : s ≠ 0)
    {a : Fin 3 → ℝ} (ha : ∑ i, a i = 1 - s) {u : Fin 3 → ℝ} (hu : ∑ i, u i = 1) :
    Finset.univ.affineCombination ℝ (subTri T s hs a).points u =
      Finset.univ.affineCombination ℝ T.points (fun i => a i + s * u i) := by
  have hw : ∑ i : Fin 3, (a i + s * u i) = 1 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ha, hu]
    ring
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hu,
    Finset.affineCombination_eq_linear_combination _ _ _ hw]
  simp only [subTri, Simplex.map_points, Function.comp_apply, homothetyMap, AffineMap.coe_mk,
    smul_add, add_smul, Finset.sum_add_distrib]
  have hsmul : ∑ i : Fin 3, u i • ∑ k : Fin 3, a k • T.points k =
      (∑ i : Fin 3, u i) • ∑ k : Fin 3, a k • T.points k :=
    Finset.sum_smul.symm
  rw [hsmul, hu, one_smul, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, mul_comm]

private lemma mem_subTri_setInterior_iff (I : Set ℝ) (T : Triangle ℝ ℝ²)
    {s : ℝ} (hs : s ≠ 0) {a : Fin 3 → ℝ} (ha : ∑ i, a i = 1 - s) {x : ℝ²} :
    x ∈ (subTri T s hs a).setInterior I ↔
      ∃ w : Fin 3 → ℝ, (∑ i, w i = 1) ∧
        (∀ i, (w i - a i) / s ∈ I) ∧
        Finset.univ.affineCombination ℝ T.points w = x := by
  constructor
  · rintro ⟨u, hu, huI, rfl⟩
    refine ⟨fun i => a i + s * u i, ?_, ?_, (subTri_affineCombination T hs ha hu).symm⟩
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ha, hu]
      ring
    · intro i
      have hdiv : (a i + s * u i - a i) / s = u i := by
        field_simp [hs]
        ring
      rw [hdiv]
      exact huI i
  · rintro ⟨w, hw, hwI, rfl⟩
    let u : Fin 3 → ℝ := fun i => (w i - a i) / s
    have hu : ∑ i : Fin 3, u i = 1 := by
      simp only [u, ← Finset.sum_div, Finset.sum_sub_distrib, hw, ha]
      field_simp [hs]
      ring
    refine ⟨u, hu, hwI, ?_⟩
    rw [subTri_affineCombination T hs ha hu]
    congr 1
    funext i
    simp only [u]
    field_simp [hs]
    ring

private lemma mem_subTri_closedInterior_pos (T : Triangle ℝ ℝ²) {s : ℝ} (hs : 0 < s)
    {a : Fin 3 → ℝ} (ha : ∑ i, a i = 1 - s) {x : ℝ²} :
    x ∈ (subTri T s (ne_of_gt hs) a).closedInterior ↔
      ∃ w : Fin 3 → ℝ, (∑ i, w i = 1) ∧
        (∀ i, a i ≤ w i) ∧
        Finset.univ.affineCombination ℝ T.points w = x := by
  change x ∈ (subTri T s (ne_of_gt hs) a).setInterior (Set.Icc 0 1) ↔ _
  rw [mem_subTri_setInterior_iff (Set.Icc 0 1) T (ne_of_gt hs) ha]
  refine exists_congr fun w => and_congr_right fun hw => and_congr_left fun _ => ?_
  constructor
  · intro h i
    have h0 : 0 ≤ (w i - a i) / s := (h i).1
    have h1 : 0 ≤ w i - a i := (div_nonneg_iff.mp h0).elim (fun h' => h'.1) (fun h' => by linarith)
    linarith
  · intro h i
    have hsum : (w 0 - a 0) + (w 1 - a 1) + (w 2 - a 2) = s := by
      rw [Fin.sum_univ_three] at hw ha
      linarith
    have h0 : 0 ≤ w 0 - a 0 := sub_nonneg.mpr (h 0)
    have h1 : 0 ≤ w 1 - a 1 := sub_nonneg.mpr (h 1)
    have h2 : 0 ≤ w 2 - a 2 := sub_nonneg.mpr (h 2)
    have hle : w i - a i ≤ s := match i with
      | 0 => by linarith
      | 1 => by linarith
      | 2 => by linarith
    exact ⟨div_nonneg (sub_nonneg.mpr (h i)) (le_of_lt hs), (div_le_one hs).mpr hle⟩

private lemma mem_subTri_interior_pos (T : Triangle ℝ ℝ²) {s : ℝ} (hs : 0 < s)
    {a : Fin 3 → ℝ} (ha : ∑ i, a i = 1 - s) {x : ℝ²} :
    x ∈ (subTri T s (ne_of_gt hs) a).interior ↔
      ∃ w : Fin 3 → ℝ, (∑ i, w i = 1) ∧
        (∀ i, a i < w i) ∧
        Finset.univ.affineCombination ℝ T.points w = x := by
  change x ∈ (subTri T s (ne_of_gt hs) a).setInterior (Set.Ioo 0 1) ↔ _
  rw [mem_subTri_setInterior_iff (Set.Ioo 0 1) T (ne_of_gt hs) ha]
  refine exists_congr fun w => and_congr_right fun hw => and_congr_left fun _ => ?_
  constructor
  · intro h i
    have h0 : 0 < (w i - a i) / s := (h i).1
    have h1 : 0 < w i - a i := (div_pos_iff.mp h0).elim (fun h' => h'.1) (fun h' => by linarith)
    linarith
  · intro h i
    have hsum : (w 0 - a 0) + (w 1 - a 1) + (w 2 - a 2) = s := by
      rw [Fin.sum_univ_three] at hw ha
      linarith
    have h0 : 0 < w 0 - a 0 := sub_pos.mpr (h 0)
    have h1 : 0 < w 1 - a 1 := sub_pos.mpr (h 1)
    have h2 : 0 < w 2 - a 2 := sub_pos.mpr (h 2)
    have hlt : w i - a i < s := match i with
      | 0 => by linarith
      | 1 => by linarith
      | 2 => by linarith
    exact ⟨div_pos (sub_pos.mpr (h i)) hs, (div_lt_one hs).mpr hlt⟩

private lemma mem_subTri_closedInterior_neg (T : Triangle ℝ ℝ²) {s : ℝ} (hs : s < 0)
    {a : Fin 3 → ℝ} (ha : ∑ i, a i = 1 - s) {x : ℝ²} :
    x ∈ (subTri T s (ne_of_lt hs) a).closedInterior ↔
      ∃ w : Fin 3 → ℝ, (∑ i, w i = 1) ∧
        (∀ i, w i ≤ a i) ∧
        Finset.univ.affineCombination ℝ T.points w = x := by
  change x ∈ (subTri T s (ne_of_lt hs) a).setInterior (Set.Icc 0 1) ↔ _
  rw [mem_subTri_setInterior_iff (Set.Icc 0 1) T (ne_of_lt hs) ha]
  refine exists_congr fun w => and_congr_right fun hw => and_congr_left fun _ => ?_
  have ht : 0 < -s := neg_pos.mpr hs
  constructor
  · intro h i
    have h0 : 0 ≤ (a i - w i) / (-s) := by
      have : (a i - w i) / (-s) = (w i - a i) / s := by field_simp [ne_of_lt hs]; ring
      rw [this]
      exact (h i).1
    have h1 : 0 ≤ a i - w i := (div_nonneg_iff.mp h0).elim (fun h' => h'.1) (fun h' => by linarith)
    linarith
  · intro h i
    have hsum : (a 0 - w 0) + (a 1 - w 1) + (a 2 - w 2) = -s := by
      rw [Fin.sum_univ_three] at hw ha
      linarith
    have h0 : 0 ≤ a 0 - w 0 := sub_nonneg.mpr (h 0)
    have h1 : 0 ≤ a 1 - w 1 := sub_nonneg.mpr (h 1)
    have h2 : 0 ≤ a 2 - w 2 := sub_nonneg.mpr (h 2)
    have hle : a i - w i ≤ -s := match i with
      | 0 => by linarith
      | 1 => by linarith
      | 2 => by linarith
    have heq : (w i - a i) / s = (a i - w i) / (-s) := by field_simp [ne_of_lt hs]; ring
    rw [heq]
    exact ⟨div_nonneg (sub_nonneg.mpr (h i)) (le_of_lt ht), (div_le_one ht).mpr hle⟩

private lemma mem_subTri_interior_neg (T : Triangle ℝ ℝ²) {s : ℝ} (hs : s < 0)
    {a : Fin 3 → ℝ} (ha : ∑ i, a i = 1 - s) {x : ℝ²} :
    x ∈ (subTri T s (ne_of_lt hs) a).interior ↔
      ∃ w : Fin 3 → ℝ, (∑ i, w i = 1) ∧
        (∀ i, w i < a i) ∧
        Finset.univ.affineCombination ℝ T.points w = x := by
  change x ∈ (subTri T s (ne_of_lt hs) a).setInterior (Set.Ioo 0 1) ↔ _
  rw [mem_subTri_setInterior_iff (Set.Ioo 0 1) T (ne_of_lt hs) ha]
  refine exists_congr fun w => and_congr_right fun hw => and_congr_left fun _ => ?_
  have ht : 0 < -s := neg_pos.mpr hs
  constructor
  · intro h i
    have h0 : 0 < (a i - w i) / (-s) := by
      have : (a i - w i) / (-s) = (w i - a i) / s := by field_simp [ne_of_lt hs]; ring
      rw [this]
      exact (h i).1
    have h1 : 0 < a i - w i := (div_pos_iff.mp h0).elim (fun h' => h'.1) (fun h' => by linarith)
    linarith
  · intro h i
    have hsum : (a 0 - w 0) + (a 1 - w 1) + (a 2 - w 2) = -s := by
      rw [Fin.sum_univ_three] at hw ha
      linarith
    have h0 : 0 < a 0 - w 0 := sub_pos.mpr (h 0)
    have h1 : 0 < a 1 - w 1 := sub_pos.mpr (h 1)
    have h2 : 0 < a 2 - w 2 := sub_pos.mpr (h 2)
    have hlt : a i - w i < -s := match i with
      | 0 => by linarith
      | 1 => by linarith
      | 2 => by linarith
    have heq : (w i - a i) / s = (a i - w i) / (-s) := by field_simp [ne_of_lt hs]; ring
    rw [heq]
    exact ⟨div_pos (sub_pos.mpr (h i)) ht, (div_lt_one ht).mpr hlt⟩

private lemma mem_closedInterior_of_nonneg (T : Triangle ℝ ℝ²) {w : Fin 3 → ℝ}
    (hw : ∑ i, w i = 1) (hnn : ∀ i, 0 ≤ w i) :
    Finset.univ.affineCombination ℝ T.points w ∈ T.closedInterior := by
  rw [T.affineCombination_mem_closedInterior_iff hw]
  intro i
  rw [Fin.sum_univ_three] at hw
  have h0 := hnn 0
  have h1 := hnn 1
  have h2 := hnn 2
  refine ⟨hnn i, ?_⟩
  match i with
  | 0 => linarith
  | 1 => linarith
  | 2 => linarith

private lemma mem_interior_of_pos (T : Triangle ℝ ℝ²) {w : Fin 3 → ℝ}
    (hw : ∑ i, w i = 1) (hpos : ∀ i, 0 < w i) :
    Finset.univ.affineCombination ℝ T.points w ∈ T.interior := by
  rw [T.affineCombination_mem_interior_iff hw]
  intro i
  rw [Fin.sum_univ_three] at hw
  have h0 := hpos 0
  have h1 := hpos 1
  have h2 := hpos 2
  refine ⟨hpos i, ?_⟩
  match i with
  | 0 => linarith
  | 1 => linarith
  | 2 => linarith

private def StrongSimiliCuttable (n : ℕ) (T : Triangle ℝ ℝ²) : Prop :=
  ∃ Ts : Fin n → Triangle ℝ ℝ²,
    (∀ i, (Ts i).points ∼ T.points) ∧
    (∀ i, (Ts i).interior ⊆ T.interior) ∧
    Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) ∧
    ⋃ i, (Ts i).closedInterior = T.closedInterior

private lemma StrongSimiliCuttable.toIsSimiliCuttable {n : ℕ} {T : Triangle ℝ ℝ²}
    (h : StrongSimiliCuttable n T) : Erdos633.IsSimiliCuttable n T := by
  rcases h with ⟨Ts, hsim, -, hdisj, hunion⟩
  exact ⟨Ts, fun i j => (hsim i).trans (hsim j).symm, hdisj, hunion⟩

private lemma strongSimiliCuttable_one (T : Triangle ℝ ℝ²) : StrongSimiliCuttable 1 T := by
  refine ⟨fun _ => T, fun _ => Similar.refl _, fun _ => Set.Subset.rfl, ?_, ?_⟩
  · intro i j hij
    exact absurd (Subsingleton.elim i j) hij
  · ext x
    simp

private lemma strongSimiliCuttable_two_mul (m : ℕ) (hm : 2 ≤ m) (T : Triangle ℝ ℝ²) :
    StrongSimiliCuttable (2 * m) T := by
  let mr : ℝ := (m : ℝ)
  have hmr_pos : 0 < mr := by
    dsimp only [mr]
    exact_mod_cast (by omega : 0 < m)
  have hmr_ge2 : (2 : ℝ) ≤ mr := by
    dsimp only [mr]
    exact_mod_cast hm
  have hs_big_pos : 0 < (mr - 1) / mr := div_pos (by linarith) hmr_pos
  have hs_up_pos : 0 < 1 / mr := div_pos one_pos hmr_pos
  have hs_inv_neg : -1 / mr < 0 := div_neg_of_neg_of_pos (by norm_num) hmr_pos
  let aBig : Fin 3 → ℝ := vec3 (1 / mr) 0 0
  have haBig : ∑ i : Fin 3, aBig i = 1 - (mr - 1) / mr := by
    rw [Fin.sum_univ_three]
    change 1 / mr + 0 + 0 = 1 - (mr - 1) / mr
    field_simp [ne_of_gt hmr_pos]
    ring
  let aUp (j : Fin m) : Fin 3 → ℝ := vec3 0 ((j.1 : ℝ) / mr) ((mr - 1 - (j.1 : ℝ)) / mr)
  have haUp (j : Fin m) : ∑ i : Fin 3, aUp j i = 1 - 1 / mr := by
    rw [Fin.sum_univ_three]
    change 0 + (j.1 : ℝ) / mr + (mr - 1 - (j.1 : ℝ)) / mr = 1 - 1 / mr
    field_simp [ne_of_gt hmr_pos]
    ring
  let aInv (j : Fin (m - 1)) : Fin 3 → ℝ :=
    vec3 (1 / mr) (((j.1 : ℝ) + 1) / mr) ((mr - 1 - (j.1 : ℝ)) / mr)
  have haInv (j : Fin (m - 1)) : ∑ i : Fin 3, aInv j i = 1 - (-1 / mr) := by
    rw [Fin.sum_univ_three]
    change 1 / mr + ((j.1 : ℝ) + 1) / mr + (mr - 1 - (j.1 : ℝ)) / mr = 1 - (-1 / mr)
    field_simp [ne_of_gt hmr_pos]
    ring
  let idx := Unit ⊕ Fin m ⊕ Fin (m - 1)
  let tile : idx → Triangle ℝ ℝ²
    | Sum.inl () => subTri T ((mr - 1) / mr) (ne_of_gt hs_big_pos) aBig
    | Sum.inr (Sum.inl j) => subTri T (1 / mr) (ne_of_gt hs_up_pos) (aUp j)
    | Sum.inr (Sum.inr j) => subTri T (-1 / mr) (ne_of_lt hs_inv_neg) (aInv j)
  have hcard : Fintype.card idx = 2 * m := by
    dsimp only [idx]
    rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Fintype.card_fin]
    omega
  let e : Fin (2 * m) ≃ idx := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => tile (e i), ?_, ?_, ?_, ?_⟩
  · intro i
    dsimp only
    generalize e i = p
    rcases p with ⟨⟩ | j | j
    · exact subTri_similar T (ne_of_gt hs_big_pos) aBig
    · exact subTri_similar T (ne_of_gt hs_up_pos) (aUp j)
    · exact subTri_similar T (ne_of_lt hs_inv_neg) (aInv j)
  · intro i x hx
    dsimp only at hx
    generalize e i = p at hx
    rcases p with ⟨⟩ | j | j
    · rw [mem_subTri_interior_pos T hs_big_pos haBig] at hx
      rcases hx with ⟨w, hw, hlt, rfl⟩
      refine mem_interior_of_pos T hw fun k => ?_
      have hk := hlt k
      match k with
      | 0 =>
        change 1 / mr < w 0 at hk
        linarith [div_pos one_pos hmr_pos]
      | 1 => exact hk
      | 2 => exact hk
    · rw [mem_subTri_interior_pos T hs_up_pos (haUp j)] at hx
      rcases hx with ⟨w, hw, hlt, rfl⟩
      have hj_le : (j.1 : ℝ) ≤ mr - 1 := by
        have h1 : j.1 + 1 ≤ m := j.2
        have h2 : (j.1 : ℝ) + 1 ≤ mr := by dsimp only [mr]; exact_mod_cast h1
        linarith
      refine mem_interior_of_pos T hw fun k => ?_
      have hk := hlt k
      match k with
      | 0 => exact hk
      | 1 =>
        change (j.1 : ℝ) / mr < w 1 at hk
        have hnn : (0 : ℝ) ≤ (j.1 : ℝ) / mr := div_nonneg (Nat.cast_nonneg _) (le_of_lt hmr_pos)
        linarith
      | 2 =>
        change (mr - 1 - (j.1 : ℝ)) / mr < w 2 at hk
        have hnn : (0 : ℝ) ≤ (mr - 1 - (j.1 : ℝ)) / mr :=
          div_nonneg (by linarith) (le_of_lt hmr_pos)
        linarith
    · rw [mem_subTri_interior_neg T hs_inv_neg (haInv j)] at hx
      rcases hx with ⟨w, hw, hlt, rfl⟩
      have hj_le : (j.1 : ℝ) + 2 ≤ mr := by
        have h1 : j.1 + 2 ≤ m := by omega
        dsimp only [mr]
        exact_mod_cast h1
      rw [Fin.sum_univ_three] at hw
      have h0 : w 0 < 1 / mr := hlt 0
      have h1 : w 1 < ((j.1 : ℝ) + 1) / mr := hlt 1
      have h2 : w 2 < (mr - 1 - (j.1 : ℝ)) / mr := hlt 2
      have hsum12 : ((j.1 : ℝ) + 1) / mr + (mr - 1 - (j.1 : ℝ)) / mr = 1 := by
        field_simp [ne_of_gt hmr_pos]; ring
      have hsum02 : 1 / mr + (mr - 1 - (j.1 : ℝ)) / mr = 1 - (j.1 : ℝ) / mr := by
        field_simp [ne_of_gt hmr_pos]; ring
      have hsum01 : 1 / mr + ((j.1 : ℝ) + 1) / mr = 1 - (mr - 2 - (j.1 : ℝ)) / mr := by
        field_simp [ne_of_gt hmr_pos]; ring
      have hnn1 : (0 : ℝ) ≤ (j.1 : ℝ) / mr := div_nonneg (Nat.cast_nonneg _) (le_of_lt hmr_pos)
      have hnn2 : (0 : ℝ) ≤ (mr - 2 - (j.1 : ℝ)) / mr :=
        div_nonneg (by linarith) (le_of_lt hmr_pos)
      refine mem_interior_of_pos T (by rw [Fin.sum_univ_three]; exact hw) fun k => ?_
      match k with
      | 0 => linarith
      | 1 => linarith
      | 2 => linarith
  · intro i₁ i₂ hne
    rw [Set.disjoint_left]
    intro x hx₁ hx₂
    have he_ne : e i₁ ≠ e i₂ := fun h => hne (e.injective h)
    have hdisj_idx : ∀ p₁ p₂ : idx, p₁ ≠ p₂ →
        x ∈ (tile p₁).interior → x ∈ (tile p₂).interior → False := by
      intro p₁ p₂ hp hx1 hx2
      rcases p₁ with ⟨⟩ | j₁ | j₁ <;> rcases p₂ with ⟨⟩ | j₂ | j₂
      · exact hp rfl
      · rw [mem_subTri_interior_pos T hs_big_pos haBig] at hx1
        rw [mem_subTri_interior_pos T hs_up_pos (haUp j₂)] at hx2
        rcases hx1 with ⟨w₁, hw₁, h1, rfl⟩
        rcases hx2 with ⟨w₂, hw₂, h2, hweq⟩
        have hww : w₁ = w₂ := affineCombination_eq_imp T hw₁ hw₂ hweq.symm
        subst hww
        rw [Fin.sum_univ_three] at hw₁
        have hb0 : 1 / mr < w₁ 0 := h1 0
        have hu1 : (j₂.1 : ℝ) / mr < w₁ 1 := h2 1
        have hu2 : (mr - 1 - (j₂.1 : ℝ)) / mr < w₁ 2 := h2 2
        have hsum : 1 / mr + (j₂.1 : ℝ) / mr + (mr - 1 - (j₂.1 : ℝ)) / mr = 1 := by
          field_simp [ne_of_gt hmr_pos]; ring
        linarith
      · rw [mem_subTri_interior_pos T hs_big_pos haBig] at hx1
        rw [mem_subTri_interior_neg T hs_inv_neg (haInv j₂)] at hx2
        rcases hx1 with ⟨w₁, hw₁, h1, rfl⟩
        rcases hx2 with ⟨w₂, hw₂, h2, hweq⟩
        have hww : w₁ = w₂ := affineCombination_eq_imp T hw₁ hw₂ hweq.symm
        subst hww
        have hb0 : 1 / mr < w₁ 0 := h1 0
        have hi0 : w₁ 0 < 1 / mr := h2 0
        linarith
      · rw [mem_subTri_interior_pos T hs_up_pos (haUp j₁)] at hx1
        rw [mem_subTri_interior_pos T hs_big_pos haBig] at hx2
        rcases hx1 with ⟨w₁, hw₁, h1, rfl⟩
        rcases hx2 with ⟨w₂, hw₂, h2, hweq⟩
        have hww : w₁ = w₂ := affineCombination_eq_imp T hw₁ hw₂ hweq.symm
        subst hww
        rw [Fin.sum_univ_three] at hw₁
        have hb0 : 1 / mr < w₁ 0 := h2 0
        have hu1 : (j₁.1 : ℝ) / mr < w₁ 1 := h1 1
        have hu2 : (mr - 1 - (j₁.1 : ℝ)) / mr < w₁ 2 := h1 2
        have hsum : 1 / mr + (j₁.1 : ℝ) / mr + (mr - 1 - (j₁.1 : ℝ)) / mr = 1 := by
          field_simp [ne_of_gt hmr_pos]; ring
        linarith
      · rw [mem_subTri_interior_pos T hs_up_pos (haUp j₁)] at hx1
        rw [mem_subTri_interior_pos T hs_up_pos (haUp j₂)] at hx2
        rcases hx1 with ⟨w₁, hw₁, h1, rfl⟩
        rcases hx2 with ⟨w₂, hw₂, h2, hweq⟩
        have hww : w₁ = w₂ := affineCombination_eq_imp T hw₁ hw₂ hweq.symm
        subst hww
        rw [Fin.sum_univ_three] at hw₁
        have hjne : j₁.1 ≠ j₂.1 := fun h => hp (by rw [Fin.ext h])
        have h0_1 : 0 < w₁ 0 := h1 0
        have h1_1 : (j₁.1 : ℝ) / mr < w₁ 1 := h1 1
        have h2_1 : (mr - 1 - (j₁.1 : ℝ)) / mr < w₁ 2 := h1 2
        have h1_2 : (j₂.1 : ℝ) / mr < w₁ 1 := h2 1
        have h2_2 : (mr - 1 - (j₂.1 : ℝ)) / mr < w₁ 2 := h2 2
        rcases lt_or_gt_of_ne hjne with hlt | hgt
        · have hle : (j₁.1 : ℝ) + 1 ≤ (j₂.1 : ℝ) := by exact_mod_cast hlt
          have hdiv : ((j₁.1 : ℝ) + 1) / mr ≤ (j₂.1 : ℝ) / mr :=
            div_le_div_of_nonneg_right hle (le_of_lt hmr_pos)
          have hsum : ((j₁.1 : ℝ) + 1) / mr + (mr - 1 - (j₁.1 : ℝ)) / mr = 1 := by
            field_simp [ne_of_gt hmr_pos]; ring
          linarith
        · have hle : (j₂.1 : ℝ) + 1 ≤ (j₁.1 : ℝ) := by exact_mod_cast hgt
          have hdiv : ((j₂.1 : ℝ) + 1) / mr ≤ (j₁.1 : ℝ) / mr :=
            div_le_div_of_nonneg_right hle (le_of_lt hmr_pos)
          have hsum : ((j₂.1 : ℝ) + 1) / mr + (mr - 1 - (j₂.1 : ℝ)) / mr = 1 := by
            field_simp [ne_of_gt hmr_pos]; ring
          linarith
      · rw [mem_subTri_interior_pos T hs_up_pos (haUp j₁)] at hx1
        rw [mem_subTri_interior_neg T hs_inv_neg (haInv j₂)] at hx2
        rcases hx1 with ⟨w₁, hw₁, h1, rfl⟩
        rcases hx2 with ⟨w₂, hw₂, h2, hweq⟩
        have hww : w₁ = w₂ := affineCombination_eq_imp T hw₁ hw₂ hweq.symm
        subst hww
        have hu1 : (j₁.1 : ℝ) / mr < w₁ 1 := h1 1
        have hu2 : (mr - 1 - (j₁.1 : ℝ)) / mr < w₁ 2 := h1 2
        have hi1 : w₁ 1 < ((j₂.1 : ℝ) + 1) / mr := h2 1
        have hi2 : w₁ 2 < (mr - 1 - (j₂.1 : ℝ)) / mr := h2 2
        rcases le_or_gt j₁.1 j₂.1 with hle | hgt
        · have hle' : (j₁.1 : ℝ) ≤ (j₂.1 : ℝ) := by exact_mod_cast hle
          have hdiv : (mr - 1 - (j₂.1 : ℝ)) / mr ≤ (mr - 1 - (j₁.1 : ℝ)) / mr :=
            div_le_div_of_nonneg_right (by linarith) (le_of_lt hmr_pos)
          linarith
        · have hle' : (j₂.1 : ℝ) + 1 ≤ (j₁.1 : ℝ) := by exact_mod_cast hgt
          have hdiv : ((j₂.1 : ℝ) + 1) / mr ≤ (j₁.1 : ℝ) / mr :=
            div_le_div_of_nonneg_right hle' (le_of_lt hmr_pos)
          linarith
      · rw [mem_subTri_interior_neg T hs_inv_neg (haInv j₁)] at hx1
        rw [mem_subTri_interior_pos T hs_big_pos haBig] at hx2
        rcases hx1 with ⟨w₁, hw₁, h1, rfl⟩
        rcases hx2 with ⟨w₂, hw₂, h2, hweq⟩
        have hww : w₁ = w₂ := affineCombination_eq_imp T hw₁ hw₂ hweq.symm
        subst hww
        have hi0 : w₁ 0 < 1 / mr := h1 0
        have hb0 : 1 / mr < w₁ 0 := h2 0
        linarith
      · rw [mem_subTri_interior_neg T hs_inv_neg (haInv j₁)] at hx1
        rw [mem_subTri_interior_pos T hs_up_pos (haUp j₂)] at hx2
        rcases hx1 with ⟨w₁, hw₁, h1, rfl⟩
        rcases hx2 with ⟨w₂, hw₂, h2, hweq⟩
        have hww : w₁ = w₂ := affineCombination_eq_imp T hw₁ hw₂ hweq.symm
        subst hww
        have hi1 : w₁ 1 < ((j₁.1 : ℝ) + 1) / mr := h1 1
        have hi2 : w₁ 2 < (mr - 1 - (j₁.1 : ℝ)) / mr := h1 2
        have hu1 : (j₂.1 : ℝ) / mr < w₁ 1 := h2 1
        have hu2 : (mr - 1 - (j₂.1 : ℝ)) / mr < w₁ 2 := h2 2
        rcases le_or_gt j₂.1 j₁.1 with hle | hgt
        · have hle' : (j₂.1 : ℝ) ≤ (j₁.1 : ℝ) := by exact_mod_cast hle
          have hdiv : (mr - 1 - (j₁.1 : ℝ)) / mr ≤ (mr - 1 - (j₂.1 : ℝ)) / mr :=
            div_le_div_of_nonneg_right (by linarith) (le_of_lt hmr_pos)
          linarith
        · have hle' : (j₁.1 : ℝ) + 1 ≤ (j₂.1 : ℝ) := by exact_mod_cast hgt
          have hdiv : ((j₁.1 : ℝ) + 1) / mr ≤ (j₂.1 : ℝ) / mr :=
            div_le_div_of_nonneg_right hle' (le_of_lt hmr_pos)
          linarith
      · rw [mem_subTri_interior_neg T hs_inv_neg (haInv j₁)] at hx1
        rw [mem_subTri_interior_neg T hs_inv_neg (haInv j₂)] at hx2
        rcases hx1 with ⟨w₁, hw₁, h1, rfl⟩
        rcases hx2 with ⟨w₂, hw₂, h2, hweq⟩
        have hww : w₁ = w₂ := affineCombination_eq_imp T hw₁ hw₂ hweq.symm
        subst hww
        rw [Fin.sum_univ_three] at hw₁
        have hjne : j₁.1 ≠ j₂.1 := fun h => hp (by rw [Fin.ext h])
        have h0_1 : w₁ 0 < 1 / mr := h1 0
        have h1_1 : w₁ 1 < ((j₁.1 : ℝ) + 1) / mr := h1 1
        have h2_1 : w₁ 2 < (mr - 1 - (j₁.1 : ℝ)) / mr := h1 2
        have h1_2 : w₁ 1 < ((j₂.1 : ℝ) + 1) / mr := h2 1
        have h2_2 : w₁ 2 < (mr - 1 - (j₂.1 : ℝ)) / mr := h2 2
        rcases lt_or_gt_of_ne hjne with hlt | hgt
        · have hle : (j₁.1 : ℝ) + 1 ≤ (j₂.1 : ℝ) := by exact_mod_cast hlt
          have hdiv : ((j₁.1 : ℝ) + 1) / mr ≤ (j₂.1 : ℝ) / mr :=
            div_le_div_of_nonneg_right hle (le_of_lt hmr_pos)
          have hsum : 1 / mr + (j₂.1 : ℝ) / mr + (mr - 1 - (j₂.1 : ℝ)) / mr = 1 := by
            field_simp [ne_of_gt hmr_pos]; ring
          linarith
        · have hle : (j₂.1 : ℝ) + 1 ≤ (j₁.1 : ℝ) := by exact_mod_cast hgt
          have hdiv : ((j₂.1 : ℝ) + 1) / mr ≤ (j₁.1 : ℝ) / mr :=
            div_le_div_of_nonneg_right hle (le_of_lt hmr_pos)
          have hsum : 1 / mr + (j₁.1 : ℝ) / mr + (mr - 1 - (j₁.1 : ℝ)) / mr = 1 := by
            field_simp [ne_of_gt hmr_pos]; ring
          linarith
    exact hdisj_idx (e i₁) (e i₂) he_ne hx₁ hx₂
  · ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hx⟩
      generalize e i = p at hx
      rcases p with ⟨⟩ | j | j
      · rw [mem_subTri_closedInterior_pos T hs_big_pos haBig] at hx
        rcases hx with ⟨w, hw, hle, rfl⟩
        refine mem_closedInterior_of_nonneg T hw fun k => ?_
        have hk := hle k
        match k with
        | 0 =>
          change 1 / mr ≤ w 0 at hk
          linarith [div_pos one_pos hmr_pos]
        | 1 => exact hk
        | 2 => exact hk
      · rw [mem_subTri_closedInterior_pos T hs_up_pos (haUp j)] at hx
        rcases hx with ⟨w, hw, hle, rfl⟩
        have hj_le : (j.1 : ℝ) ≤ mr - 1 := by
          have h1 : j.1 + 1 ≤ m := j.2
          have h2 : (j.1 : ℝ) + 1 ≤ mr := by dsimp only [mr]; exact_mod_cast h1
          linarith
        refine mem_closedInterior_of_nonneg T hw fun k => ?_
        have hk := hle k
        match k with
        | 0 => exact hk
        | 1 =>
          change (j.1 : ℝ) / mr ≤ w 1 at hk
          have hnn : (0 : ℝ) ≤ (j.1 : ℝ) / mr := div_nonneg (Nat.cast_nonneg _) (le_of_lt hmr_pos)
          linarith
        | 2 =>
          change (mr - 1 - (j.1 : ℝ)) / mr ≤ w 2 at hk
          have hnn : (0 : ℝ) ≤ (mr - 1 - (j.1 : ℝ)) / mr :=
            div_nonneg (by linarith) (le_of_lt hmr_pos)
          linarith
      · rw [mem_subTri_closedInterior_neg T hs_inv_neg (haInv j)] at hx
        rcases hx with ⟨w, hw, hle, rfl⟩
        have hj_le : (j.1 : ℝ) + 2 ≤ mr := by
          have h1 : j.1 + 2 ≤ m := by omega
          dsimp only [mr]
          exact_mod_cast h1
        rw [Fin.sum_univ_three] at hw
        have h0 : w 0 ≤ 1 / mr := hle 0
        have h1 : w 1 ≤ ((j.1 : ℝ) + 1) / mr := hle 1
        have h2 : w 2 ≤ (mr - 1 - (j.1 : ℝ)) / mr := hle 2
        have hsum12 : ((j.1 : ℝ) + 1) / mr + (mr - 1 - (j.1 : ℝ)) / mr = 1 := by
          field_simp [ne_of_gt hmr_pos]; ring
        have hsum02 : 1 / mr + (mr - 1 - (j.1 : ℝ)) / mr = 1 - (j.1 : ℝ) / mr := by
          field_simp [ne_of_gt hmr_pos]; ring
        have hsum01 : 1 / mr + ((j.1 : ℝ) + 1) / mr = 1 - (mr - 2 - (j.1 : ℝ)) / mr := by
          field_simp [ne_of_gt hmr_pos]; ring
        have hnn1 : (0 : ℝ) ≤ (j.1 : ℝ) / mr := div_nonneg (Nat.cast_nonneg _) (le_of_lt hmr_pos)
        have hnn2 : (0 : ℝ) ≤ (mr - 2 - (j.1 : ℝ)) / mr :=
          div_nonneg (by linarith) (le_of_lt hmr_pos)
        refine mem_closedInterior_of_nonneg T (by rw [Fin.sum_univ_three]; exact hw) fun k => ?_
        match k with
        | 0 => linarith
        | 1 => linarith
        | 2 => linarith
    · rintro ⟨w, hw, hwI, rfl⟩
      have hw0 : 0 ≤ w 0 := (hwI 0).1
      have hw1 : 0 ≤ w 1 := (hwI 1).1
      have hw2 : 0 ≤ w 2 := (hwI 2).1
      have hw1_le : w 1 ≤ 1 := (hwI 1).2
      have hcover : ∃ p : idx, Finset.univ.affineCombination ℝ T.points w ∈ (tile p).closedInterior := by
        by_cases hbig : 1 / mr ≤ w 0
        · refine ⟨Sum.inl (), ?_⟩
          rw [mem_subTri_closedInterior_pos T hs_big_pos haBig]
          refine ⟨w, hw, fun k => ?_, rfl⟩
          match k with
          | 0 => exact hbig
          | 1 => exact hw1
          | 2 => exact hw2
        · push Not at hbig
          by_cases hw1_eq : w 1 = 1
          · let jlast : Fin m := ⟨m - 1, by omega⟩
            refine ⟨Sum.inr (Sum.inl jlast), ?_⟩
            rw [mem_subTri_closedInterior_pos T hs_up_pos (haUp jlast)]
            have hjlast : (jlast.1 : ℝ) = mr - 1 := by
              dsimp only [jlast, mr]
              rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
            refine ⟨w, hw, fun k => ?_, rfl⟩
            match k with
            | 0 => exact hw0
            | 1 =>
              change (jlast.1 : ℝ) / mr ≤ w 1
              rw [hjlast, hw1_eq]
              exact (div_le_one hmr_pos).mpr (by linarith)
            | 2 =>
              change (mr - 1 - (jlast.1 : ℝ)) / mr ≤ w 2
              rw [hjlast]
              have hzero : (mr - 1 - (mr - 1)) / mr = 0 := by ring
              rw [hzero]
              exact hw2
          · have hw1_lt : w 1 < 1 := lt_of_le_of_ne hw1_le hw1_eq
            let jnat : ℕ := Nat.floor (mr * w 1)
            have hjnat_lt : jnat < m := by
              have hlt : mr * w 1 < mr := by nlinarith
              have hlt' : mr * w 1 < (m : ℝ) := hlt
              exact (Nat.floor_lt (mul_nonneg (le_of_lt hmr_pos) hw1)).mpr hlt'
            have hjnat_le : (jnat : ℝ) ≤ mr * w 1 :=
              Nat.floor_le (mul_nonneg (le_of_lt hmr_pos) hw1)
            have hjnat_gt : mr * w 1 < (jnat : ℝ) + 1 := Nat.lt_floor_add_one (mr * w 1)
            have hw1_lo : (jnat : ℝ) / mr ≤ w 1 := (div_le_iff₀ hmr_pos).mpr (by linarith)
            have hw1_hi : w 1 ≤ ((jnat : ℝ) + 1) / mr := (le_div_iff₀ hmr_pos).mpr (by linarith)
            by_cases hup : (mr - 1 - (jnat : ℝ)) / mr ≤ w 2
            · refine ⟨Sum.inr (Sum.inl ⟨jnat, hjnat_lt⟩), ?_⟩
              rw [mem_subTri_closedInterior_pos T hs_up_pos (haUp ⟨jnat, hjnat_lt⟩)]
              refine ⟨w, hw, fun k => ?_, rfl⟩
              match k with
              | 0 => exact hw0
              | 1 => exact hw1_lo
              | 2 => exact hup
            · push Not at hup
              have hjnat_lt' : jnat < m - 1 := by
                by_contra hge
                have hjeq : jnat = m - 1 := by omega
                have hjr : (jnat : ℝ) = mr - 1 := by
                  rw [hjeq, Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
                rw [hjr] at hup
                have hzero : (mr - 1 - (mr - 1)) / mr = 0 := by ring
                linarith
              refine ⟨Sum.inr (Sum.inr ⟨jnat, hjnat_lt'⟩), ?_⟩
              rw [mem_subTri_closedInterior_neg T hs_inv_neg (haInv ⟨jnat, hjnat_lt'⟩)]
              refine ⟨w, hw, fun k => ?_, rfl⟩
              match k with
              | 0 => exact le_of_lt hbig
              | 1 => exact hw1_hi
              | 2 => exact le_of_lt hup
      rcases hcover with ⟨p, hp⟩
      exact ⟨e.symm p, by simpa using hp⟩

private lemma strongSimiliCuttable_add_three {n : ℕ} (hn : 1 ≤ n) {T : Triangle ℝ ℝ²}
    (h : StrongSimiliCuttable n T) : StrongSimiliCuttable (n + 3) T := by
  rcases h with ⟨Ts, hsim, hint, hdisj, hunion⟩
  let i0 : Fin n := ⟨0, by omega⟩
  obtain ⟨Us, hUsim, hUint, hUdisj, hUunion⟩ := strongSimiliCuttable_two_mul 2 (le_refl 2) (Ts i0)
  let idx := Fin 4 ⊕ Fin (n - 1)
  let tile : idx → Triangle ℝ ℝ²
    | Sum.inl k => Us k
    | Sum.inr j => Ts ⟨j.1 + 1, by omega⟩
  have hcard : Fintype.card idx = n + 3 := by
    dsimp only [idx]
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    omega
  let e : Fin (n + 3) ≃ idx := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => tile (e i), ?_, ?_, ?_, ?_⟩
  · intro i
    dsimp only
    generalize e i = p
    rcases p with k | j
    · exact (hUsim k).trans (hsim i0)
    · exact hsim ⟨j.1 + 1, by omega⟩
  · intro i
    dsimp only
    generalize e i = p
    rcases p with k | j
    · exact (hUint k).trans (hint i0)
    · exact hint ⟨j.1 + 1, by omega⟩
  · intro i₁ i₂ hne
    dsimp only
    have he_ne : e i₁ ≠ e i₂ := fun h => hne (e.injective h)
    generalize e i₁ = p₁ at he_ne ⊢
    generalize e i₂ = p₂ at he_ne ⊢
    rcases p₁ with k₁ | j₁ <;> rcases p₂ with k₂ | j₂
    · have hk : k₁ ≠ k₂ := fun h => he_ne (by rw [h])
      exact hUdisj hk
    · have hne' : i0 ≠ ⟨j₂.1 + 1, by omega⟩ := by
        intro heq
        have : (0 : ℕ) = j₂.1 + 1 := congrArg Fin.val heq
        omega
      exact (hdisj hne').mono_left (hUint k₁)
    · have hne' : (⟨j₁.1 + 1, by omega⟩ : Fin n) ≠ i0 := by
        intro heq
        have : j₁.1 + 1 = 0 := congrArg Fin.val heq
        omega
      exact (hdisj hne').mono_right (hUint k₂)
    · have hj : (⟨j₁.1 + 1, by omega⟩ : Fin n) ≠ ⟨j₂.1 + 1, by omega⟩ := by
        intro heq
        have hval : j₁.1 = j₂.1 := by
          have : j₁.1 + 1 = j₂.1 + 1 := congrArg Fin.val heq
          omega
        exact he_ne (by rw [Fin.ext hval])
      exact hdisj hj
  · rw [← hunion]
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hx⟩
      generalize e i = p at hx
      rcases p with k | j
      · refine ⟨i0, ?_⟩
        rw [← hUunion]
        exact Set.mem_iUnion.mpr ⟨k, hx⟩
      · exact ⟨⟨j.1 + 1, by omega⟩, hx⟩
    · rintro ⟨j, hx⟩
      by_cases hj : j.1 = 0
      · have hjeq : j = i0 := Fin.ext hj
        rw [hjeq, ← hUunion] at hx
        rcases Set.mem_iUnion.mp hx with ⟨k, hk⟩
        exact ⟨e.symm (Sum.inl k), by simpa [tile] using hk⟩
      · let j' : Fin (n - 1) := ⟨j.1 - 1, by omega⟩
        have hjeq : (⟨j'.1 + 1, by omega⟩ : Fin n) = j := Fin.ext (by dsimp [j']; omega)
        refine ⟨e.symm (Sum.inr j'), ?_⟩
        simpa [tile, hjeq] using hx

end Erdos633SimiliCuttableProof

namespace Erdos633Imp

open Affine MeasureTheory Set Finset
open scoped EuclideanGeometry Similar NNReal Classical

/- ### Part 1: Generic triangle with ℤ-linearly independent angles -/

private lemma exists_indep_angles :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ α + β < Real.pi ∧
      ∀ p q r : ℤ, (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * Real.pi = 0 →
        p = 0 ∧ q = 0 ∧ r = 0 := by
  have hIoo_uncountable : ¬ (Set.Ioo (0 : ℝ) (Real.pi / 3)).Countable := by
    rw [← Cardinal.le_aleph0_iff_set_countable, Cardinal.mk_Ioo_real (by positivity), not_le]
    exact Cardinal.aleph0_lt_continuum
  let S₁ : Set ℝ := Set.range fun pq : ℤ × ℤ =>
    if pq.1 = 0 then (0 : ℝ) else -(pq.2 : ℝ) * Real.pi / (pq.1 : ℝ)
  have hS₁ : S₁.Countable := Set.countable_range _
  have hne₁ : (Set.Ioo (0 : ℝ) (Real.pi / 3) \ S₁).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty] at hempty
    exact hIoo_uncountable (hS₁.mono hempty)
  obtain ⟨α, hαIoo, hαS₁⟩ := hne₁
  let S₂ : Set ℝ := Set.range fun pqr : ℤ × ℤ × ℤ =>
    if pqr.2.1 = 0 then (0 : ℝ)
    else -((pqr.1 : ℝ) * α + (pqr.2.2 : ℝ) * Real.pi) / (pqr.2.1 : ℝ)
  have hS₂ : S₂.Countable := Set.countable_range _
  have hne₂ : (Set.Ioo (0 : ℝ) (Real.pi / 3) \ S₂).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty] at hempty
    exact hIoo_uncountable (hS₂.mono hempty)
  obtain ⟨β, hβIoo, hβS₂⟩ := hne₂
  refine ⟨α, β, hαIoo.1, hβIoo.1, by linarith [hαIoo.2, hβIoo.2, Real.pi_pos], ?_⟩
  intro p q r hlin
  have hq : q = 0 := by
    by_contra hq0
    apply hβS₂
    refine ⟨(p, q, r), ?_⟩
    simp only [hq0, ↓reduceIte]
    have hqR : (q : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hq0
    field_simp [hqR]
    linarith
  subst hq
  simp only [Int.cast_zero, zero_mul, add_zero] at hlin
  have hp : p = 0 := by
    by_contra hp0
    apply hαS₁
    refine ⟨(p, r), ?_⟩
    simp only [hp0, ↓reduceIte]
    have hpR : (p : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hp0
    field_simp [hpR]
    linarith
  subst hp
  simp only [Int.cast_zero, zero_mul, zero_add] at hlin
  have hr : r = 0 := by
    rcases mul_eq_zero.mp hlin with h | h
    · exact Int.cast_eq_zero.mp h
    · exact absurd h Real.pi_ne_zero
  exact ⟨rfl, rfl, hr⟩

private noncomputable def unitDir (θ : ℝ) : ℝ² := !₂[Real.cos θ, Real.sin θ]

private lemma norm_unitDir (θ : ℝ) : ‖unitDir θ‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp only [unitDir, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.norm_eq_abs, sq_abs]
  rw [Real.cos_sq_add_sin_sq, Real.sqrt_one]

private lemma inner_unitDir (θ φ : ℝ) :
    @inner ℝ ℝ² _ (unitDir θ) (unitDir φ) = Real.cos (θ - φ) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [unitDir, dotProduct, Fin.sum_univ_two, star_trivial,
    Matrix.cons_val_zero, Matrix.cons_val_one, Real.cos_sub]
  ring

private lemma angle_unitDir_zero (α : ℝ) (h0 : 0 ≤ α) (hpi : α ≤ Real.pi) :
    InnerProductGeometry.angle (unitDir 0) (unitDir α) = α := by
  rw [InnerProductGeometry.angle, inner_unitDir, norm_unitDir, norm_unitDir, mul_one, div_one,
    zero_sub, Real.cos_neg, Real.arccos_cos h0 hpi]

private noncomputable def triAngle (S : Triangle ℝ ℝ²) (k : Fin 3) : ℝ :=
  match k with
  | 0 => ∠ (S.points 1) (S.points 0) (S.points 2)
  | 1 => ∠ (S.points 2) (S.points 1) (S.points 0)
  | 2 => ∠ (S.points 0) (S.points 2) (S.points 1)

private lemma exists_indep_triangle :
    ∃ T : Triangle ℝ ℝ²,
      ∀ p q r : ℤ,
        (p : ℝ) * triAngle T 0 + (q : ℝ) * triAngle T 1 + (r : ℝ) * triAngle T 2 = 0 →
          p = 0 ∧ q = 0 ∧ r = 0 := by
  obtain ⟨α, β, hα, hβ, hαβ, hind⟩ := exists_indep_angles
  have hsin_ab : 0 < Real.sin (α + β) := Real.sin_pos_of_pos_of_lt_pi (by linarith) hαβ
  have hsin_a : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα (by linarith)
  have hsin_b : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi hβ (by linarith)
  let A : ℝ² := !₂[0, 0]
  let B : ℝ² := !₂[1, 0]
  let C : ℝ² := !₂[Real.sin β * Real.cos α / Real.sin (α + β),
                   Real.sin β * Real.sin α / Real.sin (α + β)]
  have hAff : AffineIndependent ℝ ![A, B, C] := by
    rw [affineIndependent_iff_linearIndependent_vsub ℝ _ (0 : Fin 3)]
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hsum : ∑ i : {i : Fin 3 // i ≠ 0}, g i • (![A, B, C] i.1 -ᵥ ![A, B, C] 0) =
        g ⟨1, by decide⟩ • (B - A) + g ⟨2, by decide⟩ • (C - A) := by
      have hcard : (Finset.univ : Finset {i : Fin 3 // i ≠ 0}) = {⟨1, by decide⟩, ⟨2, by decide⟩} := by
        ext ⟨x, hx⟩
        fin_cases x <;> simp at hx ⊢
      rw [hcard, Finset.sum_pair (by decide)]
      rfl
    rw [hsum] at hg
    have hc1 : g ⟨1, by decide⟩ * 1 + g ⟨2, by decide⟩ * (Real.sin β * Real.cos α / Real.sin (α + β)) = 0 := by
      have := congrArg (fun v : ℝ² => v.ofLp 0) hg
      simpa [A, B, C] using this
    have hc2 : g ⟨2, by decide⟩ * (Real.sin β * Real.sin α / Real.sin (α + β)) = 0 := by
      have := congrArg (fun v : ℝ² => v.ofLp 1) hg
      simpa [A, B, C] using this
    have hpos_cy : 0 < Real.sin β * Real.sin α / Real.sin (α + β) := by positivity
    have hg2 : g ⟨2, by decide⟩ = 0 := (mul_eq_zero.mp hc2).resolve_right hpos_cy.ne'
    have hg1 : g ⟨1, by decide⟩ = 0 := by rw [hg2] at hc1; linarith
    intro ⟨i, hi⟩
    fin_cases i
    · exact absurd rfl hi
    · exact hg1
    · exact hg2
  let T : Triangle ℝ ℝ² := ⟨![A, B, C], hAff⟩
  have hT0 : triAngle T 0 = α := by
    change ∠ B A C = α
    rw [EuclideanGeometry.angle]
    have hBA : B -ᵥ A = unitDir 0 := by
      ext i; fin_cases i <;> simp [A, B, unitDir]
    have hCA : C -ᵥ A = (Real.sin β / Real.sin (α + β)) • unitDir α := by
      ext i; fin_cases i <;> simp [A, C, unitDir] <;> ring
    rw [hBA, hCA, InnerProductGeometry.angle_smul_right_of_pos _ _ (by positivity)]
    exact angle_unitDir_zero α hα.le (by linarith)
  have hT1 : triAngle T 1 = β := by
    change ∠ C B A = β
    rw [EuclideanGeometry.angle_comm, EuclideanGeometry.angle]
    have hAB : A -ᵥ B = unitDir Real.pi := by
      ext i; fin_cases i <;> simp [A, B, unitDir]
    have hCB : C -ᵥ B = (Real.sin α / Real.sin (α + β)) • unitDir (Real.pi - β) := by
      ext i
      match i with
      | 0 =>
        change Real.sin β * Real.cos α / Real.sin (α + β) - 1 =
          (Real.sin α / Real.sin (α + β)) * Real.cos (Real.pi - β)
        rw [Real.cos_pi_sub]
        have hsin : Real.sin (α + β) = Real.sin α * Real.cos β + Real.cos α * Real.sin β :=
          Real.sin_add α β
        field_simp [hsin_ab.ne']
        linarith
      | 1 =>
        change Real.sin β * Real.sin α / Real.sin (α + β) - 0 =
          (Real.sin α / Real.sin (α + β)) * Real.sin (Real.pi - β)
        rw [Real.sin_pi_sub]
        ring
    rw [hAB, hCB, InnerProductGeometry.angle_smul_right_of_pos _ _ (by positivity),
      InnerProductGeometry.angle, inner_unitDir, norm_unitDir, norm_unitDir, mul_one, div_one]
    have : Real.pi - (Real.pi - β) = β := by ring
    rw [this, Real.arccos_cos hβ.le (by linarith)]
  have hT2 : triAngle T 2 = Real.pi - α - β := by
    change ∠ A C B = Real.pi - α - β
    have hAB_ne : B ≠ A := by
      intro h; have := congrArg (fun v : ℝ² => v.ofLp 0) h; simp [A, B] at this
    have hsum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi C hAB_ne
    have h0' : ∠ B A C = α := hT0
    have h1' : ∠ C B A = β := hT1
    rw [EuclideanGeometry.angle_comm A B C] at hsum
    linarith [EuclideanGeometry.angle_comm A C B, EuclideanGeometry.angle_comm B A C]
  refine ⟨T, fun p q r h => ?_⟩
  rw [hT0, hT1, hT2] at h
  have h' : ((p - r : ℤ) : ℝ) * α + ((q - r : ℤ) : ℝ) * β + (r : ℝ) * Real.pi = 0 := by
    push_cast; linarith
  obtain ⟨h1, h2, h3⟩ := hind (p - r) (q - r) r h'
  omega

/- ### Part 2: Barycentric coordinates in `ℝ²` -/

private noncomputable def det2 (u v : ℝ²) : ℝ :=
  u.ofLp 0 * v.ofLp 1 - u.ofLp 1 * v.ofLp 0

private lemma det2_ne_zero_of_triangle (S : Triangle ℝ ℝ²) :
    det2 (S.points 1 - S.points 0) (S.points 2 - S.points 0) ≠ 0 := by
  intro hdet
  have hli := (affineIndependent_iff_linearIndependent_vsub ℝ S.points (0 : Fin 3)).mp S.independent
  let u := S.points 1 - S.points 0
  let v := S.points 2 - S.points 0
  have hu : u ≠ 0 := by
    intro h0
    have := hli.ne_zero ⟨1, by decide⟩
    exact this h0
  -- Find nonzero linear combination
  have hcomb : ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ a • u + b • v = 0 := by
    by_cases hu0 : u.ofLp 0 ≠ 0
    · refine ⟨v.ofLp 0, -u.ofLp 0, Or.inr (neg_ne_zero.mpr hu0), ?_⟩
      ext i; match i with
      | 0 => change v.ofLp 0 * u.ofLp 0 + -u.ofLp 0 * v.ofLp 0 = 0; ring
      | 1 => change v.ofLp 0 * u.ofLp 1 + -u.ofLp 0 * v.ofLp 1 = 0
             have : u.ofLp 0 * v.ofLp 1 - u.ofLp 1 * v.ofLp 0 = 0 := hdet
             linarith
    · push_neg at hu0
      have hu1 : u.ofLp 1 ≠ 0 := by
        intro h1; apply hu; ext i; match i with | 0 => exact hu0 | 1 => exact h1
      refine ⟨v.ofLp 1, -u.ofLp 1, Or.inr (neg_ne_zero.mpr hu1), ?_⟩
      ext i; match i with
      | 0 => change v.ofLp 1 * u.ofLp 0 + -u.ofLp 1 * v.ofLp 0 = 0
             have : u.ofLp 0 * v.ofLp 1 - u.ofLp 1 * v.ofLp 0 = 0 := hdet
             linarith
      | 1 => change v.ofLp 1 * u.ofLp 1 + -u.ofLp 1 * v.ofLp 1 = 0; ring
  obtain ⟨a, b, hab, hzero⟩ := hcomb
  let g : {i : Fin 3 // i ≠ 0} → ℝ := fun i => if i.1 = 1 then a else b
  have hsum : ∑ i : {i : Fin 3 // i ≠ 0}, g i • (S.points i.1 -ᵥ S.points 0) = 0 := by
    have hcard : (Finset.univ : Finset {i : Fin 3 // i ≠ 0}) = {⟨1, by decide⟩, ⟨2, by decide⟩} := by
      ext ⟨x, hx⟩; fin_cases x <;> simp at hx ⊢
    rw [hcard, Finset.sum_pair (by decide)]
    simpa [g, u, v] using hzero
  have h0 := Fintype.linearIndependent_iff.mp hli g hsum
  have ha0 : a = 0 := by simpa [g] using h0 ⟨1, by decide⟩
  have hb0 : b = 0 := by simpa [g] using h0 ⟨2, by decide⟩
  rcases hab with ha | hb <;> contradiction

/-- Explicit barycentric coordinates for any point `x : ℝ²` relative to a triangle `S`. -/
private noncomputable def bary (S : Triangle ℝ ℝ²) (x : ℝ²) : Fin 3 → ℝ :=
  let u := S.points 1 - S.points 0
  let v := S.points 2 - S.points 0
  let d := det2 u v
  let w1 := det2 (x - S.points 0) v / d
  let w2 := det2 u (x - S.points 0) / d
  ![1 - w1 - w2, w1, w2]

/-- Linear (directional) part of `bary S`: `bary S (P + t • dir) = bary S P + t * dbary S dir`. -/
private noncomputable def dbary (S : Triangle ℝ ℝ²) (dir : ℝ²) : Fin 3 → ℝ :=
  let u := S.points 1 - S.points 0
  let v := S.points 2 - S.points 0
  let d := det2 u v
  let d1 := det2 dir v / d
  let d2 := det2 u dir / d
  ![-d1 - d2, d1, d2]

private lemma bary_sum (S : Triangle ℝ ℝ²) (x : ℝ²) : ∑ i : Fin 3, bary S x i = 1 := by
  rw [Fin.sum_univ_three]
  dsimp [bary]; ring

private lemma dbary_sum (S : Triangle ℝ ℝ²) (dir : ℝ²) : ∑ i : Fin 3, dbary S dir i = 0 := by
  rw [Fin.sum_univ_three]
  dsimp [dbary]; ring

private lemma bary_add_smul (S : Triangle ℝ ℝ²) (P dir : ℝ²) (t : ℝ) (k : Fin 3) :
    bary S (P + t • dir) k = bary S P k + t * dbary S dir k := by
  have hd1 : det2 (P + t • dir - S.points 0) (S.points 2 - S.points 0) =
      det2 (P - S.points 0) (S.points 2 - S.points 0) +
      t * det2 dir (S.points 2 - S.points 0) := by
    simp only [det2, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have hd2 : det2 (S.points 1 - S.points 0) (P + t • dir - S.points 0) =
      det2 (S.points 1 - S.points 0) (P - S.points 0) +
      t * det2 (S.points 1 - S.points 0) dir := by
    simp only [det2, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
  match k with
  | 0 => dsimp [bary, dbary]; rw [hd1, hd2]; ring
  | 1 => dsimp [bary, dbary]; rw [hd1]; ring
  | 2 => dsimp [bary, dbary]; rw [hd2]; ring

private lemma affineCombination_bary (S : Triangle ℝ ℝ²) (x : ℝ²) :
    Finset.univ.affineCombination ℝ S.points (bary S x) = x := by
  rw [Finset.affineCombination_eq_linear_combination _ _ _ (bary_sum S x)]
  set d := det2 (S.points 1 - S.points 0) (S.points 2 - S.points 0)
  have hd : d ≠ 0 := det2_ne_zero_of_triangle S
  ext i
  rw [Fin.sum_univ_three]
  match i with
  | 0 =>
    change bary S x 0 * (S.points 0).ofLp 0 + bary S x 1 * (S.points 1).ofLp 0 +
        bary S x 2 * (S.points 2).ofLp 0 = x.ofLp 0
    dsimp only [bary, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
    change (1 - det2 (x - S.points 0) (S.points 2 - S.points 0) / d -
        det2 (S.points 1 - S.points 0) (x - S.points 0) / d) * (S.points 0).ofLp 0 +
        (det2 (x - S.points 0) (S.points 2 - S.points 0) / d) * (S.points 1).ofLp 0 +
        (det2 (S.points 1 - S.points 0) (x - S.points 0) / d) * (S.points 2).ofLp 0 = x.ofLp 0
    field_simp [hd]
    simp only [d, det2, PiLp.sub_apply]; ring
  | 1 =>
    change bary S x 0 * (S.points 0).ofLp 1 + bary S x 1 * (S.points 1).ofLp 1 +
        bary S x 2 * (S.points 2).ofLp 1 = x.ofLp 1
    dsimp only [bary, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
    change (1 - det2 (x - S.points 0) (S.points 2 - S.points 0) / d -
        det2 (S.points 1 - S.points 0) (x - S.points 0) / d) * (S.points 0).ofLp 1 +
        (det2 (x - S.points 0) (S.points 2 - S.points 0) / d) * (S.points 1).ofLp 1 +
        (det2 (S.points 1 - S.points 0) (x - S.points 0) / d) * (S.points 2).ofLp 1 = x.ofLp 1
    field_simp [hd]
    simp only [d, det2, PiLp.sub_apply]; ring

private lemma bary_unique (S : Triangle ℝ ℝ²) {w : Fin 3 → ℝ} (hw : ∑ i, w i = 1)
    {x : ℝ²} (hx : Finset.univ.affineCombination ℝ S.points w = x) : w = bary S x := by
  have hind := S.independent.indicator_eq_of_affineCombination_eq
    Finset.univ Finset.univ w (bary S x) hw (bary_sum S x) (hx.trans (affineCombination_bary S x).symm)
  simpa using hind

private lemma mem_interior_iff_bary (S : Triangle ℝ ℝ²) (x : ℝ²) :
    x ∈ S.interior ↔ ∀ i : Fin 3, 0 < bary S x i := by
  change x ∈ S.setInterior (Set.Ioo 0 1) ↔ _
  constructor
  · rintro ⟨w, hw, hwI, rfl⟩
    rw [← bary_unique S hw rfl]
    intro i; exact (hwI i).1
  · intro hpos
    refine ⟨bary S x, bary_sum S x, fun i => ⟨hpos i, ?_⟩, affineCombination_bary S x⟩
    have hsum := bary_sum S x
    rw [Fin.sum_univ_three] at hsum
    have h0 := hpos 0; have h1 := hpos 1; have h2 := hpos 2
    match i with
    | 0 => linarith
    | 1 => linarith
    | 2 => linarith

private lemma mem_closedInterior_iff_bary (S : Triangle ℝ ℝ²) (x : ℝ²) :
    x ∈ S.closedInterior ↔ ∀ i : Fin 3, 0 ≤ bary S x i := by
  change x ∈ S.setInterior (Set.Icc 0 1) ↔ _
  constructor
  · rintro ⟨w, hw, hwI, rfl⟩
    rw [← bary_unique S hw rfl]
    intro i; exact (hwI i).1
  · intro hnn
    refine ⟨bary S x, bary_sum S x, fun i => ⟨hnn i, ?_⟩, affineCombination_bary S x⟩
    have hsum := bary_sum S x
    rw [Fin.sum_univ_three] at hsum
    have h0 := hnn 0; have h1 := hnn 1; have h2 := hnn 2
    match i with
    | 0 => linarith
    | 1 => linarith
    | 2 => linarith

private lemma bary_point (S : Triangle ℝ ℝ²) (k i : Fin 3) :
    bary S (S.points k) i = if i = k then 1 else 0 := by
  have hw : ∑ j : Fin 3, (if j = k then (1 : ℝ) else 0) = 1 := by simp
  have hx : Finset.univ.affineCombination ℝ S.points (fun j => if j = k then (1 : ℝ) else 0) =
      S.points k := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hw]
    simp
  exact congrFun (bary_unique S hw hx).symm i

private lemma dbary_vsub (S : Triangle ℝ ℝ²) (k j : Fin 3) :
    dbary S (S.points j - S.points k) = fun i => (if i = j then 1 else 0) - (if i = k then 1 else 0) := by
  funext i
  have h := bary_add_smul S (S.points k) (S.points j - S.points k) 1 i
  simp only [one_smul, add_sub_cancel, one_mul, bary_point] at h
  linarith

private lemma dir_eq_sum_dbary (S : Triangle ℝ ℝ²) (dir : ℝ²) :
    dir = dbary S dir 1 • (S.points 1 - S.points 0) +
          dbary S dir 2 • (S.points 2 - S.points 0) := by
  have h := affineCombination_bary S (S.points 0 + dir)
  rw [Finset.affineCombination_eq_linear_combination _ _ _ (bary_sum S _)] at h
  have h0 := bary_add_smul S (S.points 0) dir 1 0
  have h1 := bary_add_smul S (S.points 0) dir 1 1
  have h2 := bary_add_smul S (S.points 0) dir 1 2
  simp only [one_smul, one_mul, bary_point] at h0 h1 h2
  have hsum := dbary_sum S dir
  rw [Fin.sum_univ_three] at hsum
  rw [Fin.sum_univ_three, h0, h1, h2] at h
  simp only [↓reduceIte, zero_add] at h
  have h01 : (1 : Fin 3) ≠ 0 := by decide
  have h02 : (2 : Fin 3) ≠ 0 := by decide
  simp only [h01, h02, ↓reduceIte, zero_add] at h
  ext c
  have hc := congrArg (fun v : ℝ² => v.ofLp c) h
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hc ⊢
  linear_combination -hc + hsum * (S.points 0).ofLp c

private lemma dir_eq_sum_dbary_at (S : Triangle ℝ ℝ²) (k j₁ j₂ : Fin 3)
    (h1 : j₁ ≠ k) (h2 : j₂ ≠ k) (h12 : j₁ ≠ j₂) (dir : ℝ²) :
    dir = dbary S dir j₁ • (S.points j₁ - S.points k) +
          dbary S dir j₂ • (S.points j₂ - S.points k) := by
  have h := affineCombination_bary S (S.points k + dir)
  rw [Finset.affineCombination_eq_linear_combination _ _ _ (bary_sum S _)] at h
  have hsum := dbary_sum S dir
  have huniv : (Finset.univ : Finset (Fin 3)) = {k, j₁, j₂} := by
    ext x; fin_cases k <;> fin_cases j₁ <;> fin_cases j₂ <;> fin_cases x <;> simp_all
  rw [huniv] at h hsum
  have hk1 : k ∉ ({j₁, j₂} : Finset (Fin 3)) := by simp [h1.symm, h2.symm]
  have h12' : j₁ ∉ ({j₂} : Finset (Fin 3)) := by simp [h12]
  rw [Finset.sum_insert hk1, Finset.sum_insert h12', Finset.sum_singleton] at h hsum
  have hbk := bary_add_smul S (S.points k) dir 1 k
  have hbj1 := bary_add_smul S (S.points k) dir 1 j₁
  have hbj2 := bary_add_smul S (S.points k) dir 1 j₂
  simp only [one_smul, one_mul, bary_point, ↓reduceIte, h1, h2, zero_add] at hbk hbj1 hbj2
  rw [hbk, hbj1, hbj2] at h
  ext c
  have hc := congrArg (fun v : ℝ² => v.ofLp c) h
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hc ⊢
  linear_combination -hc + hsum * (S.points k).ofLp c

private lemma det2_unitDir (a b : ℝ) : det2 (unitDir a) (unitDir b) = Real.sin (b - a) := by
  simp only [det2, unitDir, Matrix.cons_val_zero, Matrix.cons_val_one, Real.sin_sub]
  ring

private lemma det2_smul_left (c : ℝ) (u v : ℝ²) : det2 (c • u) v = c * det2 u v := by
  simp only [det2, PiLp.smul_apply, smul_eq_mul]; ring

private lemma det2_smul_right (c : ℝ) (u v : ℝ²) : det2 u (c • v) = c * det2 u v := by
  simp only [det2, PiLp.smul_apply, smul_eq_mul]; ring

private lemma det2_add_left (u₁ u₂ v : ℝ²) : det2 (u₁ + u₂) v = det2 u₁ v + det2 u₂ v := by
  simp only [det2, PiLp.add_apply]; ring

private lemma det2_add_right (u v₁ v₂ : ℝ²) : det2 u (v₁ + v₂) = det2 u v₁ + det2 u v₂ := by
  simp only [det2, PiLp.add_apply]; ring

private lemma det2_self (u : ℝ²) : det2 u u = 0 := by
  simp only [det2]; ring

private lemma det2_eq_inner (v u : ℝ²) : det2 u v = @inner ℝ ℝ² _ !₂[v.ofLp 1, -v.ofLp 0] u := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [det2, dotProduct, Fin.sum_univ_two, star_trivial,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

private noncomputable def gradBary (S : Triangle ℝ ℝ²) (k : Fin 3) : ℝ² :=
  let u := S.points 1 - S.points 0
  let v := S.points 2 - S.points 0
  let d := det2 u v
  let g1 : ℝ² := (1 / d) • !₂[v.ofLp 1, -v.ofLp 0]
  let g2 : ℝ² := (1 / d) • !₂[-u.ofLp 1, u.ofLp 0]
  match k with
  | 0 => -(g1 + g2)
  | 1 => g1
  | 2 => g2

private lemma dbary_eq_inner_gradBary (S : Triangle ℝ ℝ²) (k : Fin 3) (dir : ℝ²) :
    dbary S dir k = @inner ℝ ℝ² _ (gradBary S k) dir := by
  have hg1 : det2 dir (S.points 2 - S.points 0) /
      det2 (S.points 1 - S.points 0) (S.points 2 - S.points 0) =
      @inner ℝ ℝ² _ (gradBary S 1) dir := by
    simp only [gradBary, real_inner_smul_left, ← det2_eq_inner]
    ring
  have hg2 : det2 (S.points 1 - S.points 0) dir /
      det2 (S.points 1 - S.points 0) (S.points 2 - S.points 0) =
      @inner ℝ ℝ² _ (gradBary S 2) dir := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [gradBary, det2, dotProduct, Fin.sum_univ_two, star_trivial,
      PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  fin_cases k
  · simp only [dbary, gradBary, Matrix.cons_val_zero, inner_neg_left, inner_add_left]
    change -(det2 dir (S.points 2 - S.points 0) /
        det2 (S.points 1 - S.points 0) (S.points 2 - S.points 0)) -
      det2 (S.points 1 - S.points 0) dir /
        det2 (S.points 1 - S.points 0) (S.points 2 - S.points 0) =
      -(@inner ℝ ℝ² _ (gradBary S 1) dir + @inner ℝ ℝ² _ (gradBary S 2) dir)
    linarith [hg1, hg2]
  · simpa [dbary] using hg1
  · simpa [dbary] using hg2

private lemma gradBary_ne_zero (S : Triangle ℝ ℝ²) (k : Fin 3) : gradBary S k ≠ 0 := by
  intro h0
  obtain ⟨j, hjk⟩ : ∃ j : Fin 3, j ≠ k := by
    fin_cases k
    · exact ⟨1, by decide⟩
    · exact ⟨0, by decide⟩
    · exact ⟨0, by decide⟩
  have h1 := dbary_vsub S j k
  have h2 := congrFun h1 k
  simp only [↓reduceIte, hjk.symm, sub_zero] at h2
  rw [dbary_eq_inner_gradBary, h0, inner_zero_left] at h2
  norm_num at h2

/- ### Part 3: Circular arcs, `dirSet`, and angular measure conservation -/

private lemma exists_polar (v : ℝ²) (hv : v ≠ 0) : ∃ φ : ℝ, v = ‖v‖ • unitDir φ := by
  let z : ℂ := ⟨v.ofLp 0, v.ofLp 1⟩
  have hz : z ≠ 0 := by
    intro h
    apply hv
    ext i; match i with
    | 0 => exact congrArg Complex.re h
    | 1 => exact congrArg Complex.im h
  have hnorm : ‖z‖ = ‖v‖ := by
    rw [EuclideanSpace.norm_eq, Complex.norm_def, Complex.normSq_apply]
    simp only [z, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
    simp only [sq]
  refine ⟨z.arg, ?_⟩
  ext i
  match i with
  | 0 =>
    change v.ofLp 0 = ‖v‖ * Real.cos z.arg
    rw [← hnorm, Complex.cos_arg hz, mul_div_cancel₀ _ (norm_ne_zero_iff.mpr hz)]
  | 1 =>
    change v.ofLp 1 = ‖v‖ * Real.sin z.arg
    rw [← hnorm, Complex.sin_arg, mul_div_cancel₀ _ (norm_ne_zero_iff.mpr hz)]

private def arc (a b : ℝ) : Set ℝ :=
  {θ ∈ Set.Ico 0 (2 * Real.pi) | ∃ k : ℤ, θ + (k : ℝ) * (2 * Real.pi) ∈ Set.Ioo a b}

private lemma measurableSet_arc (a b : ℝ) : MeasurableSet (arc a b) := by
  have heq : arc a b = Set.Ico 0 (2 * Real.pi) ∩
      ⋃ k : ℤ, (fun θ : ℝ => θ + (k : ℝ) * (2 * Real.pi)) ⁻¹' Set.Ioo a b := by
    ext θ; simp only [arc, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_preimage]
  rw [heq]
  refine measurableSet_Ico.inter (MeasurableSet.iUnion fun k => ?_)
  exact measurableSet_Ioo.preimage (measurable_id.add_const _)

private lemma arc_shift_int (a b : ℝ) (m : ℤ) :
    arc (a + (m : ℝ) * (2 * Real.pi)) (b + (m : ℝ) * (2 * Real.pi)) = arc a b := by
  ext θ
  simp only [arc, Set.mem_setOf_eq, Set.mem_Ioo]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨k, h1, h2⟩
    refine ⟨k - m, ?_, ?_⟩ <;> push_cast <;> linarith
  · rintro ⟨k, h1, h2⟩
    refine ⟨k + m, ?_, ?_⟩ <;> push_cast <;> linarith

private lemma volume_arc (a b : ℝ) (hab : a ≤ b) (hlen : b - a ≤ 2 * Real.pi) :
    volume (arc a b) = ENNReal.ofReal (b - a) := by
  have h2pi : 0 < 2 * Real.pi := by positivity
  let m : ℤ := ⌊a / (2 * Real.pi)⌋
  let a' : ℝ := a - (m : ℝ) * (2 * Real.pi)
  let b' : ℝ := b - (m : ℝ) * (2 * Real.pi)
  have ha'_nn : 0 ≤ a' := by
    have := Int.floor_le (a / (2 * Real.pi))
    have : (m : ℝ) * (2 * Real.pi) ≤ a := (le_div_iff₀ h2pi).mp this
    dsimp [a']; linarith
  have ha'_lt : a' < 2 * Real.pi := by
    have := Int.lt_floor_add_one (a / (2 * Real.pi))
    have : a < ((m : ℝ) + 1) * (2 * Real.pi) := (div_lt_iff₀ h2pi).mp this
    dsimp [a']; linarith
  have harc : arc a b = arc a' b' := by
    have h1 : a = a' + (m : ℝ) * (2 * Real.pi) := by dsimp [a']; ring
    have h2 : b = b' + (m : ℝ) * (2 * Real.pi) := by dsimp [b']; ring
    conv_lhs => rw [h1, h2]
    exact arc_shift_int a' b' m
  have hba : b' - a' = b - a := by dsimp [a', b']; ring
  rw [harc, ← hba]
  by_cases hb' : b' ≤ 2 * Real.pi
  · have heq : arc a' b' = Set.Ioo a' b' := by
      ext θ
      simp only [arc, Set.mem_setOf_eq, Set.mem_Ico, Set.mem_Ioo]
      constructor
      · rintro ⟨⟨hθ0, hθ2⟩, ⟨k, hk1, hk2⟩⟩
        have hk0 : k = 0 := by
          by_contra hk
          rcases lt_or_gt_of_ne hk with hneg | hpos
          · have : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hneg
            nlinarith
          · have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hpos
            nlinarith
        subst hk0
        simp only [Int.cast_zero, zero_mul, add_zero] at hk1 hk2
        exact ⟨hk1, hk2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨by linarith, by linarith⟩, ⟨0, by simp [h1, h2]⟩⟩
    rw [heq, Real.volume_Ioo]
  · push_neg at hb'
    have heq : arc a' b' = Set.Ioo a' (2 * Real.pi) ∪ Set.Ico 0 (b' - 2 * Real.pi) := by
      ext θ
      simp only [arc, Set.mem_setOf_eq, Set.mem_Ico, Set.mem_Ioo, Set.mem_union]
      constructor
      · rintro ⟨⟨hθ0, hθ2⟩, ⟨k, hk1, hk2⟩⟩
        have hk01 : k = 0 ∨ k = 1 := by
          have hge : 0 ≤ k := by
            by_contra hlt; push_neg at hlt
            have : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hlt
            nlinarith
          have hle : k ≤ 1 := by
            by_contra hgt; push_neg at hgt
            have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hgt
            nlinarith
          omega
        rcases hk01 with rfl | rfl
        · simp only [Int.cast_zero, zero_mul, add_zero] at hk1 hk2
          exact Or.inl ⟨hk1, hθ2⟩
        · simp only [Int.cast_one, one_mul] at hk1 hk2
          exact Or.inr ⟨hθ0, by linarith⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨⟨by linarith, h2⟩, ⟨0, by simp [h1]; linarith⟩⟩
        · refine ⟨⟨h1, by linarith⟩, ⟨1, ?_, ?_⟩⟩ <;> simp <;> linarith
    have hdisj : Disjoint (Set.Ioo a' (2 * Real.pi)) (Set.Ico 0 (b' - 2 * Real.pi)) := by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      simp only [Set.mem_Ioo, Set.mem_Ico] at hx1 hx2
      linarith
    rw [heq, measure_union hdisj measurableSet_Ico, Real.volume_Ioo, Real.volume_Ico,
      ← ENNReal.ofReal_add (by linarith) (by linarith)]
    congr 1; ring

private lemma sin_pos_iff_exists_int_Ioo (x : ℝ) :
    0 < Real.sin x ↔ ∃ k : ℤ, x + (k : ℝ) * (2 * Real.pi) ∈ Set.Ioo 0 Real.pi := by
  have h2pi : 0 < 2 * Real.pi := by positivity
  let m : ℤ := ⌊x / (2 * Real.pi)⌋
  let x' : ℝ := x - (m : ℝ) * (2 * Real.pi)
  have hx'0 : 0 ≤ x' := by
    have := (le_div_iff₀ h2pi).mp (Int.floor_le (x / (2 * Real.pi)))
    dsimp [x']; linarith
  have hx'2 : x' < 2 * Real.pi := by
    have := (div_lt_iff₀ h2pi).mp (Int.lt_floor_add_one (x / (2 * Real.pi)))
    dsimp [x']; linarith
  have hsin : Real.sin x = Real.sin x' := by
    have : x = x' + (m : ℝ) * (2 * Real.pi) := by dsimp [x']; ring
    rw [this, Real.sin_add_int_mul_two_pi]
  rw [hsin]
  constructor
  · intro hpos
    have hlt_pi : x' < Real.pi := by
      by_contra hge; push_neg at hge
      have hneg : Real.sin x' ≤ 0 := by
        have := Real.sin_nonneg_of_nonneg_of_le_pi (show 0 ≤ x' - Real.pi by linarith)
          (show x' - Real.pi ≤ Real.pi by linarith)
        rw [Real.sin_sub_pi] at this
        linarith
      linarith
    have hgt_0 : 0 < x' := by
      rcases eq_or_lt_of_le hx'0 with h0 | h0
      · rw [← h0, Real.sin_zero] at hpos; linarith
      · exact h0
    exact ⟨-m, by push_cast; simp only [Set.mem_Ioo]; dsimp [x'] at hgt_0 hlt_pi; constructor <;> linarith⟩
  · rintro ⟨k, hk1, hk2⟩
    have hkm : k = -m := by
      have : x + (k : ℝ) * (2 * Real.pi) = x' + ((k + m : ℤ) : ℝ) * (2 * Real.pi) := by
        dsimp [x']; push_cast; ring
      rw [this] at hk1 hk2
      have h0 : k + m = 0 := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hneg | hpos
        · have : ((k + m : ℤ) : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hneg
          nlinarith
        · have : (1 : ℝ) ≤ ((k + m : ℤ) : ℝ) := by exact_mod_cast hpos
          nlinarith
      omega
    subst hkm
    have hx'Ioo : x' ∈ Set.Ioo 0 Real.pi := by
      simp only [Set.mem_Ioo] at hk1 hk2 ⊢
      push_cast at hk1 hk2
      dsimp [x']; constructor <;> linarith
    exact Real.sin_pos_of_pos_of_lt_pi hx'Ioo.1 hx'Ioo.2

private lemma mem_arc_half_iff_cos_pos (φ θ : ℝ) (hθ : θ ∈ Set.Ico 0 (2 * Real.pi)) :
    θ ∈ arc (φ - Real.pi / 2) (φ + Real.pi / 2) ↔ 0 < Real.cos (θ - φ) := by
  have hcos : Real.cos (θ - φ) = Real.sin (θ - (φ - Real.pi / 2)) := by
    have : θ - (φ - Real.pi / 2) = (θ - φ) + Real.pi / 2 := by ring
    rw [this, Real.sin_add_pi_div_two]
  rw [hcos, sin_pos_iff_exists_int_Ioo]
  simp only [arc, Set.mem_setOf_eq, hθ, true_and, Set.mem_Ioo]
  refine exists_congr fun k => ?_
  constructor <;> intro ⟨h1, h2⟩ <;> constructor <;> linarith

private lemma mem_arc_iff_sin_pos (φ α θ : ℝ) (h0 : 0 < α) (hpi : α < Real.pi)
    (hθ : θ ∈ Set.Ico 0 (2 * Real.pi)) :
    θ ∈ arc φ (φ + α) ↔ 0 < Real.sin (θ - φ) ∧ 0 < Real.sin (φ + α - θ) := by
  constructor
  · rintro ⟨_, k, hk1, hk2⟩
    constructor
    · rw [sin_pos_iff_exists_int_Ioo]
      exact ⟨k, by constructor <;> linarith⟩
    · rw [sin_pos_iff_exists_int_Ioo]
      exact ⟨-k, by push_cast; constructor <;> linarith⟩
  · rintro ⟨hs1, hs2⟩
    obtain ⟨k, hk1, hk2⟩ := (sin_pos_iff_exists_int_Ioo _).mp hs1
    refine ⟨hθ, k, by linarith, ?_⟩
    have hsin2 : Real.sin (φ + α - θ) = Real.sin (α - (θ - φ + (k : ℝ) * (2 * Real.pi))) := by
      have : φ + α - θ = (α - (θ - φ + (k : ℝ) * (2 * Real.pi))) + (k : ℝ) * (2 * Real.pi) := by ring
      rw [this, Real.sin_add_int_mul_two_pi]
    rw [hsin2] at hs2
    by_contra hge; push_neg at hge
    have hle0 : Real.sin (α - (θ - φ + (k : ℝ) * (2 * Real.pi))) ≤ 0 := by
      have hneg := Real.sin_nonneg_of_nonneg_of_le_pi
        (show 0 ≤ (θ - φ + (k : ℝ) * (2 * Real.pi)) - α by linarith)
        (show (θ - φ + (k : ℝ) * (2 * Real.pi)) - α ≤ Real.pi by linarith)
      rw [show (θ - φ + (k : ℝ) * (2 * Real.pi)) - α = -(α - (θ - φ + (k : ℝ) * (2 * Real.pi))) by ring,
        Real.sin_neg] at hneg
      linarith
    linarith

private lemma finite_sin_zero_Ico (φ : ℝ) :
    {θ ∈ Set.Ico 0 (2 * Real.pi) | Real.sin (θ - φ) = 0}.Finite := by
  have hsub : {θ ∈ Set.Ico 0 (2 * Real.pi) | Real.sin (θ - φ) = 0} ⊆
      (fun k : ℤ => φ + (k : ℝ) * Real.pi) ''
        (Set.Icc (⌊(-φ) / Real.pi⌋ - 1) (⌈(2 * Real.pi - φ) / Real.pi⌉ + 1)) := by
    intro θ ⟨⟨hθ0, hθ2⟩, hsin⟩
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hsin
    refine ⟨k, ⟨?_, ?_⟩, by linarith⟩
    · have : (-φ) / Real.pi ≤ (k : ℝ) := by
        rw [div_le_iff₀ Real.pi_pos]; linarith
      have : ⌊(-φ) / Real.pi⌋ ≤ k := Int.floor_le_iff.mpr (by linarith)
      omega
    · have : (k : ℝ) ≤ (2 * Real.pi - φ) / Real.pi := by
        rw [le_div_iff₀ Real.pi_pos]; linarith
      have : k ≤ ⌈(2 * Real.pi - φ) / Real.pi⌉ := Int.le_ceil_iff.mpr (by linarith)
      omega
  exact ((Set.finite_Icc _ _).image _).subset hsub

private def dirSet (S : Triangle ℝ ℝ²) (P : ℝ²) : Set ℝ :=
  {θ ∈ Set.Ico 0 (2 * Real.pi) | ∃ r : ℝ, 0 < r ∧ ∀ t ∈ Set.Ioo 0 r, P + t • unitDir θ ∈ S.interior}

private lemma mem_dirSet_iff (S : Triangle ℝ ℝ²) (P : ℝ²) (θ : ℝ) :
    θ ∈ dirSet S P ↔ θ ∈ Set.Ico 0 (2 * Real.pi) ∧
      ∀ k : Fin 3, 0 < bary S P k ∨ (bary S P k = 0 ∧ 0 < dbary S (unitDir θ) k) := by
  simp only [dirSet, Set.mem_setOf_eq]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨r, hr, h⟩ k
    have hpos : ∀ t ∈ Set.Ioo 0 r, 0 < bary S P k + t * dbary S (unitDir θ) k := fun t ht => by
      have := (mem_interior_iff_bary S _).mp (h t ht) k
      rwa [bary_add_smul] at this
    by_cases hb : 0 < bary S P k
    · exact Or.inl hb
    · push_neg at hb
      have hge0 : 0 ≤ bary S P k := by
        by_contra hlt; push_neg at hlt
        let d := dbary S (unitDir θ) k
        let t := min (r / 2) (if 0 < d then (-bary S P k) / (2 * d) else r / 2)
        have ht0 : 0 < t := by
          dsimp [t]; apply lt_min (by positivity)
          split_ifs with hd
          · exact div_pos (neg_pos.mpr hlt) (by positivity)
          · positivity
        have htr : t < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
        have ht1 := hpos t ⟨ht0, htr⟩
        by_cases hd : 0 < d
        · have htle : t ≤ (-bary S P k) / (2 * d) := by
            refine (min_le_right _ _).trans ?_; simp [hd]
          have : t * d ≤ (-bary S P k) / 2 := by
            have := mul_le_mul_of_nonneg_right htle hd.le
            have hsimp : (-bary S P k) / (2 * d) * d = (-bary S P k) / 2 := by
              field_simp [hd.ne']
            linarith
          linarith
        · push_neg at hd
          nlinarith
      have hbe0 : bary S P k = 0 := le_antisymm hb hge0
      right
      refine ⟨hbe0, ?_⟩
      have := hpos (r / 2) ⟨by positivity, by linarith⟩
      rw [hbe0, zero_add] at this
      nlinarith
  · intro hall
    have hex : ∀ k : Fin 3, ∃ r : ℝ, 0 < r ∧ ∀ t ∈ Set.Ioo 0 r, 0 < bary S P k + t * dbary S (unitDir θ) k := by
      intro k
      rcases hall k with hpos | ⟨h0, hd⟩
      · by_cases hneg : dbary S (unitDir θ) k < 0
        · have hneg' : 0 < -dbary S (unitDir θ) k := neg_pos.mpr hneg
          refine ⟨bary S P k / (2 * (-dbary S (unitDir θ) k)), by positivity, fun t ht => ?_⟩
          have : t * (-dbary S (unitDir θ) k) < bary S P k / 2 := by
            have := mul_lt_mul_of_pos_right ht.2 hneg'
            have hsimp : bary S P k / (2 * -dbary S (unitDir θ) k) * -dbary S (unitDir θ) k =
                bary S P k / 2 := by
              have hdne : dbary S (unitDir θ) k ≠ 0 := hneg.ne
              field_simp [hdne]
            linarith
          linarith
        · push_neg at hneg
          exact ⟨1, zero_lt_one, fun t ht => by nlinarith [ht.1]⟩
      · exact ⟨1, zero_lt_one, fun t ht => by rw [h0, zero_add]; exact mul_pos ht.1 hd⟩
    choose rk hrk hpk using hex
    refine ⟨min (rk 0) (min (rk 1) (rk 2)), lt_min (hrk 0) (lt_min (hrk 1) (hrk 2)), fun t ht => ?_⟩
    rw [mem_interior_iff_bary]
    intro k
    rw [bary_add_smul]
    apply hpk k t ⟨ht.1, ?_⟩
    match k with
    | 0 => exact lt_of_lt_of_le ht.2 (min_le_left _ _)
    | 1 => exact lt_of_lt_of_le ht.2 ((min_le_right _ _).trans (min_le_left _ _))
    | 2 => exact lt_of_lt_of_le ht.2 ((min_le_right _ _).trans (min_le_right _ _))

private lemma exists_neg_dbary (S : Triangle ℝ ℝ²) (k : Fin 3) :
    ∃ v : ℝ², dbary S v k < 0 := by
  refine ⟨-(gradBary S k), ?_⟩
  rw [dbary_eq_inner_gradBary, inner_neg_right, real_inner_self_eq_norm_sq]
  have hne := gradBary_ne_zero S k
  have hpos : 0 < ‖gradBary S k‖ := norm_pos_iff.mpr hne
  nlinarith

private lemma interior_subset_of_closedInterior_subset {S T : Triangle ℝ ℝ²}
    (hsub : S.closedInterior ⊆ T.closedInterior) : S.interior ⊆ T.interior := by
  intro x hx
  have hxT : x ∈ T.closedInterior := hsub (by
    rw [mem_closedInterior_iff_bary]; intro i; exact ((mem_interior_iff_bary S x).mp hx i).le)
  rw [mem_interior_iff_bary]
  intro k
  have hnn := (mem_closedInterior_iff_bary T x).mp hxT k
  rcases eq_or_lt_of_le hnn with h0 | hpos
  · exfalso
    obtain ⟨v, hv⟩ := exists_neg_dbary T k
    have hex : ∃ r : ℝ, 0 < r ∧ ∀ t ∈ Set.Ioo 0 r, x + t • v ∈ S.interior := by
      have hexk : ∀ i : Fin 3, ∃ r : ℝ, 0 < r ∧ ∀ t ∈ Set.Ioo 0 r, 0 < bary S x i + t * dbary S v i := by
        intro i
        have hi := (mem_interior_iff_bary S x).mp hx i
        by_cases hneg : dbary S v i < 0
        · have hneg' : 0 < -dbary S v i := neg_pos.mpr hneg
          refine ⟨bary S x i / (2 * (-dbary S v i)), by positivity, fun t ht => ?_⟩
          have := mul_lt_mul_of_pos_right ht.2 hneg'
          have hsimp : bary S x i / (2 * -dbary S v i) * -dbary S v i = bary S x i / 2 := by
            have hdne : dbary S v i ≠ 0 := hneg.ne
            field_simp [hdne]
          linarith
        · push_neg at hneg
          exact ⟨1, zero_lt_one, fun t ht => by nlinarith [ht.1]⟩
      choose rk hrk hpk using hexk
      refine ⟨min (rk 0) (min (rk 1) (rk 2)), lt_min (hrk 0) (lt_min (hrk 1) (hrk 2)), fun t ht => ?_⟩
      rw [mem_interior_iff_bary]
      intro i; rw [bary_add_smul]
      apply hpk i t ⟨ht.1, ?_⟩
      match i with
      | 0 => exact lt_of_lt_of_le ht.2 (min_le_left _ _)
      | 1 => exact lt_of_lt_of_le ht.2 ((min_le_right _ _).trans (min_le_left _ _))
      | 2 => exact lt_of_lt_of_le ht.2 ((min_le_right _ _).trans (min_le_right _ _))
    obtain ⟨r, hr, hball⟩ := hex
    have hmem : x + (r / 2) • v ∈ S.interior := hball (r / 2) ⟨by positivity, by linarith⟩
    have hmemT : x + (r / 2) • v ∈ T.closedInterior := hsub (by
      rw [mem_closedInterior_iff_bary]; intro i; exact ((mem_interior_iff_bary S _).mp hmem i).le)
    have hnn' := (mem_closedInterior_iff_bary T _).mp hmemT k
    rw [bary_add_smul, ← h0, zero_add] at hnn'
    nlinarith
  · exact hpos

private lemma triAngle_pos_lt_pi (S : Triangle ℝ ℝ²) (k : Fin 3) :
    0 < triAngle S k ∧ triAngle S k < Real.pi := by
  have hnc : ∀ a b c : Fin 3, a ≠ b → b ≠ c → a ≠ c →
      ¬ Collinear ℝ ({S.points a, S.points b, S.points c} : Set ℝ²) := by
    intro a b c hab hbc hac hcol
    have hset : ({S.points a, S.points b, S.points c} : Set ℝ²) = Set.range S.points := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
      constructor
      · rintro (rfl | rfl | rfl) <;> exact ⟨_, rfl⟩
      · rintro ⟨i, rfl⟩
        fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases i <;> simp_all
    rw [hset] at hcol
    have hdim := hcol.finrank_le_one
    have hcard := S.independent.finrank_vectorSpan (Fintype.card_fin 3)
    omega
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  fin_cases k
  · have h := hnc 1 0 2 h01.symm h02 h12
    have hne0 := EuclideanGeometry.angle_ne_zero_of_not_collinear h
    have hnepi := EuclideanGeometry.angle_ne_pi_of_not_collinear h
    exact ⟨lt_of_le_of_ne (EuclideanGeometry.angle_nonneg _ _ _) hne0.symm,
      lt_of_le_of_ne (EuclideanGeometry.angle_le_pi _ _ _) hnepi⟩
  · have h := hnc 2 1 0 h12.symm h01.symm h02.symm
    have hne0 := EuclideanGeometry.angle_ne_zero_of_not_collinear h
    have hnepi := EuclideanGeometry.angle_ne_pi_of_not_collinear h
    exact ⟨lt_of_le_of_ne (EuclideanGeometry.angle_nonneg _ _ _) hne0.symm,
      lt_of_le_of_ne (EuclideanGeometry.angle_le_pi _ _ _) hnepi⟩
  · have h := hnc 0 2 1 h02 h12.symm h01
    have hne0 := EuclideanGeometry.angle_ne_zero_of_not_collinear h
    have hnepi := EuclideanGeometry.angle_ne_pi_of_not_collinear h
    exact ⟨lt_of_le_of_ne (EuclideanGeometry.angle_nonneg _ _ _) hne0.symm,
      lt_of_le_of_ne (EuclideanGeometry.angle_le_pi _ _ _) hnepi⟩

private lemma dirSet_vertex_eq_arc (S : Triangle ℝ ℝ²) (k : Fin 3) :
    ∃ φ : ℝ, dirSet S (S.points k) = arc φ (φ + triAngle S k) := by
  let j₁ : Fin 3 := match k with | 0 => 1 | 1 => 2 | 2 => 0
  let j₂ : Fin 3 := match k with | 0 => 2 | 1 => 0 | 2 => 1
  have h1k : j₁ ≠ k := by fin_cases k <;> decide
  have h2k : j₂ ≠ k := by fin_cases k <;> decide
  have h12 : j₁ ≠ j₂ := by fin_cases k <;> decide
  have hang : triAngle S k = ∠ (S.points j₁) (S.points k) (S.points j₂) := by
    fin_cases k <;> rfl
  let e₁ := S.points j₁ - S.points k
  let e₂ := S.points j₂ - S.points k
  have he1 : e₁ ≠ 0 := sub_ne_zero.mpr (S.independent.injective.ne h1k)
  have he2 : e₂ ≠ 0 := sub_ne_zero.mpr (S.independent.injective.ne h2k)
  obtain ⟨φ₁, hφ₁⟩ := exists_polar e₁ he1
  obtain ⟨φ₂, hφ₂⟩ := exists_polar e₂ he2
  have hr1 : 0 < ‖e₁‖ := norm_pos_iff.mpr he1
  have hr2 : 0 < ‖e₂‖ := norm_pos_iff.mpr he2
  have hdir : ∀ θ : ℝ, θ ∈ dirSet S (S.points k) ↔
      θ ∈ Set.Ico 0 (2 * Real.pi) ∧
        0 < dbary S (unitDir θ) j₁ ∧ 0 < dbary S (unitDir θ) j₂ := by
    intro θ
    rw [mem_dirSet_iff]
    refine and_congr_right fun _ => ⟨fun h => ?_, fun ⟨h1, h2⟩ i => ?_⟩
    · have hj1 := h j₁; rw [bary_point, if_neg h1k] at hj1
      have hj2 := h j₂; rw [bary_point, if_neg h2k] at hj2
      exact ⟨hj1.resolve_left (lt_irrefl 0) |>.2, hj2.resolve_left (lt_irrefl 0) |>.2⟩
    · have hi : i = k ∨ i = j₁ ∨ i = j₂ := by
        fin_cases k <;> fin_cases i <;> simp [j₁, j₂]
      rcases hi with rfl | rfl | rfl
      · left; rw [bary_point, if_pos rfl]; exact zero_lt_one
      · right; rw [bary_point, if_neg h1k]; exact ⟨rfl, h1⟩
      · right; rw [bary_point, if_neg h2k]; exact ⟨rfl, h2⟩
  have hdet1 : ∀ θ : ℝ, det2 (unitDir θ) e₂ = dbary S (unitDir θ) j₁ * det2 e₁ e₂ := by
    intro θ
    conv_lhs => rw [dir_eq_sum_dbary_at S k j₁ j₂ h1k h2k h12 (unitDir θ)]
    rw [det2_add_left, det2_smul_left, det2_smul_left, det2_self, mul_zero, add_zero]
  have hdet2 : ∀ θ : ℝ, det2 e₁ (unitDir θ) = dbary S (unitDir θ) j₂ * det2 e₁ e₂ := by
    intro θ
    conv_lhs => rw [dir_eq_sum_dbary_at S k j₁ j₂ h1k h2k h12 (unitDir θ)]
    rw [det2_add_right, det2_smul_right, det2_smul_right, det2_self, mul_zero, zero_add]
  have hdet_e12 : det2 e₁ e₂ = ‖e₁‖ * ‖e₂‖ * Real.sin (φ₂ - φ₁) := by
    conv_lhs => rw [hφ₁, hφ₂]
    rw [det2_smul_left, det2_smul_right, det2_unitDir]; ring
  have hdet_ne : det2 e₁ e₂ ≠ 0 := by
    intro h0
    have hfull : ∀ dir : ℝ², det2 dir e₂ = 0 := fun dir => by
      conv_lhs => rw [dir_eq_sum_dbary_at S k j₁ j₂ h1k h2k h12 dir]
      rw [det2_add_left, det2_smul_left, det2_smul_left, det2_self, mul_zero, add_zero, h0, mul_zero]
    have htest := hfull !₂[e₂.ofLp 1, -e₂.ofLp 0]
    have hsq : e₂.ofLp 0 ^ 2 + e₂.ofLp 1 ^ 2 = 0 := by
      have h' : e₂.ofLp 1 * e₂.ofLp 1 - (-e₂.ofLp 0) * e₂.ofLp 0 = 0 := htest
      linarith
    apply he2
    ext i; match i with
    | 0 => change e₂.ofLp 0 = 0; nlinarith
    | 1 => change e₂.ofLp 1 = 0; nlinarith
  have hsin_ne : Real.sin (φ₂ - φ₁) ≠ 0 := by
    intro h; rw [h, mul_zero] at hdet_e12; exact hdet_ne hdet_e12
  have hα_bounds := triAngle_pos_lt_pi S k
  set α := triAngle S k
  have hcos_α : Real.cos α = Real.cos (φ₂ - φ₁) := by
    have ha : α = InnerProductGeometry.angle (unitDir φ₁) (unitDir φ₂) := by
      rw [hang, EuclideanGeometry.angle]
      change _ = _
      have : S.points j₁ -ᵥ S.points k = ‖e₁‖ • unitDir φ₁ := hφ₁
      have : S.points j₂ -ᵥ S.points k = ‖e₂‖ • unitDir φ₂ := hφ₂
      rw [‹S.points j₁ -ᵥ S.points k = _›, ‹S.points j₂ -ᵥ S.points k = _›,
        InnerProductGeometry.angle_smul_left_of_pos _ _ hr1,
        InnerProductGeometry.angle_smul_right_of_pos _ _ hr2]
    rw [ha, InnerProductGeometry.cos_angle, inner_unitDir, norm_unitDir, norm_unitDir, mul_one,
      div_one, ← Real.cos_neg, neg_sub]
  rcases lt_or_gt_of_ne hsin_ne with hsin_neg | hsin_pos
  · -- sin (φ₂ - φ₁) < 0, so sin (φ₁ - φ₂) > 0, φ₁ ≡ φ₂ + α (mod 2π)
    have hsin_pos' : 0 < Real.sin (φ₁ - φ₂) := by
      rw [show φ₁ - φ₂ = -(φ₂ - φ₁) by ring, Real.sin_neg]; linarith
    have hsin_eq : Real.sin (φ₁ - φ₂) = Real.sin α := by
      have hsq : Real.sin (φ₁ - φ₂) ^ 2 = Real.sin α ^ 2 := by
        have h1 := Real.sin_sq_add_cos_sq (φ₁ - φ₂)
        have h2 := Real.sin_sq_add_cos_sq α
        have hc : Real.cos (φ₁ - φ₂) = Real.cos α := by
          rw [show φ₁ - φ₂ = -(φ₂ - φ₁) by ring, Real.cos_neg, hcos_α]
        rw [hc] at h1; linarith
      have ha_pos := Real.sin_pos_of_pos_of_lt_pi hα_bounds.1 hα_bounds.2
      nlinarith only [hsq, hsin_pos', ha_pos]
    have hcos_eq : Real.cos (φ₁ - φ₂) = Real.cos α := by
      rw [show φ₁ - φ₂ = -(φ₂ - φ₁) by ring, Real.cos_neg, hcos_α]
    have hdiff : ∀ θ : ℝ, Real.sin (φ₁ - θ) = Real.sin (φ₂ + α - θ) := fun θ => by
      have : φ₁ - θ = (φ₁ - φ₂) + (φ₂ - θ) := by ring
      have : φ₂ + α - θ = α + (φ₂ - θ) := by ring
      rw [‹φ₁ - θ = _›, ‹φ₂ + α - θ = _›, Real.sin_add, Real.sin_add, hsin_eq, hcos_eq]
    refine ⟨φ₂, ?_⟩
    ext θ
    rw [hdir]
    by_cases hθ : θ ∈ Set.Ico 0 (2 * Real.pi)
    · rw [mem_arc_iff_sin_pos φ₂ α θ hα_bounds.1 hα_bounds.2 hθ]
      simp only [hθ, true_and]
      have hd1 : dbary S (unitDir θ) j₁ * (‖e₁‖ * ‖e₂‖ * Real.sin (φ₂ - φ₁)) =
          ‖e₂‖ * Real.sin (φ₂ - θ) := by
        have h1 := hdet1 θ
        rw [hdet_e12] at h1
        rw [← h1]; conv_lhs => rw [hφ₂]
        rw [det2_smul_right, det2_unitDir]
      have hd2 : dbary S (unitDir θ) j₂ * (‖e₁‖ * ‖e₂‖ * Real.sin (φ₂ - φ₁)) =
          ‖e₁‖ * Real.sin (θ - φ₁) := by
        have h2 := hdet2 θ
        rw [hdet_e12] at h2
        rw [← h2]; conv_lhs => rw [hφ₁]
        rw [det2_smul_left, det2_unitDir]
      have hden_neg : ‖e₁‖ * ‖e₂‖ * Real.sin (φ₂ - φ₁) < 0 := by nlinarith only [mul_pos hr1 hr2, hsin_neg]
      have h1iff : 0 < dbary S (unitDir θ) j₁ ↔ 0 < Real.sin (θ - φ₂) := by
        have hsin_neg' : Real.sin (φ₂ - θ) = -Real.sin (θ - φ₂) := by
          rw [show φ₂ - θ = -(θ - φ₂) by ring, Real.sin_neg]
        rw [hsin_neg'] at hd1
        constructor <;> intro h <;> nlinarith only [hd1, hden_neg, hr2, h]
      have h2iff : 0 < dbary S (unitDir θ) j₂ ↔ 0 < Real.sin (φ₂ + α - θ) := by
        have hsin_neg' : Real.sin (θ - φ₁) = -Real.sin (φ₁ - θ) := by
          rw [show θ - φ₁ = -(φ₁ - θ) by ring, Real.sin_neg]
        rw [hsin_neg', hdiff θ] at hd2
        constructor <;> intro h <;> nlinarith only [hd2, hden_neg, hr1, h]
      rw [h1iff, h2iff]
    · simp only [arc, Set.mem_ofPred_eq, hθ, false_and]
  · -- sin (φ₂ - φ₁) > 0, so φ₂ ≡ φ₁ + α (mod 2π)
    have hsin_eq : Real.sin (φ₂ - φ₁) = Real.sin α := by
      have hsq : Real.sin (φ₂ - φ₁) ^ 2 = Real.sin α ^ 2 := by
        have h1 := Real.sin_sq_add_cos_sq (φ₂ - φ₁)
        have h2 := Real.sin_sq_add_cos_sq α
        rw [← hcos_α] at h1; linarith
      have ha_pos := Real.sin_pos_of_pos_of_lt_pi hα_bounds.1 hα_bounds.2
      nlinarith only [hsq, hsin_pos, ha_pos]
    have hdiff : ∀ θ : ℝ, Real.sin (φ₂ - θ) = Real.sin (φ₁ + α - θ) := fun θ => by
      have : φ₂ - θ = (φ₂ - φ₁) + (φ₁ - θ) := by ring
      have : φ₁ + α - θ = α + (φ₁ - θ) := by ring
      rw [‹φ₂ - θ = _›, ‹φ₁ + α - θ = _›, Real.sin_add, Real.sin_add, hsin_eq, ← hcos_α]
    refine ⟨φ₁, ?_⟩
    ext θ
    rw [hdir]
    by_cases hθ : θ ∈ Set.Ico 0 (2 * Real.pi)
    · rw [mem_arc_iff_sin_pos φ₁ α θ hα_bounds.1 hα_bounds.2 hθ]
      simp only [hθ, true_and]
      have hd1 : dbary S (unitDir θ) j₁ * (‖e₁‖ * ‖e₂‖ * Real.sin (φ₂ - φ₁)) =
          ‖e₂‖ * Real.sin (φ₂ - θ) := by
        have h1 := hdet1 θ
        rw [hdet_e12] at h1
        rw [← h1]; conv_lhs => rw [hφ₂]
        rw [det2_smul_right, det2_unitDir]
      have hd2 : dbary S (unitDir θ) j₂ * (‖e₁‖ * ‖e₂‖ * Real.sin (φ₂ - φ₁)) =
          ‖e₁‖ * Real.sin (θ - φ₁) := by
        have h2 := hdet2 θ
        rw [hdet_e12] at h2
        rw [← h2]; conv_lhs => rw [hφ₁]
        rw [det2_smul_left, det2_unitDir]
      have hden_pos : 0 < ‖e₁‖ * ‖e₂‖ * Real.sin (φ₂ - φ₁) := by nlinarith only [mul_pos hr1 hr2, hsin_pos]
      rw [hdiff θ] at hd1
      have h1iff : 0 < dbary S (unitDir θ) j₁ ↔ 0 < Real.sin (φ₁ + α - θ) := by
        constructor <;> intro h <;> nlinarith only [hd1, hden_pos, hr2, h]
      have h2iff : 0 < dbary S (unitDir θ) j₂ ↔ 0 < Real.sin (θ - φ₁) := by
        constructor <;> intro h <;> nlinarith only [hd2, hden_pos, hr1, h]
      rw [h1iff, h2iff, and_comm]
    · simp only [arc, Set.mem_ofPred_eq, hθ, false_and]

private def onOpenEdge (S : Triangle ℝ ℝ²) (P : ℝ²) : Prop :=
  P ∈ S.closedInterior ∧ P ∉ S.interior ∧ ∀ k : Fin 3, S.points k ≠ P

private lemma onOpenEdge_iff_unique_zero (S : Triangle ℝ ℝ²) (P : ℝ²) :
    onOpenEdge S P ↔ ∃ k₀ : Fin 3, bary S P k₀ = 0 ∧ ∀ j : Fin 3, j ≠ k₀ → 0 < bary S P j := by
  constructor
  · rintro ⟨hcl, hni, hnv⟩
    have hnn := (mem_closedInterior_iff_bary S P).mp hcl
    have hex0 : ∃ k₀ : Fin 3, bary S P k₀ = 0 := by
      by_contra hall; push_neg at hall
      exact hni ((mem_interior_iff_bary S P).mpr fun k => lt_of_le_of_ne (hnn k) (hall k).symm)
    obtain ⟨k₀, hk0⟩ := hex0
    refine ⟨k₀, hk0, fun j hjk => ?_⟩
    rcases eq_or_lt_of_le (hnn j) with hj0 | hjpos
    · exfalso
      -- Two barycentric coords are 0, so the third is 1, hence P is a vertex!
      have hsum := bary_sum S P
      rw [Fin.sum_univ_three] at hsum
      have hexv : ∃ m : Fin 3, bary S P m = 1 ∧ ∀ i : Fin 3, i ≠ m → bary S P i = 0 := by
        fin_cases k₀ <;> fin_cases j <;> simp_all
        · exact ⟨2, by linarith, fun i hi => by fin_cases i <;> simp_all⟩
        · exact ⟨1, by linarith, fun i hi => by fin_cases i <;> simp_all⟩
        · exact ⟨2, by linarith, fun i hi => by fin_cases i <;> simp_all⟩
        · exact ⟨0, by linarith, fun i hi => by fin_cases i <;> simp_all⟩
        · exact ⟨1, by linarith, fun i hi => by fin_cases i <;> simp_all⟩
        · exact ⟨0, by linarith, fun i hi => by fin_cases i <;> simp_all⟩
      obtain ⟨m, hm1, hm0⟩ := hexv
      apply hnv m
      have heq : bary S P = bary S (S.points m) := by
        funext i; rw [bary_point]
        by_cases him : i = m
        · subst him; simp [hm1]
        · simp [him, hm0 i him]
      rw [← affineCombination_bary S P, heq, affineCombination_bary]
    · exact hjpos
  · rintro ⟨k₀, hk0, hpos⟩
    refine ⟨(mem_closedInterior_iff_bary S P).mpr fun i => ?_, ?_, ?_⟩
    · by_cases hi : i = k₀
      · subst hi; exact hk0.ge
      · exact (hpos i hi).le
    · intro hint
      have := (mem_interior_iff_bary S P).mp hint k₀
      linarith
    · intro k hkp
      subst hkp
      have h0 := bary_point S k k₀
      have hne : k₀ ≠ k := by intro h; subst h; simp at h0; linarith
      obtain ⟨j, hjk0, hjk⟩ : ∃ j : Fin 3, j ≠ k₀ ∧ j ≠ k := by
        fin_cases k <;> fin_cases k₀ <;> simp_all <;> decide
      have hj := hpos j hjk0
      rw [bary_point, if_neg hjk] at hj
      linarith

private lemma dirSet_openEdge_eq_arc (S : Triangle ℝ ℝ²) (P : ℝ²) (h : onOpenEdge S P) :
    ∃ φ : ℝ, dirSet S P = arc (φ - Real.pi / 2) (φ + Real.pi / 2) := by
  obtain ⟨k₀, hk0, hpos⟩ := (onOpenEdge_iff_unique_zero S P).mp h
  obtain ⟨φ, hφ⟩ := exists_polar (gradBary S k₀) (gradBary_ne_zero S k₀)
  have hr : 0 < ‖gradBary S k₀‖ := norm_pos_iff.mpr (gradBary_ne_zero S k₀)
  refine ⟨φ, ?_⟩
  ext θ
  rw [mem_dirSet_iff]
  by_cases hθ : θ ∈ Set.Ico 0 (2 * Real.pi)
  · rw [mem_arc_half_iff_cos_pos φ θ hθ]
    simp only [hθ, true_and]
    have hdb : dbary S (unitDir θ) k₀ = ‖gradBary S k₀‖ * Real.cos (θ - φ) := by
      rw [dbary_eq_inner_gradBary]
      conv_lhs => rw [hφ]
      rw [real_inner_smul_left, inner_unitDir, ← Real.cos_neg, neg_sub]
    constructor
    · intro hall
      have h0 := hall k₀
      rw [hk0] at h0
      have hd := (h0.resolve_left (lt_irrefl 0)).2
      rw [hdb] at hd
      nlinarith
    · intro hcos i
      by_cases hi : i = k₀
      · subst hi; right; refine ⟨hk0, ?_⟩; rw [hdb]; exact mul_pos hr hcos
      · exact Or.inl (hpos i hi)
  · simp only [arc, Set.mem_ofPred_eq, hθ, false_and]

private noncomputable def angContrib (S : Triangle ℝ ℝ²) (P : ℝ²) : ℝ :=
  if P ∉ S.closedInterior then 0
  else if P ∈ S.interior then 2 * Real.pi
  else if onOpenEdge S P then Real.pi
  else ∑ k : Fin 3, if S.points k = P then triAngle S k else 0

private lemma angContrib_nonneg (S : Triangle ℝ ℝ²) (P : ℝ²) : 0 ≤ angContrib S P := by
  unfold angContrib
  by_cases h1 : P ∉ S.closedInterior
  · rw [if_pos h1]
  rw [if_neg h1]
  by_cases h2 : P ∈ S.interior
  · rw [if_pos h2]; positivity
  rw [if_neg h2]
  by_cases h3 : onOpenEdge S P
  · rw [if_pos h3]; positivity
  rw [if_neg h3]
  apply Finset.sum_nonneg; intro k _
  split_ifs
  · exact (triAngle_pos_lt_pi S k).1.le
  · exact le_rfl

private lemma measurableSet_and_volume_dirSet (S : Triangle ℝ ℝ²) (P : ℝ²) :
    MeasurableSet (dirSet S P) ∧ volume (dirSet S P) = ENNReal.ofReal (angContrib S P) := by
  unfold angContrib
  by_cases hcl : P ∉ S.closedInterior
  · rw [if_pos hcl]
    have hempty : dirSet S P = ∅ := by
      ext θ; simp only [mem_dirSet_iff, Set.mem_empty_iff_false, iff_false, not_and, not_forall]
      intro _
      have : ∃ k : Fin 3, bary S P k < 0 := by
        by_contra hall; push_neg at hall
        exact hcl ((mem_closedInterior_iff_bary S P).mpr hall)
      obtain ⟨k, hk⟩ := this
      exact ⟨k, by intro h; rcases h with h | ⟨h, _⟩ <;> linarith⟩
    rw [hempty]
    exact ⟨MeasurableSet.empty, by simp⟩
  · push_neg at hcl
    rw [if_neg (not_not.mpr hcl)]
    by_cases hint : P ∈ S.interior
    · rw [if_pos hint]
      have hfull : dirSet S P = Set.Ico 0 (2 * Real.pi) := by
        ext θ; simp only [mem_dirSet_iff, and_iff_left_iff_imp]
        intro _ k; exact Or.inl ((mem_interior_iff_bary S P).mp hint k)
      rw [hfull]
      exact ⟨measurableSet_Ico, by rw [Real.volume_Ico, sub_zero]⟩
    · rw [if_neg hint]
      by_cases hedge : onOpenEdge S P
      · rw [if_pos hedge]
        obtain ⟨φ, hφ⟩ := dirSet_openEdge_eq_arc S P hedge
        rw [hφ]
        refine ⟨measurableSet_arc _ _, ?_⟩
        rw [volume_arc _ _ (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
        congr 1; ring
      · rw [if_neg hedge]
        have hexv : ∃ k : Fin 3, S.points k = P := by
          by_contra hnv; push_neg at hnv
          exact hedge ⟨hcl, hint, hnv⟩
        obtain ⟨k, rfl⟩ := hexv
        obtain ⟨φ, hφ⟩ := dirSet_vertex_eq_arc S k
        rw [hφ]
        have hsum : (∑ j : Fin 3, if S.points j = S.points k then triAngle S j else 0) =
            triAngle S k := by
          rw [Finset.sum_eq_single k]
          · simp
          · intro j _ hjk
            rw [if_neg (S.independent.injective.ne hjk)]
          · intro hk; exact absurd (Finset.mem_univ k) hk
        rw [hsum]
        have hα := triAngle_pos_lt_pi S k
        refine ⟨measurableSet_arc _ _, ?_⟩
        rw [volume_arc _ _ (by linarith) (by linarith)]
        congr 1; ring

private lemma dirSet_mono {S T : Triangle ℝ ℝ²}
    (hsub : S.closedInterior ⊆ T.closedInterior) (P : ℝ²) :
    dirSet S P ⊆ dirSet T P := by
  intro θ ⟨hθ, r, hr, h⟩
  exact ⟨hθ, r, hr, fun t ht => interior_subset_of_closedInterior_subset hsub (h t ht)⟩

private lemma dirSet_disjoint {S₁ S₂ : Triangle ℝ ℝ²}
    (hdisj : Disjoint S₁.interior S₂.interior) (P : ℝ²) :
    Disjoint (dirSet S₁ P) (dirSet S₂ P) := by
  rw [Set.disjoint_left]
  intro θ ⟨_, r₁, hr₁, h₁⟩ ⟨_, r₂, hr₂, h₂⟩
  let t := min r₁ r₂ / 2
  have hmin : 0 < min r₁ r₂ := lt_min hr₁ hr₂
  have ht0 : 0 < t := by dsimp [t]; positivity
  have ht1 : t < r₁ := lt_of_lt_of_le (by dsimp [t]; linarith) (min_le_left r₁ r₂)
  have ht2 : t < r₂ := lt_of_lt_of_le (by dsimp [t]; linarith) (min_le_right r₁ r₂)
  exact Set.disjoint_left.mp hdisj (h₁ t ⟨ht0, ht1⟩) (h₂ t ⟨ht0, ht2⟩)

private lemma dirSet_diff_finite {n : ℕ} (T : Triangle ℝ ℝ²) (Ts : Fin n → Triangle ℝ ℝ²)
    (hunion : ⋃ i, (Ts i).closedInterior = T.closedInterior) (P : ℝ²) :
    (dirSet T P \ ⋃ i, dirSet (Ts i) P).Finite := by
  let badPair : Fin n × Fin 3 → Set ℝ := fun p =>
    {θ ∈ Set.Ico 0 (2 * Real.pi) | dbary (Ts p.1) (unitDir θ) p.2 = 0}
  have hbad_fin : ∀ p : Fin n × Fin 3, (badPair p).Finite := by
    intro ⟨i, k⟩
    obtain ⟨φ, hφ⟩ := exists_polar (gradBary (Ts i) k) (gradBary_ne_zero (Ts i) k)
    have hr : 0 < ‖gradBary (Ts i) k‖ := norm_pos_iff.mpr (gradBary_ne_zero (Ts i) k)
    have heq : badPair (i, k) =
        {θ ∈ Set.Ico 0 (2 * Real.pi) | Real.sin (θ - (φ - Real.pi / 2)) = 0} := by
      ext θ
      simp only [badPair, Set.mem_setOf_eq]
      refine and_congr_right fun _ => ?_
      rw [dbary_eq_inner_gradBary, hφ, real_inner_smul_left, inner_unitDir, ← Real.cos_neg,
        neg_sub, show θ - (φ - Real.pi / 2) = (θ - φ) + Real.pi / 2 by ring,
        Real.sin_add_pi_div_two]
      exact ⟨fun h => (mul_eq_zero.mp h).resolve_left hr.ne', fun h => by rw [h, mul_zero]⟩
    rw [heq]
    exact finite_sin_zero_Ico _
  have hUfin : (⋃ p : Fin n × Fin 3, badPair p).Finite := Set.finite_iUnion hbad_fin
  refine hUfin.subset fun θ ⟨hθT, hθnot⟩ => ?_
  by_contra hnotbad
  simp only [Set.mem_iUnion, not_exists] at hnotbad hθnot
  obtain ⟨hθIco, r₀, hr₀, hTr₀⟩ := hθT
  have hdb_ne : ∀ (i : Fin n) (k : Fin 3), dbary (Ts i) (unitDir θ) k ≠ 0 :=
    fun i k h0 => hnotbad (i, k) ⟨hθIco, h0⟩
  -- Choose r ∈ (0, r₀] strictly smaller than every positive root -bary / dbary
  let root (i : Fin n) (k : Fin 3) : ℝ := -bary (Ts i) P k / dbary (Ts i) (unitDir θ) k
  let posRoots : Finset ℝ :=
    (Finset.univ : Finset (Fin n × Fin 3)).image (fun p => root p.1 p.2) |>.filter (0 < ·)
  let r : ℝ := if h : posRoots.Nonempty then min r₀ (posRoots.min' h) else r₀
  have hr_pos : 0 < r := by
    dsimp [r]; split_ifs with h
    · exact lt_min hr₀ (Finset.mem_filter.mp (Finset.min'_mem posRoots h)).2
    · exact hr₀
  have hr_le : r ≤ r₀ := by
    dsimp [r]; split_ifs with h
    · exact min_le_left _ _
    · exact le_rfl
  have hno_root : ∀ (i : Fin n) (k : Fin 3) (t : ℝ), t ∈ Set.Ioo 0 r →
      bary (Ts i) P k + t * dbary (Ts i) (unitDir θ) k ≠ 0 := by
    intro i k t ht hzero
    have htr : t = root i k := by
      dsimp [root]
      have hne := hdb_ne i k
      field_simp [hne]
      linarith
    have hmem : root i k ∈ posRoots := by
      simp only [posRoots, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨(i, k), rfl⟩, htr ▸ ht.1⟩
    have hne_pr : posRoots.Nonempty := ⟨_, hmem⟩
    have hle : r ≤ root i k := by
      dsimp [r]; rw [dif_pos hne_pr]
      exact (min_le_right _ _).trans (Finset.min'_le _ _ hmem)
    linarith [ht.2]
  have ht0_mem : r / 2 ∈ Set.Ioo 0 r := ⟨by positivity, by linarith⟩
  have hx0T : P + (r / 2) • unitDir θ ∈ T.closedInterior := by
    have hin := hTr₀ (r / 2) ⟨ht0_mem.1, lt_of_lt_of_le ht0_mem.2 hr_le⟩
    rw [mem_closedInterior_iff_bary]; intro k; exact ((mem_interior_iff_bary T _).mp hin k).le
  rw [← hunion, Set.mem_iUnion] at hx0T
  obtain ⟨i, hi⟩ := hx0T
  apply hθnot i
  refine ⟨hθIco, r, hr_pos, fun t ht => ?_⟩
  rw [mem_interior_iff_bary]
  intro k
  rw [bary_add_smul]
  have hpos0 : 0 < bary (Ts i) P k + (r / 2) * dbary (Ts i) (unitDir θ) k := by
    have hnn := (mem_closedInterior_iff_bary (Ts i) _).mp hi k
    rw [bary_add_smul] at hnn
    exact lt_of_le_of_ne hnn (hno_root i k (r / 2) ht0_mem).symm
  by_contra hle; push_neg at hle
  have hlt : bary (Ts i) P k + t * dbary (Ts i) (unitDir θ) k < 0 :=
    lt_of_le_of_ne hle (hno_root i k t ht)
  -- Linear function has opposite signs at t and r/2 in (0, r), so its root lies in (0, r)!
  let d := dbary (Ts i) (unitDir θ) k
  let b := bary (Ts i) P k
  have hd_ne : d ≠ 0 := hdb_ne i k
  have hroot_mem : (-b / d) ∈ Set.Ioo 0 r := by
    have h1 : b + t * d < 0 := hlt
    have h2 : 0 < b + (r / 2) * d := hpos0
    rcases lt_or_gt_of_ne hd_ne with hdneg | hdpos
    · have hgt : r / 2 < -b / d := by
        rw [lt_div_iff_of_neg hdneg]; linarith
      have hlt' : -b / d < t := by
        rw [div_lt_iff_of_neg hdneg]; linarith
      exact ⟨lt_trans ht0_mem.1 hgt, lt_trans hlt' ht.2⟩
    · have hgt : t < -b / d := by
        rw [lt_div_iff₀ hdpos]; linarith
      have hlt' : -b / d < r / 2 := by
        rw [div_lt_iff₀ hdpos]; linarith
      exact ⟨lt_trans ht.1 hgt, lt_trans hlt' ht0_mem.2⟩
  exact hno_root i k (-b / d) hroot_mem (by change b + (-b / d) * d = 0; field_simp [hd_ne]; ring)

private lemma sum_angContrib_eq {n : ℕ} (T : Triangle ℝ ℝ²) (Ts : Fin n → Triangle ℝ ℝ²)
    (hdisj : Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior))
    (hunion : ⋃ i, (Ts i).closedInterior = T.closedInterior) (P : ℝ²) :
    ∑ i : Fin n, angContrib (Ts i) P = angContrib T P := by
  have hsub_i : ∀ i : Fin n, (Ts i).closedInterior ⊆ T.closedInterior := fun i => by
    rw [← hunion]; exact Set.subset_iUnion (fun j => (Ts j).closedInterior) i
  have hsubU : (⋃ i : Fin n, dirSet (Ts i) P) ⊆ dirSet T P :=
    Set.iUnion_subset fun i => dirSet_mono (hsub_i i) P
  have hvol_eq : volume (⋃ i : Fin n, dirSet (Ts i) P) = volume (dirSet T P) := by
    apply le_antisymm (measure_mono hsubU)
    have hcov : dirSet T P ⊆ (⋃ i : Fin n, dirSet (Ts i) P) ∪ (dirSet T P \ ⋃ i, dirSet (Ts i) P) :=
      fun x hx => by by_cases h : x ∈ ⋃ i, dirSet (Ts i) P; exact Or.inl h; exact Or.inr ⟨hx, h⟩
    calc volume (dirSet T P)
        ≤ volume ((⋃ i : Fin n, dirSet (Ts i) P) ∪ (dirSet T P \ ⋃ i, dirSet (Ts i) P)) :=
          measure_mono hcov
      _ ≤ volume (⋃ i : Fin n, dirSet (Ts i) P) + volume (dirSet T P \ ⋃ i, dirSet (Ts i) P) :=
          measure_union_le _ _
      _ = volume (⋃ i : Fin n, dirSet (Ts i) P) + 0 := by
          rw [(dirSet_diff_finite T Ts hunion P).measure_zero]
      _ = volume (⋃ i : Fin n, dirSet (Ts i) P) := add_zero _
  have hvol_sum : volume (⋃ i : Fin n, dirSet (Ts i) P) = ∑ i : Fin n, volume (dirSet (Ts i) P) := by
    rw [measure_iUnion (fun i j hij => dirSet_disjoint (hdisj hij) P)
      (fun i => (measurableSet_and_volume_dirSet (Ts i) P).1), tsum_fintype]
  rw [hvol_sum] at hvol_eq
  simp_rw [(measurableSet_and_volume_dirSet _ P).2] at hvol_eq
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => angContrib_nonneg (Ts i) P)] at hvol_eq
  exact (ENNReal.ofReal_eq_ofReal_iff
    (Finset.sum_nonneg fun i _ => angContrib_nonneg (Ts i) P) (angContrib_nonneg T P)).mp hvol_eq

/- ### Part 4: Elementary 3-element ℤ-linear independence transfer & combinatorics for n ∈ {2, 3, 5} -/

/-- If three ℤ-linearly independent reals lie in the ℤ-span of three reals, those three reals are
also ℤ-linearly independent. -/
private lemma indep_of_three_in_span_three {α₀ α₁ α₂ a₀ a₁ a₂ : ℝ}
    (hα : ∀ p q r : ℤ, (p : ℝ) * α₀ + (q : ℝ) * α₁ + (r : ℝ) * α₂ = 0 → p = 0 ∧ q = 0 ∧ r = 0)
    (u : Fin 3 → Fin 3 → ℤ)
    (hu0 : α₀ = (u 0 0 : ℝ) * a₀ + (u 0 1 : ℝ) * a₁ + (u 0 2 : ℝ) * a₂)
    (hu1 : α₁ = (u 1 0 : ℝ) * a₀ + (u 1 1 : ℝ) * a₁ + (u 1 2 : ℝ) * a₂)
    (hu2 : α₂ = (u 2 0 : ℝ) * a₀ + (u 2 1 : ℝ) * a₁ + (u 2 2 : ℝ) * a₂) :
    ∀ p q r : ℤ, (p : ℝ) * a₀ + (q : ℝ) * a₁ + (r : ℝ) * a₂ = 0 → p = 0 ∧ q = 0 ∧ r = 0 := by
  -- Helper: any 3 vectors in ℤ² have a nontrivial ℤ-linear dependence
  have dep3 : ∀ c : Fin 3 → Fin 2 → ℤ,
      ∃ d₀ d₁ d₂ : ℤ, (d₀ ≠ 0 ∨ d₁ ≠ 0 ∨ d₂ ≠ 0) ∧
        d₀ * c 0 0 + d₁ * c 1 0 + d₂ * c 2 0 = 0 ∧
        d₀ * c 0 1 + d₁ * c 1 1 + d₂ * c 2 1 = 0 := by
    intro c
    let m0 := c 1 0 * c 2 1 - c 1 1 * c 2 0
    let m1 := c 2 0 * c 0 1 - c 2 1 * c 0 0
    let m2 := c 0 0 * c 1 1 - c 0 1 * c 1 0
    by_cases hm : m0 ≠ 0 ∨ m1 ≠ 0 ∨ m2 ≠ 0
    · exact ⟨m0, m1, m2, hm, by dsimp [m0, m1, m2]; ring, by dsimp [m0, m1, m2]; ring⟩
    · push_neg at hm
      by_cases h00 : c 0 0 ≠ 0
      · have hm2 : c 0 0 * c 1 1 - c 0 1 * c 1 0 = 0 := hm.2.2
        exact ⟨c 1 0, -c 0 0, 0, Or.inr (Or.inl (neg_ne_zero.mpr h00)), by ring, by linarith⟩
      · push_neg at h00
        by_cases h01 : c 0 1 ≠ 0
        · have hm2 : c 0 0 * c 1 1 - c 0 1 * c 1 0 = 0 := hm.2.2
          rw [h00] at hm2
          exact ⟨c 1 1, -c 0 1, 0, Or.inr (Or.inl (neg_ne_zero.mpr h01)), by rw [h00]; linarith, by ring⟩
        · push_neg at h01
          exact ⟨1, 0, 0, Or.inl one_ne_zero, by simp [h00], by simp [h01]⟩
  -- Eliminate one variable using any nonzero coefficient
  have elim : ∀ (x y z : ℝ) (c : Fin 3 → Fin 2 → ℤ) (s : ℤ), s ≠ 0 →
      (s : ℝ) * α₀ = (c 0 0 : ℝ) * y + (c 0 1 : ℝ) * z →
      (s : ℝ) * α₁ = (c 1 0 : ℝ) * y + (c 1 1 : ℝ) * z →
      (s : ℝ) * α₂ = (c 2 0 : ℝ) * y + (c 2 1 : ℝ) * z → False := by
    intro _ y z c s hs h0 h1 h2
    obtain ⟨d₀, d₁, d₂, hd, heq0, heq1⟩ := dep3 c
    have hcomb : ((d₀ * s : ℤ) : ℝ) * α₀ + ((d₁ * s : ℤ) : ℝ) * α₁ + ((d₂ * s : ℤ) : ℝ) * α₂ = 0 := by
      push_cast
      have : (d₀ : ℝ) * ((s : ℝ) * α₀) + (d₁ : ℝ) * ((s : ℝ) * α₁) + (d₂ : ℝ) * ((s : ℝ) * α₂) =
          ((d₀ * c 0 0 + d₁ * c 1 0 + d₂ * c 2 0 : ℤ) : ℝ) * y +
          ((d₀ * c 0 1 + d₁ * c 1 1 + d₂ * c 2 1 : ℤ) : ℝ) * z := by
        rw [h0, h1, h2]; push_cast; ring
      rw [heq0, heq1] at this
      simp only [Int.cast_zero, zero_mul, add_zero] at this
      linarith
    obtain ⟨hds0, hds1, hds2⟩ := hα (d₀ * s) (d₁ * s) (d₂ * s) hcomb
    have h0' : d₀ = 0 := (mul_eq_zero.mp hds0).resolve_right hs
    have h1' : d₁ = 0 := (mul_eq_zero.mp hds1).resolve_right hs
    have h2' : d₂ = 0 := (mul_eq_zero.mp hds2).resolve_right hs
    rcases hd with h | h | h <;> contradiction
  intro p q r hlin
  by_contra hnot
  have hne : p ≠ 0 ∨ q ≠ 0 ∨ r ≠ 0 := by tauto
  rcases hne with hp | hq | hr
  · refine elim a₀ a₁ a₂ (fun k j => if j = 0 then p * u k 1 - q * u k 0 else p * u k 2 - r * u k 0)
      p hp ?_ ?_ ?_
    · rw [hu0]; push_cast; linear_combination (u 0 0 : ℝ) * hlin
    · rw [hu1]; push_cast; linear_combination (u 1 0 : ℝ) * hlin
    · rw [hu2]; push_cast; linear_combination (u 2 0 : ℝ) * hlin
  · refine elim a₁ a₀ a₂ (fun k j => if j = 0 then q * u k 0 - p * u k 1 else q * u k 2 - r * u k 1)
      q hq ?_ ?_ ?_
    · rw [hu0]; push_cast; linear_combination (u 0 1 : ℝ) * hlin
    · rw [hu1]; push_cast; linear_combination (u 1 1 : ℝ) * hlin
    · rw [hu2]; push_cast; linear_combination (u 2 1 : ℝ) * hlin
  · refine elim a₂ a₀ a₁ (fun k j => if j = 0 then r * u k 0 - p * u k 2 else r * u k 1 - q * u k 2)
      r hr ?_ ?_ ?_
    · rw [hu0]; push_cast; linear_combination (u 0 2 : ℝ) * hlin
    · rw [hu1]; push_cast; linear_combination (u 1 2 : ℝ) * hlin
    · rw [hu2]; push_cast; linear_combination (u 2 2 : ℝ) * hlin

/-- If two unit directions lie in the closed cone of two linearly independent directions forming
angle `α ∈ (0, π)`, and their angle is `α`, then they must be the two boundary directions. -/
private lemma cone_angle_eq_imp_boundary {e₁ e₂ w₁ w₂ : ℝ²}
    (he1 : e₁ ≠ 0) (he2 : e₂ ≠ 0) (hw1 : w₁ ≠ 0) (hw2 : w₂ ≠ 0)
    (hdet : det2 e₁ e₂ ≠ 0)
    {a₁ b₁ a₂ b₂ : ℝ} (ha1 : 0 ≤ a₁) (hb1 : 0 ≤ b₁) (ha2 : 0 ≤ a₂) (hb2 : 0 ≤ b₂)
    (hrep1 : w₁ = a₁ • e₁ + b₁ • e₂) (hrep2 : w₂ = a₂ • e₁ + b₂ • e₂)
    (hang : InnerProductGeometry.angle w₁ w₂ = InnerProductGeometry.angle e₁ e₂) :
    (a₁ = 0 ∧ b₂ = 0) ∨ (b₁ = 0 ∧ a₂ = 0) := by
  -- Use polar coordinates: after orienting so det2(u1, u2) > 0, angle between e1 and e2 is α ∈ (0, π)
  -- and w1, w2 have arguments in [φ₁, φ₁ + α]; |t1 - t2| = α forces {t1, t2} = {0, α}.
  obtain ⟨φ₁, hφ₁⟩ := exists_polar e₁ he1
  obtain ⟨φ₂, hφ₂⟩ := exists_polar e₂ he2
  have hr1 : 0 < ‖e₁‖ := norm_pos_iff.mpr he1
  have hr2 : 0 < ‖e₂‖ := norm_pos_iff.mpr he2
  have hrw1 : 0 < ‖w₁‖ := norm_pos_iff.mpr hw1
  have hrw2 : 0 < ‖w₂‖ := norm_pos_iff.mpr hw2
  set α := InnerProductGeometry.angle e₁ e₂
  have hcos_e : Real.cos α = Real.cos (φ₂ - φ₁) := by
    have ha : α = InnerProductGeometry.angle (unitDir φ₁) (unitDir φ₂) := by
      dsimp [α]; conv_lhs => rw [hφ₁, hφ₂]
      rw [InnerProductGeometry.angle_smul_left_of_pos _ _ hr1,
        InnerProductGeometry.angle_smul_right_of_pos _ _ hr2]
    rw [ha, InnerProductGeometry.cos_angle, inner_unitDir, norm_unitDir, norm_unitDir, mul_one,
      div_one, ← Real.cos_neg, neg_sub]
  have hα_pos : 0 < α := by
    have h0 : 0 ≤ α := InnerProductGeometry.angle_nonneg e₁ e₂
    rcases eq_or_lt_of_le h0 with h | h
    · exfalso
      have hc1 : Real.cos (φ₂ - φ₁) = 1 := by rw [← hcos_e, ← h, Real.cos_zero]
      have hs0 : Real.sin (φ₂ - φ₁) = 0 := by nlinarith only [Real.sin_sq_add_cos_sq (φ₂ - φ₁), hc1]
      apply hdet; rw [hφ₁, hφ₂, det2_smul_left, det2_smul_right, det2_unitDir, hs0]; ring
    · exact h
  have hα_lt : α < Real.pi := by
    have hle : α ≤ Real.pi := InnerProductGeometry.angle_le_pi e₁ e₂
    rcases eq_or_lt_of_le hle with h | h
    · exfalso
      have hc1 : Real.cos (φ₂ - φ₁) = -1 := by rw [← hcos_e, h, Real.cos_pi]
      have hs0 : Real.sin (φ₂ - φ₁) = 0 := by nlinarith only [Real.sin_sq_add_cos_sq (φ₂ - φ₁), hc1]
      apply hdet; rw [hφ₁, hφ₂, det2_smul_left, det2_smul_right, det2_unitDir, hs0]; ring
    · exact h
  -- Direct algebraic proof using Cauchy-Schwarz / dot product!
  -- Actually even simpler: compare `⟪w₁, w₂⟫` and `‖w₁‖ * ‖w₂‖ * cos α`!!
  -- Let c = cos α ∈ (-1, 1), A₁ = a₁ ‖e₁‖ ≥ 0, B₁ = b₁ ‖e₂‖ ≥ 0, A₂ = a₂ ‖e₁‖ ≥ 0, B₂ = b₂ ‖e₂‖ ≥ 0.
  -- ⟪w₁, w₂⟫ = A₁ A₂ + B₁ B₂ + (A₁ B₂ + B₁ A₂) c.
  -- ‖w₁‖² = A₁² + B₁² + 2 A₁ B₁ c, ‖w₂‖² = A₂² + B₂² + 2 A₂ B₂ c.
  -- Look at the identity:
  -- ⟪w₁, w₂⟫² - ‖w₁‖² ‖w₂‖² c² = (1 - c²) * (A₁ A₂ + B₁ B₂ + ...)?
  -- Check: ‖w₁‖² ‖w₂‖² c² - ⟪w₁, w₂⟫²!
  -- Wait: ⟪w₁, w₂⟫ = ‖w₁‖ ‖w₂‖ c implies (‖w₁‖² ‖w₂‖² - ⟪w₁, w₂⟫²) = ‖w₁‖² ‖w₂‖² (1 - c²)
  -- Wait: ‖w₁‖² ‖w₂‖² - ⟪w₁, w₂⟫² = (det2 w₁ w₂)² = (A₁ B₂ - B₁ A₂)² (1 - c²)!!
  -- OH!! MY!! GOD!! LOOK AT THAT IDENTITY:
  -- (A₁ B₂ - B₁ A₂)² (1 - c²) = ‖w₁‖² ‖w₂‖² (1 - c²), SO |A₁ B₂ - B₁ A₂| = ‖w₁‖ ‖w₂‖!!
  -- Wait: ‖w₁‖² ‖w₂‖² - (A₁ B₂ - B₁ A₂)² =
  --   (A₁² + B₁² + 2 A₁ B₁ c)(A₂² + B₂² + 2 A₂ B₂ c) - (A₁ B₂ - B₁ A₂)²
  -- = (A₁ A₂ + B₁ B₂)² + 2 c (A₁ B₁ (A₂² + B₂²) + A₂ B₂ (A₁² + B₁²)) + 4 c² A₁ B₁ A₂ B₂
  -- Wait: if c < 0 that could be tricky, UNLESS we notice:
  -- ⟪w₁, w₂⟫ - ‖w₁‖ ‖w₂‖ c = 0, AND ALSO
  -- ‖w₁‖² ‖w₂‖² - (A₁ B₂ - B₁ A₂)² = ⟪w₁, w₂⟫² / (1 - c²) * ... NO!
  -- Look: (1 - c²) (‖w₁‖² ‖w₂‖² - (A₁ B₂ - B₁ A₂)²) = 0? No, divide by (1 - c²)!
  -- We ALREADY know ⟪w₁, w₂⟫ = ‖w₁‖ ‖w₂‖ c AND ‖w₁‖² ‖w₂‖² - ⟪w₁, w₂⟫² = (det2 w₁ w₂)²!
  -- Wait: det2 w₁ w₂ = (a₁ b₂ - b₁ a₂) det2 e₁ e₂, and (det2 e₁ e₂)² = ‖e₁‖² ‖e₂‖² (1 - c²)!
  -- Therefore:
  -- ‖w₁‖² ‖w₂‖² (1 - c²) = ‖w₁‖² ‖w₂‖² - ⟪w₁, w₂⟫² = (A₁ B₂ - B₁ A₂)² (1 - c²)!!
  -- Since 1 - c² > 0:
  --   (A₁ B₂ - B₁ A₂)² = ‖w₁‖² ‖w₂‖²!!
  -- AND since ⟪w₁, w₂⟫ = ‖w₁‖ ‖w₂‖ c, look at:
  --   ‖w₁‖² ‖w₂‖² - (A₁ B₂ - B₁ A₂)² = 0
  -- Wait: ALSO expand ‖w₁‖² ≥ (A₁ + B₁ c)² + B₁² (1 - c²) ... NO! Just use:
  --   ‖w₁‖² = A₁² + B₁² + 2 A₁ B₁ c ≥ (A₁ - B₁)² + 2 A₁ B₁ (1 + c) ≥ 0,
  -- Wait: EVEN SIMPLER!!
  --   A₁² + B₁² + 2 A₁ B₁ c > A₁² + B₁² - 2 A₁ B₁ = (A₁ - B₁)² when A₁ B₁ > 0 (since c > -1)!!
  -- Better: expand
  --   (A₁² + B₁² + 2 A₁ B₁ c)(A₂² + B₂² + 2 A₂ B₂ c) - (A₁ B₂ - B₁ A₂)²
  --   = (A₁ A₂ + B₁ B₂ + c (A₁ B₂ + B₁ A₂))² - c² (A₁ B₂ - B₁ A₂)²  [NO, CHECK!]
  -- Let's check:
  --   LHS = (A₁ A₂ + B₁ B₂)² + 2c (A₁ B₁ A₂² + A₁ B₁ B₂² + A₂ B₂ A₁² + A₂ B₂ B₁²) + 4c² A₁ B₁ A₂ B₂
  --   Notice:
  --   (A₁ A₂ + B₁ B₂) = (A₁ A₂ + B₁ B₂), and
  --   A₁ B₁ A₂² + A₁ B₁ B₂² + A₂ B₂ A₁² + A₂ B₂ B₁² = (A₁ A₂ + B₁ B₂)(A₁ B₂ + B₁ A₂)!!
  --   SO:
  --   LHS = (A₁ A₂ + B₁ B₂)² + 2c (A₁ A₂ + B₁ B₂)(A₁ B₂ + B₁ A₂) + 4c² A₁ B₁ A₂ B₂!
  --   WAIT A SECOND!!
  --   Look at `⟪w₁, w₂⟫ = A₁ A₂ + B₁ B₂ + c (A₁ B₂ + B₁ A₂)`!
  --   Square it:
  --   `⟪w₁, w₂⟫² = (A₁ A₂ + B₁ B₂)² + 2c (A₁ A₂ + B₁ B₂)(A₁ B₂ + B₁ A₂) + c² (A₁ B₂ + B₁ A₂)²`!
  --   AND `c² (A₁ B₂ + B₁ A₂)² - c² (A₁ B₂ - B₁ A₂)² = 4 c² A₁ B₁ A₂ B₂`!!
  --   Wait that's an identity! What about the SIGN of `A₁ A₂ + B₁ B₂`?!
  --   Look: `‖w₁‖² ‖w₂‖² = (A₁ B₂ - B₁ A₂)²` means `‖w₁‖ ‖w₂‖ = |A₁ B₂ - B₁ A₂|`!
  --   So `A₁ A₂ + B₁ B₂ + c (A₁ B₂ + B₁ A₂) = ⟪w₁, w₂⟫ = c * |A₁ B₂ - B₁ A₂|`!
  --   NOW SPLIT ON `A₁ B₂ ≥ B₁ A₂` vs `A₁ B₂ ≤ B₁ A₂`!!
  --   - If `A₁ B₂ ≥ B₁ A₂`: `|A₁ B₂ - B₁ A₂| = A₁ B₂ - B₁ A₂`!
  --     Then `A₁ A₂ + B₁ B₂ + c (A₁ B₂ + B₁ A₂) = c (A₁ B₂ - B₁ A₂)`
  --     ⟹ `A₁ A₂ + B₁ B₂ + 2 c B₁ A₂ = 0`!
  --     Wait: `A₁ A₂ + B₁ B₂ + 2 c B₁ A₂`: NO! Look at the two terms:
  --     `A₁ A₂ ≥ 0`, `B₁ B₂ ≥ 0`, AND `A₁ A₂ + B₁ B₂ + 2 c B₁ A₂` could only be 0 if...
  --     WAIT: `A₁ B₂ ≥ B₁ A₂`, so `A₁ A₂ + B₁ B₂ ≥ 2 √(A₁ A₂ B₁ B₂) ≥ 2 B₁ A₂`!!
  --     WHOA!! CHECK THAT!!
  --     By AM-GM (or literally `(A₁ A₂ - B₁ B₂)² ≥ 0`!):
  --     Wait: `(A₁ A₂ + B₁ B₂)² ≥ 4 A₁ B₁ A₂ B₂ ≥ 4 (B₁ A₂)²` (since `A₁ B₂ ≥ B₁ A₂ ≥ 0`!)!!
  --     SO `A₁ A₂ + B₁ B₂ ≥ 2 B₁ A₂`!!
  --     AND SINCE `c > -1`:
  --     `A₁ A₂ + B₁ B₂ + 2 c B₁ A₂ ≥ 2 (1 + c) B₁ A₂ ≥ 0`!!
  --     WITH EQUALITY `= 0` **IF AND ONLY IF** `B₁ A₂ = 0` AND `A₁ A₂ + B₁ B₂ = 0`!!
  --     Since `A₁, B₁, A₂, B₂ ≥ 0`:
  --     `A₁ A₂ = 0`, `B₁ B₂ = 0`, `B₁ A₂ = 0`!
  --     Since `w₁ ≠ 0` (`A₁, B₁` not both 0) and `w₂ ≠ 0` (`A₂, B₂` not both 0):
  --     **`B₁ = 0` AND `A₂ = 0`**!!
  --   - If `B₁ A₂ ≥ A₁ B₂`: symmetrically **`A₁ = 0` AND `B₂ = 0`**!!
  -- OH!! MY!! GOD!! THAT IS A **10-LINE PURE POLYNOMIAL PROOF WITH ZERO TRIGONOMETRY**!!
  let c := Real.cos α
  have hc_gt : -1 < c := by
    have hlt := Real.cos_lt_cos_of_nonneg_of_le_pi hα_pos.le le_rfl hα_lt
    rwa [Real.cos_pi] at hlt
  have hc_lt : c < 1 := by
    have hlt := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hα_lt.le hα_pos
    rwa [Real.cos_zero] at hlt
  have h1c2 : 0 < 1 - c ^ 2 := by nlinarith
  let A₁ := a₁ * ‖e₁‖
  let B₁ := b₁ * ‖e₂‖
  let A₂ := a₂ * ‖e₁‖
  let B₂ := b₂ * ‖e₂‖
  have hA1 : 0 ≤ A₁ := mul_nonneg ha1 hr1.le
  have hB1 : 0 ≤ B₁ := mul_nonneg hb1 hr2.le
  have hA2 : 0 ≤ A₂ := mul_nonneg ha2 hr1.le
  have hB2 : 0 ≤ B₂ := mul_nonneg hb2 hr2.le
  have hinner_e : @inner ℝ ℝ² _ e₁ e₂ = ‖e₁‖ * ‖e₂‖ * c := by
    have := InnerProductGeometry.cos_angle e₁ e₂
    dsimp [α, c] at *
    have hne : ‖e₁‖ * ‖e₂‖ ≠ 0 := (mul_pos hr1 hr2).ne'
    field_simp [hne] at this
    linarith
  have hinner_w : @inner ℝ ℝ² _ w₁ w₂ = ‖w₁‖ * ‖w₂‖ * c := by
    have := InnerProductGeometry.cos_angle w₁ w₂
    rw [hang] at this
    dsimp [α, c] at *
    have hne : ‖w₁‖ * ‖w₂‖ ≠ 0 := (mul_pos hrw1 hrw2).ne'
    field_simp [hne] at this
    linarith
  have hinner_e' : @inner ℝ ℝ² _ e₂ e₁ = ‖e₁‖ * ‖e₂‖ * c := by
    rw [real_inner_comm, hinner_e]
  have hinner_exp : @inner ℝ ℝ² _ w₁ w₂ = A₁ * A₂ + B₁ * B₂ + c * (A₁ * B₂ + B₁ * A₂) := by
    rw [hrep1, hrep2, inner_add_left, inner_add_right, inner_add_right,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_right, real_inner_smul_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hinner_e, hinner_e']
    dsimp [A₁, B₁, A₂, B₂]; ring
  have hlagrange : ∀ u v : ℝ², ‖u‖ ^ 2 * ‖v‖ ^ 2 - (@inner ℝ ℝ² _ u v) ^ 2 = (det2 u v) ^ 2 := by
    intro u v
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.inner_eq_star_dotProduct]
    simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, dotProduct, star_trivial, det2]
    ring
  have hdet_w : det2 w₁ w₂ = (a₁ * b₂ - b₁ * a₂) * det2 e₁ e₂ := by
    rw [hrep1, hrep2, det2_add_left, det2_add_right, det2_add_right,
      det2_smul_left, det2_smul_left, det2_smul_left, det2_smul_left,
      det2_smul_right, det2_smul_right, det2_smul_right, det2_smul_right,
      det2_self, det2_self]
    have hanti : det2 e₂ e₁ = -det2 e₁ e₂ := by simp only [det2]; ring
    rw [hanti]; ring
  have hdet_e_sq : (det2 e₁ e₂) ^ 2 = ‖e₁‖ ^ 2 * ‖e₂‖ ^ 2 * (1 - c ^ 2) := by
    rw [← hlagrange e₁ e₂, hinner_e]; ring
  have hdet_w_sq : (det2 w₁ w₂) ^ 2 = ‖w₁‖ ^ 2 * ‖w₂‖ ^ 2 * (1 - c ^ 2) := by
    rw [← hlagrange w₁ w₂, hinner_w]; ring
  have hsq_eq : (A₁ * B₂ - B₁ * A₂) ^ 2 = (‖w₁‖ * ‖w₂‖) ^ 2 := by
    have h1 : (A₁ * B₂ - B₁ * A₂) ^ 2 * (1 - c ^ 2) = (‖w₁‖ * ‖w₂‖) ^ 2 * (1 - c ^ 2) := by
      have h2 : (A₁ * B₂ - B₁ * A₂) ^ 2 * (1 - c ^ 2) = (det2 w₁ w₂) ^ 2 := by
        rw [hdet_w, mul_pow, hdet_e_sq]; dsimp [A₁, B₁, A₂, B₂]; ring
      rw [h2, hdet_w_sq]; ring
    exact mul_right_cancel₀ h1c2.ne' h1
  have habs_eq : |A₁ * B₂ - B₁ * A₂| = ‖w₁‖ * ‖w₂‖ := by
    have hnn : 0 ≤ ‖w₁‖ * ‖w₂‖ := by positivity
    nlinarith only [hsq_eq, sq_abs (A₁ * B₂ - B₁ * A₂), abs_nonneg (A₁ * B₂ - B₁ * A₂), hnn]
  rcases le_total (B₁ * A₂) (A₁ * B₂) with hle | hle
  · -- A₁ B₂ ≥ B₁ A₂
    have hnorm_eq : ‖w₁‖ * ‖w₂‖ = A₁ * B₂ - B₁ * A₂ := by
      rw [← habs_eq, abs_of_nonneg (sub_nonneg.mpr hle)]
    have h0 : A₁ * A₂ + B₁ * B₂ + 2 * c * (B₁ * A₂) = 0 := by
      have hw' : inner ℝ w₁ w₂ = (A₁ * B₂ - B₁ * A₂) * c := by rw [hinner_w, hnorm_eq]
      linarith [hw', hinner_exp]
    have hge : 2 * (B₁ * A₂) ≤ A₁ * A₂ + B₁ * B₂ := by
      have hmul : (B₁ * A₂) * (B₁ * A₂) ≤ (B₁ * A₂) * (A₁ * B₂) :=
        mul_le_mul_of_nonneg_left hle (mul_nonneg hB1 hA2)
      have hsq : (2 * (B₁ * A₂)) ^ 2 ≤ (A₁ * A₂ + B₁ * B₂) ^ 2 := by
        nlinarith only [sq_nonneg (A₁ * A₂ - B₁ * B₂), hmul]
      nlinarith only [hsq, mul_nonneg hA1 hA2, mul_nonneg hB1 hB2, mul_nonneg hB1 hA2]
    have hBA0 : B₁ * A₂ = 0 := by nlinarith only [h0, hge, hc_gt, mul_nonneg hB1 hA2]
    have h0' : A₁ * A₂ + B₁ * B₂ = 0 := by rw [hBA0] at h0; linarith
    have hAA0 : A₁ * A₂ = 0 := by nlinarith only [h0', mul_nonneg hA1 hA2, mul_nonneg hB1 hB2]
    have hBB0 : B₁ * B₂ = 0 := by nlinarith only [h0', mul_nonneg hA1 hA2, mul_nonneg hB1 hB2]
    have hAB_ne : A₁ ≠ 0 ∨ B₁ ≠ 0 := by
      by_contra h; push_neg at h
      have ha10 : a₁ = 0 := (mul_eq_zero.mp h.1).resolve_right hr1.ne'
      have hb10 : b₁ = 0 := (mul_eq_zero.mp h.2).resolve_right hr2.ne'
      apply hw1; rw [hrep1, ha10, hb10]; simp
    have hAB2_ne : A₂ ≠ 0 ∨ B₂ ≠ 0 := by
      by_contra h; push_neg at h
      have ha20 : a₂ = 0 := (mul_eq_zero.mp h.1).resolve_right hr1.ne'
      have hb20 : b₂ = 0 := (mul_eq_zero.mp h.2).resolve_right hr2.ne'
      apply hw2; rw [hrep2, ha20, hb20]; simp
    have hB10 : B₁ = 0 := by
      rcases hAB2_ne with h2 | h2
      · exact (mul_eq_zero.mp hBA0).resolve_right h2
      · exact (mul_eq_zero.mp hBB0).resolve_right h2
    have hA20 : A₂ = 0 := by
      rcases hAB_ne with h1 | h1
      · exact (mul_eq_zero.mp hAA0).resolve_left h1
      · exact absurd hB10 h1
    exact Or.inr ⟨(mul_eq_zero.mp hB10).resolve_right hr2.ne',
      (mul_eq_zero.mp hA20).resolve_right hr1.ne'⟩
  · -- B₁ A₂ ≥ A₁ B₂
    have hnorm_eq : ‖w₁‖ * ‖w₂‖ = B₁ * A₂ - A₁ * B₂ := by
      rw [← habs_eq, abs_of_nonpos (sub_nonpos.mpr hle)]; ring
    have h0 : A₁ * A₂ + B₁ * B₂ + 2 * c * (A₁ * B₂) = 0 := by
      have hw' : inner ℝ w₁ w₂ = (B₁ * A₂ - A₁ * B₂) * c := by rw [hinner_w, hnorm_eq]
      linarith [hw', hinner_exp]
    have hge : 2 * (A₁ * B₂) ≤ A₁ * A₂ + B₁ * B₂ := by
      have hmul : (A₁ * B₂) * (A₁ * B₂) ≤ (A₁ * B₂) * (B₁ * A₂) :=
        mul_le_mul_of_nonneg_left hle (mul_nonneg hA1 hB2)
      have hsq : (2 * (A₁ * B₂)) ^ 2 ≤ (A₁ * A₂ + B₁ * B₂) ^ 2 := by
        nlinarith only [sq_nonneg (A₁ * A₂ - B₁ * B₂), hmul]
      nlinarith only [hsq, mul_nonneg hA1 hA2, mul_nonneg hB1 hB2, mul_nonneg hA1 hB2]
    have hAB0 : A₁ * B₂ = 0 := by nlinarith only [h0, hge, hc_gt, mul_nonneg hA1 hB2]
    have h0' : A₁ * A₂ + B₁ * B₂ = 0 := by rw [hAB0] at h0; linarith
    have hAA0 : A₁ * A₂ = 0 := by nlinarith only [h0', mul_nonneg hA1 hA2, mul_nonneg hB1 hB2]
    have hBB0 : B₁ * B₂ = 0 := by nlinarith only [h0', mul_nonneg hA1 hA2, mul_nonneg hB1 hB2]
    have hAB_ne : A₁ ≠ 0 ∨ B₁ ≠ 0 := by
      by_contra h; push_neg at h
      have ha10 : a₁ = 0 := (mul_eq_zero.mp h.1).resolve_right hr1.ne'
      have hb10 : b₁ = 0 := (mul_eq_zero.mp h.2).resolve_right hr2.ne'
      apply hw1; rw [hrep1, ha10, hb10]; simp
    have hAB2_ne : A₂ ≠ 0 ∨ B₂ ≠ 0 := by
      by_contra h; push_neg at h
      have ha20 : a₂ = 0 := (mul_eq_zero.mp h.1).resolve_right hr1.ne'
      have hb20 : b₂ = 0 := (mul_eq_zero.mp h.2).resolve_right hr2.ne'
      apply hw2; rw [hrep2, ha20, hb20]; simp
    have hA10 : A₁ = 0 := by
      rcases hAB2_ne with h2 | h2
      · exact (mul_eq_zero.mp hAA0).resolve_right h2
      · exact (mul_eq_zero.mp hAB0).resolve_right h2
    have hB20 : B₂ = 0 := by
      rcases hAB_ne with h1 | h1
      · exact absurd hA10 h1
      · exact (mul_eq_zero.mp hBB0).resolve_left h1
    exact Or.inl ⟨(mul_eq_zero.mp hA10).resolve_right hr1.ne',
      (mul_eq_zero.mp hB20).resolve_right hr2.ne'⟩

private lemma fin3_third {a b : Fin 3} (hab : a ≠ b) : ∃ c : Fin 3, c ≠ a ∧ c ≠ b := by
  match a, b with
  | 0, 1 | 1, 0 => exact ⟨2, by decide, by decide⟩
  | 0, 2 | 2, 0 => exact ⟨1, by decide, by decide⟩
  | 1, 2 | 2, 1 => exact ⟨0, by decide, by decide⟩
  | 0, 0 | 1, 1 | 2, 2 => exact absurd rfl hab

private lemma fin3_mem_three {a b c : Fin 3} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (j : Fin 3) : j = a ∨ j = b ∨ j = c := by omega

private lemma fin3_univ_eq {a b c : Fin 3} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    (Finset.univ : Finset (Fin 3)) = {a, b, c} := by
  ext x
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  exact fin3_mem_three hab hca hcb x

private lemma fin3_sum_three {M : Type*} [AddCommMonoid M] {a b c : Fin 3}
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) (f : Fin 3 → M) :
    ∑ i : Fin 3, f i = f a + f b + f c := by
  rw [fin3_univ_eq hab hca hcb, Finset.sum_insert (by simp [hab, hca.symm]),
    Finset.sum_insert (by simp [hcb.symm]), Finset.sum_singleton, add_assoc]

private lemma triAngle_eq_angle_of_ne (S : Triangle ℝ ℝ²) {k j₁ j₂ : Fin 3}
    (h1 : j₁ ≠ k) (h2 : j₂ ≠ k) (h12 : j₁ ≠ j₂) :
    ∠ (S.points j₁) (S.points k) (S.points j₂) = triAngle S k := by
  fin_cases k <;> fin_cases j₁ <;> fin_cases j₂ <;>
    first
    | exact absurd rfl h1
    | exact absurd rfl h2
    | exact absurd rfl h12
    | rfl
    | exact EuclideanGeometry.angle_comm _ _ _

/-- Two triangles contained in `T` that share two distinct vertices on the same edge of `T`
cannot have disjoint interiors. -/
private lemma not_disjoint_of_shared_boundary_edge {T S₁ S₂ : Triangle ℝ ℝ²}
    (hS1 : S₁.closedInterior ⊆ T.closedInterior)
    (hS2 : S₂.closedInterior ⊆ T.closedInterior)
    {P₁ P₂ : ℝ²} (hPne : P₁ ≠ P₂) (k₀ : Fin 3)
    (hP1_0 : bary T P₁ k₀ = 0) (hP2_0 : bary T P₂ k₀ = 0)
    (h1P1 : ∃ a : Fin 3, S₁.points a = P₁) (h1P2 : ∃ b : Fin 3, S₁.points b = P₂)
    (h2P1 : ∃ a : Fin 3, S₂.points a = P₁) (h2P2 : ∃ b : Fin 3, S₂.points b = P₂) :
    ¬ Disjoint S₁.interior S₂.interior := by
  intro hdisj
  let M : ℝ² := (1 / 2 : ℝ) • P₁ + (1 / 2 : ℝ) • P₂
  let u : ℝ² := gradBary T k₀
  have hu_pos : 0 < dbary T u k₀ := by
    rw [dbary_eq_inner_gradBary, real_inner_self_eq_norm_sq]
    have hpos : 0 < ‖gradBary T k₀‖ := norm_pos_iff.mpr (gradBary_ne_zero T k₀)
    nlinarith
  have helper : ∀ (S : Triangle ℝ ℝ²), S.closedInterior ⊆ T.closedInterior →
      (∃ a : Fin 3, S.points a = P₁) → (∃ b : Fin 3, S.points b = P₂) →
      ∃ r : ℝ, 0 < r ∧ ∀ t ∈ Set.Ioo 0 r, M + t • u ∈ S.interior := by
    intro S hST ⟨a, ha⟩ ⟨b, hb⟩
    have hab : a ≠ b := fun h => hPne (by rw [← ha, ← hb, h])
    obtain ⟨c, hca, hcb⟩ := fin3_third hab
    have hM_bary : ∀ i : Fin 3, bary S M i = if i = a ∨ i = b then 1 / 2 else 0 := by
      have hw : ∑ i : Fin 3, (if i = a ∨ i = b then (1 / 2 : ℝ) else 0) = 1 := by
        rw [fin3_sum_three hab hca hcb]
        simp only [true_or, or_true, ↓reduceIte, hca, hcb, or_self, add_zero]
        norm_num
      have hx : Finset.univ.affineCombination ℝ S.points
          (fun i => if i = a ∨ i = b then (1 / 2 : ℝ) else 0) = M := by
        rw [Finset.affineCombination_eq_linear_combination _ _ _ hw, fin3_sum_three hab hca hcb]
        simp only [true_or, or_true, ↓reduceIte, hca, hcb, or_self, zero_smul, add_zero, ha, hb]
        rfl
      exact congrFun (bary_unique S hw hx).symm
    -- Show dbary S u c > 0 using bary T (S.points c) k₀ > 0!
    have hSc_pos : 0 < bary T (S.points c) k₀ := by
      have hnn := (mem_closedInterior_iff_bary T (S.points c)).mp (hST (S.point_mem_closedInterior c)) k₀
      rcases eq_or_lt_of_le hnn with h0 | hpos
      · exfalso
        have hba : bary T (S.points a) k₀ = 0 := by rw [ha]; exact hP1_0
        have hbb : bary T (S.points b) k₀ = 0 := by rw [hb]; exact hP2_0
        have hall0 : ∀ j : Fin 3, bary T (S.points j) k₀ = 0 := fun j => by
          rcases fin3_mem_three hab hca hcb j with rfl | rfl | rfl
          · exact hba
          · exact hbb
          · exact h0.symm
        have hd1 : dbary T (S.points 1 - S.points 0) k₀ = 0 := by
          have h := bary_add_smul T (S.points 0) (S.points 1 - S.points 0) 1 k₀
          simp only [one_smul, add_sub_cancel, one_mul, hall0 0, hall0 1] at h; linarith
        have hd2 : dbary T (S.points 2 - S.points 0) k₀ = 0 := by
          have h := bary_add_smul T (S.points 0) (S.points 2 - S.points 0) 1 k₀
          simp only [one_smul, add_sub_cancel, one_mul, hall0 0, hall0 2] at h; linarith
        have hu0 : dbary T u k₀ = 0 := by
          conv_lhs => rw [dir_eq_sum_dbary S u]
          rw [dbary_eq_inner_gradBary, inner_add_right, real_inner_smul_right, real_inner_smul_right,
            ← dbary_eq_inner_gradBary, ← dbary_eq_inner_gradBary, hd1, hd2]; ring
        linarith
      · exact hpos
    have hduc : 0 < dbary S u c := by
      have hrep := dir_eq_sum_dbary_at S a b c hab.symm hca hcb.symm u
      have hba : dbary T (S.points b - S.points a) k₀ = 0 := by
        have h := bary_add_smul T (S.points a) (S.points b - S.points a) 1 k₀
        simp only [one_smul, add_sub_cancel, one_mul] at h
        have hpa : bary T (S.points a) k₀ = 0 := by rw [ha]; exact hP1_0
        have hpb : bary T (S.points b) k₀ = 0 := by rw [hb]; exact hP2_0
        linarith
      have hca' : dbary T (S.points c - S.points a) k₀ = bary T (S.points c) k₀ := by
        have h := bary_add_smul T (S.points a) (S.points c - S.points a) 1 k₀
        simp only [one_smul, add_sub_cancel, one_mul] at h
        have hpa : bary T (S.points a) k₀ = 0 := by rw [ha]; exact hP1_0
        linarith
      have heq : dbary T u k₀ = dbary S u c * bary T (S.points c) k₀ := by
        conv_lhs => rw [hrep]
        rw [dbary_eq_inner_gradBary, inner_add_right, real_inner_smul_right, real_inner_smul_right,
          ← dbary_eq_inner_gradBary, ← dbary_eq_inner_gradBary, hba, hca']; ring
      nlinarith only [hu_pos, hSc_pos, heq]
    -- Now for small t > 0, all 3 barycentric coords of M + t • u in S are > 0!
    have hexk : ∀ i : Fin 3, ∃ r : ℝ, 0 < r ∧ ∀ t ∈ Set.Ioo 0 r, 0 < bary S M i + t * dbary S u i := by
      intro i
      by_cases hic : i = c
      · rw [hic]
        refine ⟨1, zero_lt_one, fun t ht => ?_⟩
        rw [hM_bary c, if_neg (by simp [hca, hcb]), zero_add]
        exact mul_pos ht.1 hduc
      · have hiab : i = a ∨ i = b := by
          rcases fin3_mem_three hab hca hcb i with rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
          · exact absurd rfl hic
        have hhalf : bary S M i = 1 / 2 := by rw [hM_bary i, if_pos hiab]
        by_cases hneg : dbary S u i < 0
        · have hneg' : 0 < -dbary S u i := neg_pos.mpr hneg
          refine ⟨(1 / 4 : ℝ) / (-dbary S u i), by positivity, fun t ht => ?_⟩
          have := mul_lt_mul_of_pos_right ht.2 hneg'
          have hsimp : (1 / 4 : ℝ) / (-dbary S u i) * (-dbary S u i) = 1 / 4 := by
            have hdne : dbary S u i ≠ 0 := hneg.ne
            field_simp [hdne]
          linarith
        · push_neg at hneg
          exact ⟨1, zero_lt_one, fun t ht => by rw [hhalf]; nlinarith only [ht.1, hneg]⟩
    choose rk hrk hpk using hexk
    refine ⟨min (rk 0) (min (rk 1) (rk 2)), lt_min (hrk 0) (lt_min (hrk 1) (hrk 2)), fun t ht => ?_⟩
    rw [mem_interior_iff_bary]; intro i; rw [bary_add_smul]
    apply hpk i t ⟨ht.1, ?_⟩
    match i with
    | 0 => exact lt_of_lt_of_le ht.2 (min_le_left _ _)
    | 1 => exact lt_of_lt_of_le ht.2 ((min_le_right _ _).trans (min_le_left _ _))
    | 2 => exact lt_of_lt_of_le ht.2 ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨r₁, hr₁, h₁⟩ := helper S₁ hS1 h1P1 h1P2
  obtain ⟨r₂, hr₂, h₂⟩ := helper S₂ hS2 h2P1 h2P2
  let t := min r₁ r₂ / 2
  have hmin : 0 < min r₁ r₂ := lt_min hr₁ hr₂
  have ht0 : 0 < t := by dsimp [t]; positivity
  have ht1 : t < r₁ := lt_of_lt_of_le (by dsimp [t]; linarith) (min_le_left r₁ r₂)
  have ht2 : t < r₂ := lt_of_lt_of_le (by dsimp [t]; linarith) (min_le_right r₁ r₂)
  exact Set.disjoint_left.mp hdisj (h₁ t ⟨ht0, ht1⟩) (h₂ t ⟨ht0, ht2⟩)

set_option maxHeartbeats 800000 in
/-- Main impossibility theorem: a triangle with ℤ-linearly independent angles is not
simili-cuttable into 2, 3, or 5 similar triangles. -/
private lemma not_similiCuttable_2_3_5 (T : Triangle ℝ ℝ²)
    (hIndep : ∀ p q r : ℤ,
      (p : ℝ) * triAngle T 0 + (q : ℝ) * triAngle T 1 + (r : ℝ) * triAngle T 2 = 0 →
        p = 0 ∧ q = 0 ∧ r = 0)
    (n : ℕ) (hn : n = 2 ∨ n = 3 ∨ n = 5) : ¬ Erdos633.IsSimiliCuttable n T := by
  classical
  rintro ⟨Ts, hsim, hdisj, hunion⟩
  have hn_pos : 0 < n := by omega
  have hn_ge2 : 2 ≤ n := by omega
  let i₀ : Fin n := ⟨0, hn_pos⟩
  have hsub : ∀ i : Fin n, (Ts i).closedInterior ⊆ T.closedInterior := fun i => by
    rw [← hunion]; exact Set.subset_iUnion (fun j => (Ts j).closedInterior) i
  -- All Ts i have the same three angles as Ts i₀
  have hang_eq : ∀ (i : Fin n) (m : Fin 3), triAngle (Ts i) m = triAngle (Ts i₀) m := by
    intro i m
    have hsi : ![(Ts i).points 0, (Ts i).points 1, (Ts i).points 2] ∼
        ![(Ts i₀).points 0, (Ts i₀).points 1, (Ts i₀).points 2] := by
      have h1 : ![(Ts i).points 0, (Ts i).points 1, (Ts i).points 2] = (Ts i).points := by
        funext j; fin_cases j <;> rfl
      have h2 : ![(Ts i₀).points 0, (Ts i₀).points 1, (Ts i₀).points 2] = (Ts i₀).points := by
        funext j; fin_cases j <;> rfl
      rw [h1, h2]; exact hsim i i₀
    obtain ⟨h1, h2, h0⟩ := hsi.angle_eq_all
    fin_cases m
    · simpa [triAngle, EuclideanGeometry.angle_comm] using h0
    · simpa [triAngle, EuclideanGeometry.angle_comm] using h1
    · simpa [triAngle, EuclideanGeometry.angle_comm] using h2
  set a₀ := triAngle (Ts i₀) 0
  set a₁ := triAngle (Ts i₀) 1
  set a₂ := triAngle (Ts i₀) 2
  have ha_sum : a₀ + a₁ + a₂ = Real.pi := by
    have hne : (Ts i₀).points 1 ≠ (Ts i₀).points 0 := (Ts i₀).independent.injective.ne (by decide)
    have hsum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi ((Ts i₀).points 2) hne
    dsimp [a₀, a₁, a₂, triAngle]
    linarith [EuclideanGeometry.angle_comm ((Ts i₀).points 1) ((Ts i₀).points 0) ((Ts i₀).points 2),
      EuclideanGeometry.angle_comm ((Ts i₀).points 2) ((Ts i₀).points 1) ((Ts i₀).points 0),
      EuclideanGeometry.angle_comm ((Ts i₀).points 0) ((Ts i₀).points 2) ((Ts i₀).points 1)]
  have hT_sum : triAngle T 0 + triAngle T 1 + triAngle T 2 = Real.pi := by
    have hne : T.points 1 ≠ T.points 0 := T.independent.injective.ne (by decide)
    have hsum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi (T.points 2) hne
    dsimp [triAngle]
    linarith [EuclideanGeometry.angle_comm (T.points 1) (T.points 0) (T.points 2),
      EuclideanGeometry.angle_comm (T.points 2) (T.points 1) (T.points 0),
      EuclideanGeometry.angle_comm (T.points 0) (T.points 2) (T.points 1)]
  -- Helper: if P is a vertex of some Ts i or of T, then P is not in (Ts j).interior for any j
  have not_in_interior_of_vert : ∀ (P : ℝ²),
      ((∃ i : Fin n, ∃ m : Fin 3, (Ts i).points m = P) ∨ (∃ k : Fin 3, T.points k = P)) →
      ∀ j : Fin n, P ∉ (Ts j).interior := by
    intro P hP j hj
    rcases hP with ⟨i, m, rfl⟩ | ⟨k, rfl⟩
    · have hij : i ≠ j := by
        intro h; subst h
        have := (mem_interior_iff_bary (Ts i) _).mp hj
        obtain ⟨m', hm'⟩ : ∃ m' : Fin 3, m' ≠ m := by
          fin_cases m
          · exact ⟨1, by decide⟩
          · exact ⟨0, by decide⟩
          · exact ⟨0, by decide⟩
        have h0 := this m'; rw [bary_point, if_neg hm'] at h0; linarith
      have hd := dirSet_disjoint (hdisj hij) ((Ts i).points m)
      have hfull : dirSet (Ts j) ((Ts i).points m) = Set.Ico 0 (2 * Real.pi) := by
        ext θ; simp only [mem_dirSet_iff, and_iff_left_iff_imp]
        intro _ l; exact Or.inl ((mem_interior_iff_bary (Ts j) _).mp hj l)
      have hsub_dir : dirSet (Ts i) ((Ts i).points m) ⊆ dirSet (Ts j) ((Ts i).points m) := by
        rw [hfull]; exact fun θ hθ => hθ.1
      have hempty : dirSet (Ts i) ((Ts i).points m) = ∅ :=
        Set.eq_empty_of_subset_empty (fun x hx => Set.disjoint_left.mp (hd.mono_right hsub_dir) hx hx)
      have hvol := (measurableSet_and_volume_dirSet (Ts i) ((Ts i).points m)).2
      rw [hempty, measure_empty] at hvol
      have hpos : 0 < angContrib (Ts i) ((Ts i).points m) := by
        unfold angContrib
        rw [if_neg (not_not.mpr ((Ts i).point_mem_closedInterior m))]
        have hni : (Ts i).points m ∉ (Ts i).interior := by
          intro h; obtain ⟨m', hm'⟩ : ∃ m' : Fin 3, m' ≠ m := by
            fin_cases m
            · exact ⟨1, by decide⟩
            · exact ⟨0, by decide⟩
            · exact ⟨0, by decide⟩
          have := (mem_interior_iff_bary (Ts i) _).mp h m'; rw [bary_point, if_neg hm'] at this; linarith
        have hne : ¬ onOpenEdge (Ts i) ((Ts i).points m) := fun h => h.2.2 m rfl
        rw [if_neg hni, if_neg hne, Finset.sum_eq_single m]
        · simp [(triAngle_pos_lt_pi (Ts i) m).1]
        · intro j' _ hj'; rw [if_neg ((Ts i).independent.injective.ne hj')]
        · intro hm'; exact absurd (Finset.mem_univ m) hm'
      have hne0 : ENNReal.ofReal (angContrib (Ts i) ((Ts i).points m)) ≠ 0 :=
        (ENNReal.ofReal_pos.mpr hpos).ne'
      exact hne0 hvol.symm
    · have hTin : T.points k ∈ T.interior := interior_subset_of_closedInterior_subset (hsub j) hj
      obtain ⟨k', hk'⟩ : ∃ k' : Fin 3, k' ≠ k := by
        fin_cases k
        · exact ⟨1, by decide⟩
        · exact ⟨0, by decide⟩
        · exact ⟨0, by decide⟩
      have := (mem_interior_iff_bary T _).mp hTin k'
      rw [bary_point, if_neg hk'] at this; linarith
  -- Decomposition of angContrib (Ts i) P when P ∉ (Ts i).interior
  have angContrib_eq_of_not_mem_interior : ∀ (i : Fin n) (P : ℝ²), P ∉ (Ts i).interior →
      angContrib (Ts i) P =
        (if onOpenEdge (Ts i) P then Real.pi else 0) +
        ∑ m : Fin 3, if (Ts i).points m = P then triAngle (Ts i₀) m else 0 := by
    intro i P hni
    unfold angContrib
    by_cases hcl : P ∉ (Ts i).closedInterior
    · rw [if_pos hcl]
      have hnoe : ¬ onOpenEdge (Ts i) P := fun h => hcl h.1
      have hnv : ∀ m : Fin 3, (Ts i).points m ≠ P := fun m hm =>
        hcl (hm ▸ (Ts i).point_mem_closedInterior m)
      simp [hnoe, hnv]
    · push_neg at hcl
      rw [if_neg (not_not.mpr hcl), if_neg hni]
      by_cases hoe : onOpenEdge (Ts i) P
      · rw [if_pos hoe, if_pos hoe]
        have hnv : ∀ m : Fin 3, (Ts i).points m ≠ P := hoe.2.2
        simp [hnv]
      · rw [if_neg hoe, if_neg hoe, zero_add]
        apply Finset.sum_congr rfl; intro m _
        rw [hang_eq i m]
  -- Count functions at any point P
  let cnt (P : ℝ²) (m : Fin 3) : ℕ := (Finset.univ.filter fun i : Fin n => (Ts i).points m = P).card
  let ecnt (P : ℝ²) : ℕ := (Finset.univ.filter fun i : Fin n => onOpenEdge (Ts i) P).card
  have sum_eq_lin : ∀ P : ℝ², (∀ j : Fin n, P ∉ (Ts j).interior) →
      angContrib T P =
        (ecnt P : ℝ) * Real.pi + (cnt P 0 : ℝ) * a₀ + (cnt P 1 : ℝ) * a₁ + (cnt P 2 : ℝ) * a₂ := by
    intro P hP
    rw [← sum_angContrib_eq T Ts hdisj hunion P]
    have h1 : ∑ i : Fin n, angContrib (Ts i) P =
        (∑ i : Fin n, if onOpenEdge (Ts i) P then Real.pi else 0) +
        ∑ i : Fin n, ∑ m : Fin 3, if (Ts i).points m = P then triAngle (Ts i₀) m else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _
      exact angContrib_eq_of_not_mem_interior i P (hP i)
    rw [h1, Finset.sum_comm]
    have he : (∑ i : Fin n, if onOpenEdge (Ts i) P then Real.pi else 0) = (ecnt P : ℝ) * Real.pi := by
      simp [ecnt, Finset.sum_ite, Finset.filter_eq']
    have hc : ∀ m : Fin 3, (∑ i : Fin n, if (Ts i).points m = P then triAngle (Ts i₀) m else 0) =
        (cnt P m : ℝ) * triAngle (Ts i₀) m := fun m => by
      simp [cnt, Finset.sum_ite]
    rw [he, Fin.sum_univ_three, hc 0, hc 1, hc 2]
    dsimp [a₀, a₁, a₂]; ring
  -- Evaluate at the 3 vertices of T
  have hT_vert : ∀ k : Fin 3, angContrib T (T.points k) = triAngle T k := by
    intro k
    unfold angContrib
    rw [if_neg (not_not.mpr (T.point_mem_closedInterior k))]
    have hni : T.points k ∉ T.interior := by
      intro h; obtain ⟨k', hk'⟩ : ∃ k' : Fin 3, k' ≠ k := by
        fin_cases k
        · exact ⟨1, by decide⟩
        · exact ⟨0, by decide⟩
        · exact ⟨0, by decide⟩
      have := (mem_interior_iff_bary T _).mp h k'; rw [bary_point, if_neg hk'] at this; linarith
    have hne : ¬ onOpenEdge T (T.points k) := fun h => h.2.2 k rfl
    rw [if_neg hni, if_neg hne, Finset.sum_eq_single k]
    · simp
    · intro j _ hjk; rw [if_neg (T.independent.injective.ne hjk)]
    · intro hk; exact absurd (Finset.mem_univ k) hk
  have hecnt_T : ∀ k : Fin 3, ecnt (T.points k) = 0 := by
    intro k
    have hlin := sum_eq_lin (T.points k) (not_in_interior_of_vert (T.points k) (Or.inr ⟨k, rfl⟩))
    rw [hT_vert k] at hlin
    have hlt := (triAngle_pos_lt_pi T k).2
    have h0 := (triAngle_pos_lt_pi (Ts i₀) 0).1
    have h1 := (triAngle_pos_lt_pi (Ts i₀) 1).1
    have h2 := (triAngle_pos_lt_pi (Ts i₀) 2).1
    by_contra hne
    have hge1 : (1 : ℝ) ≤ (ecnt (T.points k) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hne
    have hc0 : (0 : ℝ) ≤ (cnt (T.points k) 0 : ℝ) := Nat.cast_nonneg _
    have hc1 : (0 : ℝ) ≤ (cnt (T.points k) 1 : ℝ) := Nat.cast_nonneg _
    have hc2 : (0 : ℝ) ≤ (cnt (T.points k) 2 : ℝ) := Nat.cast_nonneg _
    nlinarith [Real.pi_pos]
  have hT_eq : ∀ k : Fin 3,
      triAngle T k = (cnt (T.points k) 0 : ℝ) * a₀ +
                     (cnt (T.points k) 1 : ℝ) * a₁ +
                     (cnt (T.points k) 2 : ℝ) * a₂ := by
    intro k
    have hlin := sum_eq_lin (T.points k) (not_in_interior_of_vert (T.points k) (Or.inr ⟨k, rfl⟩))
    rw [hT_vert k, hecnt_T k, Nat.cast_zero, zero_mul, zero_add] at hlin
    exact hlin
  -- Therefore a₀, a₁, a₂ are ℤ-linearly independent!
  have ha_indep : ∀ p q r : ℤ, (p : ℝ) * a₀ + (q : ℝ) * a₁ + (r : ℝ) * a₂ = 0 →
      p = 0 ∧ q = 0 ∧ r = 0 := by
    refine indep_of_three_in_span_three hIndep (fun k m => (cnt (T.points k) m : ℤ)) ?_ ?_ ?_
    · simpa using hT_eq 0
    · simpa using hT_eq 1
    · simpa using hT_eq 2
  -- Sum over k = 0, 1, 2: total count of each m across the 3 corners of T is 1!
  have hsum_cnt : ∀ m : Fin 3, cnt (T.points 0) m + cnt (T.points 1) m + cnt (T.points 2) m = 1 := by
    have hcomb : (((cnt (T.points 0) 0 + cnt (T.points 1) 0 + cnt (T.points 2) 0 : ℕ) - 1 : ℤ) : ℝ) * a₀ +
        (((cnt (T.points 0) 1 + cnt (T.points 1) 1 + cnt (T.points 2) 1 : ℕ) - 1 : ℤ) : ℝ) * a₁ +
        (((cnt (T.points 0) 2 + cnt (T.points 1) 2 + cnt (T.points 2) 2 : ℕ) - 1 : ℤ) : ℝ) * a₂ = 0 := by
      push_cast; linarith [hT_eq 0, hT_eq 1, hT_eq 2, hT_sum, ha_sum]
    obtain ⟨h0, h1, h2⟩ := ha_indep _ _ _ hcomb
    intro m; match m with | 0 => omega | 1 => omega | 2 => omega
  -- At each corner k of T, total count of triangles having T.points k as a vertex is 1!
  have hcorner_deg : ∀ k : Fin 3, cnt (T.points k) 0 + cnt (T.points k) 1 + cnt (T.points k) 2 = 1 := by
    have hge1 : ∀ k : Fin 3, 1 ≤ cnt (T.points k) 0 + cnt (T.points k) 1 + cnt (T.points k) 2 := by
      intro k
      by_contra h0
      have h00 : cnt (T.points k) 0 = 0 := by omega
      have h01 : cnt (T.points k) 1 = 0 := by omega
      have h02 : cnt (T.points k) 2 = 0 := by omega
      have hk := hT_eq k
      rw [h00, h01, h02] at hk; simp at hk
      linarith [(triAngle_pos_lt_pi T k).1]
    have htot : (cnt (T.points 0) 0 + cnt (T.points 0) 1 + cnt (T.points 0) 2) +
        (cnt (T.points 1) 0 + cnt (T.points 1) 1 + cnt (T.points 1) 2) +
        (cnt (T.points 2) 0 + cnt (T.points 2) 1 + cnt (T.points 2) 2) = 3 := by
      have s0 := hsum_cnt 0; have s1 := hsum_cnt 1; have s2 := hsum_cnt 2; omega
    have g0 := hge1 0; have g1 := hge1 1; have g2 := hge1 2
    intro k; match k with | 0 => omega | 1 => omega | 2 => omega
  -- For any point P, count of triangles having P as a vertex equals cnt P 0 + cnt P 1 + cnt P 2
  let deg (P : ℝ²) : ℕ := (Finset.univ.filter fun i : Fin n => ∃ m : Fin 3, (Ts i).points m = P).card
  have deg_eq : ∀ P : ℝ², deg P = cnt P 0 + cnt P 1 + cnt P 2 := by
    intro P
    have hdisj01 : Disjoint (Finset.univ.filter fun i : Fin n => (Ts i).points 0 = P)
        (Finset.univ.filter fun i : Fin n => (Ts i).points 1 = P) := by
      rw [Finset.disjoint_left]; intro i hi0 hi1
      have e0 := (Finset.mem_filter.mp hi0).2
      have e1 := (Finset.mem_filter.mp hi1).2
      exact (Ts i).independent.injective.ne (by decide : (0 : Fin 3) ≠ 1) (e0.trans e1.symm)
    have hdisj012 : Disjoint ((Finset.univ.filter fun i : Fin n => (Ts i).points 0 = P) ∪
          (Finset.univ.filter fun i : Fin n => (Ts i).points 1 = P))
        (Finset.univ.filter fun i : Fin n => (Ts i).points 2 = P) := by
      rw [Finset.disjoint_left]; intro i hi01 hi2
      have e2 := (Finset.mem_filter.mp hi2).2
      rcases Finset.mem_union.mp hi01 with hi0 | hi1
      · exact (Ts i).independent.injective.ne (by decide : (0 : Fin 3) ≠ 2) ((Finset.mem_filter.mp hi0).2.trans e2.symm)
      · exact (Ts i).independent.injective.ne (by decide : (1 : Fin 3) ≠ 2) ((Finset.mem_filter.mp hi1).2.trans e2.symm)
    have hun : (Finset.univ.filter fun i : Fin n => ∃ m : Fin 3, (Ts i).points m = P) =
        ((Finset.univ.filter fun i : Fin n => (Ts i).points 0 = P) ∪
         (Finset.univ.filter fun i : Fin n => (Ts i).points 1 = P)) ∪
        (Finset.univ.filter fun i : Fin n => (Ts i).points 2 = P) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      constructor
      · rintro ⟨m, hm⟩
        match m with
        | 0 => exact Or.inl (Or.inl hm)
        | 1 => exact Or.inl (Or.inr hm)
        | 2 => exact Or.inr hm
      · rintro ((h | h) | h)
        · exact ⟨0, h⟩
        · exact ⟨1, h⟩
        · exact ⟨2, h⟩
    change (Finset.univ.filter fun i : Fin n => ∃ m : Fin 3, (Ts i).points m = P).card = _
    rw [hun, Finset.card_union_of_disjoint hdisj012, Finset.card_union_of_disjoint hdisj01]
  -- Unique corner triangle i_k at each corner k of T, and its other 2 vertices lie on the 2 open edges
  have hcorner_uniq : ∀ k : Fin 3, ∃! i : Fin n, ∃ m : Fin 3, (Ts i).points m = T.points k := by
    intro k
    have hcard : deg (T.points k) = 1 := by rw [deg_eq, hcorner_deg k]
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
    have hi_mem : i ∈ Finset.univ.filter (fun i : Fin n => ∃ m : Fin 3, (Ts i).points m = T.points k) := by
      rw [hi]; exact Finset.mem_singleton_self i
    refine ⟨i, (Finset.mem_filter.mp hi_mem).2, fun j hj => ?_⟩
    have hjmem : j ∈ Finset.univ.filter (fun i : Fin n => ∃ m : Fin 3, (Ts i).points m = T.points k) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
    rw [hi] at hjmem
    exact Finset.mem_singleton.mp hjmem
  choose cornerI cornerI_spec cornerI_uniq using hcorner_uniq
  -- Corner triangle Ts (cornerI k) has its angle at T.points k equal to triAngle T k
  have hcorner_ang : ∀ (k : Fin 3) (m : Fin 3), (Ts (cornerI k)).points m = T.points k →
      triAngle (Ts (cornerI k)) m = triAngle T k := by
    intro k m hm
    have h1 : 1 ≤ cnt (T.points k) m := Finset.card_pos.mpr ⟨cornerI k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩⟩
    have hsum := hcorner_deg k
    rw [hang_eq, hT_eq k]
    match m with
    | 0 =>
      have hc0 : cnt (T.points k) 0 = 1 := by omega
      have hc1 : cnt (T.points k) 1 = 0 := by omega
      have hc2 : cnt (T.points k) 2 = 0 := by omega
      rw [hc0, hc1, hc2]; simp [a₀]
    | 1 =>
      have hc0 : cnt (T.points k) 0 = 0 := by omega
      have hc1 : cnt (T.points k) 1 = 1 := by omega
      have hc2 : cnt (T.points k) 2 = 0 := by omega
      rw [hc0, hc1, hc2]; simp [a₁]
    | 2 =>
      have hc0 : cnt (T.points k) 0 = 0 := by omega
      have hc1 : cnt (T.points k) 1 = 0 := by omega
      have hc2 : cnt (T.points k) 2 = 1 := by omega
      rw [hc0, hc1, hc2]; simp [a₂]
  -- First show the other 2 vertices of Ts (cornerI k) lie on the two closed edges incident to k
  have hcorner_rays : ∀ k j₁ j₂ : Fin 3, j₁ ≠ k → j₂ ≠ k → j₁ ≠ j₂ →
      ∃ m₁ m₂ : Fin 3, m₁ ≠ m₂ ∧
        (Ts (cornerI k)).points m₁ ≠ T.points k ∧
        (Ts (cornerI k)).points m₂ ≠ T.points k ∧
        bary T ((Ts (cornerI k)).points m₁) j₂ = 0 ∧
        0 < bary T ((Ts (cornerI k)).points m₁) j₁ ∧
        bary T ((Ts (cornerI k)).points m₂) j₁ = 0 ∧
        0 < bary T ((Ts (cornerI k)).points m₂) j₂ := by
    intro k j₁ j₂ h1k h2k h12
    obtain ⟨m, hm⟩ := cornerI_spec k
    obtain ⟨m₁, m₂, hm1, hm2, hm12⟩ : ∃ m₁ m₂ : Fin 3, m₁ ≠ m ∧ m₂ ≠ m ∧ m₁ ≠ m₂ := by
      fin_cases m
      · exact ⟨1, 2, by decide, by decide, by decide⟩
      · exact ⟨2, 0, by decide, by decide, by decide⟩
      · exact ⟨0, 1, by decide, by decide, by decide⟩
    let w₁ := (Ts (cornerI k)).points m₁ - T.points k
    let w₂ := (Ts (cornerI k)).points m₂ - T.points k
    let e₁ := T.points j₁ - T.points k
    let e₂ := T.points j₂ - T.points k
    have he1 : e₁ ≠ 0 := sub_ne_zero.mpr (T.independent.injective.ne h1k)
    have he2 : e₂ ≠ 0 := sub_ne_zero.mpr (T.independent.injective.ne h2k)
    have hne1 : (Ts (cornerI k)).points m₁ ≠ T.points k := by
      rw [← hm]; exact (Ts (cornerI k)).independent.injective.ne hm1
    have hne2 : (Ts (cornerI k)).points m₂ ≠ T.points k := by
      rw [← hm]; exact (Ts (cornerI k)).independent.injective.ne hm2
    have hw1 : w₁ ≠ 0 := sub_ne_zero.mpr hne1
    have hw2 : w₂ ≠ 0 := sub_ne_zero.mpr hne2
    have hdet : det2 e₁ e₂ ≠ 0 := by
      intro h0
      have hfull : ∀ dir : ℝ², det2 dir e₂ = 0 := fun dir => by
        conv_lhs => rw [dir_eq_sum_dbary_at T k j₁ j₂ h1k h2k h12 dir]
        rw [det2_add_left, det2_smul_left, det2_smul_left, det2_self, mul_zero, add_zero, h0, mul_zero]
      have htest := hfull !₂[e₂.ofLp 1, -e₂.ofLp 0]
      have hsq : e₂.ofLp 0 ^ 2 + e₂.ofLp 1 ^ 2 = 0 := by
        have h' : e₂.ofLp 1 * e₂.ofLp 1 - (-e₂.ofLp 0) * e₂.ofLp 0 = 0 := htest
        linarith
      apply he2; ext c; match c with
      | 0 => change e₂.ofLp 0 = 0; nlinarith
      | 1 => change e₂.ofLp 1 = 0; nlinarith
    have hrep1 : w₁ = dbary T w₁ j₁ • e₁ + dbary T w₁ j₂ • e₂ :=
      dir_eq_sum_dbary_at T k j₁ j₂ h1k h2k h12 w₁
    have hrep2 : w₂ = dbary T w₂ j₁ • e₁ + dbary T w₂ j₂ • e₂ :=
      dir_eq_sum_dbary_at T k j₁ j₂ h1k h2k h12 w₂
    have hdb_eq : ∀ (x : ℝ²) (j : Fin 3), j ≠ k → dbary T (x - T.points k) j = bary T x j := by
      intro x j hjk
      have h := bary_add_smul T (T.points k) (x - T.points k) 1 j
      simp only [one_smul, add_sub_cancel, one_mul, bary_point, if_neg hjk, zero_add] at h
      exact h.symm
    have hnn1 := (mem_closedInterior_iff_bary T _).mp (hsub (cornerI k) ((Ts (cornerI k)).point_mem_closedInterior m₁))
    have hnn2 := (mem_closedInterior_iff_bary T _).mp (hsub (cornerI k) ((Ts (cornerI k)).point_mem_closedInterior m₂))
    have ha1 : 0 ≤ dbary T w₁ j₁ := by rw [hdb_eq _ _ h1k]; exact hnn1 j₁
    have hb1 : 0 ≤ dbary T w₁ j₂ := by rw [hdb_eq _ _ h2k]; exact hnn1 j₂
    have ha2 : 0 ≤ dbary T w₂ j₁ := by rw [hdb_eq _ _ h1k]; exact hnn2 j₁
    have hb2 : 0 ≤ dbary T w₂ j₂ := by rw [hdb_eq _ _ h2k]; exact hnn2 j₂
    have hang_w : InnerProductGeometry.angle w₁ w₂ = InnerProductGeometry.angle e₁ e₂ := by
      have h1 : InnerProductGeometry.angle w₁ w₂ = triAngle (Ts (cornerI k)) m := by
        dsimp [w₁, w₂]; rw [← hm]
        exact triAngle_eq_angle_of_ne (Ts (cornerI k)) hm1 hm2 hm12
      have h2 : InnerProductGeometry.angle e₁ e₂ = triAngle T k := by
        dsimp [e₁, e₂]
        exact triAngle_eq_angle_of_ne T h1k h2k h12
      rw [h1, h2]; exact hcorner_ang k m hm
    rcases cone_angle_eq_imp_boundary he1 he2 hw1 hw2 hdet ha1 hb1 ha2 hb2 hrep1 hrep2 hang_w with
      ⟨h1a, h2b⟩ | ⟨h1b, h2a⟩
    · have h1pos : 0 < dbary T w₁ j₂ := by
        rcases eq_or_lt_of_le hb1 with h0 | hpos
        · exfalso; apply hw1; rw [hrep1, h1a, ← h0]; simp
        · exact hpos
      have h2pos : 0 < dbary T w₂ j₁ := by
        rcases eq_or_lt_of_le ha2 with h0 | hpos
        · exfalso; apply hw2; rw [hrep2, h2b, ← h0]; simp
        · exact hpos
      rw [hdb_eq _ _ h1k] at h1a h2pos; rw [hdb_eq _ _ h2k] at h2b h1pos
      exact ⟨m₂, m₁, hm12.symm, hne2, hne1, h2b, h2pos, h1a, h1pos⟩
    · have h1pos : 0 < dbary T w₁ j₁ := by
        rcases eq_or_lt_of_le ha1 with h0 | hpos
        · exfalso; apply hw1; rw [hrep1, h1b, ← h0]; simp
        · exact hpos
      have h2pos : 0 < dbary T w₂ j₂ := by
        rcases eq_or_lt_of_le hb2 with h0 | hpos
        · exfalso; apply hw2; rw [hrep2, h2a, ← h0]; simp
        · exact hpos
      rw [hdb_eq _ _ h2k] at h1b h2pos; rw [hdb_eq _ _ h1k] at h2a h1pos
      exact ⟨m₁, m₂, hm12, hne1, hne2, h1b, h1pos, h2a, h2pos⟩
  -- Now prove cornerI is injective!
  have hcornerI_inj : Function.Injective cornerI := by
    intro k₁ k₂ heq
    by_contra hne
    obtain ⟨k₃, h31, h32⟩ := fin3_third hne
    obtain ⟨a₁, ha₁⟩ := cornerI_spec k₁
    obtain ⟨a₂, ha₂⟩ := cornerI_spec k₂
    rw [← heq] at ha₂
    have ha12 : a₁ ≠ a₂ := fun h => T.independent.injective.ne hne (by rw [← ha₁, ← ha₂, h])
    obtain ⟨a₃, ha31, ha32⟩ := fin3_third ha12
    -- Apply hcorner_rays at k₁ (with j₁ = k₂, j₂ = k₃)
    obtain ⟨m₁, m₂, hm12, hm1ne, hm2ne, hm1_k3, hm1_k2, hm2_k2, hm2_k3⟩ :=
      hcorner_rays k₁ k₂ k₃ (Ne.symm hne) h31 (Ne.symm h32)
    have hma2 : m₂ ≠ a₁ := fun h => hm2ne (h ▸ ha₁)
    have ha3_k2 : bary T ((Ts (cornerI k₁)).points a₃) k₂ = 0 := by
      have hne_a2 : m₂ ≠ a₂ := by
        intro h; rw [h, ha₂, bary_point, if_pos rfl] at hm2_k2; norm_num at hm2_k2
      have hm2_eq : m₂ = a₃ := by omega
      exact hm2_eq ▸ hm2_k2
    -- Symmetrically apply hcorner_rays at k₂ (with j₁ = k₁, j₂ = k₃)
    obtain ⟨r₁, r₂, hr12, hr1ne, hr2ne, _, _, hr2_k1, _⟩ :=
      hcorner_rays k₂ k₁ k₃ hne h32 h31.symm
    rw [← heq] at hr1ne hr2ne hr2_k1
    have ha3_k1 : bary T ((Ts (cornerI k₁)).points a₃) k₁ = 0 := by
      have hne_a2 : r₂ ≠ a₂ := fun h => hr2ne (h ▸ ha₂)
      have hne_a1 : r₂ ≠ a₁ := by
        intro h; rw [h, ha₁, bary_point, if_pos rfl] at hr2_k1; norm_num at hr2_k1
      have hr2_eq : r₂ = a₃ := by omega
      exact hr2_eq ▸ hr2_k1
    -- So bary T ((Ts (cornerI k₁)).points a₃) k₃ = 1, hence it equals T.points k₃!
    have ha₃ : (Ts (cornerI k₁)).points a₃ = T.points k₃ := by
      have hsum := bary_sum T ((Ts (cornerI k₁)).points a₃)
      rw [fin3_sum_three hne h31 h32] at hsum
      have h3eq : bary T ((Ts (cornerI k₁)).points a₃) k₃ = 1 := by linarith [ha3_k1, ha3_k2]
      have hbary_eq : bary T ((Ts (cornerI k₁)).points a₃) = bary T (T.points k₃) := by
        funext i; rw [bary_point]
        rcases fin3_mem_three hne h31 h32 i with rfl | rfl | rfl
        · rw [if_neg h31.symm, ha3_k1]
        · rw [if_neg h32.symm, ha3_k2]
        · rw [if_pos rfl, h3eq]
      rw [← affineCombination_bary T ((Ts (cornerI k₁)).points a₃), hbary_eq, affineCombination_bary]
    -- Hence Ts (cornerI k₁) has the exact same vertices as T, so T.interior ⊆ (Ts (cornerI k₁)).interior
    have hTs_eq : T.closedInterior ⊆ (Ts (cornerI k₁)).closedInterior := by
      intro x hx
      have hxnn := (mem_closedInterior_iff_bary T x).mp hx
      let w : Fin 3 → ℝ := fun a =>
        if a = a₁ then bary T x k₁ else if a = a₂ then bary T x k₂ else bary T x k₃
      have hw_sum : ∑ a : Fin 3, w a = 1 := by
        have hsum := bary_sum T x
        rw [fin3_sum_three ha12 ha31 ha32]
        rw [fin3_sum_three hne h31 h32] at hsum
        simp only [w, ↓reduceIte, ha12.symm, ha31, ha32]
        exact hsum
      have hw_comb : Finset.univ.affineCombination ℝ (Ts (cornerI k₁)).points w = x := by
        rw [Finset.affineCombination_eq_linear_combination _ _ _ hw_sum, ← affineCombination_bary T x,
          Finset.affineCombination_eq_linear_combination _ _ _ (bary_sum T x),
          fin3_sum_three ha12 ha31 ha32, fin3_sum_three hne h31 h32]
        simp only [w, ↓reduceIte, ha12.symm, ha31, ha32, ha₁, ha₂, ha₃]
      rw [mem_closedInterior_iff_bary, ← bary_unique (Ts (cornerI k₁)) hw_sum hw_comb]
      intro a; dsimp [w]; split_ifs <;> exact hxnn _
    -- Pick j ≠ cornerI k₁ (exists since n ≥ 2) and show (Ts j).interior is nonempty!
    obtain ⟨j, hjne⟩ : ∃ j : Fin n, j ≠ cornerI k₁ := by
      by_cases h0 : (⟨0, hn_pos⟩ : Fin n) = cornerI k₁
      · exact ⟨⟨1, by omega⟩, fun h => by have := congrArg Fin.val (h.trans h0.symm); simp at this⟩
      · exact ⟨⟨0, hn_pos⟩, h0⟩
    have hnonempty : ((Ts j).interior).Nonempty := by
      let b : ℝ² := Finset.univ.affineCombination ℝ (Ts j).points (fun _ => (1 / 3 : ℝ))
      have hw : ∑ _ : Fin 3, (1 / 3 : ℝ) = 1 := by norm_num
      refine ⟨b, (mem_interior_iff_bary (Ts j) b).mpr fun a => ?_⟩
      rw [← bary_unique (Ts j) hw rfl]; norm_num
    obtain ⟨x, hx⟩ := hnonempty
    have hxT : x ∈ T.interior := interior_subset_of_closedInterior_subset (hsub j) hx
    have hxI : x ∈ (Ts (cornerI k₁)).interior := interior_subset_of_closedInterior_subset hTs_eq hxT
    exact Set.disjoint_left.mp (hdisj hjne) hx hxI
  -- Immediately rule out n = 2!
  have hn_ge3 : 3 ≤ n := by
    have := Fintype.card_le_of_injective cornerI hcornerI_inj
    simpa using this
  -- Strengthen hcorner_rays: the other two vertices lie strictly on the open edges of T!
  have hcorner_open : ∀ k j₁ j₂ : Fin 3, j₁ ≠ k → j₂ ≠ k → j₁ ≠ j₂ →
      ∃ m₁ m₂ : Fin 3, m₁ ≠ m₂ ∧
        bary T ((Ts (cornerI k)).points m₁) j₂ = 0 ∧
        0 < bary T ((Ts (cornerI k)).points m₁) k ∧
        0 < bary T ((Ts (cornerI k)).points m₁) j₁ ∧
        bary T ((Ts (cornerI k)).points m₂) j₁ = 0 ∧
        0 < bary T ((Ts (cornerI k)).points m₂) k ∧
        0 < bary T ((Ts (cornerI k)).points m₂) j₂ := by
    intro k j₁ j₂ h1k h2k h12
    obtain ⟨m₁, m₂, hm12, _, _, hm1_j2, hm1_j1, hm2_j1, hm2_j2⟩ := hcorner_rays k j₁ j₂ h1k h2k h12
    have hnn1 := (mem_closedInterior_iff_bary T _).mp (hsub (cornerI k) ((Ts (cornerI k)).point_mem_closedInterior m₁)) k
    have hnn2 := (mem_closedInterior_iff_bary T _).mp (hsub (cornerI k) ((Ts (cornerI k)).point_mem_closedInterior m₂)) k
    have hk1 : 0 < bary T ((Ts (cornerI k)).points m₁) k := by
      rcases eq_or_lt_of_le hnn1 with h0 | hpos
      · exfalso
        have hsum := bary_sum T ((Ts (cornerI k)).points m₁)
        rw [fin3_sum_three h1k.symm h2k h12.symm] at hsum
        have h1eq : bary T ((Ts (cornerI k)).points m₁) j₁ = 1 := by linarith [h0, hm1_j2]
        have hpeq : (Ts (cornerI k)).points m₁ = T.points j₁ := by
          have hb : bary T ((Ts (cornerI k)).points m₁) = bary T (T.points j₁) := by
            funext i; rw [bary_point]
            rcases fin3_mem_three h1k.symm h2k h12.symm i with rfl | rfl | rfl
            · rw [if_neg h1k.symm, ← h0]
            · rw [if_pos rfl, h1eq]
            · rw [if_neg h12.symm, hm1_j2]
          rw [← affineCombination_bary T ((Ts (cornerI k)).points m₁), hb, affineCombination_bary]
        exact h1k.symm (hcornerI_inj (cornerI_uniq j₁ (cornerI k) ⟨m₁, hpeq⟩))
      · exact hpos
    have hk2 : 0 < bary T ((Ts (cornerI k)).points m₂) k := by
      rcases eq_or_lt_of_le hnn2 with h0 | hpos
      · exfalso
        have hsum := bary_sum T ((Ts (cornerI k)).points m₂)
        rw [fin3_sum_three h1k.symm h2k h12.symm] at hsum
        have h2eq : bary T ((Ts (cornerI k)).points m₂) j₂ = 1 := by linarith [h0, hm2_j1]
        have hpeq : (Ts (cornerI k)).points m₂ = T.points j₂ := by
          have hb : bary T ((Ts (cornerI k)).points m₂) = bary T (T.points j₂) := by
            funext i; rw [bary_point]
            rcases fin3_mem_three h1k.symm h2k h12.symm i with rfl | rfl | rfl
            · rw [if_neg h2k.symm, ← h0]
            · rw [if_neg h12, hm2_j1]
            · rw [if_pos rfl, h2eq]
          rw [← affineCombination_bary T ((Ts (cornerI k)).points m₂), hb, affineCombination_bary]
        exact h2k.symm (hcornerI_inj (cornerI_uniq j₂ (cornerI k) ⟨m₂, hpeq⟩))
      · exact hpos
    exact ⟨m₁, m₂, hm12, hm1_j2, hk1, hm1_j1, hm2_j1, hk2, hm2_j2⟩
  -- Global vertex set V_all and degree classification for P ∈ V_rest
  let V_all : Finset ℝ² := (Finset.univ : Finset (Fin n × Fin 3)).image (fun p => (Ts p.1).points p.2)
  let V_T : Finset ℝ² := {T.points 0, T.points 1, T.points 2}
  let V_rest : Finset ℝ² := V_all \ V_T
  have hVT_sub : V_T ⊆ V_all := by
    intro P hP
    simp only [V_T, Finset.mem_insert, Finset.mem_singleton] at hP
    have hmem : ∀ k : Fin 3, T.points k ∈ V_all := fun k => by
      obtain ⟨m, hm⟩ := cornerI_spec k
      exact Finset.mem_image.mpr ⟨(cornerI k, m), Finset.mem_univ _, hm⟩
    rcases hP with rfl | rfl | rfl
    · exact hmem 0
    · exact hmem 1
    · exact hmem 2
  have hVT_card : V_T.card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨T.points 0, T.points 1, T.points 2,
      T.independent.injective.ne (by decide),
      T.independent.injective.ne (by decide),
      T.independent.injective.ne (by decide), rfl⟩
  -- Degree of every P ∈ V_rest is 3 or 6 (and = 3 if onOpenEdge T P)
  have hrest_deg : ∀ P ∈ V_rest, (deg P = 3 ∨ deg P = 6) ∧ (onOpenEdge T P → deg P = 3) := by
    intro P hP
    obtain ⟨hPin, hPnotT⟩ := Finset.mem_sdiff.mp hP
    obtain ⟨⟨i, m⟩, _, rfl⟩ := Finset.mem_image.mp hPin
    dsimp only at hPnotT ⊢
    have hnotv : ∀ k : Fin 3, T.points k ≠ (Ts i).points m := fun k hk =>
      hPnotT (by match k with
        | 0 => simp [V_T, ← hk]
        | 1 => simp [V_T, ← hk]
        | 2 => simp [V_T, ← hk])
    have hcl : (Ts i).points m ∈ T.closedInterior := hsub i ((Ts i).point_mem_closedInterior m)
    have hlin := sum_eq_lin ((Ts i).points m)
      (not_in_interior_of_vert _ (Or.inl ⟨i, m, rfl⟩))
    have hdeg_pos : 1 ≤ deg ((Ts i).points m) :=
      Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨m, rfl⟩⟩⟩
    have hlin_case : ∀ t : ℕ, angContrib T ((Ts i).points m) = (t : ℝ) * Real.pi →
        (t = 1 ∨ t = 2) → deg ((Ts i).points m) = 3 * (t - ecnt ((Ts i).points m)) ∧
          ecnt ((Ts i).points m) < t := by
      intro t ht _
      let c0 : ℤ := (cnt ((Ts i).points m) 0 : ℤ) + (ecnt ((Ts i).points m) : ℤ) - (t : ℤ)
      let c1 : ℤ := (cnt ((Ts i).points m) 1 : ℤ) + (ecnt ((Ts i).points m) : ℤ) - (t : ℤ)
      let c2 : ℤ := (cnt ((Ts i).points m) 2 : ℤ) + (ecnt ((Ts i).points m) : ℤ) - (t : ℤ)
      have hcomb : (c0 : ℝ) * a₀ + (c1 : ℝ) * a₁ + (c2 : ℝ) * a₂ = 0 := by
        dsimp [c0, c1, c2]; push_cast
        have hlin' := hlin
        rw [ht, ← ha_sum] at hlin'
        linarith
      obtain ⟨h0, h1, h2⟩ := ha_indep c0 c1 c2 hcomb
      have hd := deg_eq ((Ts i).points m)
      omega
    by_cases hTint : (Ts i).points m ∈ T.interior
    · have hangT : angContrib T ((Ts i).points m) = (2 : ℕ) * Real.pi := by
        unfold angContrib
        rw [if_neg (not_not.mpr hcl), if_pos hTint]; norm_num
      obtain ⟨hdeq, hlt⟩ := hlin_case 2 hangT (Or.inr rfl)
      have hnoe : ¬ onOpenEdge T ((Ts i).points m) := fun h => h.2.1 hTint
      exact ⟨by omega, fun h => absurd h hnoe⟩
    · have hoe : onOpenEdge T ((Ts i).points m) := ⟨hcl, hTint, hnotv⟩
      have hangT : angContrib T ((Ts i).points m) = (1 : ℕ) * Real.pi := by
        unfold angContrib
        rw [if_neg (not_not.mpr hcl), if_neg hTint, if_pos hoe]; norm_num
      obtain ⟨hdeq, hlt⟩ := hlin_case 1 hangT (Or.inl rfl)
      exact ⟨Or.inl (by omega), fun _ => by omega⟩
  -- Double count ∑ P ∈ V_all, deg P = 3 * n
  have hsum_deg : ∑ P ∈ V_all, deg P = 3 * n := by
    have hcard : (Finset.univ : Finset (Fin n × Fin 3)).card = 3 * n := by
      rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]; ring
    rw [← hcard]
    have hfib := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin n × Fin 3)))
      (t := V_all) (f := fun p => (Ts p.1).points p.2)
      (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩)
    rw [hfib]
    apply Finset.sum_congr rfl
    intro P _
    -- Bijection between {(i, m) | (Ts i).points m = P} and {i | ∃ m, (Ts i).points m = P}
    symm
    refine Finset.card_bij (fun p _ => p.1) (fun p hp => ?_) (fun p₁ hp₁ p₂ hp₂ heq => ?_) (fun i hi => ?_)
    · obtain ⟨_, hpm⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨p.2, hpm⟩⟩
    · obtain ⟨_, hp1⟩ := Finset.mem_filter.mp hp₁
      obtain ⟨_, hp2⟩ := Finset.mem_filter.mp hp₂
      have hi : p₁.1 = p₂.1 := heq
      have hm : p₁.2 = p₂.2 := by
        apply (Ts p₁.1).independent.injective
        rw [hp1, ← hp2, hi]
      exact Prod.ext hi hm
    · obtain ⟨_, m, hm⟩ := Finset.mem_filter.mp hi
      exact ⟨(i, m), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩, rfl⟩
  let E_set := V_rest.filter fun P => deg P = 3
  let I_set := V_rest.filter fun P => deg P = 6
  have hEI : E_set.card + 2 * I_set.card = n - 1 := by
    have hsplit1 : ∑ P ∈ V_all, deg P = ∑ P ∈ V_T, deg P + ∑ P ∈ V_rest, deg P := by
      have hdisj_VT : Disjoint V_T V_rest := Finset.disjoint_sdiff
      have hun_VT : V_T ∪ V_rest = V_all := Finset.union_sdiff_of_subset hVT_sub
      rw [← hun_VT, Finset.sum_union hdisj_VT]
    have hsum_VT : ∑ P ∈ V_T, deg P = 3 := by
      have h1 : ∀ P ∈ V_T, deg P = 1 := by
        intro P hP
        simp only [V_T, Finset.mem_insert, Finset.mem_singleton] at hP
        rcases hP with rfl | rfl | rfl <;> rw [deg_eq, hcorner_deg]
      rw [Finset.sum_congr rfl h1, Finset.sum_const, hVT_card]; norm_num
    have hdisj_EI : Disjoint E_set I_set := by
      rw [Finset.disjoint_left]; intro P hE hI
      have := (Finset.mem_filter.mp hE).2
      have := (Finset.mem_filter.mp hI).2
      omega
    have hun_EI : E_set ∪ I_set = V_rest := by
      ext P; simp only [E_set, I_set, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro hP; rcases (hrest_deg P hP).1 with h3 | h6
        · exact Or.inl ⟨hP, h3⟩
        · exact Or.inr ⟨hP, h6⟩
    have hsum_rest : ∑ P ∈ V_rest, deg P = 3 * E_set.card + 6 * I_set.card := by
      rw [← hun_EI, Finset.sum_union hdisj_EI]
      have hE : ∑ P ∈ E_set, deg P = 3 * E_set.card := by
        rw [Finset.sum_congr rfl (fun P hP => (Finset.mem_filter.mp hP).2), Finset.sum_const,
          smul_eq_mul, mul_comm]
      have hI : ∑ P ∈ I_set, deg P = 6 * I_set.card := by
        rw [Finset.sum_congr rfl (fun P hP => (Finset.mem_filter.mp hP).2), Finset.sum_const,
          smul_eq_mul, mul_comm]
      rw [hE, hI]
    omega
  -- Extract the 6 open-edge vertices of the 3 corner triangles:
  -- corner 0: P01 on edge(0,1) [bary 2 = 0], P02 on edge(0,2) [bary 1 = 0]
  -- corner 1: P10 on edge(1,0) [bary 2 = 0], P12 on edge(1,2) [bary 0 = 0]
  -- corner 2: P21 on edge(2,1) [bary 0 = 0], P20 on edge(2,0) [bary 1 = 0]
  obtain ⟨m01, m02, hm012, h01_2, h01_0, h01_1, h02_1, h02_0, h02_2⟩ :=
    hcorner_open 0 1 2 (by decide) (by decide) (by decide)
  obtain ⟨m10, m12, hm102, h10_2, h10_1, h10_0, h12_0, h12_1, h12_2⟩ :=
    hcorner_open 1 0 2 (by decide) (by decide) (by decide)
  obtain ⟨m21, m20, hm210, h21_0, h21_2, h21_1, h20_1, h20_2, h20_0⟩ :=
    hcorner_open 2 1 0 (by decide) (by decide) (by decide)
  set P01 := (Ts (cornerI 0)).points m01
  set P02 := (Ts (cornerI 0)).points m02
  set P10 := (Ts (cornerI 1)).points m10
  set P12 := (Ts (cornerI 1)).points m12
  set P21 := (Ts (cornerI 2)).points m21
  set P20 := (Ts (cornerI 2)).points m20
  have mem_E_of_edge : ∀ (i : Fin n) (m : Fin 3) (k₀ : Fin 3),
      bary T ((Ts i).points m) k₀ = 0 →
      (∀ j : Fin 3, j ≠ k₀ → 0 < bary T ((Ts i).points m) j) →
      (Ts i).points m ∈ E_set := by
    intro i m k₀ hk0 hpos
    have hoe : onOpenEdge T ((Ts i).points m) :=
      (onOpenEdge_iff_unique_zero T _).mpr ⟨k₀, hk0, hpos⟩
    have hnotT : (Ts i).points m ∉ V_T := by
      simp only [V_T, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hoe.2.2 0 |>.symm, hoe.2.2 1 |>.symm, hoe.2.2 2 |>.symm⟩
    have hrest : (Ts i).points m ∈ V_rest :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨(i, m), Finset.mem_univ _, rfl⟩, hnotT⟩
    exact Finset.mem_filter.mpr ⟨hrest, (hrest_deg _ hrest).2 hoe⟩
  have hP01_E : P01 ∈ E_set := mem_E_of_edge (cornerI 0) m01 2 h01_2 (fun j hj => match j with
    | 0 => h01_0 | 1 => h01_1 | 2 => absurd rfl hj)
  have hP12_E : P12 ∈ E_set := mem_E_of_edge (cornerI 1) m12 0 h12_0 (fun j hj => match j with
    | 0 => absurd rfl hj | 1 => h12_1 | 2 => h12_2)
  have hP20_E : P20 ∈ E_set := mem_E_of_edge (cornerI 2) m20 1 h20_1 (fun j hj => match j with
    | 0 => h20_0 | 1 => absurd rfl hj | 2 => h20_2)
  have hP01_ne_P12 : P01 ≠ P12 := fun h => by rw [h] at h01_2; linarith
  have hP01_ne_P20 : P01 ≠ P20 := fun h => by rw [h] at h01_2; linarith
  have hP12_ne_P20 : P12 ≠ P20 := fun h => by rw [h] at h12_0; linarith
  have hE_ge3 : 3 ≤ E_set.card := by
    have hsub3 : ({P01, P12, P20} : Finset ℝ²) ⊆ E_set := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have hcard3 : ({P01, P12, P20} : Finset ℝ²).card = 3 :=
      Finset.card_eq_three.mpr ⟨P01, P12, P20, hP01_ne_P12, hP01_ne_P20, hP12_ne_P20, rfl⟩
    exact hcard3 ▸ Finset.card_le_card hsub3
  -- Rule out n = 2 and n = 3 immediately!
  have hn5 : n = 5 := by omega
  -- Now n = 5: E_set.card = 4 and I_set.card = 0, so V_rest = E_set and V_rest.card = 4
  have hI0 : I_set.card = 0 := by omega
  have hE4 : E_set.card = 4 := by omega
  have hVrest_eq_E : V_rest = E_set := by
    have hIempty : I_set = ∅ := Finset.card_eq_zero.mp hI0
    ext P; simp only [E_set, Finset.mem_filter, iff_self_and]
    intro hP
    rcases (hrest_deg P hP).1 with h3 | h6
    · exact h3
    · exfalso
      have : P ∈ I_set := Finset.mem_filter.mpr ⟨hP, h6⟩
      rw [hIempty] at this; exact Finset.notMem_empty P this
  -- Helper: the 3 vertices of Ts (cornerI k) are exactly {T.k, P_a, P_b}
  have verts_of_corner : ∀ (k : Fin 3) (ma mb : Fin 3), ma ≠ mb →
      (Ts (cornerI k)).points ma ≠ T.points k → (Ts (cornerI k)).points mb ≠ T.points k →
      ∀ m : Fin 3, (Ts (cornerI k)).points m = T.points k ∨
        (Ts (cornerI k)).points m = (Ts (cornerI k)).points ma ∨
        (Ts (cornerI k)).points m = (Ts (cornerI k)).points mb := by
    intro k ma mb hmab hma hmb m
    obtain ⟨mk, hmk⟩ := cornerI_spec k
    have h1 : ma ≠ mk := fun h => hma (h ▸ hmk)
    have h2 : mb ≠ mk := fun h => hmb (h ▸ hmk)
    have hcases : m = mk ∨ m = ma ∨ m = mb := fin3_mem_three h1.symm h2 hmab.symm m
    rcases hcases with rfl | rfl | rfl
    · exact Or.inl hmk
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  -- Helper for Case 1: if two distinct points P ≠ Q on edge k₀ belong to Ts (cornerI k₁) and Ts (cornerI k₂),
  -- then both remaining triangles share the boundary edge [P, Q], contradicting disjointness!
  have kill_edge_pair : ∀ (k₀ k₁ k₂ : Fin 3) (P Q : ℝ²),
      k₀ ≠ k₁ → k₀ ≠ k₂ → k₁ ≠ k₂ → P ≠ Q →
      bary T P k₀ = 0 → bary T Q k₀ = 0 →
      P ∈ E_set → Q ∈ E_set →
      (∀ m : Fin 3, (Ts (cornerI k₂)).points m ≠ P) →
      (∀ m : Fin 3, (Ts (cornerI k₀)).points m ≠ P) →
      (∀ m : Fin 3, (Ts (cornerI k₁)).points m ≠ Q) →
      (∀ m : Fin 3, (Ts (cornerI k₀)).points m ≠ Q) → False := by
    intro k₀ k₁ k₂ P Q h01 h02 h12 hPQ hPk0 hQk0 hPE hQE hk2P hk0P hk1Q hk0Q
    let others : Finset (Fin n) := Finset.univ \ {cornerI k₀, cornerI k₁, cornerI k₂}
    have h3card : ({cornerI k₀, cornerI k₁, cornerI k₂} : Finset (Fin n)).card = 3 :=
      Finset.card_eq_three.mpr ⟨cornerI k₀, cornerI k₁, cornerI k₂,
        hcornerI_inj.ne h01, hcornerI_inj.ne h02, hcornerI_inj.ne h12, rfl⟩
    have hothers_card : others.card = 2 := by
      have : others.card = (Finset.univ : Finset (Fin n)).card -
          ({cornerI k₀, cornerI k₁, cornerI k₂} : Finset (Fin n)).card :=
        Finset.card_sdiff_of_subset (Finset.subset_univ _)
      rw [this, Finset.card_univ, Fintype.card_fin, h3card, hn5]
    obtain ⟨i₄, i₅, hi45, hothers_eq⟩ := Finset.card_eq_two.mp hothers_card
    have hdegP : (Finset.univ.filter fun i : Fin n => ∃ m : Fin 3, (Ts i).points m = P).card = 3 :=
      (Finset.mem_filter.mp hPE).2
    have hdegQ : (Finset.univ.filter fun i : Fin n => ∃ m : Fin 3, (Ts i).points m = Q).card = 3 :=
      (Finset.mem_filter.mp hQE).2
    -- S_P ⊆ univ \ {cornerI k₂, cornerI k₀} which has card 3, so S_P = univ \ {cornerI k₂, cornerI k₀}!
    have hSP_eq : (Finset.univ.filter fun i : Fin n => ∃ m : Fin 3, (Ts i).points m = P) =
        Finset.univ \ {cornerI k₂, cornerI k₀} := by
      apply Finset.eq_of_subset_of_card_le
      · intro i hi
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        obtain ⟨m, hm⟩ := (Finset.mem_filter.mp hi).2
        exact ⟨fun h => hk2P m (h ▸ hm), fun h => hk0P m (h ▸ hm)⟩
      · rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
          Finset.card_pair (hcornerI_inj.ne h02.symm), hdegP]
        omega
    have hSQ_eq : (Finset.univ.filter fun i : Fin n => ∃ m : Fin 3, (Ts i).points m = Q) =
        Finset.univ \ {cornerI k₁, cornerI k₀} := by
      apply Finset.eq_of_subset_of_card_le
      · intro i hi
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        obtain ⟨m, hm⟩ := (Finset.mem_filter.mp hi).2
        exact ⟨fun h => hk1Q m (h ▸ hm), fun h => hk0Q m (h ▸ hm)⟩
      · rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
          Finset.card_pair (hcornerI_inj.ne h01.symm), hdegQ]
        omega
    have hi4_mem : i₄ ∈ others := by rw [hothers_eq]; exact Finset.mem_insert_self i₄ {i₅}
    have hi5_mem : i₅ ∈ others := by rw [hothers_eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self i₅)
    have hmem_of_others : ∀ i ∈ others,
        (∃ m : Fin 3, (Ts i).points m = P) ∧ (∃ m : Fin 3, (Ts i).points m = Q) := by
      intro i hi
      have hnot3 := (Finset.mem_sdiff.mp hi).2
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot3
      have h1 : i ∈ Finset.univ.filter (fun i : Fin n => ∃ m : Fin 3, (Ts i).points m = P) := by
        rw [hSP_eq]; simp [hnot3.1, hnot3.2.2]
      have h2 : i ∈ Finset.univ.filter (fun i : Fin n => ∃ m : Fin 3, (Ts i).points m = Q) := by
        rw [hSQ_eq]; simp [hnot3.1, hnot3.2.1]
      exact ⟨(Finset.mem_filter.mp h1).2, (Finset.mem_filter.mp h2).2⟩
    obtain ⟨h4P, h4Q⟩ := hmem_of_others i₄ hi4_mem
    obtain ⟨h5P, h5Q⟩ := hmem_of_others i₅ hi5_mem
    exact not_disjoint_of_shared_boundary_edge (hsub i₄) (hsub i₅) hPQ k₀ hPk0 hQk0
      h4P h4Q h5P h5Q (hdisj hi45)
  -- Vertex lists of the 3 corner triangles
  have hP01_ne0 : P01 ≠ T.points 0 := fun h => by rw [h, bary_point, if_neg (by decide)] at h01_1; linarith
  have hP02_ne0 : P02 ≠ T.points 0 := fun h => by rw [h, bary_point, if_neg (by decide)] at h02_2; linarith
  have hP10_ne1 : P10 ≠ T.points 1 := fun h => by rw [h, bary_point, if_neg (by decide)] at h10_0; linarith
  have hP12_ne1 : P12 ≠ T.points 1 := fun h => by rw [h, bary_point, if_neg (by decide)] at h12_2; linarith
  have hP21_ne2 : P21 ≠ T.points 2 := fun h => by rw [h, bary_point, if_neg (by decide)] at h21_1; linarith
  have hP20_ne2 : P20 ≠ T.points 2 := fun h => by rw [h, bary_point, if_neg (by decide)] at h20_0; linarith
  have hP10_E : P10 ∈ E_set := mem_E_of_edge (cornerI 1) m10 2 h10_2 (fun j hj => match j with
    | 0 => h10_0 | 1 => h10_1 | 2 => absurd rfl hj)
  have hP21_E : P21 ∈ E_set := mem_E_of_edge (cornerI 2) m21 0 h21_0 (fun j hj => match j with
    | 0 => absurd rfl hj | 1 => h21_1 | 2 => h21_2)
  have hP02_E : P02 ∈ E_set := mem_E_of_edge (cornerI 0) m02 1 h02_1 (fun j hj => match j with
    | 0 => h02_0 | 1 => absurd rfl hj | 2 => h02_2)
  have hv0 := verts_of_corner 0 m01 m02 hm012 hP01_ne0 hP02_ne0
  have hv1 := verts_of_corner 1 m10 m12 hm102 hP10_ne1 hP12_ne1
  have hv2 := verts_of_corner 2 m21 m20 hm210 hP21_ne2 hP20_ne2
  -- Case split on whether any edge has 2 distinct points among the corner triangles
  by_cases h01eq : P01 ≠ P10
  · refine kill_edge_pair 2 0 1 P01 P10 (by decide) (by decide) (by decide) h01eq h01_2 h10_2 hP01_E hP10_E ?_ ?_ ?_ ?_
    · intro m hm; rcases hv1 m with h | h | h
      · rw [hm] at h; rw [h, bary_point, if_neg (by decide)] at h01_0; linarith
      · exact h01eq (hm.symm.trans h)
      · rw [hm] at h; rw [h] at h01_2; linarith
    · intro m hm; rcases hv2 m with h | h | h
      · rw [hm] at h; rw [h, bary_point, if_neg (by decide)] at h01_0; linarith
      · rw [hm] at h; rw [h] at h01_2; linarith
      · rw [hm] at h; rw [h] at h01_2; linarith
    · intro m hm; rcases hv0 m with h | h | h
      · rw [hm] at h; rw [h, bary_point, if_neg (by decide)] at h10_1; linarith
      · exact h01eq (h.symm.trans hm)
      · rw [hm] at h; rw [h] at h10_2; linarith
    · intro m hm; rcases hv2 m with h | h | h
      · rw [hm] at h; rw [h, bary_point, if_neg (by decide)] at h10_0; linarith
      · rw [hm] at h; rw [h] at h10_2; linarith
      · rw [hm] at h; rw [h] at h10_2; linarith
  push_neg at h01eq
  by_cases h12eq : P12 ≠ P21
  · refine kill_edge_pair 0 1 2 P12 P21 (by decide) (by decide) (by decide) h12eq h12_0 h21_0 hP12_E hP21_E ?_ ?_ ?_ ?_
    · intro m hm; rcases hv2 m with h | h | h
      · rw [hm] at h; rw [h, bary_point, if_neg (by decide)] at h12_1; linarith
      · exact h12eq (hm.symm.trans h)
      · rw [hm] at h; rw [h] at h12_0; linarith
    · intro m hm; rcases hv0 m with h | h | h
      · rw [hm] at h; rw [h, bary_point, if_neg (by decide)] at h12_1; linarith
      · rw [hm] at h; rw [h] at h12_0; linarith
      · rw [hm] at h; rw [h] at h12_0; linarith
    · intro m hm; rcases hv1 m with h | h | h
      · rw [hm] at h; rw [h, bary_point, if_neg (by decide)] at h21_2; linarith
      · rw [hm] at h; rw [h] at h21_0; linarith
      · exact h12eq (h.symm.trans hm)
    · intro m hm; rcases hv0 m with h | h | h
      · rw [hm] at h; rw [h, bary_point, if_neg (by decide)] at h21_1; linarith
      · rw [hm] at h; rw [h] at h21_0; linarith
      · rw [hm] at h; rw [h] at h21_0; linarith
  push_neg at h12eq
  by_cases h20eq : P20 ≠ P02
  · refine kill_edge_pair 1 2 0 P20 P02 (by decide) (by decide) (by decide) h20eq h20_1 h02_1 hP20_E hP02_E ?_ ?_ ?_ ?_
    · intro m hm; rcases hv0 m with h | h | h
      · rw [hm] at h; rw [h, bary_point, if_neg (by decide)] at h20_2; linarith
      · rw [hm] at h; rw [h] at h20_1; linarith
      · exact h20eq (hm.symm.trans h)
    · intro m hm; rcases hv1 m with h | h | h
      · rw [hm] at h; rw [h, bary_point, if_neg (by decide)] at h20_2; linarith
      · rw [hm] at h; rw [h] at h20_1; linarith
      · rw [hm] at h; rw [h] at h20_1; linarith
    · intro m hm; rcases hv2 m with h | h | h
      · rw [hm] at h; rw [h, bary_point, if_neg (by decide)] at h02_0; linarith
      · rw [hm] at h; rw [h] at h02_1; linarith
      · exact h20eq (h.symm.trans hm)
    · intro m hm; rcases hv1 m with h | h | h
      · rw [hm] at h; rw [h, bary_point, if_neg (by decide)] at h02_0; linarith
      · rw [hm] at h; rw [h] at h02_1; linarith
      · rw [hm] at h; rw [h] at h02_1; linarith
  push_neg at h20eq
  -- Case 2: P01 = P10, P12 = P21, P20 = P02. There is a 4th vertex W ∈ E_set \ {P01, P12, P20}.
  have hW_exists : ∃ W ∈ E_set, W ∉ ({P01, P12, P20} : Finset ℝ²) := by
    have hcard3 : ({P01, P12, P20} : Finset ℝ²).card = 3 :=
      Finset.card_eq_three.mpr ⟨P01, P12, P20, hP01_ne_P12, hP01_ne_P20, hP12_ne_P20, rfl⟩
    exact Finset.exists_mem_notMem_of_card_lt_card (by omega)
  obtain ⟨W, hWE, hWnot3⟩ := hW_exists
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hWnot3
  have hWrest : W ∈ V_rest := by rw [hVrest_eq_E]; exact hWE
  have hWnotT : W ∉ V_T := (Finset.mem_sdiff.mp hWrest).2
  simp only [V_T, Finset.mem_insert, Finset.mem_singleton, not_or] at hWnotT
  have hW_deg : (Finset.univ.filter fun i : Fin n => ∃ m : Fin 3, (Ts i).points m = W).card = 3 :=
    (Finset.mem_filter.mp hWE).2
  have hSW_sub : (Finset.univ.filter fun i : Fin n => ∃ m : Fin 3, (Ts i).points m = W) ⊆
      Finset.univ \ {cornerI 0, cornerI 1, cornerI 2} := by
    intro i hi
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    obtain ⟨m, hm⟩ := (Finset.mem_filter.mp hi).2
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · rw [h] at hm
      rcases hv0 m with h' | h' | h'
      · exact hWnotT.1 (hm.symm.trans h')
      · exact hWnot3.1 (hm.symm.trans h')
      · exact hWnot3.2.2 (hm.symm.trans (h'.trans h20eq.symm))
    · rw [h] at hm
      rcases hv1 m with h' | h' | h'
      · exact hWnotT.2.1 (hm.symm.trans h')
      · exact hWnot3.1 (hm.symm.trans (h'.trans h01eq.symm))
      · exact hWnot3.2.1 (hm.symm.trans h')
    · rw [h] at hm
      rcases hv2 m with h' | h' | h'
      · exact hWnotT.2.2 (hm.symm.trans h')
      · exact hWnot3.2.1 (hm.symm.trans (h'.trans h12eq.symm))
      · exact hWnot3.2.2 (hm.symm.trans h')
  have h3card : ({cornerI 0, cornerI 1, cornerI 2} : Finset (Fin n)).card = 3 :=
    Finset.card_eq_three.mpr ⟨cornerI 0, cornerI 1, cornerI 2,
      hcornerI_inj.ne (by decide), hcornerI_inj.ne (by decide), hcornerI_inj.ne (by decide), rfl⟩
  have hle := Finset.card_le_card hSW_sub
  rw [hW_deg, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, h3card, hn5] at hle
  omega

theorem exists_not_similiCuttable_2_3_5 :
    ∃ T : Triangle ℝ ℝ²,
      ¬ Erdos633.IsSimiliCuttable 2 T ∧
      ¬ Erdos633.IsSimiliCuttable 3 T ∧
      ¬ Erdos633.IsSimiliCuttable 5 T := by
  obtain ⟨T, hIndep⟩ := exists_indep_triangle
  exact ⟨T,
    not_similiCuttable_2_3_5 T hIndep 2 (Or.inl rfl),
    not_similiCuttable_2_3_5 T hIndep 3 (Or.inr (Or.inl rfl)),
    not_similiCuttable_2_3_5 T hIndep 5 (Or.inr (Or.inr rfl))⟩

end Erdos633Imp

theorem OMA.solution : type_of% @Erdos633.exists_isSimiliCuttable_iff_ne_zero_two_three_five := by
  obtain ⟨T, h2, h3, h5⟩ := Erdos633Imp.exists_not_similiCuttable_2_3_5
  refine ⟨T, fun n => ⟨fun h => ⟨h.ne_zero, ?_, ?_, ?_⟩, fun ⟨hn₀, hn₂, hn₃, hn₅⟩ => ?_⟩⟩
  · rintro rfl; exact h2 h
  · rintro rfl; exact h3 h
  · rintro rfl; exact h5 h
  · by_cases hn1 : n = 1
    · subst hn1
      exact (Erdos633SimiliCuttableProof.strongSimiliCuttable_one T).toIsSimiliCuttable
    · by_cases heven : n % 2 = 0
      · have hm : 2 ≤ n / 2 := by omega
        have heq : 2 * (n / 2) = n := by omega
        rw [← heq]
        exact (Erdos633SimiliCuttableProof.strongSimiliCuttable_two_mul (n / 2) hm T).toIsSimiliCuttable
      · have hge7 : 7 ≤ n := by omega
        have hm : 2 ≤ (n - 3) / 2 := by omega
        have heq1 : 2 * ((n - 3) / 2) = n - 3 := by omega
        have heq2 : (n - 3) + 3 = n := by omega
        have hbase : Erdos633SimiliCuttableProof.StrongSimiliCuttable (n - 3) T := by
          rw [← heq1]
          exact Erdos633SimiliCuttableProof.strongSimiliCuttable_two_mul ((n - 3) / 2) hm T
        rw [← heq2]
        exact (Erdos633SimiliCuttableProof.strongSimiliCuttable_add_three (by omega) hbase).toIsSimiliCuttable
