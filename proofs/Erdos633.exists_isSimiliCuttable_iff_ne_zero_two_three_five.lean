import FormalConjectures.ErdosProblems.«633»
import Mathlib.Tactic

/-!
# Existence of a Triangle Not Simili-Cuttable into 0, 2, 3, or 5 Parts

We prove `Erdos633.exists_isSimiliCuttable_iff_ne_zero_two_three_five` (Soifer 2009):
1. Every triangle in the plane can be simili-cut into `n` mutually similar triangles for every
   `n` different from `0, 2, 3, 5`.
2. Explicitly constructing a triangle `baseTri` with `ℚ`-linearly independent angles
   `(√2 / 10) * π`, `(√3 / 10) * π`, and `π - (√2 + √3) / 10 * π`, 2D Lebesgue volume of small
   balls gives exact cone-angle additivity at every point, forcing rigid vertex multiplicities and
   ruling out `n = 2, 3, 5`.
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

namespace Erdos633Proof

open Affine
open scoped Congruent EuclideanGeometry Similar Real NNReal

noncomputable def mkPt (x y : ℝ) : ℝ² :=
  WithLp.toLp 2 ![x, y]

@[simp] lemma mkPt_apply_zero (x y : ℝ) : mkPt x y 0 = x := rfl
@[simp] lemma mkPt_apply_one (x y : ℝ) : mkPt x y 1 = y := rfl

@[simp] lemma mkPt_zero : mkPt 0 0 = 0 := by
  ext i; fin_cases i <;> rfl

@[simp] lemma mkPt_add (x₁ y₁ x₂ y₂ : ℝ) :
    mkPt x₁ y₁ + mkPt x₂ y₂ = mkPt (x₁ + x₂) (y₁ + y₂) := by
  ext i; fin_cases i <;> rfl

@[simp] lemma mkPt_smul (c x y : ℝ) :
    c • mkPt x y = mkPt (c * x) (c * y) := by
  ext i; fin_cases i <;> rfl

lemma mkPt_vsub (x₁ y₁ x₂ y₂ : ℝ) :
    mkPt x₁ y₁ -ᵥ mkPt x₂ y₂ = mkPt (x₁ - x₂) (y₁ - y₂) := by
  ext i; fin_cases i <;> simp [mkPt]

lemma inner_mkPt (x₁ y₁ x₂ y₂ : ℝ) :
    inner ℝ (mkPt x₁ y₁) (mkPt x₂ y₂) = x₁ * x₂ + y₁ * y₂ := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp [mkPt, mul_comm]

lemma norm_sq_eq (v : ℝ²) : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply, Fin.sum_univ_two]
  simp [sq]

lemma norm_sq_mkPt (x y : ℝ) : ‖mkPt x y‖ ^ 2 = x ^ 2 + y ^ 2 := by
  rw [norm_sq_eq]; rfl

lemma norm_mkPt_of_nonneg {x y r : ℝ} (hr : 0 ≤ r) (h : x ^ 2 + y ^ 2 = r ^ 2) :
    ‖mkPt x y‖ = r := by
  have h1 : ‖mkPt x y‖ ^ 2 = r ^ 2 := by rw [norm_sq_mkPt, h]
  nlinarith [norm_nonneg (mkPt x y), sq_nonneg (‖mkPt x y‖ - r)]

private lemma int_dvd_three_of_two_mul_sq_dvd {m : ℤ} (h : (2 * m ^ 2) % 3 = 0) : 3 ∣ m := by
  have hm : m = 3 * (m / 3) + m % 3 := by omega
  have hsq_mod : (2 * m ^ 2) % 3 = (2 * (m % 3) ^ 2) % 3 := by
    conv_lhs => rw [hm]
    ring_nf
    omega
  rw [hsq_mod] at h
  have hrem : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hrem with h0 | h1 | h2
  · exact Int.dvd_of_emod_eq_zero h0
  · rw [h1] at h; omega
  · rw [h2] at h; omega

lemma rat_lin_indep_sqrt2_sqrt3 {a b c : ℚ}
    (h : (a : ℝ) * √2 + (b : ℝ) * √3 + (c : ℝ) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have hirr2 : Irrational √2 := by simpa using Nat.Prime.irrational_sqrt (by decide : Nat.Prime 2)
  have hirr3 : Irrational √3 := by simpa using Nat.Prime.irrational_sqrt (by decide : Nat.Prime 3)
  have hsq : ((a : ℝ) * √2 + (c : ℝ)) ^ 2 = (-(b : ℝ) * √3) ^ 2 := by
    congr 1; linarith
  have h2 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hexp : 2 * (a : ℝ) ^ 2 + (c : ℝ) ^ 2 - 3 * (b : ℝ) ^ 2 + 2 * (a : ℝ) * (c : ℝ) * √2 = 0 := by
    nlinarith [hsq, h2, h3]
  have hac : a * c = 0 := by
    by_contra hac0
    have h2ac : (2 * a * c : ℚ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (left_ne_zero_of_mul hac0)) (right_ne_zero_of_mul hac0)
    have h2acR : ((2 * a * c : ℚ) : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr h2ac
    have h2acR' : 2 * (a : ℝ) * (c : ℝ) ≠ 0 := by push_cast at h2acR; exact h2acR
    have hrat : ((-(2 * a ^ 2 + c ^ 2 - 3 * b ^ 2) / (2 * a * c) : ℚ) : ℝ) = √2 := by
      push_cast
      rw [div_eq_iff h2acR']
      linarith
    exact hirr2.ne_rat _ hrat.symm
  rcases mul_eq_zero.mp hac with rfl | rfl
  · simp only [Rat.cast_zero, zero_mul, zero_add] at h
    have hb : b = 0 := by
      by_contra hb0
      have hrat : ((-c / b : ℚ) : ℝ) = √3 := by
        push_cast
        rw [div_eq_iff (Rat.cast_ne_zero.mpr hb0)]
        linarith
      exact hirr3.ne_rat _ hrat.symm
    subst hb
    simp only [Rat.cast_zero, zero_mul, zero_add] at h
    exact ⟨rfl, rfl, Rat.cast_eq_zero.mp h⟩
  · have hq : 2 * a ^ 2 - 3 * b ^ 2 = 0 := by
      apply (Rat.cast_eq_zero (α := ℝ)).mp
      push_cast
      have hexp0 : 2 * (a : ℝ) ^ 2 + 0 ^ 2 - 3 * (b : ℝ) ^ 2 + 2 * (a : ℝ) * 0 * √2 = 0 := by
        simpa using hexp
      linarith
    have hb : b = 0 := by
      by_contra hb0
      let r : ℚ := a / b
      have hr : 2 * r ^ 2 = 3 := by
        dsimp [r]; field_simp [hb0]; linarith
      have hden : (r.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr r.den_nz
      have hint : 2 * r.num ^ 2 = 3 * (r.den : ℤ) ^ 2 := by
        have hr' : 2 * ((r.num : ℚ) / (r.den : ℚ)) ^ 2 = 3 := by
          rwa [Rat.num_div_den]
        have hq' : (2 * r.num ^ 2 : ℚ) = 3 * (r.den : ℚ) ^ 2 := by
          rw [div_pow, mul_div_assoc', div_eq_iff (pow_ne_zero 2 hden)] at hr'
          linarith
        exact_mod_cast hq'
      obtain ⟨k, hk⟩ := int_dvd_three_of_two_mul_sq_dvd (m := r.num) (by omega)
      have hden_mod : (2 * (r.den : ℤ) ^ 2) % 3 = 0 := by
        have : 3 * (r.den : ℤ) ^ 2 = 18 * k ^ 2 := by rw [← hint, hk]; ring
        have : (r.den : ℤ) ^ 2 = 6 * k ^ 2 := by omega
        omega
      obtain ⟨l, hl⟩ := int_dvd_three_of_two_mul_sq_dvd hden_mod
      have hdvd_n : (3 : ℕ) ∣ r.num.natAbs := Int.ofNat_dvd.mp (Int.dvd_natAbs.mpr ⟨k, hk⟩)
      have hdvd_d : (3 : ℕ) ∣ r.den := Int.ofNat_dvd.mp ⟨l, hl⟩
      exact Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 3) hdvd_n hdvd_d r.reduced
    subst hb
    have ha : a = 0 := sq_eq_zero_iff.mp (by linarith)
    exact ⟨ha, rfl, rfl⟩

noncomputable def γ₀ : ℝ := √2 / 10 * π
noncomputable def γ₁ : ℝ := √3 / 10 * π
noncomputable def γ₂ : ℝ := π - γ₀ - γ₁

lemma γ_bounds : 0 < γ₀ ∧ 0 < γ₁ ∧ 0 < γ₀ + γ₁ ∧ γ₀ + γ₁ < π / 2 ∧ 0 < γ₂ ∧ γ₂ < π := by
  have hpi : 0 < π := Real.pi_pos
  have hs2_pos : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hs3_pos : 0 < √3 := Real.sqrt_pos.mpr (by norm_num)
  have hs2_lt : √2 < 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hs3_lt : √3 < 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  dsimp [γ₀, γ₁, γ₂]
  refine ⟨by positivity, by positivity, by positivity, ?_, ?_, ?_⟩ <;> nlinarith

lemma γ_linearIndependent : LinearIndependent ℚ ![γ₀, γ₁, γ₂] := by
  rw [Fintype.linearIndependent_iff]
  intro q hq
  rw [Fin.sum_univ_three] at hq
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Rat.smul_def] at hq
  have hpi : π ≠ 0 := ne_of_gt Real.pi_pos
  have hrel : ((q 0 - q 2 : ℚ) : ℝ) * √2 + ((q 1 - q 2 : ℚ) : ℝ) * √3 + ((10 * q 2 : ℚ) : ℝ) = 0 := by
    have hmul : (q 0 : ℝ) * √2 + (q 1 : ℝ) * √3 + (q 2 : ℝ) * (10 - √2 - √3) = 0 := by
      have h1 : ((q 0 : ℝ) * (√2 / 10 * π) + (q 1 : ℝ) * (√3 / 10 * π) +
          (q 2 : ℝ) * (π - √2 / 10 * π - √3 / 10 * π)) = 0 := hq
      have h2 : π * ((q 0 : ℝ) * √2 + (q 1 : ℝ) * √3 + (q 2 : ℝ) * (10 - √2 - √3)) / 10 = 0 := by
        linarith
      have h3 : π * ((q 0 : ℝ) * √2 + (q 1 : ℝ) * √3 + (q 2 : ℝ) * (10 - √2 - √3)) = 0 := by
        linarith
      exact (mul_eq_zero.mp h3).resolve_left hpi
    push_cast
    linarith
  obtain ⟨h0, h1, h2⟩ := rat_lin_indep_sqrt2_sqrt3 hrel
  have hq2 : q 2 = 0 := by linarith
  have hq0 : q 0 = 0 := by linarith
  have hq1 : q 1 = 0 := by linarith
  intro i
  fin_cases i <;> assumption

noncomputable def vertAngle (S : Triangle ℝ ℝ²) : Fin 3 → ℝ
  | 0 => ∠ (S.points 1) (S.points 0) (S.points 2)
  | 1 => ∠ (S.points 2) (S.points 1) (S.points 0)
  | 2 => ∠ (S.points 0) (S.points 2) (S.points 1)

lemma not_collinear_triangle_pts (S : Triangle ℝ ℝ²) {i j k : Fin 3}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ¬ Collinear ℝ ({S.points i, S.points j, S.points k} : Set ℝ²) := by
  intro hcol
  have hemb : Function.Injective ![i, j, k] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  have hind0 : AffineIndependent ℝ (S.points ∘ ![i, j, k]) :=
    S.independent.comp_embedding ⟨![i, j, k], hemb⟩
  have hfn : S.points ∘ ![i, j, k] = ![S.points i, S.points j, S.points k] := by
    ext r; fin_cases r <;> rfl
  rw [hfn, affineIndependent_iff_not_collinear_set] at hind0
  exact hind0 hcol

lemma vertAngle_pos (S : Triangle ℝ ℝ²) (r : Fin 3) : 0 < vertAngle S r := by
  fin_cases r
  · exact EuclideanGeometry.angle_pos_of_not_collinear
      (not_collinear_triangle_pts S (by decide) (by decide) (by decide))
  · exact EuclideanGeometry.angle_pos_of_not_collinear
      (not_collinear_triangle_pts S (by decide) (by decide) (by decide))
  · exact EuclideanGeometry.angle_pos_of_not_collinear
      (not_collinear_triangle_pts S (by decide) (by decide) (by decide))

lemma vertAngle_lt_pi (S : Triangle ℝ ℝ²) (r : Fin 3) : vertAngle S r < π := by
  fin_cases r
  · exact EuclideanGeometry.angle_lt_pi_of_not_collinear
      (not_collinear_triangle_pts S (by decide) (by decide) (by decide))
  · exact EuclideanGeometry.angle_lt_pi_of_not_collinear
      (not_collinear_triangle_pts S (by decide) (by decide) (by decide))
  · exact EuclideanGeometry.angle_lt_pi_of_not_collinear
      (not_collinear_triangle_pts S (by decide) (by decide) (by decide))

lemma sum_vertAngle (S : Triangle ℝ ℝ²) : ∑ r : Fin 3, vertAngle S r = π := by
  rw [Fin.sum_univ_three]
  dsimp [vertAngle]
  have h10 : S.points 0 ≠ S.points 1 := S.independent.injective.ne (by decide)
  have h := EuclideanGeometry.angle_add_angle_add_angle_eq_pi (S.points 2) h10
  linarith [EuclideanGeometry.angle_comm (S.points 2) (S.points 1) (S.points 0)]

private lemma angle_eq_of_dist_mul {a₁ b₁ c₁ a₂ b₂ c₂ : ℝ²} {k : ℝ} (hk : 0 < k)
    (hab : a₂ ≠ b₂) (hcb : c₂ ≠ b₂)
    (dab : dist a₁ b₁ = k * dist a₂ b₂)
    (dcb : dist c₁ b₁ = k * dist c₂ b₂)
    (dac : dist a₁ c₁ = k * dist a₂ c₂) :
    ∠ a₁ b₁ c₁ = ∠ a₂ b₂ c₂ := by
  have hd1 : 0 < dist a₂ b₂ := dist_pos.mpr hab
  have hd2 : 0 < dist c₂ b₂ := dist_pos.mpr hcb
  have law1 := EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle a₁ b₁ c₁
  have law2 := EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle a₂ b₂ c₂
  rw [dab, dcb, dac] at law1
  have hdiff : (2 * k ^ 2 * dist a₂ b₂ * dist c₂ b₂) *
      (Real.cos (∠ a₁ b₁ c₁) - Real.cos (∠ a₂ b₂ c₂)) = 0 := by
    linear_combination law1 - k ^ 2 * law2
  have hprod : 2 * k ^ 2 * dist a₂ b₂ * dist c₂ b₂ ≠ 0 := by positivity
  have hcos : Real.cos (∠ a₁ b₁ c₁) = Real.cos (∠ a₂ b₂ c₂) :=
    sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left hprod)
  exact Real.injOn_cos ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩ hcos

lemma vertAngle_eq_of_similar {S₁ S₂ : Triangle ℝ ℝ²} (hsim : S₁.points ∼ S₂.points) (r : Fin 3) :
    vertAngle S₁ r = vertAngle S₂ r := by
  rcases hsim with ⟨k, hk0, hdist⟩
  have hk : 0 < (k : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hk0)
  have hd : ∀ i j, dist (S₁.points i) (S₁.points j) = (k : ℝ) * dist (S₂.points i) (S₂.points j) := by
    intro i j
    have he := hdist i j
    rw [edist_dist, edist_dist, ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul (NNReal.coe_nonneg k)] at he
    exact (ENNReal.ofReal_eq_ofReal_iff dist_nonneg (mul_nonneg (NNReal.coe_nonneg k) dist_nonneg)).mp he
  have hinj := S₂.independent.injective
  fin_cases r
  · exact angle_eq_of_dist_mul hk (hinj.ne (by decide)) (hinj.ne (by decide)) (hd 1 0) (hd 2 0) (hd 1 2)
  · exact angle_eq_of_dist_mul hk (hinj.ne (by decide)) (hinj.ne (by decide)) (hd 2 1) (hd 0 1) (hd 2 0)
  · exact angle_eq_of_dist_mul hk (hinj.ne (by decide)) (hinj.ne (by decide)) (hd 0 2) (hd 1 2) (hd 0 1)

noncomputable def t₀ : ℝ := Real.sin γ₁ / Real.sin (γ₀ + γ₁)
noncomputable def p₀ : ℝ² := mkPt 0 0
noncomputable def p₁ : ℝ² := mkPt 1 0
noncomputable def p₂ : ℝ² := mkPt (t₀ * Real.cos γ₀) (t₀ * Real.sin γ₀)

lemma sin_γ_pos : 0 < Real.sin γ₀ ∧ 0 < Real.sin γ₁ ∧ 0 < Real.sin (γ₀ + γ₁) ∧ 0 < t₀ := by
  obtain ⟨h0, h1, h01, h01_lt, -, -⟩ := γ_bounds
  have hpi : 0 < π := Real.pi_pos
  have hs0 : 0 < Real.sin γ₀ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith)
  have hs1 : 0 < Real.sin γ₁ := Real.sin_pos_of_pos_of_lt_pi h1 (by linarith)
  have hs01 : 0 < Real.sin (γ₀ + γ₁) := Real.sin_pos_of_pos_of_lt_pi h01 (by linarith)
  exact ⟨hs0, hs1, hs01, div_pos hs1 hs01⟩

lemma baseTri_independent : AffineIndependent ℝ ![p₀, p₁, p₂] := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ ![p₀, p₁, p₂] 0, Fintype.linearIndependent_iff]
  intro g hg
  obtain ⟨hs0, -, -, ht0⟩ := sin_γ_pos
  have heq : g ⟨1, by decide⟩ • (p₁ -ᵥ p₀) + g ⟨2, by decide⟩ • (p₂ -ᵥ p₀) = 0 := by
    have huniv : (Finset.univ : Finset {x : Fin 3 // x ≠ 0}) = {⟨1, by decide⟩, ⟨2, by decide⟩} := by
      ext ⟨x, hx⟩; fin_cases x <;> simp at hx ⊢
    rw [huniv, Finset.sum_pair (by decide)] at hg
    simpa using hg
  have hlhs : g ⟨1, by decide⟩ • (p₁ -ᵥ p₀) + g ⟨2, by decide⟩ • (p₂ -ᵥ p₀) =
      mkPt (g ⟨1, by decide⟩ * 1 + g ⟨2, by decide⟩ * (t₀ * Real.cos γ₀))
        (0 + g ⟨2, by decide⟩ * (t₀ * Real.sin γ₀)) := by
    simp [p₀, p₁, p₂]
  rw [hlhs, ← mkPt_zero] at heq
  have hc1 : g ⟨2, by decide⟩ * (t₀ * Real.sin γ₀) = 0 := by
    have := congrArg (fun v : ℝ² => v 1) heq
    simpa using this
  have hg2 : g ⟨2, by decide⟩ = 0 :=
    (mul_eq_zero.mp hc1).resolve_right (ne_of_gt (mul_pos ht0 hs0))
  have hc0 : g ⟨1, by decide⟩ = 0 := by
    have := congrArg (fun v : ℝ² => v 0) heq
    simp only [mkPt_apply_zero, hg2, zero_mul, add_zero, mul_one] at this
    exact this
  rintro ⟨i, hi⟩
  fin_cases i
  · exact absurd rfl hi
  · exact hc0
  · exact hg2

noncomputable def baseTri : Triangle ℝ ℝ² :=
  ⟨![p₀, p₁, p₂], baseTri_independent⟩

lemma vertAngle_baseTri : vertAngle baseTri = ![γ₀, γ₁, γ₂] := by
  obtain ⟨h0, h1, h01, h01_lt, h2, h2_lt⟩ := γ_bounds
  obtain ⟨hs0, hs1, hs01, ht0⟩ := sin_γ_pos
  have ha0 : vertAngle baseTri 0 = γ₀ := by
    change InnerProductGeometry.angle (p₁ -ᵥ p₀) (p₂ -ᵥ p₀) = γ₀
    have hv1 : p₁ -ᵥ p₀ = mkPt 1 0 := by rw [p₁, p₀, mkPt_vsub]; ring_nf
    have hv2 : p₂ -ᵥ p₀ = mkPt (t₀ * Real.cos γ₀) (t₀ * Real.sin γ₀) := by
      rw [p₂, p₀, mkPt_vsub]; ring_nf
    have hn1 : ‖p₁ -ᵥ p₀‖ = 1 := by rw [hv1]; exact norm_mkPt_of_nonneg (by norm_num) (by ring)
    have hn2 : ‖p₂ -ᵥ p₀‖ = t₀ := by
      rw [hv2]
      refine norm_mkPt_of_nonneg (le_of_lt ht0) ?_
      linear_combination t₀ ^ 2 * Real.cos_sq_add_sin_sq γ₀
    have hcos : Real.cos (InnerProductGeometry.angle (p₁ -ᵥ p₀) (p₂ -ᵥ p₀)) = Real.cos γ₀ := by
      rw [InnerProductGeometry.cos_angle, hn1, hn2, hv1, hv2, inner_mkPt]
      field_simp [ne_of_gt ht0]
      ring
    exact Real.injOn_cos
      ⟨InnerProductGeometry.angle_nonneg _ _, InnerProductGeometry.angle_le_pi _ _⟩
      ⟨le_of_lt h0, by linarith⟩ hcos
  have ha1 : vertAngle baseTri 1 = γ₁ := by
    change InnerProductGeometry.angle (p₂ -ᵥ p₁) (p₀ -ᵥ p₁) = γ₁
    let s₀ : ℝ := Real.sin γ₀ / Real.sin (γ₀ + γ₁)
    have hs0_pos : 0 < s₀ := div_pos hs0 hs01
    have hv0 : p₀ -ᵥ p₁ = mkPt (-1) 0 := by rw [p₀, p₁, mkPt_vsub]; ring_nf
    have hsub_x : t₀ * Real.cos γ₀ - 1 = -s₀ * Real.cos γ₁ := by
      have hmul_eq : (t₀ * Real.cos γ₀ - 1) * Real.sin (γ₀ + γ₁) =
          (-s₀ * Real.cos γ₁) * Real.sin (γ₀ + γ₁) := by
        have ht_def : t₀ * Real.sin (γ₀ + γ₁) = Real.sin γ₁ := div_mul_cancel₀ _ (ne_of_gt hs01)
        have hs_def : s₀ * Real.sin (γ₀ + γ₁) = Real.sin γ₀ := div_mul_cancel₀ _ (ne_of_gt hs01)
        have hsin_add : Real.sin (γ₀ + γ₁) = Real.sin γ₀ * Real.cos γ₁ + Real.cos γ₀ * Real.sin γ₁ :=
          Real.sin_add γ₀ γ₁
        linear_combination Real.cos γ₀ * ht_def + Real.cos γ₁ * hs_def - hsin_add
      exact mul_right_cancel₀ (ne_of_gt hs01) hmul_eq
    have hsub_y : t₀ * Real.sin γ₀ = s₀ * Real.sin γ₁ := by
      dsimp [t₀, s₀]; field_simp [ne_of_gt hs01]
    have hv2 : p₂ -ᵥ p₁ = mkPt (-s₀ * Real.cos γ₁) (s₀ * Real.sin γ₁) := by
      rw [p₂, p₁, mkPt_vsub, hsub_x, hsub_y, sub_zero]
    have hn0 : ‖p₀ -ᵥ p₁‖ = 1 := by rw [hv0]; exact norm_mkPt_of_nonneg (by norm_num) (by ring)
    have hn2 : ‖p₂ -ᵥ p₁‖ = s₀ := by
      rw [hv2]
      refine norm_mkPt_of_nonneg (le_of_lt hs0_pos) ?_
      linear_combination s₀ ^ 2 * Real.cos_sq_add_sin_sq γ₁
    have hcos : Real.cos (InnerProductGeometry.angle (p₂ -ᵥ p₁) (p₀ -ᵥ p₁)) = Real.cos γ₁ := by
      rw [InnerProductGeometry.cos_angle, hn2, hn0, hv2, hv0, inner_mkPt]
      field_simp [ne_of_gt hs0_pos]
      ring
    exact Real.injOn_cos
      ⟨InnerProductGeometry.angle_nonneg _ _, InnerProductGeometry.angle_le_pi _ _⟩
      ⟨le_of_lt h1, by linarith⟩ hcos
  have ha2 : vertAngle baseTri 2 = γ₂ := by
    have hsum := sum_vertAngle baseTri
    rw [Fin.sum_univ_three, ha0, ha1] at hsum
    dsimp [γ₂]
    linarith
  ext r
  fin_cases r
  · exact ha0
  · exact ha1
  · exact ha2

noncomputable def triBasis (S : Triangle ℝ ℝ²) : AffineBasis (Fin 3) ℝ ℝ² where
  toFun := S.points
  ind' := S.independent
  tot' := S.independent.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp)

@[simp] lemma triBasis_apply (S : Triangle ℝ ℝ²) (i : Fin 3) : triBasis S i = S.points i := rfl

lemma mem_closedInterior_iff_coord (S : Triangle ℝ ℝ²) (x : ℝ²) :
    x ∈ S.closedInterior ↔ ∀ i : Fin 3, 0 ≤ (triBasis S).coord i x := by
  constructor
  · rintro ⟨w, hw, hI, rfl⟩ i
    have heq : (triBasis S).coord i (Finset.univ.affineCombination ℝ (triBasis S) w) = w i :=
      (triBasis S).coord_apply_combination_of_mem (Finset.mem_univ i) hw
    rw [triBasis] at heq
    exact heq ▸ (hI i).1
  · intro hnn
    have hsum : ∑ i : Fin 3, (triBasis S).coord i x = 1 := (triBasis S).sum_coord_apply_eq_one x
    refine ⟨fun i => (triBasis S).coord i x, hsum, fun i => ⟨hnn i, ?_⟩, ?_⟩
    · rw [Fin.sum_univ_three] at hsum
      have h0 := hnn 0; have h1 := hnn 1; have h2 := hnn 2
      fin_cases i <;> dsimp <;> linarith
    · exact (triBasis S).affineCombination_coord_eq_self x

lemma mem_interior_iff_coord (S : Triangle ℝ ℝ²) (x : ℝ²) :
    x ∈ S.interior ↔ ∀ i : Fin 3, 0 < (triBasis S).coord i x := by
  constructor
  · rintro ⟨w, hw, hI, rfl⟩ i
    have heq : (triBasis S).coord i (Finset.univ.affineCombination ℝ (triBasis S) w) = w i :=
      (triBasis S).coord_apply_combination_of_mem (Finset.mem_univ i) hw
    rw [triBasis] at heq
    exact heq ▸ (hI i).1
  · intro hpos
    have hsum : ∑ i : Fin 3, (triBasis S).coord i x = 1 := (triBasis S).sum_coord_apply_eq_one x
    refine ⟨fun i => (triBasis S).coord i x, hsum, fun i => ⟨hpos i, ?_⟩, ?_⟩
    · rw [Fin.sum_univ_three] at hsum
      have h0 := hpos 0; have h1 := hpos 1; have h2 := hpos 2
      fin_cases i <;> dsimp <;> linarith
    · exact (triBasis S).affineCombination_coord_eq_self x

lemma continuous_triCoord (S : Triangle ℝ ℝ²) (i : Fin 3) :
    Continuous ((triBasis S).coord i) :=
  AffineMap.continuous_of_finiteDimensional ((triBasis S).coord i)

lemma isClosed_closedInterior (S : Triangle ℝ ℝ²) : IsClosed S.closedInterior := by
  have heq : S.closedInterior = ⋂ i : Fin 3, {x : ℝ² | 0 ≤ (triBasis S).coord i x} := by
    ext x; simp [mem_closedInterior_iff_coord]
  rw [heq]
  exact isClosed_iInter fun i => isClosed_Ici.preimage (continuous_triCoord S i)

lemma isOpen_interior (S : Triangle ℝ ℝ²) : IsOpen S.interior := by
  have heq : S.interior = ⋂ i : Fin 3, {x : ℝ² | 0 < (triBasis S).coord i x} := by
    ext x; simp [mem_interior_iff_coord]
  rw [heq]
  exact isOpen_iInter_of_finite fun i => isOpen_Ioi.preimage (continuous_triCoord S i)

end Erdos633Proof

namespace Erdos633Proof

open Affine MeasureTheory
open scoped Congruent EuclideanGeometry Similar Real NNReal Pointwise

lemma continuous_coord0 : Continuous (fun x : ℝ² => x 0) := PiLp.continuous_apply 2 _ 0
lemma continuous_coord1 : Continuous (fun x : ℝ² => x 1) := PiLp.continuous_apply 2 _ 1

lemma ext_coord {u v : ℝ²} (h0 : u 0 = v 0) (h1 : u 1 = v 1) : u = v := by
  ext i; fin_cases i
  · exact h0
  · exact h1

noncomputable def orthoMap (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (d : ℝ)
    (hd : d ^ 2 = 1) : ℝ² ≃ₗᵢ[ℝ] ℝ² :=
  { toFun := fun x => mkPt (c * x 0 - s * x 1) (d * (s * x 0 + c * x 1))
    invFun := fun y => mkPt (c * y 0 + d * s * y 1) (-s * y 0 + d * c * y 1)
    left_inv := fun x => by
      apply ext_coord
      · simp only [mkPt_apply_zero, mkPt_apply_one]
        linear_combination x 0 * hcs + s ^ 2 * x 0 * hd + c * s * x 1 * hd
      · simp only [mkPt_apply_zero, mkPt_apply_one]
        linear_combination x 1 * hcs + c ^ 2 * x 1 * hd + c * s * x 0 * hd
    right_inv := fun y => by
      apply ext_coord
      · simp only [mkPt_apply_zero, mkPt_apply_one]
        linear_combination y 0 * hcs
      · simp only [mkPt_apply_zero, mkPt_apply_one]
        linear_combination d ^ 2 * y 1 * hcs + y 1 * hd
    map_add' := fun x y => by ext i; fin_cases i <;> simp <;> ring
    map_smul' := fun r x => by ext i; fin_cases i <;> simp <;> ring
    norm_map' := fun x => by
      refine norm_mkPt_of_nonneg (norm_nonneg x) ?_
      rw [norm_sq_eq]
      linear_combination ((x 0) ^ 2 + (x 1) ^ 2) * hcs + (s * x 0 + c * x 1) ^ 2 * hd }

@[simp] lemma orthoMap_apply (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (d : ℝ) (hd : d ^ 2 = 1) (x : ℝ²) :
    orthoMap c s hcs d hd x = mkPt (c * x 0 - s * x 1) (d * (s * x 0 + c * x 1)) := rfl

@[simp] lemma orthoMap_symm_apply (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (d : ℝ) (hd : d ^ 2 = 1) (y : ℝ²) :
    (orthoMap c s hcs d hd).symm y = mkPt (c * y 0 + d * s * y 1) (-s * y 0 + d * c * y 1) := rfl

noncomputable def rotLI (φ : ℝ) : ℝ² ≃ₗᵢ[ℝ] ℝ² :=
  orthoMap (Real.cos φ) (Real.sin φ) (Real.cos_sq_add_sin_sq φ) 1 (by ring)

noncomputable def reflY : ℝ² ≃ₗᵢ[ℝ] ℝ² :=
  orthoMap 1 0 (by ring) (-1) (by ring)

lemma li_image_eq_preimage (f : ℝ² ≃ₗᵢ[ℝ] ℝ²) (A : Set ℝ²) :
    f '' A = f.symm ⁻¹' A := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨f.symm x, hx, f.apply_symm_apply x⟩

lemma volume_image_li (f : ℝ² ≃ₗᵢ[ℝ] ℝ²) {A : Set ℝ²} (hA : MeasurableSet A) :
    volume (f '' A) = volume A := by
  rw [li_image_eq_preimage, ← Measure.map_apply f.symm.continuous.measurable hA,
    f.symm.measurePreserving.map_eq]

lemma volume_smul_pos {r : ℝ} (hr : 0 < r) (A : Set ℝ²) :
    volume (r • A) = ENNReal.ofReal (r ^ 2) * volume A := by
  rw [Measure.addHaar_smul volume r A]
  have hfr : Module.finrank ℝ ℝ² = 2 := finrank_euclideanSpace_fin
  rw [hfr, abs_of_nonneg (le_of_lt (sq_pos_of_pos hr))]

lemma volume_vadd_eq (p : ℝ²) (A : Set ℝ²) :
    volume ((fun v : ℝ² => v + p) '' A) = volume A := by
  have hpre : (fun v : ℝ² => v + p) '' A = (fun x : ℝ² => x + (-p)) ⁻¹' A := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩; simpa using hv
    · intro hx; exact ⟨x + (-p), hx, by dsimp only; rw [add_assoc, neg_add_cancel, add_zero]⟩
  rw [hpre, measure_preimage_add_right volume (-p) A]

lemma volume_ker_eq_zero {L : ℝ² →ₗ[ℝ] ℝ} (hL : L ≠ 0) :
    volume (LinearMap.ker L : Set ℝ²) = 0 := by
  apply Measure.addHaar_submodule volume (LinearMap.ker L)
  intro htop
  apply hL
  ext v
  exact LinearMap.mem_ker.mp (htop ▸ Submodule.mem_top)

lemma volume_line_eq_zero {a b : ℝ} (hab : a ≠ 0 ∨ b ≠ 0) :
    volume {x : ℝ² | a * x 0 + b * x 1 = 0} = 0 := by
  let L : ℝ² →ₗ[ℝ] ℝ :=
    { toFun := fun x => a * x 0 + b * x 1
      map_add' := fun x y => by simp; ring
      map_smul' := fun r x => by simp; ring }
  have hL : L ≠ 0 := by
    intro h0
    rcases hab with ha | hb
    · apply ha
      have := LinearMap.congr_fun h0 (mkPt 1 0)
      simpa [L] using this
    · apply hb
      have := LinearMap.congr_fun h0 (mkPt 0 1)
      simpa [L] using this
  exact volume_ker_eq_zero hL

lemma volume_affine_zero {φ : ℝ² →ᵃ[ℝ] ℝ} (hsurj : Function.Surjective φ) :
    volume {x : ℝ² | φ x = 0} = 0 := by
  obtain ⟨p₀, hp₀⟩ := hsurj 0
  obtain ⟨p₁, hp₁⟩ := hsurj 1
  have hlin : φ.linear ≠ 0 := by
    intro h0
    have hv := φ.linearMap_vsub p₁ p₀
    rw [h0, LinearMap.zero_apply, hp₁, hp₀] at hv
    norm_num at hv
  have hset : {x : ℝ² | φ x = 0} = (fun v : ℝ² => v + p₀) '' (LinearMap.ker φ.linear : Set ℝ²) := by
    ext x
    constructor
    · intro hx
      change φ x = 0 at hx
      refine ⟨x - p₀, ?_, sub_add_cancel x p₀⟩
      change φ.linear (x -ᵥ p₀) = 0
      rw [φ.linearMap_vsub, hx, hp₀, vsub_self]
    · rintro ⟨v, hv, rfl⟩
      change φ (v +ᵥ p₀) = 0
      change φ.linear v = 0 at hv
      rw [φ.map_vadd, hp₀, hv, vadd_eq_add, add_zero]
  rw [hset, volume_vadd_eq, volume_ker_eq_zero hlin]

lemma volume_closedInterior_diff_interior (S : Triangle ℝ ℝ²) :
    volume (S.closedInterior \ S.interior) = 0 := by
  have hsub : S.closedInterior \ S.interior ⊆ ⋃ i : Fin 3, {x : ℝ² | (triBasis S).coord i x = 0} := by
    rintro x ⟨hx_cl, hx_int⟩
    rw [mem_closedInterior_iff_coord] at hx_cl
    rw [mem_interior_iff_coord] at hx_int
    push Not at hx_int
    rcases hx_int with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, le_antisymm hi (hx_cl i)⟩
  refine measure_mono_null hsub (measure_iUnion_null fun i => ?_)
  exact volume_affine_zero ((triBasis S).surjective_coord i)

lemma toReal_volume_union_of_inter_null {A B : Set ℝ²} (hB : MeasurableSet B)
    (hfinA : volume A ≠ ⊤) (hfinB : volume B ≠ ⊤) (hnull : volume (A ∩ B) = 0) :
    (volume (A ∪ B)).toReal = (volume A).toReal + (volume B).toReal := by
  have hunion := measure_union_add_inter A hB (μ := volume)
  rw [hnull, add_zero] at hunion
  rw [hunion, ENNReal.toReal_add hfinA hfinB]

def B₁ : Set ℝ² := Metric.ball 0 1

lemma volume_B₁_pos : 0 < volume B₁ := Metric.measure_ball_pos volume 0 zero_lt_one
lemma volume_B₁_lt_top : volume B₁ < ⊤ := measure_ball_lt_top
lemma volume_B₁_ne_top : volume B₁ ≠ ⊤ := ne_of_lt volume_B₁_lt_top

noncomputable def V₀ : ℝ := (volume B₁).toReal

lemma V₀_pos : 0 < V₀ := ENNReal.toReal_pos (ne_of_gt volume_B₁_pos) volume_B₁_ne_top

def halfBall : Set ℝ² := B₁ ∩ {x : ℝ² | 0 ≤ x 1}

lemma measurableSet_halfBall : MeasurableSet halfBall :=
  Metric.isOpen_ball.measurableSet.inter (isClosed_Ici.preimage continuous_coord1).measurableSet

lemma volume_subset_B₁_ne_top {A : Set ℝ²} (hA : A ⊆ B₁) : volume A ≠ ⊤ :=
  ne_of_lt (lt_of_le_of_lt (measure_mono hA) volume_B₁_lt_top)

lemma volume_halfBall_toReal : (volume halfBall).toReal = V₀ / 2 := by
  let Hneg : Set ℝ² := reflY '' halfBall
  have hmeas_neg : MeasurableSet Hneg := by
    dsimp only [Hneg]
    rw [li_image_eq_preimage]
    exact reflY.symm.continuous.measurable measurableSet_halfBall
  have hvol_neg : volume Hneg = volume halfBall := volume_image_li reflY measurableSet_halfBall
  have hHneg_eq : Hneg = B₁ ∩ {x : ℝ² | x 1 ≤ 0} := by
    ext x
    change x ∈ reflY '' halfBall ↔ x ∈ B₁ ∧ x 1 ≤ 0
    rw [li_image_eq_preimage]
    change reflY.symm x ∈ B₁ ∧ 0 ≤ (reflY.symm x) 1 ↔ x ∈ B₁ ∧ x 1 ≤ 0
    have hB : reflY.symm x ∈ B₁ ↔ x ∈ B₁ := by
      simp only [B₁, Metric.mem_ball, dist_zero_right, reflY.symm.norm_map]
    have h1 : (0 ≤ (reflY.symm x) 1) ↔ x 1 ≤ 0 := by
      simp only [reflY, orthoMap_symm_apply, mkPt_apply_one]
      constructor <;> intro h <;> linarith
    exact and_congr hB h1
  have hunion : halfBall ∪ Hneg = B₁ := by
    rw [hHneg_eq]
    ext x
    change (x ∈ B₁ ∧ 0 ≤ x 1) ∨ (x ∈ B₁ ∧ x 1 ≤ 0) ↔ x ∈ B₁
    exact ⟨fun h => h.elim And.left And.left,
      fun hxB => (le_total 0 (x 1)).imp (fun h => ⟨hxB, h⟩) (fun h => ⟨hxB, h⟩)⟩
  have hinter : volume (halfBall ∩ Hneg) = 0 := by
    rw [hHneg_eq]
    refine measure_mono_null ?_ (volume_line_eq_zero (a := 0) (b := 1) (Or.inr one_ne_zero))
    rintro x ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
    change 0 ≤ x 1 at h1
    change x 1 ≤ 0 at h2
    change 0 * x 0 + 1 * x 1 = 0
    linarith
  have hfin1 : volume halfBall ≠ ⊤ := volume_subset_B₁_ne_top Set.inter_subset_left
  have hfin2 : volume Hneg ≠ ⊤ := by rw [hvol_neg]; exact hfin1
  have hsum := toReal_volume_union_of_inter_null hmeas_neg hfin1 hfin2 hinter
  rw [hunion, hvol_neg] at hsum
  dsimp [V₀]
  linarith

def stdCone (θ : ℝ) : Set ℝ² :=
  {x : ℝ² | 0 ≤ x 1 ∧ x 1 * Real.cos θ ≤ x 0 * Real.sin θ}

def stdSector (θ : ℝ) : Set ℝ² := B₁ ∩ stdCone θ

lemma measurableSet_stdSector (θ : ℝ) : MeasurableSet (stdSector θ) := by
  refine Metric.isOpen_ball.measurableSet.inter (IsClosed.measurableSet ?_)
  exact (isClosed_Ici.preimage continuous_coord1).inter
    (isClosed_le (continuous_coord1.mul continuous_const) (continuous_coord0.mul continuous_const))

noncomputable def secVol (θ : ℝ) : ℝ := (volume (stdSector θ)).toReal

lemma secVol_pos {θ : ℝ} (h0 : 0 < θ) (hpi : θ < π) : 0 < secVol θ := by
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 hpi
  let U : Set ℝ² := B₁ ∩ {x : ℝ² | 0 < x 1 ∧ x 1 * Real.cos θ < x 0 * Real.sin θ}
  have hopen : IsOpen U :=
    Metric.isOpen_ball.inter ((isOpen_Ioi.preimage continuous_coord1).inter
      (isOpen_lt (continuous_coord1.mul continuous_const) (continuous_coord0.mul continuous_const)))
  let p : ℝ² := mkPt ((1 + Real.cos θ) / 3) (Real.sin θ / 3)
  have hpU : p ∈ U := by
    refine ⟨?_, ?_, ?_⟩
    · simp only [B₁, Metric.mem_ball, dist_zero_right]
      have hsq : ‖p‖ ^ 2 < 1 := by
        rw [norm_sq_mkPt]
        have hcs := Real.cos_sq_add_sin_sq θ
        have hcos_le : Real.cos θ ≤ 1 := Real.cos_le_one θ
        nlinarith
      nlinarith [norm_nonneg p]
    · simp only [p, mkPt_apply_one]; positivity
    · simp only [p, mkPt_apply_zero, mkPt_apply_one]; nlinarith
  have hUpos : 0 < volume U := hopen.measure_pos volume ⟨p, hpU⟩
  have hsub : U ⊆ stdSector θ := fun x ⟨hxB, hx1, hx2⟩ => ⟨hxB, le_of_lt hx1, le_of_lt hx2⟩
  have hpos : 0 < volume (stdSector θ) := lt_of_lt_of_le hUpos (measure_mono hsub)
  exact ENNReal.toReal_pos (ne_of_gt hpos) (volume_subset_B₁_ne_top Set.inter_subset_left)

private lemma rotLI_image_stdSector (θ₁ θ₂ : ℝ) :
    rotLI θ₁ '' stdSector θ₂ =
      B₁ ∩ {x : ℝ² | x 0 * Real.sin θ₁ ≤ x 1 * Real.cos θ₁ ∧
        x 1 * Real.cos (θ₁ + θ₂) ≤ x 0 * Real.sin (θ₁ + θ₂)} := by
  ext x
  rw [li_image_eq_preimage]
  let y := (rotLI θ₁).symm x
  change (y ∈ B₁ ∧ 0 ≤ y 1 ∧ y 1 * Real.cos θ₂ ≤ y 0 * Real.sin θ₂) ↔
    x ∈ B₁ ∧ x 0 * Real.sin θ₁ ≤ x 1 * Real.cos θ₁ ∧
      x 1 * Real.cos (θ₁ + θ₂) ≤ x 0 * Real.sin (θ₁ + θ₂)
  have hB : y ∈ B₁ ↔ x ∈ B₁ := by
    simp only [y, B₁, Metric.mem_ball, dist_zero_right, (rotLI θ₁).symm.norm_map]
  have hy0 : y 0 = Real.cos θ₁ * x 0 + Real.sin θ₁ * x 1 := by
    simp [y, rotLI]
  have hy1 : y 1 = -Real.sin θ₁ * x 0 + Real.cos θ₁ * x 1 := by
    simp [y, rotLI]
  rw [hB, hy0, hy1, Real.cos_add, Real.sin_add]
  exact and_congr_right fun _ => ⟨fun ⟨h1, h2⟩ => ⟨by linarith, by linarith⟩,
    fun ⟨h1, h2⟩ => ⟨by linarith, by linarith⟩⟩

lemma secVol_add {θ₁ θ₂ : ℝ} (h1 : 0 < θ₁) (h2 : 0 < θ₂) (h12 : θ₁ + θ₂ < π) :
    secVol (θ₁ + θ₂) = secVol θ₁ + secVol θ₂ := by
  have hpi : 0 < π := Real.pi_pos
  have hs1 : 0 < Real.sin θ₁ := Real.sin_pos_of_pos_of_lt_pi h1 (by linarith)
  have hs2 : 0 < Real.sin θ₂ := Real.sin_pos_of_pos_of_lt_pi h2 (by linarith)
  have hs12 : 0 < Real.sin (θ₁ + θ₂) := Real.sin_pos_of_pos_of_lt_pi (by linarith) h12
  let S₂' : Set ℝ² := rotLI θ₁ '' stdSector θ₂
  have hmeas2' : MeasurableSet S₂' := by
    dsimp only [S₂']
    rw [li_image_eq_preimage]
    exact (rotLI θ₁).symm.continuous.measurable (measurableSet_stdSector θ₂)
  have hvol2' : volume S₂' = volume (stdSector θ₂) :=
    volume_image_li (rotLI θ₁) (measurableSet_stdSector θ₂)
  have hsin_sub : Real.sin θ₂ = Real.sin (θ₁ + θ₂) * Real.cos θ₁ - Real.cos (θ₁ + θ₂) * Real.sin θ₁ := by
    have : θ₂ = (θ₁ + θ₂) - θ₁ := by ring
    conv_lhs => rw [this, Real.sin_sub]
  have hunion : stdSector θ₁ ∪ S₂' = stdSector (θ₁ + θ₂) := by
    dsimp only [S₂']
    rw [rotLI_image_stdSector]
    ext x
    change (x ∈ B₁ ∧ 0 ≤ x 1 ∧ x 1 * Real.cos θ₁ ≤ x 0 * Real.sin θ₁) ∨
        (x ∈ B₁ ∧ x 0 * Real.sin θ₁ ≤ x 1 * Real.cos θ₁ ∧
          x 1 * Real.cos (θ₁ + θ₂) ≤ x 0 * Real.sin (θ₁ + θ₂)) ↔
      x ∈ B₁ ∧ 0 ≤ x 1 ∧ x 1 * Real.cos (θ₁ + θ₂) ≤ x 0 * Real.sin (θ₁ + θ₂)
    constructor
    · rintro (⟨hxB, hx1, hL⟩ | ⟨hxB, hL, hR⟩)
      · refine ⟨hxB, hx1, ?_⟩
        have hident : Real.sin θ₁ * (x 0 * Real.sin (θ₁ + θ₂) - x 1 * Real.cos (θ₁ + θ₂)) =
            Real.sin (θ₁ + θ₂) * (x 0 * Real.sin θ₁ - x 1 * Real.cos θ₁) + Real.sin θ₂ * x 1 := by
          rw [hsin_sub]; ring
        nlinarith
      · refine ⟨hxB, ?_, hR⟩
        have hident : Real.sin θ₂ * x 1 =
            Real.sin θ₁ * (x 0 * Real.sin (θ₁ + θ₂) - x 1 * Real.cos (θ₁ + θ₂)) +
            Real.sin (θ₁ + θ₂) * (x 1 * Real.cos θ₁ - x 0 * Real.sin θ₁) := by
          rw [hsin_sub]; ring
        nlinarith
    · rintro ⟨hxB, hx1, hR⟩
      rcases le_total (x 1 * Real.cos θ₁) (x 0 * Real.sin θ₁) with hle | hge
      · exact Or.inl ⟨hxB, hx1, hle⟩
      · exact Or.inr ⟨hxB, hge, hR⟩
  have hinter : volume (stdSector θ₁ ∩ S₂') = 0 := by
    dsimp only [S₂']
    rw [rotLI_image_stdSector]
    refine measure_mono_null ?_
      (volume_line_eq_zero (a := Real.sin θ₁) (b := -Real.cos θ₁) (Or.inl (ne_of_gt hs1)))
    rintro x ⟨⟨_, _, hle⟩, ⟨_, hge, _⟩⟩
    change x 1 * Real.cos θ₁ ≤ x 0 * Real.sin θ₁ at hle
    change x 0 * Real.sin θ₁ ≤ x 1 * Real.cos θ₁ at hge
    change Real.sin θ₁ * x 0 + -Real.cos θ₁ * x 1 = 0
    linarith
  have hfin1 : volume (stdSector θ₁) ≠ ⊤ := volume_subset_B₁_ne_top Set.inter_subset_left
  have hfin2' : volume S₂' ≠ ⊤ := by rw [hvol2']; exact volume_subset_B₁_ne_top Set.inter_subset_left
  have hsum := toReal_volume_union_of_inter_null hmeas2' hfin1 hfin2' hinter
  rw [hunion, hvol2'] at hsum
  exact hsum

lemma secVol_suppl {θ : ℝ} (h0 : 0 < θ) (hpi : θ < π) :
    secVol θ + secVol (π - θ) = V₀ / 2 := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 hpi
  let S₂' : Set ℝ² := rotLI θ '' stdSector (π - θ)
  have hmeas2' : MeasurableSet S₂' := by
    dsimp only [S₂']
    rw [li_image_eq_preimage]
    exact (rotLI θ).symm.continuous.measurable (measurableSet_stdSector (π - θ))
  have hvol2' : volume S₂' = volume (stdSector (π - θ)) :=
    volume_image_li (rotLI θ) (measurableSet_stdSector (π - θ))
  have hS₂'_eq : S₂' = B₁ ∩ {x : ℝ² | x 0 * Real.sin θ ≤ x 1 * Real.cos θ ∧ 0 ≤ x 1} := by
    dsimp only [S₂']
    rw [rotLI_image_stdSector]
    have hsum : θ + (π - θ) = π := by ring
    rw [hsum, Real.cos_pi, Real.sin_pi]
    ext x
    exact and_congr_right fun _ => and_congr_right fun _ => ⟨fun h => by linarith, fun h => by linarith⟩
  have hunion : stdSector θ ∪ S₂' = halfBall := by
    rw [hS₂'_eq]
    ext x
    change (x ∈ B₁ ∧ 0 ≤ x 1 ∧ x 1 * Real.cos θ ≤ x 0 * Real.sin θ) ∨
        (x ∈ B₁ ∧ x 0 * Real.sin θ ≤ x 1 * Real.cos θ ∧ 0 ≤ x 1) ↔
      x ∈ B₁ ∧ 0 ≤ x 1
    constructor
    · rintro (⟨hxB, hx1, _⟩ | ⟨hxB, _, hx1⟩) <;> exact ⟨hxB, hx1⟩
    · rintro ⟨hxB, hx1⟩
      rcases le_total (x 1 * Real.cos θ) (x 0 * Real.sin θ) with hle | hge
      · exact Or.inl ⟨hxB, hx1, hle⟩
      · exact Or.inr ⟨hxB, hge, hx1⟩
  have hinter : volume (stdSector θ ∩ S₂') = 0 := by
    rw [hS₂'_eq]
    refine measure_mono_null ?_
      (volume_line_eq_zero (a := Real.sin θ) (b := -Real.cos θ) (Or.inl (ne_of_gt hs)))
    rintro x ⟨⟨_, _, hle⟩, ⟨_, hge, _⟩⟩
    change x 1 * Real.cos θ ≤ x 0 * Real.sin θ at hle
    change x 0 * Real.sin θ ≤ x 1 * Real.cos θ at hge
    change Real.sin θ * x 0 + -Real.cos θ * x 1 = 0
    linarith
  have hfin1 : volume (stdSector θ) ≠ ⊤ := volume_subset_B₁_ne_top Set.inter_subset_left
  have hfin2' : volume S₂' ≠ ⊤ := by rw [hvol2']; exact volume_subset_B₁_ne_top Set.inter_subset_left
  have hsum := toReal_volume_union_of_inter_null hmeas2' hfin1 hfin2' hinter
  rw [hunion, hvol2', volume_halfBall_toReal] at hsum
  exact hsum.symm

lemma secVol_strictMono {θ₁ θ₂ : ℝ} (h1 : 0 < θ₁) (h12 : θ₁ < θ₂) (h2 : θ₂ < π) :
    secVol θ₁ < secVol θ₂ := by
  have heq : θ₂ = θ₁ + (θ₂ - θ₁) := by ring
  rw [heq, secVol_add h1 (sub_pos.mpr h12) (by linarith)]
  linarith [secVol_pos (sub_pos.mpr h12) (by linarith)]

lemma secVol_nat_mul : ∀ (k : ℕ), 1 ≤ k → ∀ {θ : ℝ}, 0 < θ → (k : ℝ) * θ < π →
    secVol ((k : ℝ) * θ) = (k : ℝ) * secVol θ
  | 0, hk, _, _, _ => absurd hk (by decide)
  | 1, _, θ, _, _ => by simp
  | k + 2, _, θ, hθ, hlt => by
    have hk1 : 1 ≤ k + 1 := by omega
    have hlt1 : ((k + 1 : ℕ) : ℝ) * θ < π := by push_cast at hlt ⊢; linarith
    have ih := secVol_nat_mul (k + 1) hk1 hθ hlt1
    have hsplit : ((k + 2 : ℕ) : ℝ) * θ = ((k + 1 : ℕ) : ℝ) * θ + θ := by push_cast; ring
    rw [hsplit, secVol_add (by positivity) hθ (by linarith), ih]
    push_cast; ring

lemma secVol_rat_pi {q : ℚ} (hq0 : 0 < q) (hq1 : q < 1) :
    secVol ((q : ℝ) * π) = (q : ℝ) * (V₀ / 2) := by
  have hpi : 0 < π := Real.pi_pos
  let p : ℕ := q.num.toNat
  let d : ℕ := q.den
  have hp_pos : 0 < p := by
    have hnum_pos : 0 < q.num := Rat.num_pos.mpr hq0
    dsimp [p]; omega
  have hq_eq : (q : ℝ) = (p : ℝ) / (d : ℝ) := by
    have hnum_nn : 0 ≤ q.num := le_of_lt (Rat.num_pos.mpr hq0)
    have hpZ : (p : ℤ) = q.num := Int.toNat_of_nonneg hnum_nn
    conv_lhs => rw [← Rat.num_div_den q, ← hpZ]
    push_cast; rfl
  have hpd : p < d := by
    have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr q.den_pos
    have hq1R : (q : ℝ) < 1 := by exact_mod_cast hq1
    have h1 : (p : ℝ) / (d : ℝ) < 1 := hq_eq ▸ hq1R
    have h2 : (p : ℝ) < (d : ℝ) := (div_lt_one hd_pos).mp h1
    exact_mod_cast h2
  have hd2 : 2 ≤ d := by omega
  have hd_posR : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  have hunit : secVol (π / (d : ℝ)) = (V₀ / 2) / (d : ℝ) := by
    have hu_pos : 0 < π / (d : ℝ) := div_pos hpi hd_posR
    have hu_lt : π / (d : ℝ) < π := div_lt_self hpi (by exact_mod_cast hd2)
    have hsup := secVol_suppl hu_pos hu_lt
    have hrem : π - π / (d : ℝ) = ((d - 1 : ℕ) : ℝ) * (π / (d : ℝ)) := by
      rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
      field_simp [ne_of_gt hd_posR]
    have hmul := secVol_nat_mul (d - 1) (by omega) hu_pos (by rw [← hrem]; linarith)
    rw [hrem, hmul, Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one] at hsup
    have htot : (d : ℝ) * secVol (π / (d : ℝ)) = V₀ / 2 := by linarith
    rw [eq_div_iff (ne_of_gt hd_posR)]
    linarith
  have harg : (q : ℝ) * π = (p : ℝ) * (π / (d : ℝ)) := by rw [hq_eq]; ring
  have hp_lt : (p : ℝ) * (π / (d : ℝ)) < π := by
    rw [← harg, hq_eq]
    have : (p : ℝ) / (d : ℝ) < 1 := (div_lt_one hd_posR).mpr (by exact_mod_cast hpd)
    nlinarith
  rw [harg, secVol_nat_mul p (by omega) (div_pos hpi hd_posR) hp_lt, hunit, hq_eq]
  ring

lemma secVol_eq {θ : ℝ} (h0 : 0 < θ) (hpi : θ < π) :
    secVol θ = (V₀ / (2 * π)) * θ := by
  have hpi_pos : 0 < π := Real.pi_pos
  have hH : 0 < V₀ / 2 := half_pos V₀_pos
  suffices h : secVol θ / (V₀ / 2) = θ / π by
    have := (div_eq_iff (ne_of_gt hH)).mp h
    linarith [show (θ / π) * (V₀ / 2) = (V₀ / (2 * π)) * θ by ring]
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    have hq_pos : 0 < q := by
      have : 0 < (q : ℝ) := lt_trans (div_pos (secVol_pos h0 hpi) hH) hq1
      exact_mod_cast this
    have hq_lt1 : q < 1 := by
      have : (q : ℝ) < 1 := lt_trans hq2 ((div_lt_one hpi_pos).mpr hpi)
      exact_mod_cast this
    have hq_theta : (q : ℝ) * π < θ := (lt_div_iff₀ hpi_pos).mp hq2
    have hmono := secVol_strictMono (mul_pos (Rat.cast_pos.mpr hq_pos) hpi_pos) hq_theta hpi
    rw [secVol_rat_pi hq_pos hq_lt1] at hmono
    have : (q : ℝ) < secVol θ / (V₀ / 2) := (lt_div_iff₀ hH).mpr hmono
    linarith
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hgt
    have hq_pos : 0 < q := by
      have : 0 < (q : ℝ) := lt_trans (div_pos h0 hpi_pos) hq1
      exact_mod_cast this
    have hq_lt1 : q < 1 := by
      have : (q : ℝ) < 1 := lt_trans hq2 ((div_lt_one hH).mpr (by
        have := secVol_suppl h0 hpi
        have := secVol_pos (sub_pos.mpr hpi) (by linarith)
        linarith))
      exact_mod_cast this
    have htheta_q : θ < (q : ℝ) * π := (div_lt_iff₀ hpi_pos).mp hq1
    have hmono := secVol_strictMono h0 htheta_q (by
      have : (q : ℝ) < 1 := by exact_mod_cast hq_lt1
      nlinarith)
    rw [secVol_rat_pi hq_pos hq_lt1] at hmono
    have : secVol θ / (V₀ / 2) < (q : ℝ) := (div_lt_iff₀ hH).mpr hmono
    linarith

noncomputable def κ : ℝ := V₀ / (2 * π)

lemma κ_pos : 0 < κ := div_pos V₀_pos (mul_pos two_pos Real.pi_pos)

lemma volume_ball_r_toReal {r : ℝ} (hr : 0 < r) :
    (volume (Metric.ball (0 : ℝ²) r)).toReal = κ * r ^ 2 * (2 * π) := by
  have hball : Metric.ball (0 : ℝ²) r = r • B₁ := by
    ext x
    simp only [B₁, Metric.mem_ball, dist_zero_right, Set.mem_smul_set]
    constructor
    · intro hx
      refine ⟨r⁻¹ • x, ?_, smul_inv_smul₀ (ne_of_gt hr) x⟩
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_mul_lt_iff₀ hr, mul_one]
      exact hx
    · rintro ⟨y, hy, rfl⟩
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      nlinarith [norm_nonneg y]
  rw [hball, volume_smul_pos hr, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg r)]
  dsimp [κ, V₀]
  field_simp [ne_of_gt Real.pi_pos]

lemma volume_halfBall_r_toReal {L : ℝ² →ₗ[ℝ] ℝ} (hL : L ≠ 0) {r : ℝ} (hr : 0 < r) :
    (volume (Metric.ball (0 : ℝ²) r ∩ {v : ℝ² | 0 ≤ L v})).toReal = κ * r ^ 2 * π := by
  let a : ℝ := L (mkPt 1 0)
  let b : ℝ := L (mkPt 0 1)
  have hL_eq : ∀ v : ℝ², L v = a * v 0 + b * v 1 := by
    intro v
    have hv : v = v 0 • mkPt 1 0 + v 1 • mkPt 0 1 := by
      ext i; fin_cases i <;> simp
    conv_lhs => rw [hv]
    rw [map_add, map_smul, map_smul]
    dsimp [a, b]
    ring
  have hab : a ^ 2 + b ^ 2 ≠ 0 := by
    intro h0
    apply hL
    ext v
    have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    simp [hL_eq v, ha, hb]
  let nrm : ℝ := √(a ^ 2 + b ^ 2)
  have hnrm_pos : 0 < nrm := Real.sqrt_pos.mpr (lt_of_le_of_ne (by positivity) (Ne.symm hab))
  let c : ℝ := b / nrm
  let s : ℝ := a / nrm
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    dsimp [c, s, nrm]
    rw [div_pow, div_pow, ← add_div, show b ^ 2 + a ^ 2 = a ^ 2 + b ^ 2 by ring,
      Real.sq_sqrt (by positivity)]
    exact div_self hab
  obtain ⟨O, hO_1⟩ : ∃ O : ℝ² ≃ₗᵢ[ℝ] ℝ², ∀ x : ℝ², (O x) 1 = (a * x 0 + b * x 1) / nrm := by
    refine ⟨orthoMap c s hcs 1 (by ring), fun x => ?_⟩
    simp only [orthoMap_apply, mkPt_apply_one, one_mul, c, s]
    field_simp [ne_of_gt hnrm_pos]
  have hset : Metric.ball (0 : ℝ²) r ∩ {v : ℝ² | 0 ≤ L v} = r • (O.symm '' halfBall) := by
    ext v
    rw [Set.mem_smul_set]
    change (v ∈ Metric.ball 0 r ∧ 0 ≤ L v) ↔ ∃ u ∈ O.symm '' halfBall, r • u = v
    rw [li_image_eq_preimage]
    simp only [Metric.mem_ball, dist_zero_right, hL_eq]
    constructor
    · rintro ⟨hv, hLv⟩
      refine ⟨r⁻¹ • v, ?_, smul_inv_smul₀ (ne_of_gt hr) v⟩
      change O (r⁻¹ • v) ∈ B₁ ∧ 0 ≤ (O (r⁻¹ • v)) 1
      refine ⟨?_, ?_⟩
      · simp only [B₁, Metric.mem_ball, dist_zero_right, O.norm_map, norm_smul, Real.norm_eq_abs,
          abs_inv, abs_of_pos hr, inv_mul_lt_iff₀ hr, mul_one]
        exact hv
      · rw [hO_1]
        have hlin : (a * (r⁻¹ • v) 0 + b * (r⁻¹ • v) 1) / nrm = (a * v 0 + b * v 1) / (nrm * r) := by
          change (a * (r⁻¹ * v 0) + b * (r⁻¹ * v 1)) / nrm = _
          field_simp [ne_of_gt hnrm_pos, ne_of_gt hr]
        rw [hlin]
        exact div_nonneg hLv (mul_nonneg (le_of_lt hnrm_pos) (le_of_lt hr))
    · rintro ⟨u, hu, rfl⟩
      change O u ∈ B₁ ∧ 0 ≤ (O u) 1 at hu
      rcases hu with ⟨huB, hu1⟩
      simp only [B₁, Metric.mem_ball, dist_zero_right, O.norm_map] at huB
      rw [hO_1] at hu1
      refine ⟨?_, ?_⟩
      · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
        nlinarith [norm_nonneg u]
      · have hau : 0 ≤ a * u 0 + b * u 1 := by
          have := mul_nonneg hu1 (le_of_lt hnrm_pos)
          rwa [div_mul_cancel₀ _ (ne_of_gt hnrm_pos)] at this
        change 0 ≤ a * (r * u 0) + b * (r * u 1)
        have : a * (r * u 0) + b * (r * u 1) = r * (a * u 0 + b * u 1) := by ring
        rw [this]
        exact mul_nonneg (le_of_lt hr) hau
  rw [hset, volume_smul_pos hr, volume_image_li O.symm measurableSet_halfBall,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg r), volume_halfBall_toReal]
  dsimp [κ]
  field_simp [ne_of_gt Real.pi_pos]

private lemma reflY_apply (x : ℝ²) : reflY x = mkPt (x 0) (-x 1) := by
  ext i; fin_cases i <;> simp [reflY]

private lemma exists_ortho_two_unit {e₁ e₂ : ℝ²} {θ : ℝ}
    (he1 : ‖e₁‖ = 1) (he2 : ‖e₂‖ = 1) (hsin : 0 < Real.sin θ)
    (hinner : inner ℝ e₁ e₂ = Real.cos θ) :
    ∃ O : ℝ² ≃ₗᵢ[ℝ] ℝ², O e₁ = mkPt 1 0 ∧ O e₂ = mkPt (Real.cos θ) (Real.sin θ) := by
  have hcs1 : (e₁ 0) ^ 2 + (e₁ 1) ^ 2 = 1 := by rw [← norm_sq_eq, he1, one_pow]
  obtain ⟨O₀, hO₀_e1⟩ : ∃ O₀ : ℝ² ≃ₗᵢ[ℝ] ℝ², O₀ e₁ = mkPt 1 0 := by
    refine ⟨orthoMap (e₁ 0) (-e₁ 1) (by linear_combination hcs1) 1 (by ring), ?_⟩
    apply ext_coord
    · simp only [orthoMap_apply, mkPt_apply_zero]; linear_combination hcs1
    · simp only [orthoMap_apply, mkPt_apply_one]; ring
  obtain ⟨R, hR_apply⟩ : ∃ R : ℝ² ≃ₗᵢ[ℝ] ℝ², ∀ x : ℝ², R x = mkPt (x 0) (-x 1) :=
    ⟨reflY, reflY_apply⟩
  let w : ℝ² := O₀ e₂
  have hw_norm : (w 0) ^ 2 + (w 1) ^ 2 = 1 := by
    rw [← norm_sq_eq]; dsimp [w]; rw [O₀.norm_map, he2, one_pow]
  have hw0 : w 0 = Real.cos θ := by
    have hi : inner ℝ (O₀ e₁) (O₀ e₂) = inner ℝ e₁ e₂ := O₀.inner_map_map e₁ e₂
    have hw_mk : O₀ e₂ = mkPt (w 0) (w 1) := by ext i; fin_cases i <;> rfl
    rw [hO₀_e1, hinner, hw_mk, inner_mkPt] at hi
    linarith
  have hw1_sq : (w 1) ^ 2 = (Real.sin θ) ^ 2 := by
    have hcs_θ := Real.cos_sq_add_sin_sq θ
    rw [hw0] at hw_norm
    linarith
  by_cases hw1_nn : 0 ≤ w 1
  · refine ⟨O₀, hO₀_e1, ?_⟩
    have hw1 : w 1 = Real.sin θ := by nlinarith [hw1_sq, sq_nonneg (w 1 - Real.sin θ)]
    ext i; fin_cases i
    · exact hw0
    · exact hw1
  · push Not at hw1_nn
    refine ⟨O₀.trans R, ?_, ?_⟩
    · change R (O₀ e₁) = mkPt 1 0
      rw [hO₀_e1, hR_apply]
      ext i; fin_cases i <;> simp
    · have hw1 : w 1 = -Real.sin θ := by nlinarith [hw1_sq, sq_nonneg (w 1 + Real.sin θ)]
      change R w = mkPt (Real.cos θ) (Real.sin θ)
      rw [hR_apply, hw0, hw1, neg_neg]

lemma volume_sector_r_toReal {d₁ d₂ : ℝ²}
    (hnc : ¬ Collinear ℝ ({(0 : ℝ²), d₁, d₂} : Set ℝ²)) {r : ℝ} (hr : 0 < r) :
    (volume (Metric.ball (0 : ℝ²) r ∩
      {v : ℝ² | ∃ a ≥ (0 : ℝ), ∃ b ≥ (0 : ℝ), v = a • d₁ + b • d₂})).toReal =
      κ * r ^ 2 * InnerProductGeometry.angle d₁ d₂ := by
  let θ : ℝ := InnerProductGeometry.angle d₁ d₂
  have hθ_eq : θ = ∠ d₁ (0 : ℝ²) d₂ := by
    change InnerProductGeometry.angle d₁ d₂ = InnerProductGeometry.angle (d₁ -ᵥ 0) (d₂ -ᵥ 0)
    simp
  have hnc' : ¬ Collinear ℝ ({d₁, (0 : ℝ²), d₂} : Set ℝ²) := by
    have hset_eq : ({d₁, (0 : ℝ²), d₂} : Set ℝ²) = {(0 : ℝ²), d₁, d₂} := by
      ext x; simp [or_left_comm]
    rwa [hset_eq]
  have hθ_pos : 0 < θ := hθ_eq ▸ EuclideanGeometry.angle_pos_of_not_collinear hnc'
  have hθ_lt : θ < π := hθ_eq ▸ EuclideanGeometry.angle_lt_pi_of_not_collinear hnc'
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ_pos hθ_lt
  have hd1 : d₁ ≠ 0 := by
    intro h0; apply hnc'; subst h0
    have : ({(0 : ℝ²), (0 : ℝ²), d₂} : Set ℝ²) = {0, d₂} := by ext x; simp
    rw [this]; exact collinear_pair ℝ 0 d₂
  have hd2 : d₂ ≠ 0 := by
    intro h0; apply hnc'; subst h0
    have : ({d₁, (0 : ℝ²), (0 : ℝ²)} : Set ℝ²) = {d₁, 0} := by ext x; simp
    rw [this]; exact collinear_pair ℝ d₁ 0
  have hn1 : 0 < ‖d₁‖ := norm_pos_iff.mpr hd1
  have hn2 : 0 < ‖d₂‖ := norm_pos_iff.mpr hd2
  let e₁ : ℝ² := ‖d₁‖⁻¹ • d₁
  let e₂ : ℝ² := ‖d₂‖⁻¹ • d₂
  have he1_norm : ‖e₁‖ = 1 := by simp [e₁, norm_smul, inv_mul_cancel₀ (ne_of_gt hn1)]
  have he2_norm : ‖e₂‖ = 1 := by simp [e₂, norm_smul, inv_mul_cancel₀ (ne_of_gt hn2)]
  have hinner : inner ℝ e₁ e₂ = Real.cos θ := by
    dsimp [θ]
    rw [InnerProductGeometry.cos_angle, inner_smul_left, inner_smul_right]
    simp only [RCLike.conj_to_real]
    field_simp [ne_of_gt hn1, ne_of_gt hn2]
  obtain ⟨O, hO_e1, hO_e2⟩ := exists_ortho_two_unit he1_norm he2_norm hsin hinner
  have hset : Metric.ball (0 : ℝ²) r ∩
      {v : ℝ² | ∃ a ≥ (0 : ℝ), ∃ b ≥ (0 : ℝ), v = a • d₁ + b • d₂} =
      r • (O.symm '' stdSector θ) := by
    ext v
    rw [Set.mem_smul_set]
    change (v ∈ Metric.ball 0 r ∧ ∃ a ≥ (0 : ℝ), ∃ b ≥ (0 : ℝ), v = a • d₁ + b • d₂) ↔
      ∃ u ∈ O.symm '' stdSector θ, r • u = v
    rw [li_image_eq_preimage]
    simp only [Metric.mem_ball, dist_zero_right]
    constructor
    · rintro ⟨hv, a, ha, b, hb, rfl⟩
      refine ⟨r⁻¹ • (a • d₁ + b • d₂), ?_, smul_inv_smul₀ (ne_of_gt hr) _⟩
      change O (r⁻¹ • (a • d₁ + b • d₂)) ∈ B₁ ∧
        0 ≤ (O (r⁻¹ • (a • d₁ + b • d₂))) 1 ∧
        (O (r⁻¹ • (a • d₁ + b • d₂))) 1 * Real.cos θ ≤ (O (r⁻¹ • (a • d₁ + b • d₂))) 0 * Real.sin θ
      refine ⟨?_, ?_⟩
      · simp only [B₁, Metric.mem_ball, dist_zero_right, O.norm_map, norm_smul, Real.norm_eq_abs,
          abs_inv, abs_of_pos hr, inv_mul_lt_iff₀ hr, mul_one]
        exact hv
      · have hOv : O (r⁻¹ • (a • d₁ + b • d₂)) =
            (r⁻¹ * a * ‖d₁‖) • mkPt 1 0 + (r⁻¹ * b * ‖d₂‖) • mkPt (Real.cos θ) (Real.sin θ) := by
          have hd1_e : d₁ = ‖d₁‖ • e₁ := by dsimp [e₁]; rw [smul_inv_smul₀ (ne_of_gt hn1)]
          have hd2_e : d₂ = ‖d₂‖ • e₂ := by dsimp [e₂]; rw [smul_inv_smul₀ (ne_of_gt hn2)]
          conv_lhs => rw [hd1_e, hd2_e]
          simp only [map_smul, map_add, hO_e1, hO_e2, smul_add, smul_smul]
          ring_nf
        rw [hOv]
        have hc1 : 0 ≤ r⁻¹ * a * ‖d₁‖ := by positivity
        have hc2 : 0 ≤ r⁻¹ * b * ‖d₂‖ := by positivity
        simp only [mkPt_smul, mkPt_add, mkPt_apply_zero, mkPt_apply_one, mul_one, mul_zero, zero_add]
        exact ⟨by positivity, by nlinarith⟩
    · rintro ⟨u, hu, rfl⟩
      change O u ∈ B₁ ∧ 0 ≤ (O u) 1 ∧ (O u) 1 * Real.cos θ ≤ (O u) 0 * Real.sin θ at hu
      rcases hu with ⟨huB, hu1, hu2⟩
      simp only [B₁, Metric.mem_ball, dist_zero_right, O.norm_map] at huB
      refine ⟨?_, ?_⟩
      · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
        nlinarith [norm_nonneg u]
      · let Ou := O u
        let α : ℝ := ((Ou 0) * Real.sin θ - (Ou 1) * Real.cos θ) / Real.sin θ
        let β : ℝ := (Ou 1) / Real.sin θ
        have hα : 0 ≤ α := div_nonneg (by dsimp [Ou]; linarith) (le_of_lt hsin)
        have hβ : 0 ≤ β := div_nonneg hu1 (le_of_lt hsin)
        have hOu : O u = α • O e₁ + β • O e₂ := by
          rw [hO_e1, hO_e2]
          ext i; fin_cases i
          · change (O u) 0 = (α • mkPt 1 0 + β • mkPt (Real.cos θ) (Real.sin θ)) 0
            simp only [mkPt_smul, mkPt_add, mkPt_apply_zero, mul_one, α, β, Ou]
            field_simp [ne_of_gt hsin]; ring
          · change (O u) 1 = (α • mkPt 1 0 + β • mkPt (Real.cos θ) (Real.sin θ)) 1
            simp only [mkPt_smul, mkPt_add, mkPt_apply_one, mul_zero, zero_add, β, Ou]
            exact (div_mul_cancel₀ _ (ne_of_gt hsin)).symm
        have hu_eq : u = α • e₁ + β • e₂ :=
          O.injective (by rw [hOu, ← map_smul, ← map_smul, ← map_add])
        refine ⟨r * α * ‖d₁‖⁻¹, by positivity, r * β * ‖d₂‖⁻¹, by positivity, ?_⟩
        rw [hu_eq, smul_add]
        dsimp [e₁, e₂]
        simp only [smul_smul, mul_assoc]
  rw [hset, volume_smul_pos hr, volume_image_li O.symm (measurableSet_stdSector θ),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg r)]
  change r ^ 2 * secVol θ = κ * r ^ 2 * θ
  rw [secVol_eq hθ_pos hθ_lt]
  dsimp [κ]
  ring

open Classical in
noncomputable def coneAngle (S : Triangle ℝ ℝ²) (p : ℝ²) : ℝ :=
  if p ∉ S.closedInterior then 0
  else if p ∈ S.interior then 2 * π
  else if h : ∃ j : Fin 3, S.points j = p then vertAngle S (Classical.choose h)
  else π

lemma coneAngle_of_notMem {S : Triangle ℝ ℝ²} {p : ℝ²} (hp : p ∉ S.closedInterior) :
    coneAngle S p = 0 := by
  classical simp [coneAngle, hp]

lemma coneAngle_of_mem_interior {S : Triangle ℝ ℝ²} {p : ℝ²} (hp : p ∈ S.interior) :
    coneAngle S p = 2 * π := by
  have hp_cl : p ∈ S.closedInterior := by
    rw [mem_closedInterior_iff_coord]
    intro i; exact le_of_lt ((mem_interior_iff_coord S p).mp hp i)
  classical simp [coneAngle, hp_cl, hp]

lemma coneAngle_point (S : Triangle ℝ ℝ²) (j : Fin 3) :
    coneAngle S (S.points j) = vertAngle S j := by
  classical
  have hcl : S.points j ∈ S.closedInterior := S.point_mem_closedInterior j
  have hint : S.points j ∉ S.interior := by
    rw [mem_interior_iff_coord]
    intro hpos
    let j₁ : Fin 3 := j + 1
    have hj1 : j₁ ≠ j := by fin_cases j <;> decide
    have hc0 : (triBasis S).coord j₁ (S.points j) = 0 := by
      rw [← triBasis_apply S j]
      exact (triBasis S).coord_apply_ne hj1
    linarith [hpos j₁]
  have hex : ∃ r : Fin 3, S.points r = S.points j := ⟨j, rfl⟩
  simp only [coneAngle, hcl, not_true_eq_false, ↓reduceIte, hint, hex, ↓reduceDIte]
  have hch : Classical.choose hex = j := S.independent.injective (Classical.choose_spec hex)
  rw [hch]

lemma coneAngle_of_edge {S : Triangle ℝ ℝ²} {p : ℝ²}
    (hcl : p ∈ S.closedInterior) (hint : p ∉ S.interior) (hnv : ∀ j : Fin 3, S.points j ≠ p) :
    coneAngle S p = π := by
  classical
  have hex : ¬ ∃ j : Fin 3, S.points j = p := fun ⟨j, hj⟩ => hnv j hj
  simp [coneAngle, hcl, hint, hex]

lemma coneAngle_nonneg (S : Triangle ℝ ℝ²) (p : ℝ²) : 0 ≤ coneAngle S p := by
  by_cases hcl : p ∉ S.closedInterior
  · rw [coneAngle_of_notMem hcl]
  · push Not at hcl
    by_cases hint : p ∈ S.interior
    · rw [coneAngle_of_mem_interior hint]
      exact mul_nonneg zero_le_two (le_of_lt Real.pi_pos)
    · by_cases hex : ∃ j : Fin 3, S.points j = p
      · rcases hex with ⟨j, rfl⟩
        rw [coneAngle_point]
        exact le_of_lt (vertAngle_pos S j)
      · rw [coneAngle_of_edge hcl hint (fun j hj => hex ⟨j, hj⟩)]
        exact le_of_lt Real.pi_pos

lemma fin3_other_two (k : Fin 3) :
    ∃ k₁ k₂ : Fin 3, k₁ ≠ k ∧ k₂ ≠ k ∧ k₁ ≠ k₂ ∧
      ∀ m : Fin 3, m = k ∨ m = k₁ ∨ m = k₂ := by
  fin_cases k
  · exact ⟨1, 2, by decide, by decide, by decide, fun m => by fin_cases m <;> simp⟩
  · exact ⟨2, 0, by decide, by decide, by decide, fun m => by fin_cases m <;> simp⟩
  · exact ⟨0, 1, by decide, by decide, by decide, fun m => by fin_cases m <;> simp⟩

lemma fin3_sum_perm {M : Type*} [AddCommMonoid M] {j j₁ j₂ : Fin 3}
    (h1 : j₁ ≠ j) (h2 : j₂ ≠ j) (h12 : j₁ ≠ j₂) (f : Fin 3 → M) :
    ∑ k : Fin 3, f k = f j + f j₁ + f j₂ := by
  have huniv : (Finset.univ : Finset (Fin 3)) = insert j (insert j₁ {j₂}) := by
    ext m
    fin_cases j <;> fin_cases j₁ <;> fin_cases j₂ <;> fin_cases m <;> simp_all
  rw [huniv, Finset.sum_insert (by simp [h1.symm, h2.symm]),
    Finset.sum_insert (by simp [h12]), Finset.sum_singleton, add_assoc]

lemma local_ball_volume_coneAngle (S : Triangle ℝ ℝ²) (p : ℝ²) :
    ∃ r₀ > (0 : ℝ), ∀ r, 0 < r → r < r₀ →
      (volume (Metric.ball p r ∩ S.closedInterior)).toReal = κ * r ^ 2 * coneAngle S p := by
  by_cases hcl : p ∉ S.closedInterior
  · obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.mp (isClosed_closedInterior S).isOpen_compl p hcl
    refine ⟨r₀, hr₀, fun r _ hr_lt => ?_⟩
    have hemp : Metric.ball p r ∩ S.closedInterior = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hxB
      exact hball (Metric.ball_subset_ball (le_of_lt hr_lt) hxB)
    rw [hemp, coneAngle_of_notMem hcl, measure_empty, ENNReal.toReal_zero, mul_zero]
  · push Not at hcl
    by_cases hint : p ∈ S.interior
    · obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.mp (isOpen_interior S) p hint
      refine ⟨r₀, hr₀, fun r hr_pos hr_lt => ?_⟩
      have hsub : S.interior ⊆ S.closedInterior := fun x hx =>
        (mem_closedInterior_iff_coord S x).mpr fun i => le_of_lt ((mem_interior_iff_coord S x).mp hx i)
      have heq : Metric.ball p r ∩ S.closedInterior = (fun v : ℝ² => v + p) '' Metric.ball 0 r := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_image, Metric.mem_ball, dist_zero_right]
        constructor
        · rintro ⟨hx, _⟩
          refine ⟨x - p, ?_, sub_add_cancel x p⟩
          rwa [← dist_eq_norm]
        · rintro ⟨v, hv, rfl⟩
          have hxp : v + p ∈ Metric.ball p r := by
            rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right]; exact hv
          exact ⟨hxp, hsub (hball (Metric.ball_subset_ball (le_of_lt hr_lt) hxp))⟩
      rw [heq, volume_vadd_eq, volume_ball_r_toReal hr_pos, coneAngle_of_mem_interior hint]
    · by_cases hex : ∃ j : Fin 3, S.points j = p
      · rcases hex with ⟨j, rfl⟩
        obtain ⟨j₁, j₂, hj_ne1, hj_ne2, hj12, hj_all⟩ := fin3_other_two j
        have hopen_j : IsOpen {x : ℝ² | 0 < (triBasis S).coord j x} :=
          isOpen_Ioi.preimage (continuous_triCoord S j)
        have hmem_j : S.points j ∈ {x : ℝ² | 0 < (triBasis S).coord j x} := by
          change 0 < (triBasis S).coord j (triBasis S j)
          rw [(triBasis S).coord_apply_eq j]
          exact zero_lt_one
        obtain ⟨r₀, hr₀, hball_j⟩ := Metric.isOpen_iff.mp hopen_j (S.points j) hmem_j
        refine ⟨r₀, hr₀, fun r hr_pos hr_lt => ?_⟩
        let d₁ : ℝ² := S.points j₁ -ᵥ S.points j
        let d₂ : ℝ² := S.points j₂ -ᵥ S.points j
        have hset : Metric.ball (S.points j) r ∩ S.closedInterior =
            (fun v : ℝ² => v + S.points j) ''
              (Metric.ball (0 : ℝ²) r ∩ {v : ℝ² | ∃ a ≥ (0 : ℝ), ∃ b ≥ (0 : ℝ), v = a • d₁ + b • d₂}) := by
          ext x
          simp only [Set.mem_inter_iff, Set.mem_image, Metric.mem_ball, dist_zero_right]
          constructor
          · rintro ⟨hxB, hxS⟩
            rw [mem_closedInterior_iff_coord] at hxS
            let a : ℝ := (triBasis S).coord j₁ x
            let b : ℝ := (triBasis S).coord j₂ x
            refine ⟨x - S.points j, ⟨by rwa [← dist_eq_norm], ?_⟩, sub_add_cancel x _⟩
            refine ⟨a, hxS j₁, b, hxS j₂, ?_⟩
            have hx_comb := (triBasis S).affineCombination_coord_eq_self x
            have hsum_c := (triBasis S).sum_coord_apply_eq_one x
            rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum_c] at hx_comb
            rw [fin3_sum_perm hj_ne1 hj_ne2 hj12] at hx_comb hsum_c
            have hcj : (triBasis S).coord j x = 1 - a - b := by dsimp [a, b]; linarith
            have hx_eq : x = (1 - a - b) • S.points j + a • S.points j₁ + b • S.points j₂ := by
              rw [← hx_comb, hcj]; rfl
            rw [hx_eq]
            dsimp only [d₁, d₂]
            simp only [vsub_eq_sub]
            module
          · rintro ⟨v, ⟨hvB, hv_cone⟩, rfl⟩
            rcases hv_cone with ⟨a, ha, b, hb, rfl⟩
            have hxp : (a • d₁ + b • d₂) + S.points j ∈ Metric.ball (S.points j) r := by
              rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right]; exact hvB
            refine ⟨hxp, (mem_closedInterior_iff_coord S _).mpr fun k => ?_⟩
            have hcj_pos : 0 < (triBasis S).coord j ((a • d₁ + b • d₂) + S.points j) :=
              hball_j (Metric.ball_subset_ball (le_of_lt hr_lt) hxp)
            have hlin1 : (triBasis S).coord j₁ ((a • d₁ + b • d₂) + S.points j) = a := by
              change (triBasis S).coord j₁ ((a • d₁ + b • d₂) +ᵥ triBasis S j) = a
              rw [AffineMap.map_vadd, vadd_eq_add, (triBasis S).coord_apply_ne hj_ne1]
              dsimp only [d₁, d₂]
              rw [← triBasis_apply S j, ← triBasis_apply S j₁, ← triBasis_apply S j₂,
                map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
                AffineMap.linearMap_vsub, AffineMap.linearMap_vsub,
                vsub_eq_sub, vsub_eq_sub,
                (triBasis S).coord_apply_eq, (triBasis S).coord_apply_ne hj_ne1,
                (triBasis S).coord_apply_ne hj12]
              ring
            have hlin2 : (triBasis S).coord j₂ ((a • d₁ + b • d₂) + S.points j) = b := by
              change (triBasis S).coord j₂ ((a • d₁ + b • d₂) +ᵥ triBasis S j) = b
              rw [AffineMap.map_vadd, vadd_eq_add, (triBasis S).coord_apply_ne hj_ne2]
              dsimp only [d₁, d₂]
              rw [← triBasis_apply S j, ← triBasis_apply S j₁, ← triBasis_apply S j₂,
                map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
                AffineMap.linearMap_vsub, AffineMap.linearMap_vsub,
                vsub_eq_sub, vsub_eq_sub,
                (triBasis S).coord_apply_eq, (triBasis S).coord_apply_ne hj_ne2,
                (triBasis S).coord_apply_ne hj12.symm]
              ring
            rcases hj_all k with rfl | rfl | rfl
            · exact le_of_lt hcj_pos
            · linarith
            · linarith
        have hnc0 : ¬ Collinear ℝ ({(0 : ℝ²), d₁, d₂} : Set ℝ²) := by
          have hemb : Function.Injective ![j, j₁, j₂] := by
            intro a b hab
            fin_cases a <;> fin_cases b <;> simp_all [hj_ne1.symm, hj_ne2.symm]
          have hind_pts : AffineIndependent ℝ ![S.points j, S.points j₁, S.points j₂] := by
            have h0 : AffineIndependent ℝ (S.points ∘ ![j, j₁, j₂]) :=
              S.independent.comp_embedding ⟨![j, j₁, j₂], hemb⟩
            have hfn : S.points ∘ ![j, j₁, j₂] = ![S.points j, S.points j₁, S.points j₂] := by
              ext m; fin_cases m <;> rfl
            rwa [hfn] at h0
          have hind0 : AffineIndependent ℝ ![(0 : ℝ²), d₁, d₂] := by
            rw [affineIndependent_iff_linearIndependent_vsub ℝ _ 0]
            rw [affineIndependent_iff_linearIndependent_vsub ℝ _ 0] at hind_pts
            convert hind_pts using 1
            ext ⟨m, hm⟩
            fin_cases m
            · exact absurd rfl hm
            · simp [d₁]
            · simp [d₂]
          rwa [affineIndependent_iff_not_collinear_set] at hind0
        have hang_eq : InnerProductGeometry.angle d₁ d₂ = vertAngle S j := by
          change ∠ (S.points j₁) (S.points j) (S.points j₂) = vertAngle S j
          fin_cases j
          · have h1 : j₁ = 1 ∨ j₁ = 2 := by fin_cases j₁ <;> simp_all
            rcases h1 with rfl | rfl
            · have : j₂ = 2 := by fin_cases j₂ <;> simp_all
              subst this; rfl
            · have : j₂ = 1 := by fin_cases j₂ <;> simp_all
              subst this; exact EuclideanGeometry.angle_comm _ _ _
          · have h1 : j₁ = 2 ∨ j₁ = 0 := by fin_cases j₁ <;> simp_all
            rcases h1 with rfl | rfl
            · have : j₂ = 0 := by fin_cases j₂ <;> simp_all
              subst this; rfl
            · have : j₂ = 2 := by fin_cases j₂ <;> simp_all
              subst this; exact EuclideanGeometry.angle_comm _ _ _
          · have h1 : j₁ = 0 ∨ j₁ = 1 := by fin_cases j₁ <;> simp_all
            rcases h1 with rfl | rfl
            · have : j₂ = 1 := by fin_cases j₂ <;> simp_all
              subst this; rfl
            · have : j₂ = 0 := by fin_cases j₂ <;> simp_all
              subst this; exact EuclideanGeometry.angle_comm _ _ _
        rw [hset, volume_vadd_eq, volume_sector_r_toReal hnc0 hr_pos, hang_eq, coneAngle_point]
      · have hnv : ∀ j : Fin 3, S.points j ≠ p := fun j hj => hex ⟨j, hj⟩
        have hcl_c := (mem_closedInterior_iff_coord S p).mp hcl
        have hint_c := mt (mem_interior_iff_coord S p).mpr hint
        push Not at hint_c
        rcases hint_c with ⟨k, hk_le⟩
        have hk0 : (triBasis S).coord k p = 0 := le_antisymm hk_le (hcl_c k)
        obtain ⟨k₁, k₂, hk_ne1, hk_ne2, hk12, hk_all⟩ := fin3_other_two k
        have hsum_p : (triBasis S).coord k p + (triBasis S).coord k₁ p + (triBasis S).coord k₂ p = 1 := by
          rw [← fin3_sum_perm hk_ne1 hk_ne2 hk12 (fun m => (triBasis S).coord m p)]
          exact (triBasis S).sum_coord_apply_eq_one p
        have hk1_pos : 0 < (triBasis S).coord k₁ p := by
          refine lt_of_le_of_ne (hcl_c k₁) fun h0 => ?_
          have hk2_1 : (triBasis S).coord k₂ p = 1 := by linarith
          apply hnv k₂
          apply (triBasis S).ext_elem
          intro m
          rw [← triBasis_apply S k₂]
          rcases hk_all m with rfl | rfl | rfl
          · rw [(triBasis S).coord_apply_ne hk_ne2.symm, hk0]
          · rw [(triBasis S).coord_apply_ne hk12, ← h0]
          · rw [(triBasis S).coord_apply_eq, hk2_1]
        have hk2_pos : 0 < (triBasis S).coord k₂ p := by
          refine lt_of_le_of_ne (hcl_c k₂) fun h0 => ?_
          have hk1_1 : (triBasis S).coord k₁ p = 1 := by linarith
          apply hnv k₁
          apply (triBasis S).ext_elem
          intro m
          rw [← triBasis_apply S k₁]
          rcases hk_all m with rfl | rfl | rfl
          · rw [(triBasis S).coord_apply_ne hk_ne1.symm, hk0]
          · rw [(triBasis S).coord_apply_eq, hk1_1]
          · rw [(triBasis S).coord_apply_ne hk12.symm, ← h0]
        have hopen12 : IsOpen {x : ℝ² | 0 < (triBasis S).coord k₁ x ∧ 0 < (triBasis S).coord k₂ x} :=
          (isOpen_Ioi.preimage (continuous_triCoord S k₁)).inter
            (isOpen_Ioi.preimage (continuous_triCoord S k₂))
        obtain ⟨r₀, hr₀, hball12⟩ := Metric.isOpen_iff.mp hopen12 p ⟨hk1_pos, hk2_pos⟩
        refine ⟨r₀, hr₀, fun r hr_pos hr_lt => ?_⟩
        let L : ℝ² →ₗ[ℝ] ℝ := ((triBasis S).coord k).linear
        have hL_ne : L ≠ 0 := by
          obtain ⟨q₀, hq0⟩ := (triBasis S).surjective_coord k 0
          obtain ⟨q₁, hq1⟩ := (triBasis S).surjective_coord k 1
          intro h0
          have hv := ((triBasis S).coord k).linearMap_vsub q₁ q₀
          rw [show ((triBasis S).coord k).linear = L from rfl, h0, LinearMap.zero_apply, hq1, hq0] at hv
          norm_num at hv
        have hset : Metric.ball p r ∩ S.closedInterior =
            (fun v : ℝ² => v + p) '' (Metric.ball (0 : ℝ²) r ∩ {v : ℝ² | 0 ≤ L v}) := by
          ext x
          simp only [Set.mem_inter_iff, Set.mem_image, Metric.mem_ball, dist_zero_right]
          constructor
          · rintro ⟨hxB, hxS⟩
            rw [mem_closedInterior_iff_coord] at hxS
            refine ⟨x - p, ⟨by rwa [← dist_eq_norm], ?_⟩, sub_add_cancel x p⟩
            change 0 ≤ L (x -ᵥ p)
            have hv : L (x -ᵥ p) = (triBasis S).coord k x -ᵥ (triBasis S).coord k p :=
              ((triBasis S).coord k).linearMap_vsub x p
            rw [hv, hk0, vsub_eq_sub, sub_zero]
            exact hxS k
          · rintro ⟨v, ⟨hvB, hvL⟩, rfl⟩
            change 0 ≤ L v at hvL
            have hxp : v + p ∈ Metric.ball p r := by
              rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right]; exact hvB
            obtain ⟨hc1, hc2⟩ := hball12 (Metric.ball_subset_ball (le_of_lt hr_lt) hxp)
            refine ⟨hxp, (mem_closedInterior_iff_coord S _).mpr fun m => ?_⟩
            rcases hk_all m with hmk | hmk | hmk
            · rw [hmk]
              change 0 ≤ (triBasis S).coord k (v +ᵥ p)
              rw [AffineMap.map_vadd, vadd_eq_add, hk0, add_zero]
              exact hvL
            · rw [hmk]; exact le_of_lt hc1
            · rw [hmk]; exact le_of_lt hc2
        rw [hset, volume_vadd_eq, volume_halfBall_r_toReal hL_ne hr_pos, coneAngle_of_edge hcl hint hnv]

lemma coneAngle_sum_eq {n : ℕ} {T : Triangle ℝ ℝ²} {Ts : Fin n → Triangle ℝ ℝ²}
    (hdisj : Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior))
    (hunion : ⋃ i, (Ts i).closedInterior = T.closedInterior) (p : ℝ²) :
    ∑ i : Fin n, coneAngle (Ts i) p = coneAngle T p := by
  obtain ⟨rT, hrT_pos, hrT⟩ := local_ball_volume_coneAngle T p
  choose rS hrS_pos hrS using fun i : Fin n => local_ball_volume_coneAngle (Ts i) p
  have hex_r : ∃ r : ℝ, 0 < r ∧ r < rT ∧ ∀ i : Fin n, r < rS i := by
    let Sset : Finset ℝ := insert rT (Finset.univ.image rS)
    have hne : Sset.Nonempty := Finset.insert_nonempty _ _
    let m : ℝ := Sset.min' hne
    have hm_pos : 0 < m := by
      have hm_mem : m ∈ Sset := Sset.min'_mem hne
      simp only [Sset, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hm_mem
      rcases hm_mem with hm_eq | ⟨i, hm_eq⟩
      · rw [hm_eq]; exact hrT_pos
      · rw [← hm_eq]; exact hrS_pos i
    refine ⟨m / 2, half_pos hm_pos, ?_, fun i => ?_⟩
    · exact lt_of_lt_of_le (half_lt_self hm_pos) (Sset.min'_le rT (Finset.mem_insert_self _ _))
    · exact lt_of_lt_of_le (half_lt_self hm_pos)
        (Sset.min'_le (rS i) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i))))
  obtain ⟨r, hr_pos, hr_T, hr_S⟩ := hex_r
  let Bp : Set ℝ² := Metric.ball p r
  have hBp_fin : ∀ A : Set ℝ², volume (Bp ∩ A) ≠ ⊤ := fun A =>
    ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_left) measure_ball_lt_top)
  have hcl_eq_int : ∀ i : Fin n, volume (Bp ∩ (Ts i).closedInterior) = volume (Bp ∩ (Ts i).interior) := by
    intro i
    have hsub : (Ts i).interior ⊆ (Ts i).closedInterior := fun x hx =>
      (mem_closedInterior_iff_coord (Ts i) x).mpr fun k =>
        le_of_lt ((mem_interior_iff_coord (Ts i) x).mp hx k)
    refine le_antisymm ?_ (measure_mono (Set.inter_subset_inter_right Bp hsub))
    have hcov : Bp ∩ (Ts i).closedInterior ⊆
        (Bp ∩ (Ts i).interior) ∪ ((Ts i).closedInterior \ (Ts i).interior) := by
      rintro x ⟨hxB, hxC⟩
      by_cases hxI : x ∈ (Ts i).interior
      · exact Or.inl ⟨hxB, hxI⟩
      · exact Or.inr ⟨hxC, hxI⟩
    calc volume (Bp ∩ (Ts i).closedInterior)
        ≤ volume ((Bp ∩ (Ts i).interior) ∪ ((Ts i).closedInterior \ (Ts i).interior)) := measure_mono hcov
      _ ≤ volume (Bp ∩ (Ts i).interior) + volume ((Ts i).closedInterior \ (Ts i).interior) :=
          measure_union_le _ _
      _ = volume (Bp ∩ (Ts i).interior) := by rw [volume_closedInterior_diff_interior, add_zero]
  have hvol_T : volume (Bp ∩ T.closedInterior) = ∑ i : Fin n, volume (Bp ∩ (Ts i).interior) := by
    have hpw : Pairwise (fun i j : Fin n => Disjoint (Bp ∩ (Ts i).interior) (Bp ∩ (Ts j).interior)) :=
      fun i j hij => (hdisj hij).mono Set.inter_subset_right Set.inter_subset_right
    have hmI : ∀ i : Fin n, MeasurableSet (Bp ∩ (Ts i).interior) := fun i =>
      Metric.isOpen_ball.measurableSet.inter (isOpen_interior (Ts i)).measurableSet
    apply le_antisymm
    · have hcov : Bp ∩ T.closedInterior ⊆
          (⋃ i, (Bp ∩ (Ts i).interior)) ∪ (⋃ i, ((Ts i).closedInterior \ (Ts i).interior)) := by
        rintro x ⟨hxB, hxT⟩
        rw [← hunion, Set.mem_iUnion] at hxT
        rcases hxT with ⟨i, hxC⟩
        by_cases hxI : x ∈ (Ts i).interior
        · exact Or.inl (Set.mem_iUnion.mpr ⟨i, hxB, hxI⟩)
        · exact Or.inr (Set.mem_iUnion.mpr ⟨i, hxC, hxI⟩)
      calc volume (Bp ∩ T.closedInterior)
          ≤ volume ((⋃ i, (Bp ∩ (Ts i).interior)) ∪ (⋃ i, ((Ts i).closedInterior \ (Ts i).interior))) :=
            measure_mono hcov
        _ ≤ volume (⋃ i, (Bp ∩ (Ts i).interior)) +
            volume (⋃ i, ((Ts i).closedInterior \ (Ts i).interior)) := measure_union_le _ _
        _ = volume (⋃ i, (Bp ∩ (Ts i).interior)) := by
            rw [measure_iUnion_null (fun i => volume_closedInterior_diff_interior (Ts i)), add_zero]
        _ = ∑ i : Fin n, volume (Bp ∩ (Ts i).interior) := by
            rw [measure_iUnion hpw hmI, tsum_fintype]
    · calc ∑ i : Fin n, volume (Bp ∩ (Ts i).interior)
          = volume (⋃ i, (Bp ∩ (Ts i).interior)) := by rw [measure_iUnion hpw hmI, tsum_fintype]
        _ ≤ volume (Bp ∩ T.closedInterior) := by
            refine measure_mono ?_
            rintro x hx
            rcases Set.mem_iUnion.mp hx with ⟨i, hxB, hxI⟩
            refine ⟨hxB, ?_⟩
            rw [← hunion]
            refine Set.mem_iUnion.mpr ⟨i, ?_⟩
            exact (mem_closedInterior_iff_coord (Ts i) x).mpr fun k =>
              le_of_lt ((mem_interior_iff_coord (Ts i) x).mp hxI k)
  have htoReal : (volume (Bp ∩ T.closedInterior)).toReal =
      ∑ i : Fin n, (volume (Bp ∩ (Ts i).closedInterior)).toReal := by
    rw [hvol_T, ENNReal.toReal_sum (fun i _ => hBp_fin _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcl_eq_int i]
  rw [hrT r hr_pos hr_T] at htoReal
  have hsum_rhs : ∑ i : Fin n, (volume (Bp ∩ (Ts i).closedInterior)).toReal =
      κ * r ^ 2 * ∑ i : Fin n, coneAngle (Ts i) p := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact hrS i r hr_pos (hr_S i)
  rw [hsum_rhs] at htoReal
  have hκ : 0 < κ := κ_pos
  have hκr : κ * r ^ 2 ≠ 0 := by positivity
  exact mul_left_cancel₀ hκr htoReal.symm

end Erdos633Proof

namespace Erdos633Proof

open Affine
open scoped Congruent EuclideanGeometry Similar Real NNReal

lemma fin3_eq_three {a b c : Fin 3} (hab : b ≠ a) (hac : c ≠ a) (hbc : b ≠ c) (x : Fin 3) :
    x = a ∨ x = b ∨ x = c := by
  rcases a with ⟨a, ha⟩; rcases b with ⟨b, hb⟩; rcases c with ⟨c, hc⟩; rcases x with ⟨x, hx⟩
  simp only [Fin.mk.injEq, ne_eq] at hab hac hbc ⊢
  omega

lemma fin3_third {a b : Fin 3} (hab : a ≠ b) :
    ∃ c : Fin 3, c ≠ a ∧ c ≠ b ∧ ∀ m : Fin 3, m = a ∨ m = b ∨ m = c := by
  fin_cases a <;> fin_cases b
  · exact absurd rfl hab
  · exact ⟨2, by decide, by decide, fin3_eq_three (by decide) (by decide) (by decide)⟩
  · exact ⟨1, by decide, by decide, fin3_eq_three (by decide) (by decide) (by decide)⟩
  · exact ⟨2, by decide, by decide, fin3_eq_three (by decide) (by decide) (by decide)⟩
  · exact absurd rfl hab
  · exact ⟨0, by decide, by decide, fin3_eq_three (by decide) (by decide) (by decide)⟩
  · exact ⟨1, by decide, by decide, fin3_eq_three (by decide) (by decide) (by decide)⟩
  · exact ⟨0, by decide, by decide, fin3_eq_three (by decide) (by decide) (by decide)⟩
  · exact absurd rfl hab

lemma sum_ite_const {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P] (c : ℝ) :
    (∑ i : ι, if P i then c else 0) = ((Finset.univ.filter P).card : ℝ) * c := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

lemma comb3_mem_interior (S : Triangle ℝ ℝ²) {r₀ r₁ r₂ : Fin 3}
    (h01 : r₁ ≠ r₀) (h02 : r₂ ≠ r₀) (h12 : r₁ ≠ r₂)
    {w₀ w₁ w₂ : ℝ} (hw0 : 0 < w₀) (hw1 : 0 < w₁) (hw2 : 0 < w₂)
    (hsum : w₀ + w₁ + w₂ = 1) :
    w₀ • S.points r₀ + w₁ • S.points r₁ + w₂ • S.points r₂ ∈ S.interior := by
  let f : Fin 3 → ℝ := fun r => if r = r₀ then w₀ else if r = r₁ then w₁ else w₂
  have hf0 : f r₀ = w₀ := by simp [f]
  have hf1 : f r₁ = w₁ := by simp [f, h01]
  have hf2 : f r₂ = w₂ := by simp [f, h02, h12.symm]
  have hf_sum : ∑ r : Fin 3, f r = 1 := by
    rw [fin3_sum_perm h01 h02 h12, hf0, hf1, hf2, hsum]
  have hf_comb : Finset.univ.affineCombination ℝ (triBasis S) f =
      w₀ • S.points r₀ + w₁ • S.points r₁ + w₂ • S.points r₂ := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hf_sum,
      fin3_sum_perm h01 h02 h12, hf0, hf1, hf2]
    rfl
  rw [← hf_comb, mem_interior_iff_coord]
  intro m
  rw [(triBasis S).coord_apply_combination_of_mem (Finset.mem_univ m) hf_sum]
  rcases fin3_eq_three h01 h02 h12 m with rfl | rfl | rfl
  · rw [hf0]; exact hw0
  · rw [hf1]; exact hw1
  · rw [hf2]; exact hw2

lemma shared_edge_interior_overlap (T S₁ S₂ : Triangle ℝ ℝ²) (k : Fin 3)
    {u₁ u₂ q₁ q₂ : ℝ²} {r₀ r₁ r₂ s₀ s₁ s₂ : Fin 3}
    (hr01 : r₁ ≠ r₀) (hr02 : r₂ ≠ r₀) (hr12 : r₁ ≠ r₂)
    (hs01 : s₁ ≠ s₀) (hs02 : s₂ ≠ s₀) (hs12 : s₁ ≠ s₂)
    (hp10 : S₁.points r₀ = u₁) (hp11 : S₁.points r₁ = q₁) (hp12 : S₁.points r₂ = q₂)
    (hp20 : S₂.points s₀ = u₂) (hp21 : S₂.points s₁ = q₁) (hp22 : S₂.points s₂ = q₂)
    (hq1 : (triBasis T).coord k q₁ = 0) (hq2 : (triBasis T).coord k q₂ = 0)
    (hu1 : 0 < (triBasis T).coord k u₁) (hu2 : 0 < (triBasis T).coord k u₂) :
    ¬ Disjoint S₁.interior S₂.interior := by
  let α₀ : ℝ := (triBasis S₁).coord r₀ u₂
  let α₁ : ℝ := (triBasis S₁).coord r₁ u₂
  let α₂ : ℝ := (triBasis S₁).coord r₂ u₂
  have hα_sum : α₀ + α₁ + α₂ = 1 := by
    rw [← fin3_sum_perm hr01 hr02 hr12 (fun r => (triBasis S₁).coord r u₂)]
    exact (triBasis S₁).sum_coord_apply_eq_one u₂
  have hu2_comb : α₀ • u₁ + α₁ • q₁ + α₂ • q₂ = u₂ := by
    have hc := (triBasis S₁).affineCombination_coord_eq_self u₂
    rw [Finset.affineCombination_eq_linear_combination _ _ _
      ((triBasis S₁).sum_coord_apply_eq_one u₂),
      fin3_sum_perm hr01 hr02 hr12] at hc
    simpa [α₀, α₁, α₂, hp10, hp11, hp12] using hc
  have hvsub : u₂ -ᵥ q₁ = α₀ • (u₁ -ᵥ q₁) + α₂ • (q₂ -ᵥ q₁) := by
    have hq1_one : q₁ = (α₀ + α₁ + α₂) • q₁ := by rw [hα_sum, one_smul]
    calc u₂ -ᵥ q₁ = u₂ - (α₀ + α₁ + α₂) • q₁ := by rw [← hq1_one]; rfl
      _ = (α₀ • u₁ + α₁ • q₁ + α₂ • q₂) - (α₀ + α₁ + α₂) • q₁ := by rw [← hu2_comb]
      _ = α₀ • (u₁ -ᵥ q₁) + α₂ • (q₂ -ᵥ q₁) := by
          simp only [vsub_eq_sub]; module
  let φ : ℝ² →ᵃ[ℝ] ℝ := (triBasis T).coord k
  have hφ_rel : φ u₂ = α₀ * φ u₁ := by
    have hv := φ.linearMap_vsub u₂ q₁
    rw [hvsub, map_add, map_smul, map_smul, φ.linearMap_vsub, φ.linearMap_vsub] at hv
    simp only [φ, vsub_eq_sub, smul_eq_mul, hq1, hq2, sub_zero] at hv
    linarith
  have hα0_pos : 0 < α₀ := by
    dsimp only [φ] at hφ_rel
    nlinarith
  let M : ℝ := |α₁| + |α₂| + 1
  have hM_pos : 0 < M := by dsimp [M]; positivity
  have hM_ge1 : 1 ≤ M := by dsimp [M]; linarith [abs_nonneg α₁, abs_nonneg α₂]
  let δ : ℝ := 1 / (8 * M)
  have hδ_pos : 0 < δ := div_pos one_pos (by positivity)
  have hδ_le : δ ≤ 1 / 8 := by
    dsimp [δ]
    exact div_le_div_of_nonneg_left zero_le_one (by norm_num) (by linarith)
  have hδ_mul_M : 2 * δ * M = 1 / 4 := by
    dsimp [δ]; field_simp [ne_of_gt hM_pos]; ring
  have hw1_1 : 0 < 1 / 2 - δ + 2 * δ * α₁ := by
    have habs : -|α₁| ≤ α₁ := neg_abs_le α₁
    have hleM : |α₁| ≤ M := by dsimp [M]; linarith [abs_nonneg α₂]
    nlinarith
  have hw1_2 : 0 < 1 / 2 - δ + 2 * δ * α₂ := by
    have habs : -|α₂| ≤ α₂ := neg_abs_le α₂
    have hleM : |α₂| ≤ M := by dsimp [M]; linarith [abs_nonneg α₁]
    nlinarith
  let z : ℝ² := (2 * δ) • u₂ + (1 / 2 - δ) • q₁ + (1 / 2 - δ) • q₂
  have hz2 : z ∈ S₂.interior := by
    have hz_eq : z = (2 * δ) • S₂.points s₀ + (1 / 2 - δ) • S₂.points s₁ +
        (1 / 2 - δ) • S₂.points s₂ := by simp [z, hp20, hp21, hp22]
    rw [hz_eq]
    exact comb3_mem_interior S₂ hs01 hs02 hs12 (by linarith) (by linarith) (by linarith) (by ring)
  have hz1 : z ∈ S₁.interior := by
    have hz_eq : z = (2 * δ * α₀) • S₁.points r₀ + (1 / 2 - δ + 2 * δ * α₁) • S₁.points r₁ +
        (1 / 2 - δ + 2 * δ * α₂) • S₁.points r₂ := by
      simp only [z, hp10, hp11, hp12, ← hu2_comb]
      module
    rw [hz_eq]
    refine comb3_mem_interior S₁ hr01 hr02 hr12 (mul_pos (by linarith) hα0_pos) hw1_1 hw1_2 ?_
    linear_combination 2 * δ * hα_sum
  exact Set.not_disjoint_iff.mpr ⟨z, hz1, hz2⟩

lemma theta_linearIndependent {γ θ : Fin 3 → ℝ} {c : Fin 3 → Fin 3 → ℕ}
    (hγ : LinearIndependent ℚ γ)
    (heq : ∀ m : Fin 3, γ m = ∑ r : Fin 3, (c m r : ℝ) * θ r) :
    LinearIndependent ℚ θ := by
  let f : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 3 → ℚ) :=
    { toFun := fun u r => ∑ m : Fin 3, u m * (c m r : ℚ)
      map_add' := fun u v => by
        ext r; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun a u => by
        ext r; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, Finset.mul_sum] }
  have hf_rel : ∀ u : Fin 3 → ℚ, ∑ m : Fin 3, u m • γ m = ∑ r : Fin 3, (f u r) • θ r := by
    intro u
    simp only [Rat.smul_def, heq, f, LinearMap.coe_mk, AddHom.coe_mk]
    calc ∑ m : Fin 3, (u m : ℝ) * ∑ r : Fin 3, (c m r : ℝ) * θ r
        = ∑ m : Fin 3, ∑ r : Fin 3, (u m : ℝ) * (c m r : ℝ) * θ r := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun r _ => by ring
      _ = ∑ r : Fin 3, ∑ m : Fin 3, (u m : ℝ) * (c m r : ℝ) * θ r := Finset.sum_comm
      _ = ∑ r : Fin 3, ((∑ m : Fin 3, u m * (c m r : ℚ) : ℚ) : ℝ) * θ r := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [← Finset.sum_mul]
          push_cast; rfl
  have hf_inj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro u hu
    rw [LinearMap.mem_ker] at hu
    have h0 : ∑ m : Fin 3, u m • γ m = 0 := by
      rw [hf_rel, hu]
      simp
    exact funext (Fintype.linearIndependent_iff.mp hγ u h0)
  have hf_surj : Function.Surjective f := LinearMap.injective_iff_surjective.mp hf_inj
  rw [Fintype.linearIndependent_iff]
  intro q hq
  obtain ⟨u, rfl⟩ := hf_surj q
  have h0 : ∑ m : Fin 3, u m • γ m = 0 := by rw [hf_rel]; exact hq
  have hu_eq : u = 0 := funext (Fintype.linearIndependent_iff.mp hγ u h0)
  rw [hu_eq, map_zero]
  intro r; rfl

def openEdge (T : Triangle ℝ ℝ²) (k : Fin 3) : Set ℝ² :=
  {x : ℝ² | (triBasis T).coord k x = 0 ∧ ∀ l : Fin 3, l ≠ k → 0 < (triBasis T).coord l x}

lemma openEdge_disjoint (T : Triangle ℝ ℝ²) {k₁ k₂ : Fin 3} (hne : k₁ ≠ k₂) :
    Disjoint (openEdge T k₁) (openEdge T k₂) := by
  rw [Set.disjoint_left]
  rintro x ⟨h0, _⟩ ⟨_, hpos⟩
  linarith [hpos k₁ hne]

lemma point_notMem_openEdge (T : Triangle ℝ ℝ²) (m k : Fin 3) :
    T.points m ∉ openEdge T k := by
  rintro ⟨hk0, hpos⟩
  obtain ⟨k₁, k₂, hk1, hk2, hk12, hall⟩ := fin3_other_two k
  rcases hall m with rfl | rfl | rfl
  · have : (triBasis T).coord m (T.points m) = 1 := (triBasis T).coord_apply_eq m
    linarith
  · have h0 : (triBasis T).coord k₂ (T.points m) = 0 := by
      rw [← triBasis_apply T m]
      exact (triBasis T).coord_apply_ne hk12.symm
    linarith [hpos k₂ hk2]
  · have h0 : (triBasis T).coord k₁ (T.points m) = 0 := by
      rw [← triBasis_apply T m]
      exact (triBasis T).coord_apply_ne hk12
    linarith [hpos k₁ hk1]

lemma affineMap_apply_linear_combination (S : Triangle ℝ ℝ²) (φ : ℝ² →ᵃ[ℝ] ℝ)
    {u : Fin 3 → ℝ} (hu : ∑ r : Fin 3, u r = 1) :
    φ (∑ r : Fin 3, u r • S.points r) = ∑ r : Fin 3, u r * φ (S.points r) := by
  have h1 := Finset.univ.map_affineCombination S.points u hu φ
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hu,
    Finset.affineCombination_eq_linear_combination _ _ _ hu] at h1
  simpa [smul_eq_mul] using h1

open Classical in
noncomputable def vertMult {n : ℕ} (Ts : Fin n → Triangle ℝ ℝ²) (p : ℝ²) (r : Fin 3) : ℕ :=
  (Finset.univ.filter fun i : Fin n => (Ts i).points r = p).card

open Classical in
noncomputable def incAt {n : ℕ} (Ts : Fin n → Triangle ℝ ℝ²) (i : Fin n) (p : ℝ²) : ℕ :=
  (Finset.univ.filter fun r : Fin 3 => (Ts i).points r = p).card

lemma incAt_le_one {n : ℕ} (Ts : Fin n → Triangle ℝ ℝ²) (i : Fin n) (p : ℝ²) :
    incAt Ts i p ≤ 1 := by
  classical
  refine Finset.card_le_one.mpr fun r₁ hr₁ r₂ hr₂ => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr₁ hr₂
  exact (Ts i).independent.injective (hr₁.trans hr₂.symm)

lemma sum_vertMult_eq_sum_incAt {n : ℕ} (Ts : Fin n → Triangle ℝ ℝ²) (p : ℝ²) :
    ∑ r : Fin 3, vertMult Ts p r = ∑ i : Fin n, incAt Ts i p := by
  classical
  simp only [vertMult, incAt, Finset.card_filter]
  exact Finset.sum_comm

lemma sum_vertMult_le_n {n : ℕ} (Ts : Fin n → Triangle ℝ ℝ²) (p : ℝ²) :
    ∑ r : Fin 3, vertMult Ts p r ≤ n := by
  rw [sum_vertMult_eq_sum_incAt]
  calc ∑ i : Fin n, incAt Ts i p ≤ ∑ _i : Fin n, 1 :=
        Finset.sum_le_sum fun i _ => incAt_le_one Ts i p
    _ = n := by simp

/-- Step 3A: Vertex multiplicities at original vertices and extra vertices when `2 ≤ n < 6`. -/
lemma simili_multiplicity_structure {n : ℕ} (hn_ge2 : 2 ≤ n) (hn_lt6 : n < 6)
    {T : Triangle ℝ ℝ²} (hT_indep : LinearIndependent ℚ (vertAngle T))
    {Ts : Fin n → Triangle ℝ ℝ²}
    (hsim : ∀ i j : Fin n, (Ts i).points ∼ (Ts j).points)
    (hdisj : Pairwise fun i j => Disjoint (Ts i).interior (Ts j).interior)
    (hunion : ⋃ i, (Ts i).closedInterior = T.closedInterior) :
    (∀ m : Fin 3, ∑ r : Fin 3, vertMult Ts (T.points m) r = 1) ∧
    (∀ r : Fin 3, ∑ m : Fin 3, vertMult Ts (T.points m) r = 1) ∧
    (∀ m : Fin 3, ∃ i_m : Fin n, ∃ r_m : Fin 3,
      (Ts i_m).points r_m = T.points m ∧
      ∀ j : Fin n, j ≠ i_m → T.points m ∉ (Ts j).closedInterior) ∧
    (∀ w : ℝ², (∃ i r, (Ts i).points r = w) → (∀ m : Fin 3, T.points m ≠ w) →
      ∀ r : Fin 3, vertMult Ts w r = 1) := by
  classical
  let i₀₀ : Fin n := ⟨0, by omega⟩
  let θ : Fin 3 → ℝ := vertAngle (Ts i₀₀)
  have hθ_eq : ∀ (i : Fin n) (r : Fin 3), vertAngle (Ts i) r = θ r :=
    fun i r => vertAngle_eq_of_similar (hsim i i₀₀) r
  have hθ_pos : ∀ r : Fin 3, 0 < θ r := vertAngle_pos (Ts i₀₀)
  have hθ_lt_pi : ∀ r : Fin 3, θ r < π := vertAngle_lt_pi (Ts i₀₀)
  have hθ_sum : ∑ r : Fin 3, θ r = π := sum_vertAngle (Ts i₀₀)
  have hcl_sub : ∀ i : Fin n, (Ts i).closedInterior ⊆ T.closedInterior := by
    intro i x hx; rw [← hunion]; exact Set.mem_iUnion.mpr ⟨i, hx⟩
  have horig_cone : ∀ (m : Fin 3) (i : Fin n),
      (T.points m ∈ (Ts i).closedInterior → ∃ r : Fin 3, (Ts i).points r = T.points m) ∧
      coneAngle (Ts i) (T.points m) =
        ∑ r : Fin 3, if (Ts i).points r = T.points m then θ r else 0 := by
    intro m i
    have hsum := coneAngle_sum_eq hdisj hunion (T.points m)
    have hle : coneAngle (Ts i) (T.points m) ≤ vertAngle T m := by
      rw [← coneAngle_point T m, ← hsum]
      exact Finset.single_le_sum (fun j _ => coneAngle_nonneg (Ts j) _) (Finset.mem_univ i)
    have hlt_pi : coneAngle (Ts i) (T.points m) < π := lt_of_le_of_lt hle (vertAngle_lt_pi T m)
    by_cases hcl : T.points m ∉ (Ts i).closedInterior
    · refine ⟨fun h => absurd h hcl, ?_⟩
      rw [coneAngle_of_notMem hcl]
      symm
      refine Finset.sum_eq_zero fun r _ => if_neg fun (hr : (Ts i).points r = T.points m) =>
        hcl (hr ▸ (Ts i).point_mem_closedInterior r)
    · push Not at hcl
      have hnint : T.points m ∉ (Ts i).interior := by
        intro hint; rw [coneAngle_of_mem_interior hint] at hlt_pi; linarith [Real.pi_pos]
      have hex : ∃ r : Fin 3, (Ts i).points r = T.points m := by
        by_contra hno
        rw [coneAngle_of_edge hcl hnint (fun r hr => hno ⟨r, hr⟩)] at hlt_pi
        linarith
      refine ⟨fun _ => hex, ?_⟩
      rcases hex with ⟨r₀, hr₀⟩
      have hcone : coneAngle (Ts i) (T.points m) = θ r₀ := by
        rw [← hr₀, coneAngle_point, hθ_eq]
      rw [hcone]
      symm
      rw [Finset.sum_eq_single r₀]
      · simp [hr₀]
      · intro r _ hr_ne
        exact if_neg fun hr => hr_ne ((Ts i).independent.injective (hr.trans hr₀.symm))
      · intro hmem; exact absurd (Finset.mem_univ r₀) hmem
  have horig_eq : ∀ m : Fin 3, vertAngle T m =
      ∑ r : Fin 3, (vertMult Ts (T.points m) r : ℝ) * θ r := by
    intro m
    rw [← coneAngle_point T m, ← coneAngle_sum_eq hdisj hunion (T.points m)]
    calc ∑ i : Fin n, coneAngle (Ts i) (T.points m)
        = ∑ i : Fin n, ∑ r : Fin 3, if (Ts i).points r = T.points m then θ r else 0 :=
          Finset.sum_congr rfl fun i _ => (horig_cone m i).2
      _ = ∑ r : Fin 3, ∑ i : Fin n, if (Ts i).points r = T.points m then θ r else 0 :=
          Finset.sum_comm
      _ = ∑ r : Fin 3, (vertMult Ts (T.points m) r : ℝ) * θ r := by
          refine Finset.sum_congr rfl fun r _ => ?_
          exact sum_ite_const (fun i : Fin n => (Ts i).points r = T.points m) (θ r)
  have hθ_indep : LinearIndependent ℚ θ :=
    theta_linearIndependent hT_indep horig_eq
  have hcol_sum : ∀ r : Fin 3, ∑ m : Fin 3, vertMult Ts (T.points m) r = 1 := by
    have htot : ∑ r : Fin 3, ((∑ m : Fin 3, (vertMult Ts (T.points m) r : ℚ)) - 1) • θ r = 0 := by
      have h1 : ∑ m : Fin 3, vertAngle T m = ∑ r : Fin 3, θ r := by
        rw [sum_vertAngle T, hθ_sum]
      have h2 : ∑ m : Fin 3, vertAngle T m =
          ∑ r : Fin 3, (∑ m : Fin 3, (vertMult Ts (T.points m) r : ℝ)) * θ r := by
        calc ∑ m : Fin 3, vertAngle T m
            = ∑ m : Fin 3, ∑ r : Fin 3, (vertMult Ts (T.points m) r : ℝ) * θ r :=
              Finset.sum_congr rfl fun m _ => horig_eq m
          _ = ∑ r : Fin 3, ∑ m : Fin 3, (vertMult Ts (T.points m) r : ℝ) * θ r := Finset.sum_comm
          _ = ∑ r : Fin 3, (∑ m : Fin 3, (vertMult Ts (T.points m) r : ℝ)) * θ r := by
              refine Finset.sum_congr rfl fun r _ => (Finset.sum_mul _ _ _).symm
      simp only [Rat.smul_def]
      push_cast
      simp only [sub_mul, one_mul, Finset.sum_sub_distrib]
      linarith
    intro r
    have hq0 := Fintype.linearIndependent_iff.mp hθ_indep _ htot r
    have hq1 : ∑ m : Fin 3, (vertMult Ts (T.points m) r : ℚ) = 1 := sub_eq_zero.mp hq0
    exact_mod_cast hq1
  have hrow_pos : ∀ m : Fin 3, 1 ≤ ∑ r : Fin 3, vertMult Ts (T.points m) r := by
    intro m
    by_contra h0
    have hzero : ∀ r : Fin 3, vertMult Ts (T.points m) r = 0 := by
      rw [Fin.sum_univ_three] at h0
      intro r; fin_cases r <;> dsimp <;> omega
    have hγ0 : vertAngle T m = 0 := by
      rw [horig_eq m]
      exact Finset.sum_eq_zero fun r _ => by simp [hzero r]
    linarith [vertAngle_pos T m]
  have hrow_sum : ∀ m : Fin 3, ∑ r : Fin 3, vertMult Ts (T.points m) r = 1 := by
    have htot3 : ∑ m : Fin 3, ∑ r : Fin 3, vertMult Ts (T.points m) r = 3 := by
      rw [Finset.sum_comm]
      simp [hcol_sum]
    have h0 := hrow_pos 0; have h1 := hrow_pos 1; have h2 := hrow_pos 2
    rw [Fin.sum_univ_three] at htot3
    intro m; fin_cases m <;> dsimp <;> omega
  have hex_corner : ∀ m : Fin 3, ∃ i_m : Fin n, ∃ r_m : Fin 3,
      (Ts i_m).points r_m = T.points m ∧
      ∀ j : Fin n, j ≠ i_m → T.points m ∉ (Ts j).closedInterior := by
    intro m
    have hinc1 : ∑ i : Fin n, incAt Ts i (T.points m) = 1 := by
      rw [← sum_vertMult_eq_sum_incAt, hrow_sum m]
    have hne : ∃ i_m : Fin n, incAt Ts i_m (T.points m) ≠ 0 := by
      by_contra hall0
      push Not at hall0
      have : ∑ i : Fin n, incAt Ts i (T.points m) = 0 :=
        Finset.sum_eq_zero fun i _ => hall0 i
      omega
    rcases hne with ⟨i_m, hi_ne⟩
    obtain ⟨r_m, hr_m⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hi_ne)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr_m
    refine ⟨i_m, r_m, hr_m, fun j hj hcl => ?_⟩
    obtain ⟨r_j, hr_j⟩ := (horig_cone m j).1 hcl
    have hj_pos : 1 ≤ incAt Ts j (T.points m) :=
      Finset.card_pos.mpr ⟨r_j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr_j⟩⟩
    have hi_pos : 1 ≤ incAt Ts i_m (T.points m) := Nat.one_le_iff_ne_zero.mpr hi_ne
    have hpair : incAt Ts j (T.points m) + incAt Ts i_m (T.points m) ≤
        ∑ i : Fin n, incAt Ts i (T.points m) := by
      rw [← Finset.sum_pair (f := fun i => incAt Ts i (T.points m)) hj]
      exact Finset.sum_le_sum_of_subset_of_nonneg (fun _ _ => Finset.mem_univ _)
        (fun _ _ _ => Nat.zero_le _)
    omega
  refine ⟨hrow_sum, hcol_sum, hex_corner, ?_⟩
  rintro w ⟨i_w, r_w, hr_w⟩ hnw
  have hw_clT : w ∈ T.closedInterior := hcl_sub i_w (hr_w ▸ (Ts i_w).point_mem_closedInterior r_w)
  have hconeT : ∃ kT : ℕ, (kT = 1 ∨ kT = 2) ∧ coneAngle T w = (kT : ℝ) * π := by
    by_cases hintT : w ∈ T.interior
    · exact ⟨2, Or.inr rfl, by rw [coneAngle_of_mem_interior hintT]; push_cast; ring⟩
    · exact ⟨1, Or.inl rfl, by rw [coneAngle_of_edge hw_clT hintT hnw]; simp⟩
  rcases hconeT with ⟨kT, hkT_cases, hconeT_eq⟩
  have hno_int : ∀ i : Fin n, w ∉ (Ts i).interior := by
    intro i hint_i
    by_cases hii : i = i_w
    · subst hii
      have h1 : coneAngle (Ts i) w = 2 * π := coneAngle_of_mem_interior hint_i
      have h2 : coneAngle (Ts i) w = θ r_w := by rw [← hr_w, coneAngle_point, hθ_eq]
      linarith [hθ_lt_pi r_w, Real.pi_pos]
    · have hpair_le : coneAngle (Ts i) w + coneAngle (Ts i_w) w ≤ coneAngle T w := by
        rw [← coneAngle_sum_eq hdisj hunion w, ← Finset.sum_pair (f := fun j => coneAngle (Ts j) w) hii]
        exact Finset.sum_le_sum_of_subset_of_nonneg (fun _ _ => Finset.mem_univ _)
          (fun j _ _ => coneAngle_nonneg (Ts j) w)
      have hc_iw : coneAngle (Ts i_w) w = θ r_w := by rw [← hr_w, coneAngle_point, hθ_eq]
      rw [coneAngle_of_mem_interior hint_i, hc_iw, hconeT_eq] at hpair_le
      have hkT_le2 : (kT : ℝ) ≤ 2 := by rcases hkT_cases with rfl | rfl <;> norm_num
      nlinarith [hθ_pos r_w, Real.pi_pos]
  let edgeSet : Finset (Fin n) :=
    Finset.univ.filter fun i : Fin n => w ∈ (Ts i).closedInterior ∧ ∀ r : Fin 3, (Ts i).points r ≠ w
  have hcone_each : ∀ i : Fin n, coneAngle (Ts i) w =
      (if i ∈ edgeSet then π else 0) +
        ∑ r : Fin 3, if (Ts i).points r = w then θ r else 0 := by
    intro i
    by_cases hex_r : ∃ r : Fin 3, (Ts i).points r = w
    · rcases hex_r with ⟨r₀, hr₀⟩
      have hnotE : i ∉ edgeSet := by
        simp only [edgeSet, Finset.mem_filter, Finset.mem_univ, true_and, not_and]
        intro _; push Not; exact ⟨r₀, hr₀⟩
      have hc_i : coneAngle (Ts i) w = θ r₀ := by rw [← hr₀, coneAngle_point, hθ_eq]
      rw [if_neg hnotE, zero_add, hc_i]
      symm
      rw [Finset.sum_eq_single r₀]
      · simp [hr₀]
      · intro r _ hr_ne
        exact if_neg fun h_eq => hr_ne ((Ts i).independent.injective (h_eq.trans hr₀.symm))
      · intro hmem; exact absurd (Finset.mem_univ r₀) hmem
    · have hnv_i : ∀ r : Fin 3, (Ts i).points r ≠ w := fun r hr => hex_r ⟨r, hr⟩
      have hsum0 : (∑ r : Fin 3, if (Ts i).points r = w then θ r else 0) = 0 :=
        Finset.sum_eq_zero fun r _ => if_neg (hnv_i r)
      rw [hsum0, add_zero]
      by_cases hcl_i : w ∈ (Ts i).closedInterior
      · have hmemE : i ∈ edgeSet := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcl_i, hnv_i⟩
        rw [if_pos hmemE, coneAngle_of_edge hcl_i (hno_int i) hnv_i]
      · have hnotE : i ∉ edgeSet := by simp [edgeSet, hcl_i]
        rw [if_neg hnotE, coneAngle_of_notMem hcl_i]
  have hsum_w : (edgeSet.card : ℝ) * π + ∑ r : Fin 3, (vertMult Ts w r : ℝ) * θ r = (kT : ℝ) * π := by
    rw [← hconeT_eq, ← coneAngle_sum_eq hdisj hunion w]
    calc (edgeSet.card : ℝ) * π + ∑ r : Fin 3, (vertMult Ts w r : ℝ) * θ r
        = (∑ i : Fin n, if i ∈ edgeSet then π else 0) +
            ∑ r : Fin 3, ∑ i : Fin n, if (Ts i).points r = w then θ r else 0 := by
          congr 1
          · rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
            simp [edgeSet]
          · refine Finset.sum_congr rfl fun r _ => ?_
            exact (sum_ite_const (fun i : Fin n => (Ts i).points r = w) (θ r)).symm
      _ = (∑ i : Fin n, if i ∈ edgeSet then π else 0) +
            ∑ i : Fin n, ∑ r : Fin 3, if (Ts i).points r = w then θ r else 0 := by
          rw [Finset.sum_comm]
      _ = ∑ i : Fin n, coneAngle (Ts i) w := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => (hcone_each i).symm
  have hpos_sum : 0 < ∑ r : Fin 3, (vertMult Ts w r : ℝ) * θ r := by
    have h1 : (1 : ℝ) ≤ vertMult Ts w r_w := by
      exact_mod_cast Finset.card_pos.mpr ⟨i_w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr_w⟩⟩
    have hsingle : (vertMult Ts w r_w : ℝ) * θ r_w ≤ ∑ r : Fin 3, (vertMult Ts w r : ℝ) * θ r :=
      Finset.single_le_sum (fun r _ => mul_nonneg (Nat.cast_nonneg _) (le_of_lt (hθ_pos r)))
        (Finset.mem_univ r_w)
    nlinarith [hθ_pos r_w]
  have he_lt : edgeSet.card < kT := by
    have hltR : (edgeSet.card : ℝ) < (kT : ℝ) := by
      have hpi : 0 < π := Real.pi_pos
      nlinarith
    exact_mod_cast hltR
  let mw : ℕ := kT - edgeSet.card
  have hmw_cases : mw = 1 ∨ mw = 2 := by
    rcases hkT_cases with rfl | rfl <;> omega
  have hmw_eq : ∑ r : Fin 3, ((vertMult Ts w r : ℚ) - (mw : ℚ)) • θ r = 0 := by
    have hmwR : (mw : ℝ) = (kT : ℝ) - (edgeSet.card : ℝ) := by
      dsimp [mw]; rw [Nat.cast_sub (le_of_lt he_lt)]
    have h1 : ∑ r : Fin 3, (vertMult Ts w r : ℝ) * θ r = ∑ r : Fin 3, (mw : ℝ) * θ r := by
      rw [← Finset.mul_sum, hθ_sum, hmwR]
      linarith
    simp only [Rat.smul_def]
    push_cast
    simp only [sub_mul, Finset.sum_sub_distrib]
    linarith
  have hmult_mw : ∀ r : Fin 3, vertMult Ts w r = mw := by
    intro r
    have hq0 := Fintype.linearIndependent_iff.mp hθ_indep _ hmw_eq r
    have hq1 : (vertMult Ts w r : ℚ) = (mw : ℚ) := sub_eq_zero.mp hq0
    exact_mod_cast hq1
  have h3mw_le : 3 * mw ≤ n := by
    have hle := sum_vertMult_le_n Ts w
    simp only [hmult_mw, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hle
    exact hle
  have hmw1 : mw = 1 := by rcases hmw_cases with h1 | h2 <;> omega
  intro r
  rw [hmult_mw r, hmw1]

/-- Step 3B: Corner subtriangles are distinct and their non-corner vertices lie on open edges of `T`. -/
lemma corner_subtriangles_structure {n : ℕ} (hn_ge2 : 2 ≤ n)
    {T : Triangle ℝ ℝ²} {Ts : Fin n → Triangle ℝ ℝ²}
    (hdisj : Pairwise fun i j => Disjoint (Ts i).interior (Ts j).interior)
    (hunion : ⋃ i, (Ts i).closedInterior = T.closedInterior)
    {i_fn : Fin 3 → Fin n} {r_fn : Fin 3 → Fin 3}
    (hpt_corner : ∀ m : Fin 3, (Ts (i_fn m)).points (r_fn m) = T.points m)
    (hnot_other_cl : ∀ (m : Fin 3) (j : Fin n), j ≠ i_fn m → T.points m ∉ (Ts j).closedInterior) :
    Function.Injective i_fn ∧
    ∀ (m m₁ m₂ : Fin 3), m₁ ≠ m → m₂ ≠ m → m₁ ≠ m₂ →
      ∃ r₁ r₂ : Fin 3, r₁ ≠ r_fn m ∧ r₂ ≠ r_fn m ∧ r₁ ≠ r₂ ∧
        (∀ m' : Fin 3, T.points m' ≠ (Ts (i_fn m)).points r₁) ∧
        (Ts (i_fn m)).points r₁ ∈ openEdge T m₂ ∧
        (∀ m' : Fin 3, T.points m' ≠ (Ts (i_fn m)).points r₂) ∧
        (Ts (i_fn m)).points r₂ ∈ openEdge T m₁ := by
  classical
  have hcl_sub : ∀ i : Fin n, (Ts i).closedInterior ⊆ T.closedInterior := by
    intro i x hx; rw [← hunion]; exact Set.mem_iUnion.mpr ⟨i, hx⟩
  have hcorner_ray : ∀ (m m₁ m₂ : Fin 3), m₁ ≠ m → m₂ ≠ m → m₁ ≠ m₂ →
      ∃ r : Fin 3, 0 < (triBasis T).coord m₁ ((Ts (i_fn m)).points r) ∧
        (triBasis T).coord m₂ ((Ts (i_fn m)).points r) = 0 := by
    intro m m₁ m₂ hm1 hm2 hm12
    let otherIdx : Finset (Fin n) := Finset.univ.erase (i_fn m)
    let otherCl : Set ℝ² := ⋃ j ∈ (otherIdx : Set (Fin n)), (Ts j).closedInterior
    have hclosed_other : IsClosed otherCl :=
      otherIdx.finite_toSet.isClosed_biUnion fun j _ => isClosed_closedInterior (Ts j)
    have hnotMem_other : T.points m ∉ otherCl := by
      simp only [otherCl, Set.mem_iUnion, Finset.mem_coe, otherIdx, Finset.mem_erase, ne_eq,
        Finset.mem_univ, and_true, not_exists]
      intro j hj
      exact hnot_other_cl m j hj
    let ray : ℝ → ℝ² := fun t => (1 - t) • T.points m + t • T.points m₁
    have hcont_ray : Continuous ray :=
      ((continuous_const.sub continuous_id).smul continuous_const).add
        (continuous_id.smul continuous_const)
    have hopen_pre : IsOpen (ray ⁻¹' otherClᶜ) := hclosed_other.isOpen_compl.preimage hcont_ray
    have h0_mem : (0 : ℝ) ∈ ray ⁻¹' otherClᶜ := by
      change ray 0 ∉ otherCl
      simpa [ray] using hnotMem_other
    obtain ⟨ε, hε_pos, hball_ε⟩ := Metric.isOpen_iff.mp hopen_pre 0 h0_mem
    let δ : ℝ := min (ε / 2) (1 / 2)
    have hδ_pos : 0 < δ := lt_min (half_pos hε_pos) (by norm_num)
    have hδ_lt1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have hδ_lt_ε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε_pos)
    have hray_not_other : ray δ ∉ otherCl := by
      have hd : δ ∈ Metric.ball (0 : ℝ) ε := by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hδ_pos]
        exact hδ_lt_ε
      exact hball_ε hd
    let wT : Fin 3 → ℝ := fun k => if k = m then 1 - δ else if k = m₁ then δ else 0
    have hwT_m : wT m = 1 - δ := by simp [wT]
    have hwT_m1 : wT m₁ = δ := by simp [wT, hm1]
    have hwT_m2 : wT m₂ = 0 := by simp [wT, hm2, hm12.symm]
    have hwT_sum : ∑ k : Fin 3, wT k = 1 := by
      rw [fin3_sum_perm hm1 hm2 hm12, hwT_m, hwT_m1, hwT_m2]; ring
    have hwT_comb : Finset.univ.affineCombination ℝ (triBasis T) wT = ray δ := by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hwT_sum,
        fin3_sum_perm hm1 hm2 hm12, hwT_m, hwT_m1, hwT_m2]
      dsimp [ray]; simp
    have hcoord_ray : ∀ k : Fin 3, (triBasis T).coord k (ray δ) = wT k := fun k => by
      rw [← hwT_comb]
      exact (triBasis T).coord_apply_combination_of_mem (Finset.mem_univ k) hwT_sum
    have hray_clT : ray δ ∈ T.closedInterior := by
      rw [mem_closedInterior_iff_coord]
      intro k
      rw [hcoord_ray]
      rcases fin3_eq_three hm1 hm2 hm12 k with rfl | rfl | rfl
      · rw [hwT_m]; linarith
      · rw [hwT_m1]; linarith
      · rw [hwT_m2]
    have hray_cl_im : ray δ ∈ (Ts (i_fn m)).closedInterior := by
      rw [← hunion, Set.mem_iUnion] at hray_clT
      rcases hray_clT with ⟨j, hj_cl⟩
      by_cases hij : j = i_fn m
      · rwa [← hij]
      · exfalso
        apply hray_not_other
        simp only [otherCl, Set.mem_iUnion, Finset.mem_coe, otherIdx, Finset.mem_erase, ne_eq,
          Finset.mem_univ, and_true]
        exact ⟨j, hij, hj_cl⟩
    let Sm : Triangle ℝ ℝ² := Ts (i_fn m)
    let u : Fin 3 → ℝ := fun r => (triBasis Sm).coord r (ray δ)
    have hu_nn : ∀ r : Fin 3, 0 ≤ u r := (mem_closedInterior_iff_coord Sm (ray δ)).mp hray_cl_im
    have hu_sum : ∑ r : Fin 3, u r = 1 := (triBasis Sm).sum_coord_apply_eq_one (ray δ)
    have hu_comb : ∑ r : Fin 3, u r • Sm.points r = ray δ := by
      have hc := (triBasis Sm).affineCombination_coord_eq_self (ray δ)
      rwa [Finset.affineCombination_eq_linear_combination _ _ _ hu_sum] at hc
    have hφ1_eq : ∑ r : Fin 3, u r * (triBasis T).coord m₁ (Sm.points r) = δ := by
      rw [← affineMap_apply_linear_combination Sm ((triBasis T).coord m₁) hu_sum, hu_comb,
        hcoord_ray m₁, hwT_m1]
    have hφ2_eq : ∑ r : Fin 3, u r * (triBasis T).coord m₂ (Sm.points r) = 0 := by
      rw [← affineMap_apply_linear_combination Sm ((triBasis T).coord m₂) hu_sum, hu_comb,
        hcoord_ray m₂, hwT_m2]
    have hex_pos : ∃ r : Fin 3, 0 < u r * (triBasis T).coord m₁ (Sm.points r) := by
      by_contra hall_le
      push Not at hall_le
      have hle0 : ∑ r : Fin 3, u r * (triBasis T).coord m₁ (Sm.points r) ≤ 0 :=
        Finset.sum_nonpos fun r _ => hall_le r
      linarith
    rcases hex_pos with ⟨r, hr_pos⟩
    have hpts_nn : ∀ (r' : Fin 3) (k : Fin 3), 0 ≤ (triBasis T).coord k (Sm.points r') :=
      fun r' k => (mem_closedInterior_iff_coord T _).mp
        (hcl_sub (i_fn m) (Sm.point_mem_closedInterior r')) k
    have hur_pos : 0 < u r := by
      by_contra hur0
      have hu_eq0 : u r = 0 := le_antisymm (not_lt.mp hur0) (hu_nn r)
      rw [hu_eq0, zero_mul] at hr_pos
      exact lt_irrefl 0 hr_pos
    have hc1_pos : 0 < (triBasis T).coord m₁ (Sm.points r) :=
      pos_of_mul_pos_right hr_pos (hu_nn r)
    have hc2_zero : (triBasis T).coord m₂ (Sm.points r) = 0 := by
      have hterm_nn : ∀ r' : Fin 3, 0 ≤ u r' * (triBasis T).coord m₂ (Sm.points r') :=
        fun r' => mul_nonneg (hu_nn r') (hpts_nn r' m₂)
      have hle : u r * (triBasis T).coord m₂ (Sm.points r) ≤ 0 := by
        rw [← hφ2_eq]
        exact Finset.single_le_sum (fun r' _ => hterm_nn r') (Finset.mem_univ r)
      have heq0 : u r * (triBasis T).coord m₂ (Sm.points r) = 0 :=
        le_antisymm hle (hterm_nn r)
      exact (mul_eq_zero.mp heq0).resolve_left (ne_of_gt hur_pos)
    exact ⟨r, hc1_pos, hc2_zero⟩
  have hcorner_no_other_orig : ∀ (m : Fin 3) (r : Fin 3),
      r ≠ r_fn m → ∀ m₁ : Fin 3, T.points m₁ ≠ (Ts (i_fn m)).points r := by
    intro m r hr_ne m₁ hm₁_eq
    have hm₁_eq' : (Ts (i_fn m)).points r = T.points m₁ := hm₁_eq.symm
    have hm1_ne : m₁ ≠ m := by
      intro heq
      subst m₁
      exact hr_ne ((Ts (i_fn m)).independent.injective (hm₁_eq'.trans (hpt_corner m).symm))
    have hi_eq : i_fn m = i_fn m₁ := by
      by_contra hne_i
      exact hnot_other_cl m₁ (i_fn m) hne_i
        (hm₁_eq' ▸ (Ts (i_fn m)).point_mem_closedInterior r)
    obtain ⟨m₂, hm2_m, hm2_m1, hm_all⟩ := fin3_third hm1_ne.symm
    obtain ⟨r₂, hr2_rm, hr2_r, hr_all⟩ := fin3_third hr_ne.symm
    let Sm : Triangle ℝ ℝ² := Ts (i_fn m)
    obtain ⟨r_a, hra_pos, hra_zero⟩ := hcorner_ray m m₂ m₁ hm2_m hm1_ne hm2_m1
    have hra_eq : r_a = r₂ := by
      rcases hr_all r_a with h1 | h2 | h3
      · exfalso
        have : (triBasis T).coord m₂ (Sm.points r_a) = 0 := by
          dsimp [Sm]; rw [h1, hpt_corner m, ← triBasis_apply T m]
          exact (triBasis T).coord_apply_ne hm2_m
        linarith
      · exfalso
        have : (triBasis T).coord m₂ (Sm.points r_a) = 0 := by
          dsimp [Sm]; rw [h2, hm₁_eq', ← triBasis_apply T m₁]
          exact (triBasis T).coord_apply_ne hm2_m1
        linarith
      · exact h3
    rw [hra_eq] at hra_zero
    obtain ⟨r_b, hrb_pos, hrb_zero⟩ := hcorner_ray m₁ m₂ m hm2_m1 hm1_ne.symm hm2_m
    rw [← hi_eq] at hrb_pos hrb_zero
    have hrb_eq : r_b = r₂ := by
      rcases hr_all r_b with h1 | h2 | h3
      · exfalso
        have : (triBasis T).coord m₂ (Sm.points r_b) = 0 := by
          dsimp [Sm]; rw [h1, hpt_corner m, ← triBasis_apply T m]
          exact (triBasis T).coord_apply_ne hm2_m
        linarith
      · exfalso
        have : (triBasis T).coord m₂ (Sm.points r_b) = 0 := by
          dsimp [Sm]; rw [h2, hm₁_eq', ← triBasis_apply T m₁]
          exact (triBasis T).coord_apply_ne hm2_m1
        linarith
      · exact h3
    rw [hrb_eq] at hrb_zero
    have hr2_pt : Sm.points r₂ = T.points m₂ := by
      have hsum_r2 : (triBasis T).coord m (Sm.points r₂) +
          (triBasis T).coord m₁ (Sm.points r₂) +
          (triBasis T).coord m₂ (Sm.points r₂) = 1 := by
        rw [← fin3_sum_perm hm1_ne hm2_m hm2_m1.symm (fun k => (triBasis T).coord k (Sm.points r₂))]
        exact (triBasis T).sum_coord_apply_eq_one _
      have hc2_1 : (triBasis T).coord m₂ (Sm.points r₂) = 1 := by linarith
      apply (triBasis T).ext_elem
      intro k
      rw [← triBasis_apply T m₂]
      rcases hm_all k with rfl | rfl | rfl
      · rw [(triBasis T).coord_apply_ne hm2_m.symm]; exact hrb_zero
      · rw [(triBasis T).coord_apply_ne hm2_m1.symm]; exact hra_zero
      · rw [(triBasis T).coord_apply_eq]; exact hc2_1
    have hT_sub_Sm : T.interior ⊆ Sm.interior := by
      intro x hx
      have hx_pos := (mem_interior_iff_coord T x).mp hx
      have hx_comb := (triBasis T).affineCombination_coord_eq_self x
      have hx_sum := (triBasis T).sum_coord_apply_eq_one x
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hx_sum] at hx_comb
      rw [fin3_sum_perm hm1_ne hm2_m hm2_m1.symm] at hx_comb
      rw [fin3_sum_perm hm1_ne hm2_m hm2_m1.symm] at hx_sum
      have hx_eq : x = (triBasis T).coord m x • Sm.points (r_fn m) +
          (triBasis T).coord m₁ x • Sm.points r +
          (triBasis T).coord m₂ x • Sm.points r₂ := by
        conv_lhs => rw [← hx_comb]
        simp only [Sm, hpt_corner m, hm₁_eq', hr2_pt, triBasis_apply]
      rw [hx_eq]
      exact comb3_mem_interior Sm hr_ne hr2_rm hr2_r.symm (hx_pos m) (hx_pos m₁) (hx_pos m₂) hx_sum
    let j_other : Fin n := if i_fn m = ⟨0, by omega⟩ then ⟨1, by omega⟩ else ⟨0, by omega⟩
    have hj_ne : j_other ≠ i_fn m := by
      dsimp [j_other]
      split_ifs with h0
      · rw [h0]; intro h; have hv : (1 : ℕ) = 0 := congrArg Fin.val h; omega
      · exact fun h => h0 h.symm
    let z_j : ℝ² := (1 / 3 : ℝ) • (Ts j_other).points 0 +
      (1 / 3 : ℝ) • (Ts j_other).points 1 + (1 / 3 : ℝ) • (Ts j_other).points 2
    have hzj_int : z_j ∈ (Ts j_other).interior :=
      comb3_mem_interior (Ts j_other) (by decide) (by decide) (by decide)
        (by norm_num) (by norm_num) (by norm_num) (by ring)
    have hzj_intT : z_j ∈ T.interior := by
      have hsum_z := coneAngle_sum_eq hdisj hunion z_j
      have hle_z : coneAngle (Ts j_other) z_j ≤ coneAngle T z_j := by
        rw [← hsum_z]
        exact Finset.single_le_sum (fun j _ => coneAngle_nonneg (Ts j) z_j) (Finset.mem_univ j_other)
      rw [coneAngle_of_mem_interior hzj_int] at hle_z
      by_contra hnot_int
      have hclT : z_j ∈ T.closedInterior :=
        hcl_sub j_other ((mem_closedInterior_iff_coord _ _).mpr fun k =>
          le_of_lt ((mem_interior_iff_coord _ _).mp hzj_int k))
      by_cases hex_m : ∃ m' : Fin 3, T.points m' = z_j
      · rcases hex_m with ⟨m', hm'_eq⟩
        rw [← hm'_eq, coneAngle_point] at hle_z
        linarith [vertAngle_lt_pi T m', Real.pi_pos]
      · rw [coneAngle_of_edge hclT hnot_int (fun m' hm' => hex_m ⟨m', hm'⟩)] at hle_z
        linarith [Real.pi_pos]
    exact Set.disjoint_left.mp (hdisj hj_ne) hzj_int (hT_sub_Sm hzj_intT)
  have hi_fn_inj : Function.Injective i_fn := by
    intro m₁ m₂ heq
    by_contra hne
    have hr_ne : r_fn m₂ ≠ r_fn m₁ := by
      intro hreq
      have hp1 := hpt_corner m₁
      have hp2 := hpt_corner m₂
      rw [← heq, hreq, hp1] at hp2
      exact hne (T.independent.injective hp2)
    exact hcorner_no_other_orig m₁ (r_fn m₂) hr_ne m₂ (by rw [heq, hpt_corner m₂])
  refine ⟨hi_fn_inj, fun m m₁ m₂ hm1 hm2 hm12 => ?_⟩
  have hmk_edge : ∀ (a b : Fin 3), a ≠ m → b ≠ m → a ≠ b →
      ∃ r : Fin 3, r ≠ r_fn m ∧
        (∀ m' : Fin 3, T.points m' ≠ (Ts (i_fn m)).points r) ∧
        (Ts (i_fn m)).points r ∈ openEdge T b := by
    intro a b ha hb hab
    obtain ⟨r, hc_a, hc_b⟩ := hcorner_ray m a b ha hb hab
    let p := (Ts (i_fn m)).points r
    have hr_ne : r ≠ r_fn m := by
      intro hreq
      have : (triBasis T).coord a p = 0 := by
        dsimp [p]; rw [hreq, hpt_corner m, ← triBasis_apply T m]
        exact (triBasis T).coord_apply_ne ha
      linarith
    have hp_not_orig : ∀ m' : Fin 3, T.points m' ≠ p := hcorner_no_other_orig m r hr_ne
    have hp_clT : ∀ k : Fin 3, 0 ≤ (triBasis T).coord k p :=
      (mem_closedInterior_iff_coord T p).mp (hcl_sub (i_fn m) ((Ts (i_fn m)).point_mem_closedInterior r))
    have hc_m : 0 < (triBasis T).coord m p := by
      refine lt_of_le_of_ne (hp_clT m) fun h0 => ?_
      have hsum_p : (triBasis T).coord m p + (triBasis T).coord a p + (triBasis T).coord b p = 1 := by
        rw [← fin3_sum_perm ha hb hab (fun k => (triBasis T).coord k p)]
        exact (triBasis T).sum_coord_apply_eq_one p
      have hca_1 : (triBasis T).coord a p = 1 := by linarith
      apply hp_not_orig a
      symm
      apply (triBasis T).ext_elem
      intro k
      rw [← triBasis_apply T a]
      rcases fin3_eq_three ha hb hab k with rfl | rfl | rfl
      · rw [(triBasis T).coord_apply_ne ha.symm, ← h0]
      · rw [(triBasis T).coord_apply_eq, hca_1]
      · rw [(triBasis T).coord_apply_ne hab.symm, hc_b]
    have hp_edge : p ∈ openEdge T b := by
      refine ⟨hc_b, fun l hl => ?_⟩
      rcases fin3_eq_three ha hb hab l with rfl | rfl | rfl
      · exact hc_m
      · exact hc_a
      · exact absurd rfl hl
    exact ⟨r, hr_ne, hp_not_orig, hp_edge⟩
  obtain ⟨r₁, hr1_ne, hr1_no, hr1_edge⟩ := hmk_edge m₁ m₂ hm1 hm2 hm12
  obtain ⟨r₂, hr2_ne, hr2_no, hr2_edge⟩ := hmk_edge m₂ m₁ hm2 hm1 hm12.symm
  have hr12 : r₁ ≠ r₂ := by
    intro heq
    rw [heq] at hr1_edge
    exact Set.disjoint_left.mp (openEdge_disjoint T hm12.symm) hr1_edge hr2_edge
  exact ⟨r₁, r₂, hr1_ne, hr2_ne, hr12, hr1_no, hr1_edge, hr2_no, hr2_edge⟩

lemma not_isSimiliCuttable_two_three_five {n : ℕ} (hn_cases : n = 2 ∨ n = 3 ∨ n = 5) :
    ¬ Erdos633.IsSimiliCuttable n baseTri := by
  classical
  rintro ⟨Ts, hsim, hdisj, hunion⟩
  let T : Triangle ℝ ℝ² := baseTri
  have hT_indep : LinearIndependent ℚ (vertAngle T) := by
    dsimp [T]; rw [vertAngle_baseTri]; exact γ_linearIndependent
  have hn_ge2 : 2 ≤ n := by rcases hn_cases with rfl | rfl | rfl <;> decide
  have hn_lt6 : n < 6 := by rcases hn_cases with rfl | rfl | rfl <;> decide
  obtain ⟨hrow_sum, hcol_sum, hex_corner, hW_mult_raw⟩ :=
    simili_multiplicity_structure hn_ge2 hn_lt6 hT_indep hsim hdisj hunion
  choose i_fn r_fn hpt_corner hnot_other_cl using hex_corner
  obtain ⟨hi_fn_inj, hcorner_edges_raw⟩ :=
    corner_subtriangles_structure hn_ge2 hdisj hunion hpt_corner hnot_other_cl
  let allVerts : Finset ℝ² := Finset.univ.biUnion fun i : Fin n => Finset.univ.image (Ts i).points
  let origVerts : Finset ℝ² := Finset.univ.image T.points
  let W : Finset ℝ² := allVerts \ origVerts
  have horig_sub : origVerts ⊆ allVerts := by
    intro p hp
    simp only [origVerts, Finset.mem_image, Finset.mem_univ, true_and] at hp
    rcases hp with ⟨m, rfl⟩
    simp only [allVerts, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
    exact ⟨i_fn m, r_fn m, hpt_corner m⟩
  have hW_mult : ∀ w ∈ W, ∀ r : Fin 3, vertMult Ts w r = 1 := by
    intro w hw
    have hw_all : w ∈ allVerts := (Finset.mem_sdiff.mp hw).1
    have hw_not_orig : w ∉ origVerts := (Finset.mem_sdiff.mp hw).2
    simp only [allVerts, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image] at hw_all
    exact hW_mult_raw w hw_all fun m hm => hw_not_orig (Finset.mem_image.mpr ⟨m, Finset.mem_univ m, hm⟩)
  have hW_card : W.card = n - 1 := by
    have hall_sum : ∑ p ∈ allVerts, vertMult Ts p 0 = n := by
      calc ∑ p ∈ allVerts, vertMult Ts p 0
          = ∑ p ∈ allVerts, ∑ i : Fin n, if (Ts i).points 0 = p then 1 else 0 := by
            refine Finset.sum_congr rfl fun p _ => ?_
            simp only [vertMult, Finset.card_filter]
        _ = ∑ i : Fin n, ∑ p ∈ allVerts, if (Ts i).points 0 = p then 1 else 0 := Finset.sum_comm
        _ = ∑ _i : Fin n, 1 := by
            refine Finset.sum_congr rfl fun i _ => ?_
            have hmem : (Ts i).points 0 ∈ allVerts := by
              simp only [allVerts, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
              exact ⟨i, 0, rfl⟩
            rw [Finset.sum_ite_eq allVerts ((Ts i).points 0) (fun _ => 1), if_pos hmem]
        _ = n := by simp
    have hunion_W : origVerts ∪ W = allVerts := Finset.union_sdiff_of_subset horig_sub
    have hdisj_W : Disjoint origVerts W := Finset.disjoint_sdiff
    rw [← hunion_W, Finset.sum_union hdisj_W] at hall_sum
    have horig_sum0 : ∑ p ∈ origVerts, vertMult Ts p 0 = 1 := by
      dsimp [origVerts]
      rw [Finset.sum_image (fun a _ b _ hab => T.independent.injective hab)]
      exact hcol_sum 0
    have hW_sum0 : ∑ p ∈ W, vertMult Ts p 0 = W.card := by
      calc ∑ p ∈ W, vertMult Ts p 0 = ∑ _p ∈ W, 1 :=
            Finset.sum_congr rfl fun w hw => hW_mult w hw 0
        _ = W.card := by simp
    rw [horig_sum0, hW_sum0] at hall_sum
    omega
  have hcorner_edges : ∀ (m m₁ m₂ : Fin 3), m₁ ≠ m → m₂ ≠ m → m₁ ≠ m₂ →
      ∃ r₁ r₂ : Fin 3, r₁ ≠ r_fn m ∧ r₂ ≠ r_fn m ∧ r₁ ≠ r₂ ∧
        (Ts (i_fn m)).points r₁ ∈ W ∧ (Ts (i_fn m)).points r₁ ∈ openEdge T m₂ ∧
        (Ts (i_fn m)).points r₂ ∈ W ∧ (Ts (i_fn m)).points r₂ ∈ openEdge T m₁ := by
    intro m m₁ m₂ hm1 hm2 hm12
    obtain ⟨r₁, r₂, hr1, hr2, hr12, hno1, he1, hno2, he2⟩ :=
      hcorner_edges_raw m m₁ m₂ hm1 hm2 hm12
    have hW1 : (Ts (i_fn m)).points r₁ ∈ W := by
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · simp only [allVerts, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
        exact ⟨i_fn m, r₁, rfl⟩
      · simp only [origVerts, Finset.mem_image, Finset.mem_univ, true_and, not_exists]
        exact hno1
    have hW2 : (Ts (i_fn m)).points r₂ ∈ W := by
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · simp only [allVerts, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
        exact ⟨i_fn m, r₂, rfl⟩
      · simp only [origVerts, Finset.mem_image, Finset.mem_univ, true_and, not_exists]
        exact hno2
    exact ⟨r₁, r₂, hr1, hr2, hr12, hW1, he1, hW2, he2⟩
  let W_edge (k : Fin 3) : Finset ℝ² := W.filter fun x => x ∈ openEdge T k
  have hW_edge_disj : Pairwise fun k₁ k₂ : Fin 3 => Disjoint (W_edge k₁) (W_edge k₂) := by
    intro k₁ k₂ hne
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [W_edge, Finset.mem_filter] at hx1 hx2
    exact Set.disjoint_left.mp (openEdge_disjoint T hne) hx1.2 hx2.2
  have hW_edge_pos : ∀ k : Fin 3, 1 ≤ (W_edge k).card := by
    intro k
    obtain ⟨k₁, k₂, hk1, hk2, hk12, _⟩ := fin3_other_two k
    obtain ⟨r₁, _, _, _, _, hr1_W, hr1_edge, _, _⟩ := hcorner_edges k₁ k₂ k hk12.symm hk1.symm hk2
    exact Finset.card_pos.mpr ⟨(Ts (i_fn k₁)).points r₁, Finset.mem_filter.mpr ⟨hr1_W, hr1_edge⟩⟩
  rcases hn_cases with rfl | rfl | rfl
  · -- Case n = 2
    have hcard_le := Fintype.card_le_of_injective i_fn hi_fn_inj
    simp at hcard_le
  · -- Case n = 3
    have hsum_le : ∑ k : Fin 3, (W_edge k).card ≤ W.card := by
      rw [← Finset.card_biUnion (fun k₁ _ k₂ _ hne => hW_edge_disj hne)]
      refine Finset.card_le_card fun x hx => ?_
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, W_edge, Finset.mem_filter] at hx
      rcases hx with ⟨_, hxW, _⟩
      exact hxW
    have h0 := hW_edge_pos 0; have h1 := hW_edge_pos 1; have h2 := hW_edge_pos 2
    rw [Fin.sum_univ_three, hW_card] at hsum_le
    omega
  · -- Case n = 5
    have hW4 : W.card = 4 := by rw [hW_card]
    let cornerIdx : Finset (Fin 5) := Finset.univ.image i_fn
    have hcorner_card : cornerIdx.card = 3 := by
      dsimp [cornerIdx]
      rw [Finset.card_image_of_injective _ hi_fn_inj, Finset.card_univ, Fintype.card_fin]
    let remIdx : Finset (Fin 5) := Finset.univ \ cornerIdx
    have hrem_card : remIdx.card = 2 := by
      dsimp [remIdx]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, hcorner_card]
    obtain ⟨ia, ib, hab_ne, hrem_eq⟩ := Finset.card_eq_two.mp hrem_card
    have hunion_idx : cornerIdx ∪ remIdx = Finset.univ :=
      Finset.union_sdiff_of_subset (Finset.subset_univ _)
    have hdisj_idx : Disjoint cornerIdx remIdx := Finset.disjoint_sdiff
    have hw_inc_split : ∀ p : ℝ²,
        (∑ i ∈ cornerIdx, incAt Ts i p) + (∑ i ∈ remIdx, incAt Ts i p) = ∑ i : Fin 5, incAt Ts i p := by
      intro p
      rw [← Finset.sum_union hdisj_idx, hunion_idx]
    have hw_corner_pos : ∀ w ∈ W, 1 ≤ ∑ i ∈ cornerIdx, incAt Ts i w := by
      intro w hw
      have htot3 : ∑ i : Fin 5, incAt Ts i w = 3 := by
        rw [← sum_vertMult_eq_sum_incAt]
        simp [hW_mult w hw]
      have hrem_le2 : ∑ i ∈ remIdx, incAt Ts i w ≤ 2 := by
        rw [hrem_eq, Finset.sum_pair hab_ne]
        linarith [incAt_le_one Ts ia w, incAt_le_one Ts ib w]
      have hsp := hw_inc_split w
      omega
    have hcorner_vert_in_edges : ∀ (m : Fin 3) (r : Fin 3),
        (Ts (i_fn m)).points r ∈ W →
        ∃ k : Fin 3, k ≠ m ∧ (Ts (i_fn m)).points r ∈ openEdge T k := by
      intro m r hpW
      obtain ⟨m₁, m₂, hm1, hm2, hm12, _⟩ := fin3_other_two m
      obtain ⟨r₁, r₂, hr1_ne, hr2_ne, hr12, _, hr1_edge, _, hr2_edge⟩ :=
        hcorner_edges m m₁ m₂ hm1 hm2 hm12
      rcases fin3_eq_three hr1_ne hr2_ne hr12 r with rfl | rfl | rfl
      · exfalso
        have hnot_orig := (Finset.mem_sdiff.mp hpW).2
        rw [hpt_corner m] at hnot_orig
        exact hnot_orig (Finset.mem_image_of_mem T.points (Finset.mem_univ m))
      · exact ⟨m₂, hm2, hr1_edge⟩
      · exact ⟨m₁, hm1, hr2_edge⟩
    have hW_union_edges : Finset.univ.biUnion W_edge = W := by
      apply Finset.Subset.antisymm
      · intro x hx
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, W_edge, Finset.mem_filter] at hx
        rcases hx with ⟨_, hxW, _⟩
        exact hxW
      · intro w hw
        have hpos := hw_corner_pos w hw
        have hex_i : ∃ i ∈ cornerIdx, incAt Ts i w ≠ 0 := by
          by_contra hall0
          push Not at hall0
          have : ∑ i ∈ cornerIdx, incAt Ts i w = 0 := Finset.sum_eq_zero hall0
          omega
        rcases hex_i with ⟨i, hi_c, hi_ne⟩
        simp only [cornerIdx, Finset.mem_image, Finset.mem_univ, true_and] at hi_c
        rcases hi_c with ⟨m, rfl⟩
        obtain ⟨r, hr⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hi_ne)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
        obtain ⟨k, _, hk_edge⟩ := hcorner_vert_in_edges m r (hr ▸ hw)
        rw [hr] at hk_edge
        exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, Finset.mem_filter.mpr ⟨hw, hk_edge⟩⟩
    have hsum_W_edges : ∑ k : Fin 3, (W_edge k).card = 4 := by
      rw [← Finset.card_biUnion (fun k₁ _ k₂ _ hne => hW_edge_disj hne), hW_union_edges, hW4]
    have hex_k2 : ∃ k : Fin 3, (W_edge k).card = 2 := by
      have h0 := hW_edge_pos 0; have h1 := hW_edge_pos 1; have h2 := hW_edge_pos 2
      rw [Fin.sum_univ_three] at hsum_W_edges
      by_cases hc0 : (W_edge 0).card = 2
      · exact ⟨0, hc0⟩
      · by_cases hc1 : (W_edge 1).card = 2
        · exact ⟨1, hc1⟩
        · exact ⟨2, by omega⟩
    rcases hex_k2 with ⟨k, hk_card2⟩
    obtain ⟨k₁, k₂, hk1, hk2, hk12, _⟩ := fin3_other_two k
    have hcorner_in_Wk_le : ∀ m : Fin 3,
        ∑ w ∈ W_edge k, incAt Ts (i_fn m) w ≤ if m = k then 0 else 1 := by
      intro m
      have hrewrite : ∑ w ∈ W_edge k, incAt Ts (i_fn m) w =
          (Finset.univ.filter fun r : Fin 3 => (Ts (i_fn m)).points r ∈ W_edge k).card := by
        simp only [incAt, Finset.card_filter]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.sum_ite_eq]
      rw [hrewrite]
      obtain ⟨m₁, m₂, hm1, hm2, hm12, _⟩ := fin3_other_two m
      obtain ⟨r₁, r₂, hr1_ne, hr2_ne, hr12, _, hr1_edge, _, hr2_edge⟩ :=
        hcorner_edges m m₁ m₂ hm1 hm2 hm12
      have hnot_rm : (Ts (i_fn m)).points (r_fn m) ∉ W_edge k := by
        rw [hpt_corner m]
        intro hmem
        exact point_notMem_openEdge T m k (Finset.mem_filter.mp hmem).2
      split_ifs with hmk
      · subst hmk
        have hemp : (Finset.univ.filter fun r : Fin 3 => (Ts (i_fn m)).points r ∈ W_edge m) = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro r hr
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
          rcases fin3_eq_three hr1_ne hr2_ne hr12 r with rfl | rfl | rfl
          · exact hnot_rm hr
          · exact Set.disjoint_left.mp (openEdge_disjoint T hm2) hr1_edge (Finset.mem_filter.mp hr).2
          · exact Set.disjoint_left.mp (openEdge_disjoint T hm1) hr2_edge (Finset.mem_filter.mp hr).2
        rw [hemp, Finset.card_empty]
      · refine Finset.card_le_one.mpr fun ra hra rb hrb => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hra hrb
        have h_cases : ∀ r : Fin 3, (Ts (i_fn m)).points r ∈ W_edge k →
            (m₂ = k ∧ r = r₁) ∨ (m₁ = k ∧ r = r₂) := by
          intro r hr
          have hr_e := (Finset.mem_filter.mp hr).2
          rcases fin3_eq_three hr1_ne hr2_ne hr12 r with rfl | rfl | rfl
          · exact absurd hr hnot_rm
          · refine Or.inl ⟨?_, rfl⟩
            by_contra hne_k
            exact Set.disjoint_left.mp (openEdge_disjoint T hne_k) hr1_edge hr_e
          · refine Or.inr ⟨?_, rfl⟩
            by_contra hne_k
            exact Set.disjoint_left.mp (openEdge_disjoint T hne_k) hr2_edge hr_e
        rcases h_cases ra hra with ⟨hm2k, rfl⟩ | ⟨hm1k, rfl⟩ <;>
          rcases h_cases rb hrb with ⟨hm2k', rfl⟩ | ⟨hm1k', rfl⟩
        · rfl
        · exact absurd (hm1k'.trans hm2k.symm) hm12
        · exact absurd (hm1k.trans hm2k'.symm) hm12
        · rfl
    have hsum_Wk_corner_le2 : ∑ w ∈ W_edge k, ∑ i ∈ cornerIdx, incAt Ts i w ≤ 2 := by
      rw [Finset.sum_comm]
      dsimp [cornerIdx]
      rw [Finset.sum_image (fun a _ b _ hab => hi_fn_inj hab),
        fin3_sum_perm hk1 hk2 hk12]
      have h0 := hcorner_in_Wk_le k
      have h1 := hcorner_in_Wk_le k₁
      have h2 := hcorner_in_Wk_le k₂
      simp only [↓reduceIte, hk1, hk2] at h0 h1 h2
      omega
    obtain ⟨q₁, q₂, hq_ne, hWk_eq⟩ := Finset.card_eq_two.mp hk_card2
    have hq1_Wk : q₁ ∈ W_edge k := by rw [hWk_eq]; simp
    have hq2_Wk : q₂ ∈ W_edge k := by rw [hWk_eq]; simp
    have hq1_W : q₁ ∈ W := (Finset.mem_filter.mp hq1_Wk).1
    have hq2_W : q₂ ∈ W := (Finset.mem_filter.mp hq2_Wk).1
    have hq1_edge : q₁ ∈ openEdge T k := (Finset.mem_filter.mp hq1_Wk).2
    have hq2_edge : q₂ ∈ openEdge T k := (Finset.mem_filter.mp hq2_Wk).2
    rw [hWk_eq, Finset.sum_pair hq_ne] at hsum_Wk_corner_le2
    have hq1_cpos := hw_corner_pos q₁ hq1_W
    have hq2_cpos := hw_corner_pos q₂ hq2_W
    have hq1_c1 : ∑ i ∈ cornerIdx, incAt Ts i q₁ = 1 := by omega
    have hq2_c1 : ∑ i ∈ cornerIdx, incAt Ts i q₂ = 1 := by omega
    have hrem_has_q : ∀ i_rem ∈ remIdx, ∀ q : ℝ², q ∈ W →
        ∑ i ∈ cornerIdx, incAt Ts i q = 1 → ∃ r : Fin 3, (Ts i_rem).points r = q := by
      intro i_rem hi_rem q hqW hqc1
      have htot3 : ∑ i : Fin 5, incAt Ts i q = 3 := by
        rw [← sum_vertMult_eq_sum_incAt]; simp [hW_mult q hqW]
      have hrem2 : ∑ i ∈ remIdx, incAt Ts i q = 2 := by
        have hsp := hw_inc_split q; omega
      rw [hrem_eq, Finset.sum_pair hab_ne] at hrem2
      have hia_le := incAt_le_one Ts ia q
      have hib_le := incAt_le_one Ts ib q
      have hi_cases : i_rem = ia ∨ i_rem = ib := by
        rw [hrem_eq] at hi_rem; simpa using hi_rem
      have hinc1 : incAt Ts i_rem q = 1 := by
        rcases hi_cases with rfl | rfl <;> omega
      obtain ⟨r, hr⟩ := Finset.card_pos.mp (by omega : 0 < incAt Ts i_rem q)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
      exact ⟨r, hr⟩
    have hrem_third : ∀ i_rem ∈ remIdx,
        ∃ r₀ r₁ r₂ : Fin 3, r₁ ≠ r₀ ∧ r₂ ≠ r₀ ∧ r₁ ≠ r₂ ∧
          (Ts i_rem).points r₁ = q₁ ∧ (Ts i_rem).points r₂ = q₂ ∧
          0 < (triBasis T).coord k ((Ts i_rem).points r₀) := by
      intro i_rem hi_rem
      obtain ⟨r₁, hr₁⟩ := hrem_has_q i_rem hi_rem q₁ hq1_W hq1_c1
      obtain ⟨r₂, hr₂⟩ := hrem_has_q i_rem hi_rem q₂ hq2_W hq2_c1
      have hr12 : r₁ ≠ r₂ := by
        intro heq; rw [heq, hr₂] at hr₁; exact hq_ne hr₁.symm
      obtain ⟨r₀, hr01, hr02, _⟩ := fin3_third hr12
      let u := (Ts i_rem).points r₀
      have hu_not_orig : u ∉ origVerts := by
        intro hu_orig
        simp only [origVerts, Finset.mem_image, Finset.mem_univ, true_and] at hu_orig
        rcases hu_orig with ⟨m, hm_eq⟩
        have htot1 : ∑ i : Fin 5, incAt Ts i (T.points m) = 1 := by
          rw [← sum_vertMult_eq_sum_incAt, hrow_sum m]
        have hc_ge1 : 1 ≤ ∑ i ∈ cornerIdx, incAt Ts i (T.points m) := by
          have him_mem : i_fn m ∈ cornerIdx := Finset.mem_image_of_mem i_fn (Finset.mem_univ m)
          have him_pos : 1 ≤ incAt Ts (i_fn m) (T.points m) :=
            Finset.card_pos.mpr ⟨r_fn m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpt_corner m⟩⟩
          exact le_trans him_pos
            (Finset.single_le_sum (f := fun i => incAt Ts i (T.points m)) (fun _ _ => Nat.zero_le _) him_mem)
        have hrem_pos : 1 ≤ ∑ i ∈ remIdx, incAt Ts i (T.points m) := by
          have hu_pos : 1 ≤ incAt Ts i_rem (T.points m) :=
            Finset.card_pos.mpr ⟨r₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm_eq.symm⟩⟩
          exact le_trans hu_pos
            (Finset.single_le_sum (f := fun i => incAt Ts i (T.points m)) (fun _ _ => Nat.zero_le _) hi_rem)
        have hsp := hw_inc_split (T.points m)
        omega
      have hu_all : u ∈ allVerts := by
        simp only [allVerts, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
        exact ⟨i_rem, r₀, rfl⟩
      have hu_W : u ∈ W := Finset.mem_sdiff.mpr ⟨hu_all, hu_not_orig⟩
      rw [← hW_union_edges, Finset.mem_biUnion] at hu_W
      rcases hu_W with ⟨ku, _, hku_mem⟩
      have hku_ne_k : ku ≠ k := by
        intro heq
        rw [heq, hWk_eq] at hku_mem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hku_mem
        rcases hku_mem with hu_q1 | hu_q2
        · exact hr01 ((Ts i_rem).independent.injective (hu_q1.trans hr₁.symm))
        · exact hr02 ((Ts i_rem).independent.injective (hu_q2.trans hr₂.symm))
      have hu_edge : u ∈ openEdge T ku := (Finset.mem_filter.mp hku_mem).2
      exact ⟨r₀, r₁, r₂, hr01.symm, hr02.symm, hr12, hr₁, hr₂, hu_edge.2 k hku_ne_k.symm⟩
    have hia_mem : ia ∈ remIdx := by rw [hrem_eq]; simp
    have hib_mem : ib ∈ remIdx := by rw [hrem_eq]; simp
    obtain ⟨r₀, r₁, r₂, hr01, hr02, hr12, hp11, hp12, hu1_pos⟩ := hrem_third ia hia_mem
    obtain ⟨s₀, s₁, s₂, hs01, hs02, hs12, hp21, hp22, hu2_pos⟩ := hrem_third ib hib_mem
    exact shared_edge_interior_overlap T (Ts ia) (Ts ib) k
      hr01 hr02 hr12 hs01 hs02 hs12 rfl hp11 hp12 rfl hp21 hp22
      hq1_edge.1 hq2_edge.1 hu1_pos hu2_pos (hdisj hab_ne)

end Erdos633Proof

namespace Erdos633Proof

lemma of_ne_zero_two_three_five_all {n : ℕ} (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)))
    (hn₀ : n ≠ 0) (hn₂ : n ≠ 2) (hn₃ : n ≠ 3) (hn₅ : n ≠ 5) :
    Erdos633.IsSimiliCuttable n T := by
  by_cases hn1 : n = 1
  · subst hn1
    exact (Erdos633SimiliCuttableProof.strongSimiliCuttable_one T).toIsSimiliCuttable
  · by_cases heven : n % 2 = 0
    · have hm : 2 ≤ n / 2 := by omega
      have heq : 2 * (n / 2) = n := by omega
      rw [← heq]
      exact (Erdos633SimiliCuttableProof.strongSimiliCuttable_two_mul (n / 2) hm T).toIsSimiliCuttable
    · have hm : 2 ≤ (n - 3) / 2 := by omega
      have heq1 : 2 * ((n - 3) / 2) = n - 3 := by omega
      have heq2 : (n - 3) + 3 = n := by omega
      have hbase : Erdos633SimiliCuttableProof.StrongSimiliCuttable (n - 3) T := by
        rw [← heq1]
        exact Erdos633SimiliCuttableProof.strongSimiliCuttable_two_mul ((n - 3) / 2) hm T
      rw [← heq2]
      exact (Erdos633SimiliCuttableProof.strongSimiliCuttable_add_three (by omega) hbase).toIsSimiliCuttable

lemma isSimiliCuttable_baseTri_iff (n : ℕ) :
    Erdos633.IsSimiliCuttable n baseTri ↔ n ≠ 0 ∧ n ≠ 2 ∧ n ≠ 3 ∧ n ≠ 5 := by
  constructor
  · intro h
    refine ⟨h.ne_zero, ?_, ?_, ?_⟩
    · rintro rfl; exact not_isSimiliCuttable_two_three_five (Or.inl rfl) h
    · rintro rfl; exact not_isSimiliCuttable_two_three_five (Or.inr (Or.inl rfl)) h
    · rintro rfl; exact not_isSimiliCuttable_two_three_five (Or.inr (Or.inr rfl)) h
  · rintro ⟨hn0, hn2, hn3, hn5⟩
    exact of_ne_zero_two_three_five_all baseTri hn0 hn2 hn3 hn5

end Erdos633Proof

theorem OMA.solution :
    type_of% @Erdos633.exists_isSimiliCuttable_iff_ne_zero_two_three_five :=
  ⟨Erdos633Proof.baseTri, Erdos633Proof.isSimiliCuttable_baseTri_iff⟩
