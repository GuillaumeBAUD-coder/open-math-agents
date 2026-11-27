import FormalConjectures.ErdosProblems.«505»

/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

/-!
# Borsuk covers in dimensions at most three

Adapted from Moritz Firsching's low-dimensional Borsuk formalization
in mo271/formal-conjectures, revision 07a6d25f07ba0e16a916be14e9830c36cfcb9777.
https://github.com/mo271/formal-conjectures/tree/07a6d25f07ba0e16a916be14e9830c36cfcb9777/FormalConjectures/Wikipedia/Borsuk

This version combines the proofs in one file and uses the project's definitions for the
cover and the conjecture. The planar proof uses Jung's theorem and three sectors.
The spatial proof uses the Gale–Grünbaum–Heppes cover and an octahedron dissection.
-/

namespace Borsuk

open Metric Bornology Set
open scoped Pointwise ENNReal EuclideanGeometry

section PseudoEMetric

variable {E F : Type*} [PseudoEMetricSpace E] [PseudoEMetricSpace F]

namespace HasBorsukCover

/-- Borsuk covers are preserved by isometries (applied to the whole space).  This is the
workhorse for transferring the Borsuk problem along coordinate changes, e.g. identifying a
hyperplane in `ℝ^(n+1)` with `ℝ^n`. -/
theorem image {k : ℕ} {s : Set E} (e : E ≃ᵢ F) (h : HasBorsukCover k s) :
    HasBorsukCover k (e '' s) := by
  obtain ⟨c, hcov, hdiam⟩ := h
  refine ⟨fun i => e '' c i, ?_, fun i => ?_⟩
  · rw [← image_iUnion]
    exact image_mono hcov
  · rw [e.ediam_image, e.ediam_image]
    exact hdiam i

/-- Borsuk covers are preserved by nonzero scalar rescalings. -/
theorem smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ} {s : Set E}
    {r : ℝ} (hr : r ≠ 0) (h : HasBorsukCover k s) : HasBorsukCover k (r • s) := by
  obtain ⟨c, hcov, hdiam⟩ := h
  refine ⟨fun i => r • c i, ?_, fun i => ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov hx)
    exact mem_iUnion.mpr ⟨i, smul_mem_smul_set hi⟩
  · rw [ediam_smul₀, ediam_smul₀]
    have hr0 : (0 : ℝ≥0∞) < (‖r‖₊ : ℝ≥0∞) := by
      simpa [pos_iff_ne_zero] using hr
    rw [ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, mul_comm,
      mul_comm (‖r‖₊ : ℝ≥0∞)]
    exact ENNReal.mul_lt_mul_left hr0.ne' ENNReal.coe_ne_top (hdiam i)

end HasBorsukCover

end PseudoEMetric

end Borsuk

namespace Borsuk

open Metric Set Module

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E]

section SupRadius

/-- The radius of the smallest ball centred at `c` containing `K`. -/
noncomputable def supRadius (K : Set E) (c : E) : ℝ := sSup ((dist c) '' K)

variable {K : Set E}

theorem dist_le_supRadius (hK : IsCompact K) {x : E} (hx : x ∈ K) (c : E) :
    dist c x ≤ supRadius K c :=
  le_csSup (hK.image (continuous_const.dist continuous_id)).bddAbove ⟨x, hx, rfl⟩

theorem supRadius_le (hne : K.Nonempty) {c : E} {r : ℝ} (h : ∀ x ∈ K, dist c x ≤ r) :
    supRadius K c ≤ r :=
  csSup_le (hne.image _) (by rintro _ ⟨x, hx, rfl⟩; exact h x hx)

theorem supRadius_nonneg (hK : IsCompact K) (hne : K.Nonempty) (c : E) :
    0 ≤ supRadius K c := by
  obtain ⟨x, hx⟩ := hne
  exact dist_nonneg.trans (dist_le_supRadius hK hx c)

/-- The supremal distance is attained on a compact set. -/
theorem exists_supRadius_eq_dist (hK : IsCompact K) (hne : K.Nonempty) (c : E) :
    ∃ x ∈ K, dist c x = supRadius K c := by
  obtain ⟨x, hx, hmax⟩ :=
    hK.exists_isMaxOn hne (continuous_const.dist continuous_id).continuousOn
  exact ⟨x, hx, le_antisymm (dist_le_supRadius hK hx c)
    (supRadius_le ⟨x, hx⟩ fun y hy => hmax hy)⟩

theorem supRadius_le_add (hK : IsCompact K) (hne : K.Nonempty) (c c' : E) :
    supRadius K c ≤ supRadius K c' + dist c c' :=
  supRadius_le hne fun x hx =>
    (dist_triangle c c' x).trans (by have := dist_le_supRadius hK hx c'; linarith)

theorem continuous_supRadius (hK : IsCompact K) (hne : K.Nonempty) :
    Continuous (supRadius K) := by
  refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun c c' => ?_)
  rw [Real.dist_eq, NNReal.coe_one, one_mul, abs_sub_le_iff]
  constructor
  · have := supRadius_le_add hK hne c c'
    linarith
  · have := supRadius_le_add hK hne c' c
    rw [dist_comm] at this
    linarith

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The minimal enclosing ball: a global minimiser of `supRadius K` exists. -/
theorem exists_min_supRadius (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ c : E, ∀ c' : E, supRadius K c ≤ supRadius K c' := by
  obtain ⟨x₀, hx₀⟩ := id hne
  set R := supRadius K x₀ with hR
  have hR0 : 0 ≤ R := supRadius_nonneg hK hne x₀
  obtain ⟨c, hcball, hcmin⟩ := (isCompact_closedBall x₀ (2 * R + 1)).exists_isMinOn
    ⟨x₀, mem_closedBall_self (by linarith)⟩ (continuous_supRadius hK hne).continuousOn
  refine ⟨c, fun c' => ?_⟩
  by_cases h : c' ∈ closedBall x₀ (2 * R + 1)
  · exact hcmin h
  · have h1 : supRadius K c ≤ R := hcmin (mem_closedBall_self (by linarith))
    rw [mem_closedBall, not_le] at h
    have h3 : dist c' x₀ ≤ supRadius K c' := dist_le_supRadius hK hx₀ c'
    linarith

end SupRadius

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section DitePad

/-- Summing a `Fin k`-indexed family padded by zeros over `Fin n` (`k ≤ n`). -/
theorem sum_dite_fin {M : Type*} [AddCommMonoid M] {n k : ℕ} (hkn : k ≤ n)
    (f : Fin k → M) :
    (∑ i : Fin n, if h : (i : ℕ) < k then f ⟨(i : ℕ), h⟩ else 0) = ∑ i : Fin k, f i := by
  have hfilter : (Finset.range n).filter (· < k) = Finset.range k := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hzero : ∑ i ∈ (Finset.range n).filter (¬ · < k),
      (if h : i < k then f ⟨i, h⟩ else 0) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.mem_filter] at hi
    exact dif_neg hi.2
  rw [Fin.sum_univ_eq_sum_range (fun i => if h : i < k then f ⟨i, h⟩ else 0) n,
    ← Finset.sum_filter_add_sum_filter_not (Finset.range n) (· < k), hfilter, hzero,
    add_zero, ← Fin.sum_univ_eq_sum_range (fun i => if h : i < k then f ⟨i, h⟩ else 0) k]
  exact Finset.sum_congr rfl fun i _ => by rw [dif_pos i.isLt]

end DitePad

section CompactHull

/-- In a finite-dimensional real normed space, the convex hull of a compact set is
compact (Carathéodory). -/
theorem _root_.IsCompact.convexHull_of_finiteDimensional {s : Set E} (hs : IsCompact s) :
    IsCompact (convexHull ℝ s) := by
  classical
  rcases eq_empty_or_nonempty s with rfl | ⟨z₀, hz₀⟩
  · simp
  set n := finrank ℝ E + 1 with hn
  have himg : convexHull ℝ s =
      (fun p : (Fin n → ℝ) × (Fin n → E) => ∑ i, p.1 i • p.2 i) ''
        (stdSimplex ℝ (Fin n) ×ˢ Set.univ.pi fun _ => s) := by
    apply Set.Subset.antisymm
    · intro x hx
      rw [convexHull_eq_union] at hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨t, hts, hai, hxt⟩ := hx
      have hcard : t.card ≤ n := by
        have h1 := hai.card_le_finrank_succ
        have h2 : finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → E))) ≤ finrank ℝ E :=
          Submodule.finrank_le _
        rw [Fintype.card_coe] at h1
        omega
      rw [Finset.convexHull_eq] at hxt
      obtain ⟨w, hw0, hw1, hcw⟩ := hxt
      set e : ↥t ≃ Fin t.card := Fintype.equivFinOfCardEq (Fintype.card_coe t) with he
      set q : Fin t.card → E := fun i => ((e.symm i : ↥t) : E) with hq
      have hqmem : ∀ i, q i ∈ t := fun i => (e.symm i).2
      have hsum_tR : ∀ F : E → ℝ, ∑ i : Fin t.card, F (q i) = ∑ y ∈ t, F y := by
        intro F
        rw [← Finset.sum_attach t F]
        exact Fintype.sum_equiv e (fun a => F ((a : ↥t) : E)) (fun i => F (q i))
          (fun a => by rw [hq]; simp) |>.symm
      have hsum_tE : ∀ F : E → E, ∑ i : Fin t.card, F (q i) = ∑ y ∈ t, F y := by
        intro F
        rw [← Finset.sum_attach t F]
        exact Fintype.sum_equiv e (fun a => F ((a : ↥t) : E)) (fun i => F (q i))
          (fun a => by rw [hq]; simp) |>.symm
      refine ⟨(fun i : Fin n => if h : (i : ℕ) < t.card then w (q ⟨(i : ℕ), h⟩) else 0,
               fun i : Fin n => if h : (i : ℕ) < t.card then q ⟨(i : ℕ), h⟩ else z₀),
              ⟨⟨fun i => ?_, ?_⟩, ?_⟩, ?_⟩
      · dsimp only
        split
        · exact hw0 _ (hqmem _)
        · exact le_rfl
      · rw [sum_dite_fin hcard (fun i => w (q i)), hsum_tR (fun y => w y)]
        exact hw1
      · rw [Set.mem_pi]
        intro i _
        dsimp only
        split
        · exact hts (hqmem _)
        · exact hz₀
      · dsimp only
        have hsummand : ∀ i : Fin n,
            (if h : (i : ℕ) < t.card then w (q ⟨(i : ℕ), h⟩) else 0) •
              (if h : (i : ℕ) < t.card then q ⟨(i : ℕ), h⟩ else z₀) =
            (if h : (i : ℕ) < t.card then w (q ⟨(i : ℕ), h⟩) • q ⟨(i : ℕ), h⟩ else 0) := by
          intro i
          by_cases h : (i : ℕ) < t.card
          · rw [dif_pos h, dif_pos h, dif_pos h]
          · rw [dif_neg h, dif_neg h, dif_neg h, zero_smul]
        rw [Finset.sum_congr rfl fun i _ => hsummand i,
          sum_dite_fin hcard (fun i => w (q i) • q i), hsum_tE (fun y => w y • y)]
        rw [Finset.centerMass_eq_of_sum_1 _ _ hw1] at hcw
        simpa using hcw
    · rintro x ⟨⟨wv, xv⟩, ⟨hwv, hxv⟩, rfl⟩
      rw [Set.mem_pi] at hxv
      have h1 : Finset.univ.centerMass wv xv ∈ convexHull ℝ s :=
        Finset.centerMass_mem_convexHull _ (fun i _ => hwv.1 i)
          (by rw [hwv.2]; norm_num) (fun i _ => hxv i (Set.mem_univ i))
      rwa [Finset.centerMass_eq_of_sum_1 _ _ hwv.2] at h1
  rw [himg]
  exact ((isCompact_stdSimplex ℝ (Fin n)).prod (isCompact_univ_pi fun _ => hs)).image
    (by fun_prop)

end CompactHull

section Contact

variable {K : Set E}

/-- At a minimiser of `supRadius`, the centre lies in the convex hull of the contact
set. -/
theorem center_mem_convexHull_contact (hK : IsCompact K) (hne : K.Nonempty) {c : E}
    (hmin : ∀ c', supRadius K c ≤ supRadius K c') (hr : 0 < supRadius K c) :
    c ∈ convexHull ℝ (K ∩ {x | dist c x = supRadius K c}) := by
  classical
  set r := supRadius K c with hrdef
  set T := K ∩ {x | dist c x = r} with hT
  by_contra hc
  have hTsub : T ⊆ K := fun x hx => hx.1
  have hTc : IsCompact T := hK.of_isClosed_subset
    (hK.isClosed.inter (isClosed_eq (continuous_const.dist continuous_id)
      continuous_const)) hTsub
  obtain ⟨x₁, hx₁K, hx₁⟩ := exists_supRadius_eq_dist hK hne c
  have hx₁T : x₁ ∈ T := ⟨hx₁K, hx₁⟩
  -- separate `c` from the compact convex hull of `T`
  obtain ⟨f, u, hfc, hfT⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ T)
    hTc.convexHull_of_finiteDimensional.isClosed hc
  set v := (InnerProductSpace.toDual ℝ E).symm f with hv
  have hfv : ∀ z, ⟪v, z⟫ = f z := fun z => InnerProductSpace.toDual_symm_apply
  set δ := u - f c with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hvT : ∀ x ∈ T, δ ≤ ⟪v, x - c⟫ := by
    intro x hx
    rw [inner_sub_right, hfv, hfv]
    have := hfT x (subset_convexHull ℝ T hx)
    rw [hδ]
    linarith
  have hvne : v ≠ 0 := by
    intro h0
    have := hvT x₁ hx₁T
    rw [h0, inner_zero_left] at this
    linarith
  -- the low-progress part of `K` stays strictly inside radius `r`
  set K' := K ∩ {x | ⟪v, x - c⟫ ≤ δ / 2} with hK'
  have hK'c : IsCompact K' := hK.of_isClosed_subset
    (hK.isClosed.inter (isClosed_le
      (continuous_const.inner (continuous_id.sub continuous_const)) continuous_const))
    (fun x hx => hx.1)
  obtain ⟨s', hs'r, hs'le⟩ : ∃ s' : ℝ, s' < r ∧ ∀ x ∈ K', dist c x ≤ s' := by
    rcases eq_empty_or_nonempty K' with hemp | hne'
    · exact ⟨0, hr, fun x hx => absurd (hemp ▸ hx) (Set.notMem_empty x)⟩
    · obtain ⟨y, hyK', hy⟩ := exists_supRadius_eq_dist hK'c hne' c
      refine ⟨supRadius K' c, lt_of_le_of_ne
        (supRadius_le hne' fun x hx => dist_le_supRadius hK hx.1 c) ?_,
        fun x hx => dist_le_supRadius hK'c hx c⟩
      intro heq
      have hyT : y ∈ T := ⟨hyK'.1, by rw [Set.mem_ofPred_eq, hy, heq]⟩
      have h1 := hvT y hyT
      have h2 := hyK'.2
      rw [Set.mem_ofPred_eq] at h2
      linarith
  -- move the centre by `ε • v`
  set nv := ‖v‖ with hnv
  have hnv0 : 0 < nv := norm_pos_iff.mpr hvne
  set ε := min (δ / (2 * nv ^ 2)) ((r - s') / (2 * nv)) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (by positivity)
  have hε1 : ε ≤ δ / (2 * nv ^ 2) := min_le_left _ _
  have hε2 : ε ≤ (r - s') / (2 * nv) := min_le_right _ _
  set c₁ := c + ε • v with hc₁
  have hδnv : δ ≤ nv * (2 * r) := by
    have h2 := hvT x₁ hx₁T
    have h3 : ⟪v, x₁ - c⟫ ≤ nv * ‖x₁ - c‖ := real_inner_le_norm v (x₁ - c)
    have h4 : ‖x₁ - c‖ = r := by rw [← dist_eq_norm', hx₁]
    nlinarith
  have hεδ : ε * δ ≤ 2 * r ^ 2 := by
    have h1 : ε * (2 * nv ^ 2) ≤ δ := (le_div_iff₀ (by positivity)).mp hε1
    have h2 : δ ^ 2 ≤ (nv * (2 * r)) ^ 2 := by nlinarith
    nlinarith [mul_pos hnv0 hnv0, hε0, hδ0]
  have hbound : ∀ x ∈ K, dist c₁ x ≤ max (s' + ε * nv) (r - ε * δ / (4 * r)) := by
    intro x hx
    by_cases hxK' : x ∈ K'
    · refine le_trans ?_ (le_max_left _ _)
      have h1 : dist c₁ c = ε * nv := by
        rw [hc₁, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos hε0, hnv]
      calc dist c₁ x ≤ dist c₁ c + dist c x := dist_triangle _ _ _
        _ ≤ ε * nv + s' := by have := hs'le x hxK'; linarith
        _ = s' + ε * nv := by ring
    · refine le_trans ?_ (le_max_right _ _)
      have hvx : δ / 2 < ⟪v, x - c⟫ := by
        rw [hK'] at hxK'
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, not_and, not_le] at hxK'
        exact hxK' hx
      have hsq : dist c₁ x ^ 2 = dist c x ^ 2 - 2 * ε * ⟪v, x - c⟫ + ε ^ 2 * nv ^ 2 := by
        have h0 : c₁ - x = -((x - c) - ε • v) := by rw [hc₁]; abel
        rw [dist_eq_norm, h0, norm_neg, norm_sub_sq_real, real_inner_smul_right,
          norm_smul, Real.norm_eq_abs, abs_of_pos hε0, real_inner_comm, dist_eq_norm',
          ← hnv]
        ring
      have hd : dist c x ≤ r := dist_le_supRadius hK hx c
      have hεnv : ε ^ 2 * nv ^ 2 ≤ ε * δ / 2 := by
        have h1 : ε * nv ^ 2 ≤ δ / 2 := by
          calc ε * nv ^ 2 ≤ δ / (2 * nv ^ 2) * nv ^ 2 :=
              mul_le_mul_of_nonneg_right hε1 (by positivity)
            _ = δ / 2 := by field_simp
        calc ε ^ 2 * nv ^ 2 = ε * (ε * nv ^ 2) := by ring
          _ ≤ ε * (δ / 2) := mul_le_mul_of_nonneg_left h1 hε0.le
          _ = ε * δ / 2 := by ring
      have hsqle : dist c₁ x ^ 2 ≤ r ^ 2 - ε * δ / 2 := by
        rw [hsq]
        have h2 : 0 ≤ ε * (⟪v, x - c⟫ - δ / 2) :=
          mul_nonneg hε0.le (by linarith)
        nlinarith [hd, dist_nonneg (x := c) (y := x)]
      have htnn : 0 ≤ r - ε * δ / (4 * r) := by
        rw [sub_nonneg, div_le_iff₀ (by positivity)]
        nlinarith
      have htarget : r ^ 2 - ε * δ / 2 ≤ (r - ε * δ / (4 * r)) ^ 2 := by
        have hexpand : (r - ε * δ / (4 * r)) ^ 2 =
            r ^ 2 - ε * δ / 2 + (ε * δ / (4 * r)) ^ 2 := by
          field_simp
          ring
        nlinarith [sq_nonneg (ε * δ / (4 * r))]
      calc dist c₁ x = Real.sqrt (dist c₁ x ^ 2) := (Real.sqrt_sq dist_nonneg).symm
        _ ≤ Real.sqrt ((r - ε * δ / (4 * r)) ^ 2) := Real.sqrt_le_sqrt (by linarith)
        _ = r - ε * δ / (4 * r) := Real.sqrt_sq htnn
  have hlt : max (s' + ε * nv) (r - ε * δ / (4 * r)) < r := by
    rw [max_lt_iff]
    refine ⟨?_, ?_⟩
    · have h1 : ε * nv ≤ (r - s') / 2 := by
        calc ε * nv ≤ (r - s') / (2 * nv) * nv := mul_le_mul_of_nonneg_right hε2 hnv0.le
          _ = (r - s') / 2 := by field_simp
      linarith
    · have h2 : 0 < ε * δ / (4 * r) := by positivity
      linarith
  have hcontra := hmin c₁
  have hle : supRadius K c₁ ≤ max (s' + ε * nv) (r - ε * δ / (4 * r)) :=
    supRadius_le hne hbound
  linarith

end Contact

section Pair

/-- The quadratic pair lemma in arbitrary dimension: if `c` is a convex combination of
points of `T`, all at distance `r > 0` from `c`, and `finrank ℝ E ≤ n`, then two points
of `T` have inner product at most `-r²/n` at `c`. -/
theorem exists_pair_of_center_mem {T : Set E} {c : E} {r : ℝ} {n : ℕ} (hn : 0 < n)
    (hr : 0 < r) (hT : ∀ x ∈ T, dist c x = r) (hc : c ∈ convexHull ℝ T)
    (hrank : finrank ℝ E ≤ n) :
    ∃ x ∈ T, ∃ y ∈ T, ⟪x - c, y - c⟫ ≤ -(r ^ 2 / (n : ℝ)) := by
  classical
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [convexHull_eq_union] at hc
  simp only [Set.mem_iUnion] at hc
  obtain ⟨t, hts, hai, hct⟩ := hc
  have hcard : t.card ≤ n + 1 := by
    have h1 := hai.card_le_finrank_succ
    have h2 : finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → E))) ≤ finrank ℝ E :=
      Submodule.finrank_le _
    rw [Fintype.card_coe] at h1
    omega
  rw [Finset.convexHull_eq] at hct
  obtain ⟨w, hw0, hw1, hcw⟩ := hct
  rw [Finset.centerMass_eq_of_sum_1 _ _ hw1] at hcw
  simp only [id] at hcw
  have hzero : ∑ i ∈ t, w i • (i - c) = 0 := by
    have h2 : ∑ i ∈ t, w i • (i - c) = (∑ i ∈ t, w i • i) - (∑ i ∈ t, w i) • c := by
      rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => smul_sub _ _ _
    rw [h2, hcw, hw1, one_smul, sub_self]
  have hexp : (0 : ℝ) = ∑ i ∈ t, ∑ j ∈ t, w i * w j * ⟪i - c, j - c⟫ := by
    have h1 : (0 : ℝ) = ⟪∑ i ∈ t, w i • (i - c), ∑ j ∈ t, w j • (j - c)⟫ := by
      rw [hzero, inner_zero_left]
    rw [h1, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_smul_left, inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_right]
    ring
  have hnorm : ∀ i ∈ t, ⟪i - c, i - c⟫ = r ^ 2 := by
    intro i hi
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm', hT i (hts hi)]
  by_contra hno
  push Not at hno
  have hgt : ∀ x ∈ t, ∀ y ∈ t, -(r ^ 2 / (n : ℝ)) < ⟪x - c, y - c⟫ := fun x hx y hy =>
    hno x (hts hx) y (hts hy)
  set S := ∑ i ∈ t, w i ^ 2 with hS
  have hScard : 1 ≤ ((n : ℝ) + 1) * S := by
    have h1 := sq_sum_le_card_mul_sum_sq (s := t) (f := w)
    rw [hw1] at h1
    have h2 : (t.card : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hcard
    have h3 : (0 : ℝ) ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
    nlinarith
  by_cases hpair : ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ 0 < w i ∧ 0 < w j
  · -- strict comparison of the double sum against its quadratic lower bound
    obtain ⟨i₀, hi₀, j₀, hj₀, hij₀, hwi₀, hwj₀⟩ := hpair
    have hFle : ∀ p ∈ t ×ˢ t,
        -(r ^ 2 / (n : ℝ)) * (w p.1 * w p.2) +
          (if p.1 = p.2 then w p.1 ^ 2 * (((n : ℝ) + 1) / (n : ℝ) * r ^ 2) else 0) ≤
        w p.1 * w p.2 * ⟪p.1 - c, p.2 - c⟫ := by
      rintro ⟨i, j⟩ hp
      rw [Finset.mem_product] at hp
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl, hnorm i hp.1]
        refine le_of_eq ?_
        field_simp
        ring
      · rw [if_neg hij]
        have h1 := hgt i hp.1 j hp.2
        have h2 : 0 ≤ w i * w j := mul_nonneg (hw0 i hp.1) (hw0 j hp.2)
        nlinarith
    have hFlt : ∃ p ∈ t ×ˢ t,
        -(r ^ 2 / (n : ℝ)) * (w p.1 * w p.2) +
          (if p.1 = p.2 then w p.1 ^ 2 * (((n : ℝ) + 1) / (n : ℝ) * r ^ 2) else 0) <
        w p.1 * w p.2 * ⟪p.1 - c, p.2 - c⟫ := by
      refine ⟨(i₀, j₀), Finset.mem_product.mpr ⟨hi₀, hj₀⟩, ?_⟩
      rw [if_neg hij₀]
      have h1 := hgt i₀ hi₀ j₀ hj₀
      have h2 : 0 < w i₀ * w j₀ := mul_pos hwi₀ hwj₀
      nlinarith
    have hsum := Finset.sum_lt_sum hFle hFlt
    have hGsum : ∑ p ∈ t ×ˢ t, w p.1 * w p.2 * ⟪p.1 - c, p.2 - c⟫ = 0 := by
      rw [Finset.sum_product]
      exact hexp.symm
    have hL : ∑ p ∈ t ×ˢ t,
        (-(r ^ 2 / (n : ℝ)) * (w p.1 * w p.2) +
          (if p.1 = p.2 then w p.1 ^ 2 * (((n : ℝ) + 1) / (n : ℝ) * r ^ 2) else 0)) =
        r ^ 2 / (n : ℝ) * (((n : ℝ) + 1) * S - 1) := by
      rw [Finset.sum_add_distrib]
      have h1 : ∑ p ∈ t ×ˢ t, -(r ^ 2 / (n : ℝ)) * (w p.1 * w p.2) =
          -(r ^ 2 / (n : ℝ)) := by
        rw [Finset.sum_product]
        have h2 : ∀ i ∈ t, ∑ j ∈ t, -(r ^ 2 / (n : ℝ)) * (w i * w j) =
            -(r ^ 2 / (n : ℝ)) * w i := by
          intro i _
          calc ∑ j ∈ t, -(r ^ 2 / (n : ℝ)) * (w i * w j)
              = (-(r ^ 2 / (n : ℝ)) * w i) * ∑ j ∈ t, w j := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun j _ => by ring
            _ = -(r ^ 2 / (n : ℝ)) * w i := by rw [hw1, mul_one]
        rw [Finset.sum_congr rfl h2, ← Finset.mul_sum, hw1, mul_one]
      have h3 : ∑ p ∈ t ×ˢ t,
          (if p.1 = p.2 then w p.1 ^ 2 * (((n : ℝ) + 1) / (n : ℝ) * r ^ 2) else 0) =
          S * (((n : ℝ) + 1) / (n : ℝ) * r ^ 2) := by
        rw [Finset.sum_product]
        have h4 : ∀ i ∈ t,
            ∑ j ∈ t, (if i = j then w i ^ 2 * (((n : ℝ) + 1) / (n : ℝ) * r ^ 2) else 0) =
            w i ^ 2 * (((n : ℝ) + 1) / (n : ℝ) * r ^ 2) := by
          intro i hi
          rw [Finset.sum_ite_eq t i
            (fun _ => w i ^ 2 * (((n : ℝ) + 1) / (n : ℝ) * r ^ 2)), if_pos hi]
        rw [Finset.sum_congr rfl h4, hS, Finset.sum_mul]
      rw [h1, h3]
      field_simp
      ring
    rw [hGsum, hL] at hsum
    have hpos : 0 ≤ r ^ 2 / (n : ℝ) * (((n : ℝ) + 1) * S - 1) :=
      mul_nonneg (by positivity) (by linarith)
    linarith
  · -- all off-diagonal weight products vanish, so `r = 0`: contradiction
    push Not at hpair
    have hoff : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → w i * w j = 0 := by
      intro i hi j hj hij
      rcases eq_or_lt_of_le (hw0 i hi) with h | h
      · rw [← h, zero_mul]
      · have h2 := hpair i hi j hj hij h
        have hj0 : w j = 0 := le_antisymm h2 (hw0 j hj)
        rw [hj0, mul_zero]
    have hP : (0 : ℝ) = S * r ^ 2 := by
      have hterm : ∀ i ∈ t, ∀ j ∈ t, w i * w j * ⟪i - c, j - c⟫ =
          if i = j then w i ^ 2 * r ^ 2 else 0 := by
        intro i hi j hj
        by_cases hij : i = j
        · subst hij
          rw [if_pos rfl, hnorm i hi]
          ring
        · rw [if_neg hij, hoff i hi j hj hij, zero_mul]
      calc (0 : ℝ) = ∑ i ∈ t, ∑ j ∈ t, w i * w j * ⟪i - c, j - c⟫ := hexp
        _ = ∑ i ∈ t, ∑ j ∈ t, (if i = j then w i ^ 2 * r ^ 2 else 0) :=
            Finset.sum_congr rfl fun i hi =>
              Finset.sum_congr rfl fun j hj => hterm i hi j hj
        _ = ∑ i ∈ t, w i ^ 2 * r ^ 2 := Finset.sum_congr rfl fun i hi => by
            rw [Finset.sum_ite_eq t i (fun _ => w i ^ 2 * r ^ 2), if_pos hi]
        _ = S * r ^ 2 := by rw [hS, Finset.sum_mul]
    have hS0 : S = 0 := by
      rcases mul_eq_zero.mp hP.symm with h | h
      · exact h
      · nlinarith
    have hw00 : ∀ i ∈ t, w i = 0 := by
      intro i hi
      have h1 : w i ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (w j)).mp
          (hS ▸ hS0) i hi
      exact pow_eq_zero_iff (two_ne_zero) |>.mp h1
    rw [Finset.sum_eq_zero hw00] at hw1
    norm_num at hw1

end Pair

section Jung

variable {K : Set E}

/-- **Jung's inequality** in arbitrary dimension: a compact set with at least two
points in a space of dimension at most `n` is contained in a closed ball whose radius
`r` satisfies `(2n+2) r² ≤ n (diam K)²`, i.e. `r ≤ diam K · √(n/(2n+2))`. -/
theorem exists_jung_center_of_finrank_le {n : ℕ} (hn : 0 < n) (hK : IsCompact K)
    (hnt : K.Nontrivial) (hrank : finrank ℝ E ≤ n) :
    ∃ (c : E) (r : ℝ), 0 < r ∧ (2 * (n : ℝ) + 2) * r ^ 2 ≤ (n : ℝ) * diam K ^ 2 ∧
      K ⊆ closedBall c r := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hne : K.Nonempty := hnt.nonempty
  obtain ⟨c, hmin⟩ := exists_min_supRadius hK hne
  set r := supRadius K c with hrdef
  have hr : 0 < r := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hnt
    have h1 := dist_le_supRadius hK hx c
    have h2 := dist_le_supRadius hK hy c
    have h3 : 0 < dist x y := dist_pos.mpr hxy
    have h4 := dist_triangle x c y
    have h5 : dist x c = dist c x := dist_comm x c
    linarith
  have hc := center_mem_convexHull_contact hK hne hmin hr
  obtain ⟨x, hxT, y, hyT, hxy⟩ :=
    exists_pair_of_center_mem hn hr (fun x hx => hx.2) hc hrank
  refine ⟨c, r, hr, ?_, fun z hz => mem_closedBall'.mpr (dist_le_supRadius hK hz c)⟩
  have h1 : dist x y ≤ diam K := dist_le_diam_of_mem hK.isBounded hxT.1 hyT.1
  have h2 : dist x y ^ 2 = ‖x - c‖ ^ 2 - 2 * ⟪x - c, y - c⟫ + ‖y - c‖ ^ 2 := by
    have h3 : x - y = (x - c) - (y - c) := by abel
    rw [dist_eq_norm, h3, norm_sub_sq_real]
  have hx2 : ‖x - c‖ = r := by rw [← dist_eq_norm', hxT.2]
  have hy2 : ‖y - c‖ = r := by rw [← dist_eq_norm', hyT.2]
  rw [hx2, hy2] at h2
  have h6 : 2 * r ^ 2 + 2 * (r ^ 2 / (n : ℝ)) ≤ dist x y ^ 2 := by
    rw [h2]
    linarith
  have h7 : dist x y ^ 2 ≤ diam K ^ 2 := by
    nlinarith [diam_nonneg (s := K), dist_nonneg (x := x) (y := y)]
  have h8 : (n : ℝ) * (2 * r ^ 2 + 2 * (r ^ 2 / (n : ℝ))) = (2 * (n : ℝ) + 2) * r ^ 2 := by
    field_simp
  nlinarith
end Jung

section JungTwo

variable {K : Set E}

/-- Jung's inequality in dimension at most `2`, in the form used by the planar Borsuk
development: `3 r² ≤ (diam K)²`. -/
theorem exists_jung_center (hK : IsCompact K) (hnt : K.Nontrivial)
    (hrank : finrank ℝ E ≤ 2) :
    ∃ (c : E) (r : ℝ), 0 < r ∧ 3 * r ^ 2 ≤ diam K ^ 2 ∧ K ⊆ closedBall c r := by
  obtain ⟨c, r, hr, hj, hs⟩ :=
    exists_jung_center_of_finrank_le (by norm_num) hK hnt hrank
  refine ⟨c, r, hr, ?_, hs⟩
  push_cast at hj
  linarith

end JungTwo

end Borsuk

namespace Borsuk

open Complex ComplexConjugate Metric Set

namespace Plane

noncomputable section

/-- The primitive cube root of unity `(-1 + √3 i)/2`. -/
def ζ : ℂ := ⟨-(1 / 2), Real.sqrt 3 / 2⟩

theorem s3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

theorem s3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)

@[simp] theorem ζ_re : ζ.re = -(1 / 2) := rfl

@[simp] theorem ζ_im : ζ.im = Real.sqrt 3 / 2 := rfl

theorem ζ_sq : ζ ^ 2 = ⟨-(1 / 2), -(Real.sqrt 3 / 2)⟩ := by
  rw [sq]
  apply Complex.ext
  · simp only [Complex.mul_re, ζ_re, ζ_im]
    nlinarith [s3_sq]
  · simp only [Complex.mul_im, ζ_re, ζ_im]
    ring

@[simp] theorem ζ_sq_re : (ζ ^ 2).re = -(1 / 2) := by rw [ζ_sq]

@[simp] theorem ζ_sq_im : (ζ ^ 2).im = -(Real.sqrt 3 / 2) := by rw [ζ_sq]

theorem ζ_pow3 : ζ ^ 3 = 1 := by
  have h : ζ ^ 3 = ζ ^ 2 * ζ := by ring
  rw [h, ζ_sq]
  apply Complex.ext
  · simp only [Complex.mul_re, ζ_re, ζ_im, Complex.one_re]
    nlinarith [s3_sq]
  · simp only [Complex.mul_im, ζ_re, ζ_im, Complex.one_im]
    ring

theorem normSq_ζ : normSq ζ = 1 := by
  rw [normSq_apply]
  simp only [ζ_re, ζ_im]
  nlinarith [s3_sq]

theorem norm_ζ : ‖ζ‖ = 1 := by
  have h := Complex.sq_norm ζ
  rw [normSq_ζ] at h
  nlinarith [norm_nonneg ζ]

theorem conj_ζ : (starRingEnd ℂ) ζ = ζ ^ 2 := by
  rw [ζ_sq]
  apply Complex.ext <;> simp

/-- ‖z‖² decomposed into real and imaginary parts. -/
theorem sq_norm_eq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, normSq_apply]
  ring

/-- **Sector cover**: the three closed 120°-sectors around directions `w, wζ, wζ²` cover
the plane. -/
theorem mem_sector_cover (u : ℂ) {w : ℂ} (hw : ‖w‖ = 1) :
    ‖u‖ / 2 ≤ (u * conj w).re ∨ ‖u‖ / 2 ≤ (u * conj (w * ζ)).re ∨
      ‖u‖ / 2 ≤ (u * conj (w * ζ ^ 2)).re := by
  by_contra hno
  push Not at hno
  obtain ⟨h0, h1, h2⟩ := hno
  set p := u * conj w with hp
  have hnp : ‖p‖ = ‖u‖ := by
    rw [hp, norm_mul, RCLike.norm_conj, hw, mul_one]
  set a := p.re with ha
  set b := p.im with hb
  set m := ‖u‖ with hm
  have hm2 : m ^ 2 = a ^ 2 + b ^ 2 := by rw [← hnp, sq_norm_eq, ha, hb]
  have hm0 : 0 ≤ m := hm ▸ norm_nonneg u
  -- expand the three sector values
  have e1 : (u * conj (w * ζ)).re = -(1 / 2) * a + Real.sqrt 3 / 2 * b := by
    rw [map_mul, ← mul_assoc, ← hp, Complex.mul_re, conj_ζ, ζ_sq_re, ζ_sq_im, ha, hb]
    ring
  have e2 : (u * conj (w * ζ ^ 2)).re = -(1 / 2) * a - Real.sqrt 3 / 2 * b := by
    have hcc : (starRingEnd ℂ) (ζ ^ 2) = ζ := by
      have h3 := ζ_pow3
      calc (starRingEnd ℂ) (ζ ^ 2) = ((starRingEnd ℂ) ζ) ^ 2 := by rw [map_pow]
        _ = ζ ^ 4 := by rw [conj_ζ]; ring
        _ = ζ ^ 3 * ζ := by ring
        _ = ζ := by rw [h3, one_mul]
    rw [map_mul, ← mul_assoc, ← hp, Complex.mul_re, hcc, ζ_re, ζ_im, ha, hb]
    ring
  rw [e1] at h1
  rw [e2] at h2
  -- now a < m/2, -a/2 + √3 b/2 < m/2, -a/2 - √3 b/2 < m/2, m² = a² + b², m ≥ 0
  have k1 : 0 < m + a + Real.sqrt 3 * b := by nlinarith
  have k2 : 0 < m + a - Real.sqrt 3 * b := by nlinarith
  nlinarith [mul_pos k1 k2, s3_sq, hm2, hm0]

set_option maxHeartbeats 800000 in
-- the chain of `nlinarith` calls below needs more than the default budget
/-- **Rigidity of far pairs in a sector**: two points of a closed sector at distance at
most `r` from the apex whose mutual inner product is at most `-r²/2` are conjugate,
lie on the circle of radius `r`, and sit on the two edges of the sector. -/
theorem sector_pair_eq {p q : ℂ} {r : ℝ} (hr : 0 < r) (hpr : ‖p‖ ≤ r) (hqr : ‖q‖ ≤ r)
    (hpsec : ‖p‖ / 2 ≤ p.re) (hqsec : ‖q‖ / 2 ≤ q.re)
    (hfar : (p * conj q).re ≤ -(r ^ 2 / 2)) :
    q = conj p ∧ ‖p‖ = r ∧ p.re = r / 2 := by
  set ap := p.re with hap
  set bp := p.im with hbp
  set aq := q.re with haq
  set bq := q.im with hbq
  set np := ‖p‖ with hnp
  set nq := ‖q‖ with hnq
  have hp2 : np ^ 2 = ap ^ 2 + bp ^ 2 := by rw [hnp, sq_norm_eq, hap, hbp]
  have hq2 : nq ^ 2 = aq ^ 2 + bq ^ 2 := by rw [hnq, sq_norm_eq, haq, hbq]
  have hnp0 : 0 ≤ np := hnp ▸ norm_nonneg p
  have hnq0 : 0 ≤ nq := hnq ▸ norm_nonneg q
  have hre : (p * conj q).re = ap * aq + bp * bq := by
    rw [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [hre] at hfar
  have hap0 : 0 ≤ ap := le_trans (by positivity) hpsec
  have haq0 : 0 ≤ aq := le_trans (by positivity) hqsec
  have haa : np * nq / 4 ≤ ap * aq := by nlinarith
  have hbsq : (bp * bq) ^ 2 = (np ^ 2 - ap ^ 2) * (nq ^ 2 - aq ^ 2) := by
    rw [hp2, hq2]
    ring
  -- Stage A: the radii are forced to equal r
  have hXneg : bp * bq ≤ -(r ^ 2 / 2 + np * nq / 4) := by linarith
  have hX0 : 0 ≤ r ^ 2 / 2 + np * nq / 4 := by nlinarith [mul_nonneg hnp0 hnq0]
  have hsq1 : (r ^ 2 / 2 + np * nq / 4) ^ 2 ≤ (bp * bq) ^ 2 := by
    have h := sq_le_sq' (a := r ^ 2 / 2 + np * nq / 4) (b := -(bp * bq))
      (by linarith) (by linarith)
    rwa [neg_sq] at h
  have hsq2 : (bp * bq) ^ 2 ≤ 9 / 16 * (np * nq) ^ 2 := by
    have h1 : np ^ 2 - ap ^ 2 ≤ 3 / 4 * np ^ 2 := by nlinarith
    have h2 : nq ^ 2 - aq ^ 2 ≤ 3 / 4 * nq ^ 2 := by nlinarith
    have h3 : 0 ≤ nq ^ 2 - aq ^ 2 := by nlinarith [sq_nonneg bq]
    have h4 : 0 ≤ np ^ 2 - ap ^ 2 := by nlinarith [sq_nonneg bp]
    calc (bp * bq) ^ 2 = (np ^ 2 - ap ^ 2) * (nq ^ 2 - aq ^ 2) := hbsq
      _ ≤ (3 / 4 * np ^ 2) * (3 / 4 * nq ^ 2) := by
          exact mul_le_mul h1 h2 h3 (by positivity)
      _ = 9 / 16 * (np * nq) ^ 2 := by ring
  have hprod_ge : r ^ 2 ≤ np * nq := by
    have hX0' : 0 ≤ np * nq := mul_nonneg hnp0 hnq0
    nlinarith [hsq1, hsq2, hX0, hX0']
  have hnq_ge : r ≤ nq := by
    nlinarith [mul_le_mul_of_nonneg_right hpr hnq0]
  have hnqr : nq = r := le_antisymm hqr hnq_ge
  have hnp_ge : r ≤ np := by
    nlinarith [mul_le_mul_of_nonneg_left hqr hnp0]
  have hnpr : np = r := le_antisymm hpr hnp_ge
  -- Stage B: the sector conditions now read r/2 ≤ ap, aq
  have hap2 : r / 2 ≤ ap := by rw [← hnpr]; exact hpsec
  have haq2 : r / 2 ≤ aq := by rw [← hnqr]; exact hqsec
  have hb2 : (r ^ 2 / 2 + ap * aq) ^ 2 ≤ (r ^ 2 - ap ^ 2) * (r ^ 2 - aq ^ 2) := by
    have hXneg' : bp * bq ≤ -(r ^ 2 / 2 + ap * aq) := by linarith
    have hX0' : 0 ≤ r ^ 2 / 2 + ap * aq := by nlinarith [mul_nonneg hap0 haq0]
    have hsq' : (r ^ 2 / 2 + ap * aq) ^ 2 ≤ (bp * bq) ^ 2 := by
      have h := sq_le_sq' (a := r ^ 2 / 2 + ap * aq) (b := -(bp * bq))
        (by linarith) (by linarith)
      rwa [neg_sq] at h
    calc (r ^ 2 / 2 + ap * aq) ^ 2 ≤ (bp * bq) ^ 2 := hsq'
      _ = (np ^ 2 - ap ^ 2) * (nq ^ 2 - aq ^ 2) := hbsq
      _ = (r ^ 2 - ap ^ 2) * (r ^ 2 - aq ^ 2) := by rw [hnpr, hnqr]
  -- expanding: the (ap·aq)² terms cancel, leaving a linear bound
  have hsum : ap * aq + ap ^ 2 + aq ^ 2 ≤ 3 / 4 * r ^ 2 := by
    have h5 : r ^ 2 * (ap * aq + ap ^ 2 + aq ^ 2) ≤ r ^ 2 * (3 / 4 * r ^ 2) := by
      nlinarith [hb2]
    exact le_of_mul_le_mul_left h5 (by positivity)
  have hap_le : ap ≤ r / 2 := by nlinarith [hsum, hap2, haq2]
  have hapr : ap = r / 2 := le_antisymm hap_le hap2
  have haq_le : aq ≤ r / 2 := by nlinarith [hsum, hap2, haq2]
  have haqr : aq = r / 2 := le_antisymm haq_le haq2
  -- Stage C: the imaginary parts are opposite
  have hbps : bp ^ 2 = 3 / 4 * r ^ 2 := by nlinarith [hp2]
  have hbqs : bq ^ 2 = 3 / 4 * r ^ 2 := by nlinarith [hq2]
  have hbpbq : bp * bq = -(3 / 4 * r ^ 2) := by
    have hup : bp * bq ≤ -(3 / 4 * r ^ 2) := by nlinarith
    have hdn : -(3 / 4 * r ^ 2) ≤ bp * bq := by nlinarith [sq_nonneg (bp + bq)]
    linarith
  have hbsum : (bp + bq) ^ 2 = 0 := by
    have h0 : (bp + bq) ^ 2 ≤ 0 := by nlinarith
    exact le_antisymm h0 (sq_nonneg _)
  have hbqe : bq = -bp := by
    have h1 : bp + bq = 0 := by
      exact pow_eq_zero_iff two_ne_zero |>.mp hbsum
    linarith
  refine ⟨?_, hnpr, hapr⟩
  apply Complex.ext
  · rw [Complex.conj_re, ← haq, ← hap, haqr, hapr]
  · rw [Complex.conj_im, ← hbq, ← hbp, hbqe]

/-- Two contact-circle points at mutual inner product exactly `-r²/2` differ by `ζ`
or `ζ²`. -/
theorem ratio_of_far_pair {u v : ℂ} {r : ℝ} (hr : 0 < r) (hu : ‖u‖ = r) (hv : ‖v‖ = r)
    (hre : (v * conj u).re = -(r ^ 2 / 2)) : v = ζ * u ∨ v = ζ ^ 2 * u := by
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu
    exact absurd hu.symm hr.ne'
  set w := v / u with hw
  have hvw : v = w * u := by rw [hw, div_mul_cancel₀ _ hu0]
  have hnw : ‖w‖ = 1 := by
    rw [hw, norm_div, hu, hv, div_self hr.ne']
  have hwre : w.re = -(1 / 2) := by
    have h1 : v * conj u = w * ((normSq u : ℝ) : ℂ) := by
      calc v * conj u = w * (u * conj u) := by rw [hvw]; ring
        _ = w * ((normSq u : ℝ) : ℂ) := by rw [Complex.mul_conj]
    have h2 : normSq u = r ^ 2 := by rw [normSq_eq_norm_sq, hu]
    rw [h1, h2] at hre
    have h3 : (w * ((r ^ 2 : ℝ) : ℂ)).re = w.re * r ^ 2 := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [h3] at hre
    have h4 : w.re * r ^ 2 = -(1 / 2) * r ^ 2 := by linarith
    exact mul_right_cancel₀ (by positivity : (r : ℝ) ^ 2 ≠ 0) h4
  have hwim : w.im ^ 2 = 3 / 4 := by
    have h1 : w.re ^ 2 + w.im ^ 2 = 1 := by
      rw [← sq_norm_eq, hnw]
      norm_num
    rw [hwre] at h1
    nlinarith
  have hfac : (w.im - Real.sqrt 3 / 2) * (w.im + Real.sqrt 3 / 2) = 0 := by
    nlinarith [s3_sq]
  rcases mul_eq_zero.mp hfac with h | h
  · left
    rw [hvw]
    congr 1
    apply Complex.ext
    · rw [hwre, ζ_re]
    · rw [ζ_im]
      linarith
  · right
    rw [hvw]
    congr 1
    apply Complex.ext
    · rw [hwre, ζ_sq_re]
    · rw [ζ_sq_im]
      linarith

/-- **The cube-root trap**: a unit complex number `w` with
`w.re, (ζw).re, (ζ²w).re ≥ -1/2` is a cube root of unity. -/
theorem cube_root_trap {w : ℂ} (hw : ‖w‖ = 1) (h0 : -(1 / 2) ≤ w.re)
    (h1 : -(1 / 2) ≤ (ζ * w).re) (h2 : -(1 / 2) ≤ (ζ ^ 2 * w).re) :
    w = 1 ∨ w = ζ ∨ w = ζ ^ 2 := by
  set x := w.re with hx
  set y := w.im with hy
  have hxy : x ^ 2 + y ^ 2 = 1 := by
    rw [hx, hy, ← sq_norm_eq, hw]
    norm_num
  have e1 : (ζ * w).re = -(1 / 2) * x - Real.sqrt 3 / 2 * y := by
    rw [Complex.mul_re, ζ_re, ζ_im, ← hx, ← hy]
  have e2 : (ζ ^ 2 * w).re = -(1 / 2) * x + Real.sqrt 3 / 2 * y := by
    rw [Complex.mul_re, ζ_sq_re, ζ_sq_im, ← hx, ← hy]
    ring
  rw [e1] at h1
  rw [e2] at h2
  have hxle : x ≤ 1 := by nlinarith
  have hkey : (1 - x) * (2 + 4 * x) ≤ 0 := by
    have k1 : Real.sqrt 3 * y ≤ 1 - x := by nlinarith [s3_pos]
    have k2 : -(1 - x) ≤ Real.sqrt 3 * y := by nlinarith [s3_pos]
    nlinarith [s3_sq, sq_nonneg (Real.sqrt 3 * y)]
  have hx2 : -(1 / 2) ≤ x := h0
  rcases eq_or_lt_of_le hx2 with heq | hlt
  · have hyv : y ^ 2 = 3 / 4 := by nlinarith
    have hfac : (y - Real.sqrt 3 / 2) * (y + Real.sqrt 3 / 2) = 0 := by
      nlinarith [s3_sq]
    rcases mul_eq_zero.mp hfac with h | h
    · right; left
      apply Complex.ext
      · rw [← hx, ← heq, ζ_re]
      · rw [← hy, ζ_im]
        linarith
    · right; right
      apply Complex.ext
      · rw [← hx, ← heq, ζ_sq_re]
      · rw [← hy, ζ_sq_im]
        linarith
  · have hx1 : x = 1 := by nlinarith
    left
    apply Complex.ext
    · rw [← hx, hx1, Complex.one_re]
    · rw [← hy, Complex.one_im]
      have hy0 : y ^ 2 = 0 := by nlinarith
      exact pow_eq_zero_iff two_ne_zero |>.mp hy0

/-- Powers of `ζ` cycle with period three. -/
theorem ζ_pow4 : ζ ^ 4 = ζ := by
  have h : ζ ^ 4 = ζ ^ 3 * ζ := by ring
  rw [h, ζ_pow3, one_mul]

theorem ζ_pow5 : ζ ^ 5 = ζ ^ 2 := by
  have h : ζ ^ 5 = ζ ^ 3 * ζ ^ 2 := by ring
  rw [h, ζ_pow3, one_mul]

theorem ζ_pow6 : ζ ^ 6 = 1 := by
  have h : ζ ^ 6 = ζ ^ 3 * ζ ^ 3 := by ring
  rw [h, ζ_pow3, one_mul]

theorem ζ_ne_zero : ζ ≠ 0 := by
  intro h
  have h1 := norm_ζ
  rw [h, norm_zero] at h1
  norm_num at h1

theorem re_mul_conj_comm (z w : ℂ) : (z * conj w).re = (w * conj z).re := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- Squared distance in `ℂ` via the real inner product. -/
theorem sq_dist_eq (A B : ℂ) : ‖A - B‖ ^ 2 = ‖A‖ ^ 2 + ‖B‖ ^ 2 - 2 * (A * conj B).re := by
  rw [sq_norm_eq, sq_norm_eq, sq_norm_eq, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- Rewriting `(z * conj u).re` through the ratio `z / u` when `‖u‖ = r`. -/
theorem re_mul_conj_ratio {u : ℂ} {r : ℝ} (hu : ‖u‖ = r) (hu0 : u ≠ 0) (z : ℂ) :
    (z * conj u).re = (z / u).re * r ^ 2 := by
  have h1 : z * conj u = z / u * ((normSq u : ℝ) : ℂ) := by
    calc z * conj u = z / u * (u * conj u) := by
          field_simp
      _ = z / u * ((normSq u : ℝ) : ℂ) := by rw [Complex.mul_conj]
  rw [h1, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, normSq_eq_norm_sq, hu]
  ring

set_option maxHeartbeats 1600000 in
-- twelve case leaves with `linear_combination` batteries need a large budget
/-- **Products of far pairs lie in a single `ζ`-orbit**: given two contact-circle pairs
at mutual inner product `-r²/2` whose four cross inner products are at least `-r²/2`,
the products `u·v` and `u₀·v₀` differ by a power of `ζ`. -/
theorem product_orbit {u₀ v₀ u v : ℂ} {r : ℝ} (hr : 0 < r)
    (h₀u : ‖u₀‖ = r) (h₀v : ‖v₀‖ = r) (hu : ‖u‖ = r) (hv : ‖v‖ = r)
    (hre₀ : (v₀ * conj u₀).re = -(r ^ 2 / 2)) (hre : (v * conj u).re = -(r ^ 2 / 2))
    (b1 : -(r ^ 2 / 2) ≤ (u * conj u₀).re) (b2 : -(r ^ 2 / 2) ≤ (v * conj u₀).re)
    (b3 : -(r ^ 2 / 2) ≤ (u * conj v₀).re) (b4 : -(r ^ 2 / 2) ≤ (v * conj v₀).re) :
    u * v = u₀ * v₀ ∨ u * v = ζ * (u₀ * v₀) ∨ u * v = ζ ^ 2 * (u₀ * v₀) := by
  have hu₀0 : u₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at h₀u
    exact absurd h₀u.symm hr.ne'
  have hv₀0 : v₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at h₀v
    exact absurd h₀v.symm hr.ne'
  have hr2 : (0 : ℝ) < r ^ 2 := by positivity
  have hζ0 : ζ ≠ 0 := ζ_ne_zero
  have ha := ratio_of_far_pair hr h₀u h₀v hre₀
  have hb := ratio_of_far_pair hr hu hv hre
  obtain ⟨w, hwdef, huw, hnw⟩ : ∃ w : ℂ, w = u / u₀ ∧ u = w * u₀ ∧ ‖w‖ = 1 :=
    ⟨u / u₀, rfl, (div_mul_cancel₀ u hu₀0).symm,
      by rw [norm_div, hu, h₀u, div_self hr.ne']⟩
  have htrans : ∀ z : ℂ, -(r ^ 2 / 2) ≤ (z * conj u₀).re → -(1 / 2) ≤ (z / u₀).re := by
    intro z hz
    rw [re_mul_conj_ratio h₀u hu₀0 z] at hz
    nlinarith
  have htrans' : ∀ z : ℂ, -(r ^ 2 / 2) ≤ (z * conj v₀).re → -(1 / 2) ≤ (z / v₀).re := by
    intro z hz
    rw [re_mul_conj_ratio h₀v hv₀0 z] at hz
    nlinarith
  have c1 : -(1 / 2) ≤ w.re := by
    have h := htrans u b1
    rwa [← hwdef] at h
  have key : w = 1 ∨ w = ζ ∨ w = ζ ^ 2 := by
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · -- v₀ = ζ u₀, v = ζ u
      refine cube_root_trap hnw c1 ?_ ?_
      · have h := htrans v b2
        have hid : v / u₀ = ζ * w := by
          rw [hb, huw]
          field_simp
        rwa [hid] at h
      · have h := htrans' u b3
        have hid : u / v₀ = ζ ^ 2 * w := by
          rw [ha, huw]
          field_simp
          all_goals ring_nf
          all_goals try simp only [ζ_pow3, mul_one]
        rwa [hid] at h
    · -- v₀ = ζ u₀, v = ζ² u
      refine cube_root_trap hnw c1 ?_ ?_
      · have h := htrans' v b4
        have hid : v / v₀ = ζ * w := by
          rw [hb, ha, huw]
          field_simp
        rwa [hid] at h
      · have h := htrans' u b3
        have hid : u / v₀ = ζ ^ 2 * w := by
          rw [ha, huw]
          field_simp
          all_goals ring_nf
          all_goals try simp only [ζ_pow3, mul_one]
        rwa [hid] at h
    · -- v₀ = ζ² u₀, v = ζ u
      refine cube_root_trap hnw c1 ?_ ?_
      · have h := htrans v b2
        have hid : v / u₀ = ζ * w := by
          rw [hb, huw]
          field_simp
        rwa [hid] at h
      · have h := htrans' v b4
        have hid : v / v₀ = ζ ^ 2 * w := by
          rw [hb, ha, huw]
          field_simp
          all_goals ring_nf
          all_goals try simp only [ζ_pow3, one_mul]
        rwa [hid] at h
    · -- v₀ = ζ² u₀, v = ζ² u
      refine cube_root_trap hnw c1 ?_ ?_
      · have h := htrans' u b3
        have hid : u / v₀ = ζ * w := by
          rw [ha, huw]
          field_simp
          all_goals ring_nf
          all_goals try simp only [ζ_pow3, mul_one]
        rwa [hid] at h
      · have h := htrans v b2
        have hid : v / u₀ = ζ ^ 2 * w := by
          rw [hb, huw]
          field_simp
        rwa [hid] at h
  -- assemble the product in each of the twelve leaves
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · rcases key with hk | hk | hk
    · refine Or.inl ?_
      rw [hb, huw, ha, hk]
      ring
    · refine Or.inr (Or.inr ?_)
      rw [hb, huw, ha, hk]
      ring
    · refine Or.inr (Or.inl ?_)
      rw [hb, huw, ha, hk]
      ring_nf
      simp only [ζ_pow5]
      try ring1
  · rcases key with hk | hk | hk
    · refine Or.inr (Or.inl ?_)
      rw [hb, huw, ha, hk]
      ring
    · refine Or.inl ?_
      rw [hb, huw, ha, hk]
      ring_nf
      simp only [ζ_pow4]
      try ring1
    · refine Or.inr (Or.inr ?_)
      rw [hb, huw, ha, hk]
      ring_nf
      simp only [ζ_pow3, ζ_pow6, one_mul]
      try ring1
  · rcases key with hk | hk | hk
    · refine Or.inr (Or.inr ?_)
      rw [hb, huw, ha, hk]
      ring_nf
      simp only [ζ_pow4]
      try ring1
    · refine Or.inr (Or.inl ?_)
      rw [hb, huw, ha, hk]
      ring
    · refine Or.inl ?_
      rw [hb, huw, ha, hk]
      ring_nf
      simp only [ζ_pow5]
      try ring1
  · rcases key with hk | hk | hk
    · refine Or.inl ?_
      rw [hb, huw, ha, hk]
      ring
    · refine Or.inr (Or.inr ?_)
      rw [hb, huw, ha, hk]
      ring
    · refine Or.inr (Or.inl ?_)
      rw [hb, huw, ha, hk]
      ring_nf
      simp only [ζ_pow3, ζ_pow6, one_mul]
      try ring1

end

end Plane

end Borsuk

namespace Borsuk

open Complex ComplexConjugate Metric Set Module Bornology

namespace Plane

noncomputable section

/-- On a compact set the diameter is attained. -/
theorem exists_dist_eq_diam {α : Type*} [PseudoMetricSpace α] {K : Set α}
    (hK : IsCompact K) (hne : K.Nonempty) : ∃ x ∈ K, ∃ y ∈ K, dist x y = diam K := by
  obtain ⟨⟨x, y⟩, hxy, hmax⟩ := (hK.prod hK).exists_isMaxOn (hne.prod hne)
    continuous_dist.continuousOn
  rw [Set.mem_prod] at hxy
  refine ⟨x, hxy.1, y, hxy.2, le_antisymm
    (dist_le_diam_of_mem hK.isBounded hxy.1 hxy.2) ?_⟩
  refine diam_le_of_forall_dist_le dist_nonneg fun a ha b hb => ?_
  exact hmax (Set.mk_mem_prod ha hb)

/-- The primitive twelfth root of unity `e^{iπ/6}`; its powers `1, μ, μ², μ³` are the
four candidate sector frames. -/
def μ : ℂ := ⟨Real.sqrt 3 / 2, 1/2⟩

@[simp] theorem μ_re : μ.re = Real.sqrt 3 / 2 := rfl

@[simp] theorem μ_im : μ.im = 1/2 := rfl

theorem norm_μ : ‖μ‖ = 1 := by
  have h : ‖μ‖ ^ 2 = 1 := by
    rw [sq_norm_eq, μ_re, μ_im]
    nlinarith [s3_sq]
  nlinarith [norm_nonneg μ]

theorem μ_sq : μ ^ 2 = ⟨1/2, Real.sqrt 3 / 2⟩ := by
  rw [sq]
  apply Complex.ext
  · simp only [Complex.mul_re, μ_re, μ_im]
    nlinarith [s3_sq]
  · simp only [Complex.mul_im, μ_re, μ_im]
    ring

theorem μ_pow4 : (μ ^ 2) ^ 2 = ζ := by
  rw [μ_sq]
  apply Complex.ext
  · rw [ζ_re, sq]
    simp only [Complex.mul_re]
    nlinarith [s3_sq]
  · rw [ζ_im, sq]
    simp only [Complex.mul_im]
    ring

theorem μ_pow3 : μ ^ 3 = Complex.I := by
  have h : μ ^ 3 = μ ^ 2 * μ := by ring
  rw [h, μ_sq]
  apply Complex.ext
  · simp only [Complex.mul_re, μ_re, μ_im, Complex.I_re]
    nlinarith [s3_sq]
  · simp only [Complex.mul_im, μ_re, μ_im, Complex.I_im]
    nlinarith [s3_sq]

theorem μ_pow6 : (μ ^ 3) ^ 2 = -1 := by
  rw [μ_pow3, Complex.I_sq]

/-- **The three-sector decomposition**: every compact set with at least two points in
the plane is covered by three sets of strictly smaller diameter. -/
theorem hasBorsukCover_three_of_isCompact {K : Set ℂ} (hK : IsCompact K)
    (hnt : K.Nontrivial) : HasBorsukCover 3 K := by
  classical
  obtain ⟨c, r, hr, hjung, hsub⟩ := exists_jung_center hK hnt
    (le_of_eq Complex.finrank_real_complex)
  set D := diam K with hD_def
  have hD : 0 < D := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hnt
    exact lt_of_lt_of_le (dist_pos.mpr hxy) (dist_le_diam_of_mem hK.isBounded hx hy)
  have hrad : ∀ x ∈ K, ‖x - c‖ ≤ r := fun x hx => by
    have h := hsub hx
    rwa [mem_closedBall, dist_eq_norm] at h
  have hre_formula : ∀ x y : ℂ, ((x - c) * conj (y - c)).re =
      (‖x - c‖ ^ 2 + ‖y - c‖ ^ 2 - dist x y ^ 2) / 2 := by
    intro x y
    have h := sq_dist_eq (x - c) (y - c)
    have h2 : (x - c) - (y - c) = x - y := by ring
    rw [h2, ← dist_eq_norm] at h
    linarith
  have hr2C : ((r ^ 2 : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  -- choice of the sector frame
  obtain ⟨ω, hω1, hωblock⟩ : ∃ ω : ℂ, ‖ω‖ = 1 ∧
      ∀ x y : ℂ, x ∈ K → y ∈ K → ‖x - c‖ = r → ‖y - c‖ = r →
        ((y - c) * conj (x - c)).re = -(r ^ 2 / 2) → 3 * r ^ 2 = D ^ 2 →
        ∀ k : ℕ, k < 3 → (x - c) * (y - c) ≠ ((r ^ 2 : ℝ) : ℂ) * (ω * ζ ^ k) ^ 2 := by
    rcases em (3 * r ^ 2 = D ^ 2) with hDeq | hDne
    · rcases em (∃ x₀ y₀ : ℂ, x₀ ∈ K ∧ y₀ ∈ K ∧ ‖x₀ - c‖ = r ∧ ‖y₀ - c‖ = r ∧
        ((y₀ - c) * conj (x₀ - c)).re = -(r ^ 2 / 2)) with hbad | hnobad
      · obtain ⟨x₀, y₀, hx₀K, hy₀K, hx₀r, hy₀r, h₀re⟩ := hbad
        set P₀ := (x₀ - c) * (y₀ - c) with hP₀
        -- every bad pair has product in the ζ-orbit of P₀
        have hcross : ∀ z z' : ℂ, z ∈ K → z' ∈ K → ‖z - c‖ = r → ‖z' - c‖ = r →
            -(r ^ 2 / 2) ≤ ((z - c) * conj (z' - c)).re := by
          intro z z' hz hz' hzr hz'r
          rw [hre_formula z z', hzr, hz'r]
          have hd := dist_le_diam_of_mem hK.isBounded hz hz'
          have hd0 : (0 : ℝ) ≤ dist z z' := dist_nonneg
          nlinarith
        have horbit : ∀ x y : ℂ, x ∈ K → y ∈ K → ‖x - c‖ = r → ‖y - c‖ = r →
            ((y - c) * conj (x - c)).re = -(r ^ 2 / 2) →
            (x - c) * (y - c) = P₀ ∨ (x - c) * (y - c) = ζ * P₀ ∨
              (x - c) * (y - c) = ζ ^ 2 * P₀ := by
          intro x y hxK hyK hxr hyr hxyre
          exact product_orbit hr hx₀r hy₀r hxr hyr h₀re hxyre
            (hcross x x₀ hxK hx₀K hxr hx₀r) (hcross y x₀ hyK hx₀K hyr hx₀r)
            (hcross x y₀ hxK hy₀K hxr hy₀r) (hcross y y₀ hyK hy₀K hyr hy₀r)
        -- shifting the orbit by ζ
        have horb_shift : ∀ Q : ℂ, (Q = P₀ ∨ Q = ζ * P₀ ∨ Q = ζ ^ 2 * P₀) →
            (Q * ζ = P₀ ∨ Q * ζ = ζ * P₀ ∨ Q * ζ = ζ ^ 2 * P₀) := by
          rintro Q (rfl | rfl | rfl)
          · right; left; ring
          · right; right; ring
          · left; linear_combination P₀ * ζ_pow3
        -- a good frame: r²ω² avoids the orbit
        have hgood : ∃ ω : ℂ, ‖ω‖ = 1 ∧
            ¬(((r ^ 2 : ℝ) : ℂ) * ω ^ 2 = P₀ ∨ ((r ^ 2 : ℝ) : ℂ) * ω ^ 2 = ζ * P₀ ∨
              ((r ^ 2 : ℝ) : ℂ) * ω ^ 2 = ζ ^ 2 * P₀) := by
          by_cases g0 : ((r ^ 2 : ℝ) : ℂ) * 1 ^ 2 = P₀ ∨
              ((r ^ 2 : ℝ) : ℂ) * 1 ^ 2 = ζ * P₀ ∨ ((r ^ 2 : ℝ) : ℂ) * 1 ^ 2 = ζ ^ 2 * P₀
          swap
          · exact ⟨1, norm_one, g0⟩
          by_cases g1 : ((r ^ 2 : ℝ) : ℂ) * μ ^ 2 = P₀ ∨
              ((r ^ 2 : ℝ) : ℂ) * μ ^ 2 = ζ * P₀ ∨ ((r ^ 2 : ℝ) : ℂ) * μ ^ 2 = ζ ^ 2 * P₀
          swap
          · exact ⟨μ, norm_μ, g1⟩
          by_cases g2 : ((r ^ 2 : ℝ) : ℂ) * (μ ^ 2) ^ 2 = P₀ ∨
              ((r ^ 2 : ℝ) : ℂ) * (μ ^ 2) ^ 2 = ζ * P₀ ∨
              ((r ^ 2 : ℝ) : ℂ) * (μ ^ 2) ^ 2 = ζ ^ 2 * P₀
          swap
          · exact ⟨μ ^ 2, by rw [norm_pow, norm_μ, one_pow], g2⟩
          by_cases g3 : ((r ^ 2 : ℝ) : ℂ) * (μ ^ 3) ^ 2 = P₀ ∨
              ((r ^ 2 : ℝ) : ℂ) * (μ ^ 3) ^ 2 = ζ * P₀ ∨
              ((r ^ 2 : ℝ) : ℂ) * (μ ^ 3) ^ 2 = ζ ^ 2 * P₀
          swap
          · exact ⟨μ ^ 3, by rw [norm_pow, norm_μ, one_pow], g3⟩
          -- all four squares in a three-element set: contradiction by cardinality
          exfalso
          set S3 : Finset ℂ := {P₀, ζ * P₀, ζ ^ 2 * P₀} with hS3
          have hmem : ∀ Q : ℂ, (Q = P₀ ∨ Q = ζ * P₀ ∨ Q = ζ ^ 2 * P₀) → Q ∈ S3 := by
            rintro Q (rfl | rfl | rfl) <;> simp [hS3]
          -- the four squares, in explicit coordinates
          have e1 : ((r ^ 2 : ℝ) : ℂ) * 1 ^ 2 = ((r ^ 2 : ℝ) : ℂ) * 1 := by norm_num
          have e2 : ((r ^ 2 : ℝ) : ℂ) * (μ ^ 2) ^ 2 = ((r ^ 2 : ℝ) : ℂ) * ζ := by
            rw [μ_pow4]
          have e3 : ((r ^ 2 : ℝ) : ℂ) * (μ ^ 3) ^ 2 = ((r ^ 2 : ℝ) : ℂ) * (-1) := by
            rw [μ_pow6]
          have hd01 : (1 : ℂ) ≠ μ ^ 2 := by
            rw [μ_sq]
            intro h
            have h1 := congrArg Complex.re h
            simp only [Complex.one_re] at h1
            norm_num at h1
          have hd02 : (1 : ℂ) ≠ ζ := by
            intro h
            have h1 := congrArg Complex.re h
            rw [Complex.one_re, ζ_re] at h1
            norm_num at h1
          have hd03 : (1 : ℂ) ≠ -1 := by
            intro h
            have := congrArg Complex.re h
            simp at this
            norm_num at this
          have hd12 : μ ^ 2 ≠ ζ := by
            rw [μ_sq]
            intro h
            have h1 := congrArg Complex.re h
            rw [ζ_re] at h1
            norm_num at h1
          have hd13 : μ ^ 2 ≠ -1 := by
            rw [μ_sq]
            intro h
            have h1 := congrArg Complex.im h
            simp only [Complex.neg_im, Complex.one_im, neg_zero] at h1
            nlinarith [s3_pos]
          have hd23 : ζ ≠ -1 := by
            intro h
            have h1 := congrArg Complex.im h
            rw [ζ_im] at h1
            simp only [Complex.neg_im, Complex.one_im, neg_zero] at h1
            nlinarith [s3_pos]
          have hmul : ∀ a b : ℂ, a ≠ b →
              ((r ^ 2 : ℝ) : ℂ) * a ≠ ((r ^ 2 : ℝ) : ℂ) * b := fun a b hab h =>
            hab (mul_left_cancel₀ hr2C h)
          set S4 : Finset ℂ := {((r ^ 2 : ℝ) : ℂ) * 1, ((r ^ 2 : ℝ) : ℂ) * μ ^ 2,
            ((r ^ 2 : ℝ) : ℂ) * ζ, ((r ^ 2 : ℝ) : ℂ) * (-1)} with hS4
          have hsub4 : S4 ⊆ S3 := by
            intro q hq
            simp only [hS4, Finset.mem_insert, Finset.mem_singleton] at hq
            rcases hq with rfl | rfl | rfl | rfl
            · exact hmem _ (by rw [← e1] at *; exact e1 ▸ g0)
            · exact hmem _ g1
            · exact hmem _ (e2 ▸ g2)
            · exact hmem _ (e3 ▸ g3)
          have h3card : S3.card ≤ 3 := by
            refine le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ ?_)
            refine le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ ?_)
            simp
          have h4card : S4.card = 4 := by
            rw [hS4]
            rw [Finset.card_insert_of_notMem (by
              simp only [Finset.mem_insert, Finset.mem_singleton]
              push Not
              exact ⟨hmul _ _ hd01, hmul _ _ hd02, hmul _ _ hd03⟩)]
            rw [Finset.card_insert_of_notMem (by
              simp only [Finset.mem_insert, Finset.mem_singleton]
              push Not
              exact ⟨hmul _ _ hd12, hmul _ _ hd13⟩)]
            rw [Finset.card_insert_of_notMem (by
              simp only [Finset.mem_singleton]
              exact hmul _ _ hd23)]
            simp
          have := Finset.card_le_card hsub4
          omega
        obtain ⟨ω, hω1, hωgood⟩ := hgood
        refine ⟨ω, hω1, fun x y hxK hyK hxr hyr hxyre _ k hk heq => ?_⟩
        have horb := horbit x y hxK hyK hxr hyr hxyre
        rw [heq] at horb
        -- reduce r²(ωζᵏ)² to r²ω² inside the orbit
        have hexp : ((r ^ 2 : ℝ) : ℂ) * (ω * ζ ^ k) ^ 2 =
            ((r ^ 2 : ℝ) : ℂ) * ω ^ 2 * (ζ ^ k) ^ 2 := by ring
        rw [hexp] at horb
        interval_cases k
        · rw [pow_zero, one_pow, mul_one] at horb
          exact hωgood horb
        · rw [pow_one] at horb
          have h1 := horb_shift _ horb
          have h2 : ((r ^ 2 : ℝ) : ℂ) * ω ^ 2 * ζ ^ 2 * ζ = ((r ^ 2 : ℝ) : ℂ) * ω ^ 2 := by
            linear_combination (((r ^ 2 : ℝ) : ℂ) * ω ^ 2) * ζ_pow3
          rw [h2] at h1
          exact hωgood h1
        · have h0 : ((r ^ 2 : ℝ) : ℂ) * ω ^ 2 * (ζ ^ 2) ^ 2 =
              ((r ^ 2 : ℝ) : ℂ) * ω ^ 2 * ζ ^ 2 * ζ ^ 2 := by ring
          rw [h0] at horb
          have h1 := horb_shift _ (horb_shift _ horb)
          have h2 : ((r ^ 2 : ℝ) : ℂ) * ω ^ 2 * ζ ^ 2 * ζ ^ 2 * ζ * ζ =
              ((r ^ 2 : ℝ) : ℂ) * ω ^ 2 * ζ ^ 3 * ζ ^ 3 := by ring
          rw [h2] at h1
          have h3 : ((r ^ 2 : ℝ) : ℂ) * ω ^ 2 * ζ ^ 3 * ζ ^ 3 =
              ((r ^ 2 : ℝ) : ℂ) * ω ^ 2 := by
            rw [ζ_pow3]
            ring
          rw [h3] at h1
          exact hωgood h1
      · exact ⟨1, norm_one, fun x y hxK hyK hxr hyr hxyre _ _ _ _ =>
          hnobad ⟨x, y, hxK, hyK, hxr, hyr, hxyre⟩⟩
    · exact ⟨1, norm_one, fun _ _ _ _ _ _ _ hDeq => absurd hDeq hDne⟩
  -- the three sector pieces
  refine ⟨fun k => K ∩ {z | ‖z - c‖ / 2 ≤ ((z - c) * conj (ω * ζ ^ (k : ℕ))).re}, ?_, ?_⟩
  · -- the pieces cover K
    intro z hz
    simp only [Set.mem_iUnion]
    rcases mem_sector_cover (z - c) hω1 with h | h | h
    · exact ⟨0, hz, by
        change ‖z - c‖ / 2 ≤ ((z - c) * conj (ω * ζ ^ ((0 : Fin 3) : ℕ))).re
        simpa [pow_zero, mul_one] using h⟩
    · exact ⟨1, hz, by
        change ‖z - c‖ / 2 ≤ ((z - c) * conj (ω * ζ ^ ((1 : Fin 3) : ℕ))).re
        simpa [pow_one] using h⟩
    · exact ⟨2, hz, h⟩
  · -- each piece has strictly smaller diameter
    intro k
    set W := ω * ζ ^ (k : ℕ) with hW
    have hWnorm : ‖W‖ = 1 := by
      rw [hW, norm_mul, hω1, norm_pow, norm_ζ, one_pow, mul_one]
    set P := K ∩ {z | ‖z - c‖ / 2 ≤ ((z - c) * conj W).re} with hP
    have hPc : IsCompact P := hK.inter_right (isClosed_le
      (((continuous_id.sub continuous_const).norm).div_const 2)
      (Complex.continuous_re.comp ((continuous_id.sub continuous_const).mul
        continuous_const)))
    have hPsub : P ⊆ K := inter_subset_left
    have hPbounded : IsBounded P := hK.isBounded.subset hPsub
    have hdiam_lt : diam P < D := by
      rcases eq_empty_or_nonempty P with hemp | hne'
      · rw [hemp, diam_empty]
        exact hD
      by_contra hge
      push Not at hge
      have hle : diam P ≤ D := diam_mono hPsub hK.isBounded
      obtain ⟨x, hx, y, hy, hxyd⟩ := exists_dist_eq_diam hPc hne'
      have hdxy : dist x y = D := le_antisymm
        (hxyd ▸ hle) (le_trans hge (le_of_eq hxyd.symm))
      -- the two sector coordinates
      set p := (x - c) * conj W with hp
      set q := (y - c) * conj W with hq
      have hnp : ‖p‖ = ‖x - c‖ := by rw [hp, norm_mul, RCLike.norm_conj, hWnorm, mul_one]
      have hnq : ‖q‖ = ‖y - c‖ := by rw [hq, norm_mul, RCLike.norm_conj, hWnorm, mul_one]
      have hWW : conj W * W = 1 := by
        have h := Complex.mul_conj W
        rw [normSq_eq_norm_sq, hWnorm] at h
        rw [mul_comm] at h
        rw [h]
        norm_num
      have hpq : p * conj q = (x - c) * conj (y - c) := by
        have hcq : conj ((y - c) * conj W) = conj (y - c) * W := by
          rw [map_mul, Complex.conj_conj]
        rw [hp, hq, hcq]
        calc (x - c) * conj W * (conj (y - c) * W)
            = (x - c) * conj (y - c) * (conj W * W) := by ring
          _ = (x - c) * conj (y - c) := by rw [hWW, mul_one]
      have hfar : (p * conj q).re ≤ -(r ^ 2 / 2) := by
        rw [hpq, hre_formula x y, hdxy]
        have h1 := hrad x hx.1
        have h2 := hrad y hy.1
        have h3 := norm_nonneg (x - c)
        have h4 := norm_nonneg (y - c)
        nlinarith [hjung]
      have hpsec : ‖p‖ / 2 ≤ p.re := by
        rw [hnp]
        exact hx.2
      have hqsec : ‖q‖ / 2 ≤ q.re := by
        rw [hnq]
        exact hy.2
      obtain ⟨hq_eq, hp_r, hp_re⟩ := sector_pair_eq hr (hnp ▸ hrad x hx.1)
        (hnq ▸ hrad y hy.1) hpsec hqsec hfar
      have hxr : ‖x - c‖ = r := by rw [← hnp]; exact hp_r
      have hyr : ‖y - c‖ = r := by
        rw [← hnq, hq_eq, RCLike.norm_conj]
        exact hp_r
      -- recover x - c and y - c from p and q
      have hxc : x - c = p * W := by
        rw [hp]
        calc x - c = (x - c) * (conj W * W) := by rw [hWW, mul_one]
          _ = (x - c) * conj W * W := by ring
      have hyc : y - c = conj p * W := by
        rw [← hq_eq, hq]
        calc y - c = (y - c) * (conj W * W) := by rw [hWW, mul_one]
          _ = (y - c) * conj W * W := by ring
      have hpim : p.im ^ 2 = 3 / 4 * r ^ 2 := by
        have h := sq_norm_eq p
        rw [hp_r, hp_re] at h
        nlinarith
      -- the pair (x, y) is a bad pair with product r²W²
      have hprod : (x - c) * (y - c) = ((r ^ 2 : ℝ) : ℂ) * W ^ 2 := by
        rw [hxc, hyc]
        have h1 : p * W * (conj p * W) = p * conj p * W ^ 2 := by ring
        rw [h1, Complex.mul_conj, normSq_eq_norm_sq, hp_r]
      have hre_bad : ((y - c) * conj (x - c)).re = -(r ^ 2 / 2) := by
        have hWW' : W * conj W = 1 := by rw [mul_comm]; exact hWW
        have h1 : (y - c) * conj (x - c) = conj p * conj p := by
          have hcx : conj (x - c) = conj p * conj W := by
            rw [hxc, map_mul]
          rw [hyc, hcx]
          calc conj p * W * (conj p * conj W)
              = conj p * conj p * (W * conj W) := by ring
            _ = conj p * conj p := by rw [hWW', mul_one]
        have h2 : conj p * conj p = conj (p * p) := (map_mul (starRingEnd ℂ) p p).symm
        rw [h1, h2, Complex.conj_re, Complex.mul_re, hp_re,
          show p.im * p.im = p.im ^ 2 from (sq p.im).symm, hpim]
        ring
      have hD3 : 3 * r ^ 2 = D ^ 2 := by
        have h1 := hre_formula y x
        rw [hyr, hxr, dist_comm, hdxy, hre_bad] at h1
        linarith
      rw [hW] at hprod
      exact hωblock x y hx.1 hy.1 hxr hyr hre_bad hD3 (k : ℕ) k.isLt hprod
    -- convert the strict diameter bound to `ediam`
    calc ediam P = ENNReal.ofReal (diam P) :=
          (ENNReal.ofReal_toReal hPbounded.ediam_ne_top).symm
      _ < ENNReal.ofReal D := (ENNReal.ofReal_lt_ofReal_iff hD).mpr hdiam_lt
      _ = ediam K := ENNReal.ofReal_toReal hK.isBounded.ediam_ne_top

/-- **Borsuk's conjecture holds in the plane** (Borsuk 1933): every bounded set of at
least two points in `ℝ²` can be divided into three parts of strictly smaller diameter.

The proof avoids Pál's hexagonal universal cover entirely: it combines Jung's
inequality (`exists_jung_center`) with the rigidity of 120°-sectors around the Jung
centre (`sector_pair_eq`, `product_orbit`) and an explicit choice of sector frame among
`1, e^{iπ/6}, e^{iπ/3}, i`. -/
theorem _root_.Borsuk.borsukConjecture_two : BorsukConjecture 2 := by
  intro s hbs hs
  let b : OrthonormalBasis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)) :=
    (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin 2))).reindex
      (finCongr finrank_euclideanSpace_fin)
  let e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) := Complex.isometryOfOrthonormal b
  set K : Set ℂ := closure (⇑e.symm '' s) with hKdef
  have hbK : IsBounded (⇑e.symm '' s) := e.symm.isometry.lipschitz.isBounded_image hbs
  have hcomp : IsCompact K := hbK.isCompact_closure
  have hnt : K.Nontrivial := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hs
    exact ⟨e.symm x, subset_closure (mem_image_of_mem _ hx),
      e.symm y, subset_closure (mem_image_of_mem _ hy),
      fun h => hxy (e.symm.injective h)⟩
  have hK3 := hasBorsukCover_three_of_isCompact hcomp hnt
  have himg : HasBorsukCover 3 (⇑e.symm '' s) := by
    obtain ⟨cov, hcov, hdi⟩ := hK3
    refine ⟨cov, subset_trans subset_closure hcov, fun i => ?_⟩
    calc ediam (cov i) < ediam K := hdi i
      _ = ediam (⇑e.symm '' s) := by rw [hKdef, Metric.ediam_closure]
  have h2 := himg.image e.toIsometryEquiv
  have h3 : ⇑e.toIsometryEquiv '' (⇑e.symm '' s) = s := by
    rw [Set.image_image]
    simp
  rwa [h3] at h2

end

end Plane

end Borsuk

namespace Borsuk

open Metric Bornology Set Real

namespace Space

/-- Three-dimensional Euclidean space. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/- ### The four octahedral functionals -/

/-- First octahedral functional, `x₁ + x₂ + x₃`. -/
def L1 (y : E3) : ℝ := y 0 + y 1 + y 2

/-- Second octahedral functional, `x₁ - x₂ - x₃`. -/
def L2 (y : E3) : ℝ := y 0 - y 1 - y 2

/-- Third octahedral functional, `-x₁ + x₂ - x₃`. -/
def L3 (y : E3) : ℝ := -y 0 + y 1 - y 2

/-- Fourth octahedral functional, `-x₁ - x₂ + x₃`. -/
def L4 (y : E3) : ℝ := -y 0 - y 1 + y 2

/-- The four functionals sum to zero. -/
theorem L_sum (y : E3) : L1 y + L2 y + L3 y + L4 y = 0 := by
  simp only [L1, L2, L3, L4]; ring

/- ### Rotation about the third axis -/

/-- Rotation by angle `t` about the third coordinate axis. -/
noncomputable def rot (t : ℝ) (x : E3) : E3 :=
  !₂[cos t * x 0 - sin t * x 1, sin t * x 0 + cos t * x 1, x 2]

@[simp] theorem rot_apply_zero (t : ℝ) (x : E3) :
    rot t x 0 = cos t * x 0 - sin t * x 1 := rfl

@[simp] theorem rot_apply_one (t : ℝ) (x : E3) :
    rot t x 1 = sin t * x 0 + cos t * x 1 := rfl

@[simp] theorem rot_apply_two (t : ℝ) (x : E3) : rot t x 2 = x 2 := rfl

/-- The rotation preserves distances. -/
theorem dist_rot (t : ℝ) (x y : E3) : dist (rot t x) (rot t y) = dist x y := by
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
  congr 1
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [rot_apply_zero, rot_apply_one, rot_apply_two, Real.dist_eq, sq_abs]
  have h := sin_sq_add_cos_sq t
  linear_combination ((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2) * h

/-- Rotations compose additively in the angle. -/
theorem rot_rot (s t : ℝ) (x : E3) : rot s (rot t x) = rot (s + t) x := by
  refine PiLp.ext fun i => ?_
  fin_cases i
  · change rot s (rot t x) 0 = rot (s + t) x 0
    simp only [rot_apply_zero, rot_apply_one, cos_add, sin_add]; ring
  · change rot s (rot t x) 1 = rot (s + t) x 1
    simp only [rot_apply_zero, rot_apply_one, cos_add, sin_add]; ring
  · rfl

/-- Rotation by `0` is the identity. -/
theorem rot_zero (x : E3) : rot 0 x = x := by
  refine PiLp.ext fun i => ?_
  fin_cases i
  · change rot 0 x 0 = x 0
    simp
  · change rot 0 x 1 = x 1
    simp
  · rfl

/- ### The frame-swap identities

Rotating by an extra `π/2` carries each functional to the negation of another:
the 4-cycle `L₁ ↦ -L₃ ↦ -(-L₄) …`, recorded functional-by-functional. -/

theorem L1_rot_add (t : ℝ) (x : E3) : L1 (rot (t + π / 2) x) = -L3 (rot t x) := by
  simp only [L1, L3, rot_apply_zero, rot_apply_one, rot_apply_two,
    Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
  ring

theorem L2_rot_add (t : ℝ) (x : E3) : L2 (rot (t + π / 2) x) = -L1 (rot t x) := by
  simp only [L1, L2, rot_apply_zero, rot_apply_one, rot_apply_two,
    Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
  ring

theorem L3_rot_add (t : ℝ) (x : E3) : L3 (rot (t + π / 2) x) = -L4 (rot t x) := by
  simp only [L3, L4, rot_apply_zero, rot_apply_one, rot_apply_two,
    Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
  ring

theorem L4_rot_add (t : ℝ) (x : E3) : L4 (rot (t + π / 2) x) = -L2 (rot t x) := by
  simp only [L2, L4, rot_apply_zero, rot_apply_one, rot_apply_two,
    Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
  ring

/- ### Lipschitz estimates -/

/-- Distance in `E3`, written out in coordinates. -/
theorem dist_eq_sqrt (y z : E3) :
    dist y z = Real.sqrt ((y 0 - z 0) ^ 2 + (y 1 - z 1) ^ 2 + (y 2 - z 2) ^ 2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_three]
  simp only [Real.dist_eq, sq_abs]

/-- From `u² ≤ 3v²` with `v ≥ 0` conclude `u ≤ √3 v`. -/
private theorem le_sqrt3_mul_of_sq_le {u v : ℝ} (hv : 0 ≤ v) (h : u ^ 2 ≤ 3 * v ^ 2) :
    u ≤ Real.sqrt 3 * v := by
  have h1 : u ≤ |u| := le_abs_self u
  have h2 : |u| = Real.sqrt (u ^ 2) := (Real.sqrt_sq_eq_abs u).symm
  have h3 : Real.sqrt (u ^ 2) ≤ Real.sqrt (3 * v ^ 2) := Real.sqrt_le_sqrt h
  have h4 : Real.sqrt (3 * v ^ 2) = Real.sqrt 3 * v := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hv]
  linarith

/-- Each octahedral functional is `√3`-Lipschitz (Cauchy–Schwarz, `‖nᵢ‖ = √3`). -/
theorem L1_lip (y z : E3) : L1 y - L1 z ≤ Real.sqrt 3 * dist y z := by
  refine le_sqrt3_mul_of_sq_le dist_nonneg ?_
  rw [dist_eq_sqrt, Real.sq_sqrt (by positivity)]
  simp only [L1]
  nlinarith [sq_nonneg ((y 0 - z 0) - (y 1 - z 1)), sq_nonneg ((y 0 - z 0) - (y 2 - z 2)),
    sq_nonneg ((y 1 - z 1) - (y 2 - z 2)), sq_nonneg ((y 0 - z 0) + (y 1 - z 1)),
    sq_nonneg ((y 0 - z 0) + (y 2 - z 2)), sq_nonneg ((y 1 - z 1) + (y 2 - z 2))]

theorem L2_lip (y z : E3) : L2 y - L2 z ≤ Real.sqrt 3 * dist y z := by
  refine le_sqrt3_mul_of_sq_le dist_nonneg ?_
  rw [dist_eq_sqrt, Real.sq_sqrt (by positivity)]
  simp only [L2]
  nlinarith [sq_nonneg ((y 0 - z 0) - (y 1 - z 1)), sq_nonneg ((y 0 - z 0) - (y 2 - z 2)),
    sq_nonneg ((y 1 - z 1) - (y 2 - z 2)), sq_nonneg ((y 0 - z 0) + (y 1 - z 1)),
    sq_nonneg ((y 0 - z 0) + (y 2 - z 2)), sq_nonneg ((y 1 - z 1) + (y 2 - z 2))]

theorem L3_lip (y z : E3) : L3 y - L3 z ≤ Real.sqrt 3 * dist y z := by
  refine le_sqrt3_mul_of_sq_le dist_nonneg ?_
  rw [dist_eq_sqrt, Real.sq_sqrt (by positivity)]
  simp only [L3]
  nlinarith [sq_nonneg ((y 0 - z 0) - (y 1 - z 1)), sq_nonneg ((y 0 - z 0) - (y 2 - z 2)),
    sq_nonneg ((y 1 - z 1) - (y 2 - z 2)), sq_nonneg ((y 0 - z 0) + (y 1 - z 1)),
    sq_nonneg ((y 0 - z 0) + (y 2 - z 2)), sq_nonneg ((y 1 - z 1) + (y 2 - z 2))]

theorem L4_lip (y z : E3) : L4 y - L4 z ≤ Real.sqrt 3 * dist y z := by
  refine le_sqrt3_mul_of_sq_le dist_nonneg ?_
  rw [dist_eq_sqrt, Real.sq_sqrt (by positivity)]
  simp only [L4]
  nlinarith [sq_nonneg ((y 0 - z 0) - (y 1 - z 1)), sq_nonneg ((y 0 - z 0) - (y 2 - z 2)),
    sq_nonneg ((y 1 - z 1) - (y 2 - z 2)), sq_nonneg ((y 0 - z 0) + (y 1 - z 1)),
    sq_nonneg ((y 0 - z 0) + (y 2 - z 2)), sq_nonneg ((y 1 - z 1) + (y 2 - z 2))]

/-- The squared norm is the sum of squared coordinates. -/
theorem norm_sq_eq (x : E3) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three,
    Real.sq_sqrt (by positivity)]
  simp only [Real.norm_eq_abs, sq_abs]

/-- Rotating a point through nearby angles moves it at most proportionally to the
angle difference. -/
theorem dist_rot_rot (t s : ℝ) (x : E3) :
    dist (rot t x) (rot s x) ≤ 2 * |t - s| * ‖x‖ := by
  have hB : (0 : ℝ) ≤ 2 * |t - s| * ‖x‖ := by positivity
  have hc2 : (cos t - cos s) ^ 2 ≤ (t - s) ^ 2 := by
    have h := abs_le.mp (Real.abs_cos_sub_cos_le t s)
    have h2 := sq_le_sq' h.1 h.2
    rwa [sq_abs] at h2
  have hs2 : (sin t - sin s) ^ 2 ≤ (t - s) ^ 2 := by
    have h := abs_le.mp (Real.abs_sin_sub_sin_le t s)
    have h2 := sq_le_sq' h.1 h.2
    rwa [sq_abs] at h2
  have hx01 : x 0 ^ 2 + x 1 ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [norm_sq_eq]
    nlinarith [sq_nonneg (x 2)]
  rw [dist_eq_sqrt]
  have hA : (rot t x 0 - rot s x 0) ^ 2 + (rot t x 1 - rot s x 1) ^ 2 +
      (rot t x 2 - rot s x 2) ^ 2 ≤ (2 * |t - s| * ‖x‖) ^ 2 := by
    simp only [rot_apply_zero, rot_apply_one, rot_apply_two]
    have hid : (cos t * x 0 - sin t * x 1 - (cos s * x 0 - sin s * x 1)) ^ 2 +
        (sin t * x 0 + cos t * x 1 - (sin s * x 0 + cos s * x 1)) ^ 2 +
        (x 2 - x 2) ^ 2 =
        ((cos t - cos s) ^ 2 + (sin t - sin s) ^ 2) * (x 0 ^ 2 + x 1 ^ 2) := by ring
    rw [hid]
    have hsq : (2 * |t - s| * ‖x‖) ^ 2 = 4 * (t - s) ^ 2 * ‖x‖ ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs]
      ring
    rw [hsq]
    have h1 : (cos t - cos s) ^ 2 + (sin t - sin s) ^ 2 ≤ 2 * (t - s) ^ 2 := by linarith
    have h2 : ((cos t - cos s) ^ 2 + (sin t - sin s) ^ 2) * (x 0 ^ 2 + x 1 ^ 2) ≤
        2 * (t - s) ^ 2 * (x 0 ^ 2 + x 1 ^ 2) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : 2 * (t - s) ^ 2 * (x 0 ^ 2 + x 1 ^ 2) ≤ 2 * (t - s) ^ 2 * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hx01 (by positivity)
    nlinarith [sq_nonneg (t - s), sq_nonneg ‖x‖]
  calc Real.sqrt ((rot t x 0 - rot s x 0) ^ 2 + (rot t x 1 - rot s x 1) ^ 2 +
        (rot t x 2 - rot s x 2) ^ 2)
      ≤ Real.sqrt ((2 * |t - s| * ‖x‖) ^ 2) := Real.sqrt_le_sqrt hA
    _ = 2 * |t - s| * ‖x‖ := Real.sqrt_sq hB

/- ### Support values along the rotation -/

/-- Supremum of a functional over the rotated set. -/
noncomputable def suppMax (f : E3 → ℝ) (K : Set E3) (t : ℝ) : ℝ :=
  sSup ((fun x => f (rot t x)) '' K)

/-- Infimum of a functional over the rotated set. -/
noncomputable def suppMin (f : E3 → ℝ) (K : Set E3) (t : ℝ) : ℝ :=
  sInf ((fun x => f (rot t x)) '' K)

section Support

variable {K : Set E3} {f g : E3 → ℝ}

theorem bddAbove_rotImage (hf : ∀ y z : E3, f y - f z ≤ Real.sqrt 3 * dist y z)
    (hb : IsBounded K) (hne : K.Nonempty) (t : ℝ) :
    BddAbove ((fun x => f (rot t x)) '' K) := by
  obtain ⟨x₀, hx₀⟩ := hne
  refine ⟨f (rot t x₀) + Real.sqrt 3 * diam K, ?_⟩
  rintro v ⟨x, hx, rfl⟩
  have h1 := hf (rot t x) (rot t x₀)
  rw [dist_rot] at h1
  have h2 : dist x x₀ ≤ diam K := dist_le_diam_of_mem hb hx hx₀
  have h3 : Real.sqrt 3 * dist x x₀ ≤ Real.sqrt 3 * diam K :=
    mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg 3)
  linarith

theorem bddBelow_rotImage (hf : ∀ y z : E3, f y - f z ≤ Real.sqrt 3 * dist y z)
    (hb : IsBounded K) (hne : K.Nonempty) (t : ℝ) :
    BddBelow ((fun x => f (rot t x)) '' K) := by
  obtain ⟨x₀, hx₀⟩ := hne
  refine ⟨f (rot t x₀) - Real.sqrt 3 * diam K, ?_⟩
  rintro v ⟨x, hx, rfl⟩
  have h1 := hf (rot t x₀) (rot t x)
  rw [dist_rot] at h1
  have h2 : dist x₀ x ≤ diam K := dist_le_diam_of_mem hb hx₀ hx
  have h3 : Real.sqrt 3 * dist x₀ x ≤ Real.sqrt 3 * diam K :=
    mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg 3)
  linarith

theorem le_suppMax (hf : ∀ y z : E3, f y - f z ≤ Real.sqrt 3 * dist y z)
    (hb : IsBounded K) (hne : K.Nonempty) {t : ℝ} {x : E3} (hx : x ∈ K) :
    f (rot t x) ≤ suppMax f K t :=
  le_csSup (bddAbove_rotImage hf hb hne t) ⟨x, hx, rfl⟩

theorem suppMin_le (hf : ∀ y z : E3, f y - f z ≤ Real.sqrt 3 * dist y z)
    (hb : IsBounded K) (hne : K.Nonempty) {t : ℝ} {x : E3} (hx : x ∈ K) :
    suppMin f K t ≤ f (rot t x) :=
  csInf_le (bddBelow_rotImage hf hb hne t) ⟨x, hx, rfl⟩

/-- The width bound: the slab has width at most `√3 · diam K`. -/
theorem suppMax_le (hf : ∀ y z : E3, f y - f z ≤ Real.sqrt 3 * dist y z)
    (hb : IsBounded K) (hne : K.Nonempty) (t : ℝ) :
    suppMax f K t ≤ suppMin f K t + Real.sqrt 3 * diam K := by
  apply csSup_le (hne.image _)
  rintro v ⟨x, hx, rfl⟩
  have h1 : f (rot t x) - Real.sqrt 3 * diam K ≤ suppMin f K t := by
    apply le_csInf (hne.image _)
    rintro w ⟨y, hy, rfl⟩
    have h2 := hf (rot t x) (rot t y)
    rw [dist_rot] at h2
    have h3 : dist x y ≤ diam K := dist_le_diam_of_mem hb hx hy
    have h4 : Real.sqrt 3 * dist x y ≤ Real.sqrt 3 * diam K :=
      mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg 3)
    linarith
  linarith

/-- One-sided Lipschitz estimate for the support values in the angle. -/
theorem suppMax_sub_le (hf : ∀ y z : E3, f y - f z ≤ Real.sqrt 3 * dist y z)
    (hb : IsBounded K) (hne : K.Nonempty) {R : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R)
    (t s : ℝ) : suppMax f K t ≤ suppMax f K s + 2 * Real.sqrt 3 * R * |t - s| := by
  apply csSup_le (hne.image _)
  rintro v ⟨x, hx, rfl⟩
  have h1 := hf (rot t x) (rot s x)
  have h2 := dist_rot_rot t s x
  have h3 : f (rot s x) ≤ suppMax f K s := le_suppMax hf hb hne hx
  have h4 : Real.sqrt 3 * dist (rot t x) (rot s x) ≤
      Real.sqrt 3 * (2 * |t - s| * ‖x‖) :=
    mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg 3)
  have h5 : Real.sqrt 3 * (2 * |t - s| * ‖x‖) ≤ Real.sqrt 3 * (2 * |t - s| * R) := by
    have h6 : 2 * |t - s| * ‖x‖ ≤ 2 * |t - s| * R :=
      mul_le_mul_of_nonneg_left (hR x hx) (by positivity)
    exact mul_le_mul_of_nonneg_left h6 (Real.sqrt_nonneg 3)
  have h7 : Real.sqrt 3 * (2 * |t - s| * R) = 2 * Real.sqrt 3 * R * |t - s| := by ring
  linarith

theorem suppMin_sub_le (hf : ∀ y z : E3, f y - f z ≤ Real.sqrt 3 * dist y z)
    (hb : IsBounded K) (hne : K.Nonempty) {R : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R)
    (t s : ℝ) : suppMin f K t ≤ suppMin f K s + 2 * Real.sqrt 3 * R * |t - s| := by
  have h0 : suppMin f K t ≤ suppMin f K s + 2 * Real.sqrt 3 * R * |t - s| := by
    have h1 : suppMin f K s + 2 * Real.sqrt 3 * R * |t - s| ≥ suppMin f K t := by
      have h2 : ∀ x ∈ K, suppMin f K t - 2 * Real.sqrt 3 * R * |t - s| ≤ f (rot s x) := by
        intro x hx
        have h3 := suppMin_le hf hb hne (t := t) hx
        have h4 := hf (rot t x) (rot s x)
        have h5 := dist_rot_rot t s x
        have h6 : Real.sqrt 3 * dist (rot t x) (rot s x) ≤
            Real.sqrt 3 * (2 * |t - s| * R) := by
          have h7 : dist (rot t x) (rot s x) ≤ 2 * |t - s| * R :=
            h5.trans (mul_le_mul_of_nonneg_left (hR x hx) (by positivity))
          exact mul_le_mul_of_nonneg_left h7 (Real.sqrt_nonneg 3)
        have h8 : Real.sqrt 3 * (2 * |t - s| * R) = 2 * Real.sqrt 3 * R * |t - s| := by
          ring
        linarith
      have h9 : suppMin f K t - 2 * Real.sqrt 3 * R * |t - s| ≤ suppMin f K s := by
        apply le_csInf (hne.image _)
        rintro w ⟨y, hy, rfl⟩
        exact h2 y hy
      linarith
    linarith
  exact h0

/-- Transfer of the frame-swap identities to suprema. -/
private theorem suppMax_swap {t : ℝ}
    (hfg : ∀ x : E3, f (rot (t + π / 2) x) = -g (rot t x)) :
    suppMax f K (t + π / 2) = -suppMin g K t := by
  unfold suppMax suppMin
  have himg : (fun x => f (rot (t + π / 2) x)) '' K =
      -((fun x => g (rot t x)) '' K) := by
    rw [← Set.image_neg_eq_neg, Set.image_image]
    exact Set.image_congr fun x _ => hfg x
  rw [himg, Real.sSup_neg]

/-- Transfer of the frame-swap identities to infima. -/
private theorem suppMin_swap {t : ℝ}
    (hfg : ∀ x : E3, f (rot (t + π / 2) x) = -g (rot t x)) :
    suppMin f K (t + π / 2) = -suppMax g K t := by
  unfold suppMax suppMin
  have himg : (fun x => f (rot (t + π / 2) x)) '' K =
      -((fun x => g (rot t x)) '' K) := by
    rw [← Set.image_neg_eq_neg, Set.image_image]
    exact Set.image_congr fun x _ => hfg x
  rw [himg, Real.sInf_neg]

end Support

/- ### The midpoint sum and the intermediate value argument -/

/-- Twice the sum of the four slab midpoints of the rotated set. -/
noncomputable def Fmid (K : Set E3) (t : ℝ) : ℝ :=
  suppMax L1 K t + suppMin L1 K t + (suppMax L2 K t + suppMin L2 K t) +
    (suppMax L3 K t + suppMin L3 K t) + (suppMax L4 K t + suppMin L4 K t)

/-- The frame swap makes the midpoint sum anti-periodic with period `π/2`. -/
theorem Fmid_add (K : Set E3) (t : ℝ) : Fmid K (t + π / 2) = -Fmid K t := by
  unfold Fmid
  rw [suppMax_swap (fun x => L1_rot_add t x), suppMin_swap (fun x => L1_rot_add t x),
    suppMax_swap (fun x => L2_rot_add t x), suppMin_swap (fun x => L2_rot_add t x),
    suppMax_swap (fun x => L3_rot_add t x), suppMin_swap (fun x => L3_rot_add t x),
    suppMax_swap (fun x => L4_rot_add t x), suppMin_swap (fun x => L4_rot_add t x)]
  ring

section IVT

variable {K : Set E3}

/-- The midpoint sum is continuous in the angle. -/
theorem continuous_Fmid (hb : IsBounded K) (hne : K.Nonempty) {R : ℝ}
    (hR : ∀ x ∈ K, ‖x‖ ≤ R) : Continuous (Fmid K) := by
  have hC : ∀ t s : ℝ, Fmid K t - Fmid K s ≤ 16 * Real.sqrt 3 * R * |t - s| := by
    intro t s
    have h1 := suppMax_sub_le L1_lip hb hne hR t s
    have h2 := suppMax_sub_le L2_lip hb hne hR t s
    have h3 := suppMax_sub_le L3_lip hb hne hR t s
    have h4 := suppMax_sub_le L4_lip hb hne hR t s
    have h5 := suppMin_sub_le L1_lip hb hne hR t s
    have h6 := suppMin_sub_le L2_lip hb hne hR t s
    have h7 := suppMin_sub_le L3_lip hb hne hR t s
    have h8 := suppMin_sub_le L4_lip hb hne hR t s
    unfold Fmid
    linarith
  have habs : ∀ t s : ℝ, |Fmid K t - Fmid K s| ≤ 16 * Real.sqrt 3 * R * |t - s| := by
    intro t s
    rw [abs_le]
    constructor
    · have h := hC s t
      rw [abs_sub_comm] at h
      linarith
    · exact hC t s
  have hlip : LipschitzWith (Real.toNNReal (16 * Real.sqrt 3 * R)) (Fmid K) := by
    apply LipschitzWith.of_dist_le_mul
    intro t s
    rw [Real.dist_eq, Real.dist_eq]
    calc |Fmid K t - Fmid K s| ≤ 16 * Real.sqrt 3 * R * |t - s| := habs t s
      _ ≤ Real.toNNReal (16 * Real.sqrt 3 * R) * |t - s| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          rw [Real.coe_toNNReal']
          exact le_max_left _ _
  exact hlip.continuous

/-- **Gale's octahedron cover**: a nonempty bounded subset of `ℝ³` of diameter at most
`√3` can be rotated and translated into the regular octahedron
`{y : |y₁| + |y₂| + |y₃| ≤ 3/2}`, whose opposite faces lie at distance `√3`. -/
theorem exists_oct_position (hb : IsBounded K) (hne : K.Nonempty)
    (hd : diam K ≤ Real.sqrt 3) :
    ∃ (t : ℝ) (c : E3), ∀ x ∈ K,
      |(rot t x - c) 0| + |(rot t x - c) 1| + |(rot t x - c) 2| ≤ 3 / 2 := by
  obtain ⟨R, hRsub⟩ := hb.subset_closedBall (0 : E3)
  have hR : ∀ x ∈ K, ‖x‖ ≤ R := fun x hx => by
    have h := hRsub hx
    rwa [mem_closedBall, dist_zero_right] at h
  -- the intermediate value theorem produces an angle with vanishing midpoint sum
  have hcont : Continuous (Fmid K) := continuous_Fmid hb hne hR
  have hanti : Fmid K (0 + π / 2) = -Fmid K 0 := Fmid_add K 0
  rw [zero_add] at hanti
  have h0mem : (0 : ℝ) ∈ Set.uIcc (Fmid K 0) (Fmid K (π / 2)) := by
    rw [hanti]
    rcases le_total 0 (Fmid K 0) with h | h
    · exact Set.mem_uIcc.mpr (Or.inr ⟨by linarith, h⟩)
    · exact Set.mem_uIcc.mpr (Or.inl ⟨h, by linarith⟩)
  obtain ⟨t₀, -, hF0⟩ := intermediate_value_uIcc hcont.continuousOn h0mem
  -- the four slab midpoints, which sum to zero at `t₀`
  set γ1 := (suppMax L1 K t₀ + suppMin L1 K t₀) / 2 with hγ1
  set γ2 := (suppMax L2 K t₀ + suppMin L2 K t₀) / 2 with hγ2
  set γ3 := (suppMax L3 K t₀ + suppMin L3 K t₀) / 2 with hγ3
  set γ4 := (suppMax L4 K t₀ + suppMin L4 K t₀) / 2 with hγ4
  have hγsum : γ1 + γ2 + γ3 + γ4 = 0 := by
    unfold Fmid at hF0
    rw [hγ1, hγ2, hγ3, hγ4]
    linarith
  -- the simultaneous centering translation
  set c : E3 := !₂[(γ1 + γ2) / 2, (γ1 + γ3) / 2, -(γ2 + γ3) / 2] with hc
  have hc0 : c 0 = (γ1 + γ2) / 2 := rfl
  have hc1 : c 1 = (γ1 + γ3) / 2 := rfl
  have hc2 : c 2 = -(γ2 + γ3) / 2 := rfl
  refine ⟨t₀, c, fun x hx => ?_⟩
  -- per-functional slab bounds around the midpoints
  have hwidth : ∀ f : E3 → ℝ, (∀ y z : E3, f y - f z ≤ Real.sqrt 3 * dist y z) →
      suppMax f K t₀ - suppMin f K t₀ ≤ 3 := by
    intro f hf
    have h := suppMax_le hf hb hne t₀
    have h2 : Real.sqrt 3 * diam K ≤ Real.sqrt 3 * Real.sqrt 3 :=
      mul_le_mul_of_nonneg_left hd (Real.sqrt_nonneg 3)
    rw [Real.mul_self_sqrt (by norm_num)] at h2
    linarith
  have hbound : ∀ f : E3 → ℝ, (∀ y z : E3, f y - f z ≤ Real.sqrt 3 * dist y z) →
      f (rot t₀ x) - (suppMax f K t₀ + suppMin f K t₀) / 2 ≤ 3 / 2 ∧
      (suppMax f K t₀ + suppMin f K t₀) / 2 - f (rot t₀ x) ≤ 3 / 2 := by
    intro f hf
    have h1 := le_suppMax hf hb hne (t := t₀) hx
    have h2 := suppMin_le hf hb hne (t := t₀) hx
    have h3 := hwidth f hf
    constructor <;> linarith
  obtain ⟨e1, e1'⟩ := hbound L1 L1_lip
  obtain ⟨e2, e2'⟩ := hbound L2 L2_lip
  obtain ⟨e3, e3'⟩ := hbound L3 L3_lip
  obtain ⟨e4, e4'⟩ := hbound L4 L4_lip
  rw [← hγ1] at e1 e1'
  rw [← hγ2] at e2 e2'
  rw [← hγ3] at e3 e3'
  rw [← hγ4] at e4 e4'
  -- rewrite everything in the coordinates of `rot t₀ x - c`
  have hsub0 : (rot t₀ x - c) 0 = rot t₀ x 0 - c 0 := rfl
  have hsub1 : (rot t₀ x - c) 1 = rot t₀ x 1 - c 1 := rfl
  have hsub2 : (rot t₀ x - c) 2 = rot t₀ x 2 - c 2 := rfl
  have hL1 : L1 (rot t₀ x) =
      (rot t₀ x - c) 0 + (rot t₀ x - c) 1 + (rot t₀ x - c) 2 + γ1 := by
    rw [hsub0, hsub1, hsub2, hc0, hc1, hc2]
    simp only [L1]
    ring
  have hL2 : L2 (rot t₀ x) =
      (rot t₀ x - c) 0 - (rot t₀ x - c) 1 - (rot t₀ x - c) 2 + γ2 := by
    rw [hsub0, hsub1, hsub2, hc0, hc1, hc2]
    simp only [L2]
    ring
  have hL3 : L3 (rot t₀ x) =
      -(rot t₀ x - c) 0 + (rot t₀ x - c) 1 - (rot t₀ x - c) 2 + γ3 := by
    rw [hsub0, hsub1, hsub2, hc0, hc1, hc2]
    simp only [L3]
    ring
  have hL4 : L4 (rot t₀ x) =
      -(rot t₀ x - c) 0 - (rot t₀ x - c) 1 + (rot t₀ x - c) 2 + γ4 := by
    rw [hsub0, hsub1, hsub2, hc0, hc1, hc2]
    simp only [L4]
    have h4 : γ4 = -γ1 - γ2 - γ3 := by linarith
    rw [h4]
    ring
  rw [hL1] at e1 e1'
  rw [hL2] at e2 e2'
  rw [hL3] at e3 e3'
  rw [hL4] at e4 e4'
  -- the eight sign patterns
  rcases abs_cases ((rot t₀ x - c) 0) with ⟨h₁, -⟩ | ⟨h₁, -⟩ <;>
    rcases abs_cases ((rot t₀ x - c) 1) with ⟨h₂, -⟩ | ⟨h₂, -⟩ <;>
      rcases abs_cases ((rot t₀ x - c) 2) with ⟨h₃, -⟩ | ⟨h₃, -⟩ <;>
        rw [h₁, h₂, h₃] <;> linarith

end IVT

end Space

end Borsuk

namespace Borsuk

open Metric Bornology Set Real

namespace Space

/-- Coordinate distances are bounded by the Euclidean distance. -/
theorem abs_coord_sub_le_dist (j : Fin 3) (y z : E3) : |y j - z j| ≤ dist y z := by
  rw [dist_eq_sqrt, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  fin_cases j
  · change (y 0 - z 0) ^ 2 ≤ _
    nlinarith [sq_nonneg (y 1 - z 1), sq_nonneg (y 2 - z 2)]
  · change (y 1 - z 1) ^ 2 ≤ _
    nlinarith [sq_nonneg (y 0 - z 0), sq_nonneg (y 2 - z 2)]
  · change (y 2 - z 2) ^ 2 ≤ _
    nlinarith [sq_nonneg (y 0 - z 0), sq_nonneg (y 1 - z 1)]

/-- The rotation `rot t` as an isometric equivalence. -/
noncomputable def rotIso (t : ℝ) : E3 ≃ᵢ E3 where
  toFun := rot t
  invFun := rot (-t)
  left_inv x := by rw [rot_rot, neg_add_cancel, rot_zero]
  right_inv x := by rw [rot_rot, add_neg_cancel, rot_zero]
  isometry_toFun := Isometry.of_dist_eq fun x y => dist_rot t x y

@[simp] theorem rotIso_apply (t : ℝ) (x : E3) : rotIso t x = rot t x := rfl

/-- Reflection of coordinates by a sign vector, as an isometric equivalence. -/
def reflectIso (σ : Fin 3 → ℝ) (hσ : ∀ j, σ j = 1 ∨ σ j = -1) : E3 ≃ᵢ E3 where
  toFun x := !₂[σ 0 * x 0, σ 1 * x 1, σ 2 * x 2]
  invFun x := !₂[σ 0 * x 0, σ 1 * x 1, σ 2 * x 2]
  left_inv x := by
    refine PiLp.ext fun i => ?_
    fin_cases i
    · change σ 0 * (σ 0 * x 0) = x 0
      rcases hσ 0 with h | h <;> rw [h] <;> ring
    · change σ 1 * (σ 1 * x 1) = x 1
      rcases hσ 1 with h | h <;> rw [h] <;> ring
    · change σ 2 * (σ 2 * x 2) = x 2
      rcases hσ 2 with h | h <;> rw [h] <;> ring
  right_inv x := by
    refine PiLp.ext fun i => ?_
    fin_cases i
    · change σ 0 * (σ 0 * x 0) = x 0
      rcases hσ 0 with h | h <;> rw [h] <;> ring
    · change σ 1 * (σ 1 * x 1) = x 1
      rcases hσ 1 with h | h <;> rw [h] <;> ring
    · change σ 2 * (σ 2 * x 2) = x 2
      rcases hσ 2 with h | h <;> rw [h] <;> ring
  isometry_toFun := Isometry.of_dist_eq fun x y => by
    have hsq : ∀ j, σ j ^ 2 = 1 := fun j => by
      rcases hσ j with h | h <;> rw [h] <;> norm_num
    rw [dist_eq_sqrt, dist_eq_sqrt]
    congr 1
    change (σ 0 * x 0 - σ 0 * y 0) ^ 2 + (σ 1 * x 1 - σ 1 * y 1) ^ 2 +
      (σ 2 * x 2 - σ 2 * y 2) ^ 2 = _
    linear_combination (x 0 - y 0) ^ 2 * hsq 0 + (x 1 - y 1) ^ 2 * hsq 1 +
      (x 2 - y 2) ^ 2 * hsq 2

/-- **Truncated cover.**  A nonempty bounded set of diameter at most `√3` can be moved
by an isometric equivalence into the truncated octahedron: the `ℓ¹`-ball of radius
`3/2` with the three corner caps above height `13/15` removed. -/
theorem exists_truncated_position {K : Set E3} (hb : IsBounded K) (hne : K.Nonempty)
    (hd : diam K ≤ Real.sqrt 3) :
    ∃ e : E3 ≃ᵢ E3, ∀ x ∈ K,
      (|e x 0| + |e x 1| + |e x 2| ≤ 3 / 2) ∧
      e x 0 ≤ 13 / 15 ∧ e x 1 ≤ 13 / 15 ∧ e x 2 ≤ 13 / 15 := by
  have h26 : Real.sqrt 3 ≤ 26 / 15 := by
    rw [show (26 : ℝ) / 15 = Real.sqrt ((26 / 15) ^ 2) from
      (Real.sqrt_sq (by norm_num)).symm]
    apply Real.sqrt_le_sqrt
    norm_num
  obtain ⟨t, c, hpos⟩ := exists_oct_position hb hne hd
  -- for each axis, either all points stay below the upper cut, or all stay above the
  -- lower cut (two points in opposite caps would be more than `√3` apart)
  have hlow : ∀ j : Fin 3, ¬(∀ x ∈ K, (rot t x - c) j ≤ 13 / 15) →
      ∀ x ∈ K, -(13 / 15) ≤ (rot t x - c) j := by
    intro j hj x hx
    push Not at hj
    obtain ⟨x₀, hx₀K, hx₀⟩ := hj
    have h1 : |(rot t x₀ - c) j - (rot t x - c) j| ≤ dist (rot t x₀ - c) (rot t x - c) :=
      abs_coord_sub_le_dist j _ _
    have h2 : dist (rot t x₀ - c) (rot t x - c) = dist x₀ x := by
      rw [dist_sub_right]
      exact dist_rot t x₀ x
    have h3 : dist x₀ x ≤ diam K := dist_le_diam_of_mem hb hx₀K hx
    have h4 : dist (rot t x₀ - c) (rot t x - c) ≤ Real.sqrt 3 := by
      rw [h2]
      exact h3.trans hd
    have h5 := (abs_le.mp (h1.trans h4)).2
    linarith
  -- choose the reflection signs axis by axis
  classical
  set σ : Fin 3 → ℝ :=
    fun j => if ∀ x ∈ K, (rot t x - c) j ≤ 13 / 15 then 1 else -1 with hσdef
  have hσ : ∀ j, σ j = 1 ∨ σ j = -1 := fun j => by
    simp only [hσdef]
    split <;> simp
  have hσbound : ∀ j : Fin 3, ∀ x ∈ K, σ j * (rot t x - c) j ≤ 13 / 15 := by
    intro j x hx
    simp only [hσdef]
    split
    · rename_i h
      have := h x hx
      linarith
    · rename_i h
      have := hlow j h x hx
      linarith
  -- assemble the isometric equivalence
  refine ⟨((rotIso t).trans (IsometryEquiv.addRight (-c))).trans (reflectIso σ hσ),
    fun x hx => ?_⟩
  have hex : ∀ j : Fin 3,
      (((rotIso t).trans (IsometryEquiv.addRight (-c))).trans (reflectIso σ hσ)) x j =
      σ j * (rot t x - c) j := by
    intro j
    have h1 : (((rotIso t).trans (IsometryEquiv.addRight (-c))).trans
        (reflectIso σ hσ)) x = (reflectIso σ hσ) (rot t x - c) := by
      simp only [IsometryEquiv.trans_apply, rotIso_apply, IsometryEquiv.addRight_apply]
      rw [sub_eq_add_neg]
    rw [h1]
    fin_cases j
    · rfl
    · rfl
    · rfl
  have habs : ∀ j : Fin 3, |σ j * (rot t x - c) j| = |(rot t x - c) j| := by
    intro j
    rw [abs_mul]
    rcases hσ j with h | h <;> rw [h] <;> norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hex 0, hex 1, hex 2, habs 0, habs 1, habs 2]
    exact hpos x hx
  · rw [hex 0]
    exact hσbound 0 x hx
  · rw [hex 1]
    exact hσbound 1 x hx
  · rw [hex 2]
    exact hσbound 2 x hx

end Space

end Borsuk

namespace Borsuk

-- the certificate lemmas share a uniform machine-generated hypothesis interface, in
-- which individual facet hypotheses may go unused by a particular certificate


namespace Space.Cert

set_option maxHeartbeats 1600000 in
-- the branch-and-certify case tree is large
theorem certAA (x0 x1 x2 y0 y1 y2 : ℝ)
    (hx0 : (0 : ℝ) ≤ 3 / 2 - (x0 + x1 + x2)) (hx1 : (0 : ℝ) ≤ 3 / 2 - (x0 + x1 - x2))
    (hx2 : (0 : ℝ) ≤ 3 / 2 - (x0 - x1 + x2)) (_hx3 : (0 : ℝ) ≤ 3 / 2 - (x0 - x1 - x2))
    (hx4 : (0 : ℝ) ≤ 3 / 2 - (-x0 + x1 + x2)) (hx5 : (0 : ℝ) ≤ 3 / 2 - (-x0 + x1 - x2))
    (hx6 : (0 : ℝ) ≤ 3 / 2 - (-x0 - x1 + x2)) (_hx7 : (0 : ℝ) ≤ 3 / 2 - (-x0 - x1 - x2))
    (hx8 : (0 : ℝ) ≤ 13 / 15 - x0) (hx9 : (0 : ℝ) ≤ 13 / 15 - x1)
    (hx10 : (0 : ℝ) ≤ 13 / 15 - x2) (hx11 : (0 : ℝ) ≤ x0 + x1 + x2 - 5 / 12)
    (hx12 : (0 : ℝ) ≤ x0 + 7 / 24) (hx13 : (0 : ℝ) ≤ x1 + 7 / 24)
    (hx14 : (0 : ℝ) ≤ x2 + 7 / 24) (hy0 : (0 : ℝ) ≤ 3 / 2 - (y0 + y1 + y2))
    (hy1 : (0 : ℝ) ≤ 3 / 2 - (y0 + y1 - y2)) (hy2 : (0 : ℝ) ≤ 3 / 2 - (y0 - y1 + y2))
    (_hy3 : (0 : ℝ) ≤ 3 / 2 - (y0 - y1 - y2)) (hy4 : (0 : ℝ) ≤ 3 / 2 - (-y0 + y1 + y2))
    (hy5 : (0 : ℝ) ≤ 3 / 2 - (-y0 + y1 - y2)) (hy6 : (0 : ℝ) ≤ 3 / 2 - (-y0 - y1 + y2))
    (_hy7 : (0 : ℝ) ≤ 3 / 2 - (-y0 - y1 - y2)) (hy8 : (0 : ℝ) ≤ 13 / 15 - y0)
    (hy9 : (0 : ℝ) ≤ 13 / 15 - y1) (hy10 : (0 : ℝ) ≤ 13 / 15 - y2)
    (hy11 : (0 : ℝ) ≤ y0 + y1 + y2 - 5 / 12) (hy12 : (0 : ℝ) ≤ y0 + 7 / 24)
    (hy13 : (0 : ℝ) ≤ y1 + 7 / 24) (hy14 : (0 : ℝ) ≤ y2 + 7 / 24)
    :
    (x0 - y0) ^ 2 + (x1 - y1) ^ 2 + (x2 - y2) ^ 2 ≤ 149 / 50 := by
  rcases le_total y1 (1 / 2 : ℝ) with hbr0 | hbr0
  · have hbr0n : (0 : ℝ) ≤ 1 / 2 - y1 := by linarith
    rcases le_total y2 (1 / 2 : ℝ) with hbr1 | hbr1
    · have hbr1n : (0 : ℝ) ≤ 1 / 2 - y2 := by linarith
      rcases le_total x2 (1 / 2 : ℝ) with hbr2 | hbr2
      · have hbr2n : (0 : ℝ) ≤ 1 / 2 - x2 := by linarith
        rcases le_total x0 (1 / 2 : ℝ) with hbr3 | hbr3
        · have hbr3n : (0 : ℝ) ≤ 1 / 2 - x0 := by linarith
          rcases le_total y2 (0 : ℝ) with hbr4 | hbr4
          · have hbr4n : (0 : ℝ) ≤ 0 - y2 := by linarith
            linarith [mul_nonneg hx0 hx12, mul_nonneg hx4 hx11, mul_nonneg hx4 hbr0n,
              mul_nonneg hx4 hbr3n, mul_nonneg hx4 hbr4n, mul_nonneg hx9 hy14,
              mul_nonneg hx9 hbr0n, mul_nonneg hx9 hbr2n, mul_nonneg hx11 hy8,
              mul_nonneg hx11 hy11, mul_nonneg hx12 hy11, mul_nonneg hx12 hbr3n,
              mul_nonneg hy0 hy11, mul_nonneg hy2 hy11, mul_nonneg hy8 hy11, mul_nonneg hy8 hbr0n,
              mul_nonneg hy8 hbr3n, mul_nonneg hy8 hbr4n, mul_nonneg hy11 hbr4n,
              mul_nonneg hy13 hy14, mul_nonneg hy13 hbr0n, mul_nonneg hy13 hbr2n,
              mul_nonneg hy13 hbr3n, mul_nonneg hbr2n hbr4n]
          · have hbr4n : (0 : ℝ) ≤ y2 - (0) := by linarith
            rcases le_total y1 (0 : ℝ) with hbr5 | hbr5
            · have hbr5n : (0 : ℝ) ≤ 0 - y1 := by linarith
              linarith [mul_nonneg hx1 hy8, mul_nonneg hx4 hx11, mul_nonneg hx4 hx14,
                mul_nonneg hx9 hx13, mul_nonneg hx9 hy11, mul_nonneg hx9 hbr2n,
                mul_nonneg hx9 hbr5n, mul_nonneg hx11 hy11, mul_nonneg hx11 hy13,
                mul_nonneg hx11 hbr2n, mul_nonneg hx11 hbr4n, mul_nonneg hx12 hx14,
                mul_nonneg hx12 hy11, mul_nonneg hx12 hbr1n, mul_nonneg hx12 hbr3n,
                mul_nonneg hx14 hy8, mul_nonneg hx14 hy13, mul_nonneg hy2 hy11,
                mul_nonneg hy2 hbr2n, mul_nonneg hy8 hbr1n, mul_nonneg hy8 hbr3n,
                mul_nonneg hy13 hbr3n, mul_nonneg hy13 hbr5n]
            · have hbr5n : (0 : ℝ) ≤ y1 - (0) := by linarith
              linarith [mul_nonneg hx9 hx13, mul_nonneg hx9 hy11, mul_nonneg hx9 hbr0n,
                mul_nonneg hx9 hbr2n, mul_nonneg hx9 hbr4n, mul_nonneg hx11 hy11,
                mul_nonneg hx11 hbr0n, mul_nonneg hx11 hbr2n, mul_nonneg hx11 hbr4n,
                mul_nonneg hx12 hx14, mul_nonneg hx12 hy12, mul_nonneg hx12 hbr1n,
                mul_nonneg hx12 hbr3n, mul_nonneg hx13 hbr5n, mul_nonneg hx14 hy8,
                mul_nonneg hx14 hbr2n, mul_nonneg hy8 hy12, mul_nonneg hy8 hbr3n,
                mul_nonneg hbr0n hbr5n, mul_nonneg hbr1n hbr2n, mul_nonneg hbr1n hbr4n,
                mul_nonneg hbr2n hbr5n, mul_nonneg hbr3n hbr5n]
        · have hbr3n : (0 : ℝ) ≤ x0 - (1 / 2) := by linarith
          linarith [mul_nonneg hx0 hx8, mul_nonneg hx0 hx11, mul_nonneg hx0 hy12,
            mul_nonneg hx0 hbr0n, mul_nonneg hx1 hx13, mul_nonneg hx1 hy14, mul_nonneg hx1 hbr0n,
            mul_nonneg hx8 hx9, mul_nonneg hx8 hy11, mul_nonneg hx8 hy13, mul_nonneg hx8 hbr3n,
            mul_nonneg hx9 hbr0n, mul_nonneg hx11 hy11, mul_nonneg hx13 hy13,
            mul_nonneg hx13 hbr1n, mul_nonneg hx14 hy11, mul_nonneg hx14 hy14,
            mul_nonneg hx14 hbr2n, mul_nonneg hy8 hy12, mul_nonneg hy12 hbr2n,
            mul_nonneg hy12 hbr3n, mul_nonneg hy13 hbr0n, mul_nonneg hy14 hbr1n,
            mul_nonneg hbr1n hbr2n]
      · have hbr2n : (0 : ℝ) ≤ x2 - (1 / 2) := by linarith
        rcases le_total y0 (1 / 2 : ℝ) with hbr6 | hbr6
        · have hbr6n : (0 : ℝ) ≤ 1 / 2 - y0 := by linarith
          linarith [mul_nonneg hx0 hx10, mul_nonneg hx0 hx11, mul_nonneg hx0 hy14,
            mul_nonneg hx2 hx12, mul_nonneg hx2 hbr6n, mul_nonneg hx4 hx13, mul_nonneg hx4 hbr0n,
            mul_nonneg hx8 hx12, mul_nonneg hx8 hbr6n, mul_nonneg hx9 hx13, mul_nonneg hx9 hbr0n,
            mul_nonneg hx10 hy11, mul_nonneg hx10 hbr1n, mul_nonneg hx10 hbr2n,
            mul_nonneg hx11 hy11, mul_nonneg hx12 hy12, mul_nonneg hx13 hy13,
            mul_nonneg hy12 hbr6n, mul_nonneg hy13 hbr0n, mul_nonneg hy14 hbr1n,
            mul_nonneg hy14 hbr2n]
        · have hbr6n : (0 : ℝ) ≤ y0 - (1 / 2) := by linarith
          rcases le_total y2 (0 : ℝ) with hbr7 | hbr7
          · have hbr7n : (0 : ℝ) ≤ 0 - y2 := by linarith
            rcases le_total y1 (0 : ℝ) with hbr8 | hbr8
            · have hbr8n : (0 : ℝ) ≤ 0 - y1 := by linarith
              linarith [mul_nonneg hx0 hx12, mul_nonneg hx0 hy14, mul_nonneg hx1 hx12,
                mul_nonneg hx4 hx13, mul_nonneg hx4 hy12, mul_nonneg hx4 hbr8n, mul_nonneg hx8 hy8,
                mul_nonneg hx9 hx10, mul_nonneg hx9 hy14, mul_nonneg hx10 hy13,
                mul_nonneg hx10 hbr2n, mul_nonneg hx10 hbr7n, mul_nonneg hx11 hy11,
                mul_nonneg hx12 hbr2n, mul_nonneg hx12 hbr6n, mul_nonneg hx12 hbr7n,
                mul_nonneg hx13 hy8, mul_nonneg hx14 hy8, mul_nonneg hy4 hy11, mul_nonneg hy8 hy12,
                mul_nonneg hy8 hbr8n, mul_nonneg hy11 hbr8n, mul_nonneg hy13 hy14,
                mul_nonneg hy14 hbr2n, mul_nonneg hy14 hbr7n]
            · have hbr8n : (0 : ℝ) ≤ y1 - (0) := by linarith
              rcases le_total x1 (1 / 2 : ℝ) with hbr9 | hbr9
              · have hbr9n : (0 : ℝ) ≤ 1 / 2 - x1 := by linarith
                linarith [mul_nonneg hx1 hx10, mul_nonneg hx2 hx12, mul_nonneg hx2 hy8,
                  mul_nonneg hx8 hx10, mul_nonneg hx8 hy8, mul_nonneg hx10 hbr2n,
                  mul_nonneg hx10 hbr6n, mul_nonneg hx10 hbr8n, mul_nonneg hx10 hbr9n,
                  mul_nonneg hx11 hbr8n, mul_nonneg hx11 hbr9n, mul_nonneg hx12 hbr0n,
                  mul_nonneg hx12 hbr6n, mul_nonneg hx13 hy8, mul_nonneg hx13 hy14,
                  mul_nonneg hy1 hbr8n, mul_nonneg hy1 hbr9n, mul_nonneg hy8 hbr0n,
                  mul_nonneg hy8 hbr6n, mul_nonneg hy14 hbr0n, mul_nonneg hy14 hbr2n,
                  mul_nonneg hy14 hbr7n]
              · have hbr9n : (0 : ℝ) ≤ x1 - (1 / 2) := by linarith
                linarith [mul_nonneg hx0 hy8, mul_nonneg hx0 hbr9n, mul_nonneg hx4 hx8,
                  mul_nonneg hx4 hy12, mul_nonneg hx4 hbr2n, mul_nonneg hx4 hbr6n,
                  mul_nonneg hx8 hy8, mul_nonneg hx10 hx12, mul_nonneg hx13 hbr8n,
                  mul_nonneg hx14 hy14, mul_nonneg hy8 hy12, mul_nonneg hy14 hbr1n,
                  mul_nonneg hy14 hbr2n, mul_nonneg hbr0n hbr8n, mul_nonneg hbr2n hbr9n,
                  mul_nonneg hbr8n hbr9n]
          · have hbr7n : (0 : ℝ) ≤ y2 - (0) := by linarith
            linarith [mul_nonneg hx0 hx12, mul_nonneg hx0 hy8, mul_nonneg hx4 hx13,
              mul_nonneg hx4 hbr0n, mul_nonneg hx4 hbr6n, mul_nonneg hx8 hy8, mul_nonneg hx8 hbr7n,
              mul_nonneg hx9 hx10, mul_nonneg hx9 hbr0n, mul_nonneg hx10 hy13,
              mul_nonneg hx10 hbr2n, mul_nonneg hx11 hy13, mul_nonneg hx11 hbr2n,
              mul_nonneg hx12 hy11, mul_nonneg hx12 hbr2n, mul_nonneg hx13 hy13,
              mul_nonneg hx14 hbr7n, mul_nonneg hy8 hbr6n, mul_nonneg hy13 hbr0n,
              mul_nonneg hbr1n hbr7n, mul_nonneg hbr2n hbr7n]
    · have hbr1n : (0 : ℝ) ≤ y2 - (1 / 2) := by linarith
      rcases le_total x1 (1 / 2 : ℝ) with hbr10 | hbr10
      · have hbr10n : (0 : ℝ) ≤ 1 / 2 - x1 := by linarith
        rcases le_total x0 (1 / 2 : ℝ) with hbr11 | hbr11
        · have hbr11n : (0 : ℝ) ≤ 1 / 2 - x0 := by linarith
          linarith [mul_nonneg hx10 hx14, mul_nonneg hx11 hy10, mul_nonneg hx11 hy11,
            mul_nonneg hx11 hy13, mul_nonneg hx12 hy10, mul_nonneg hx12 hy12,
            mul_nonneg hx12 hbr11n, mul_nonneg hx13 hy2, mul_nonneg hx13 hy13,
            mul_nonneg hx13 hbr10n, mul_nonneg hx14 hy0, mul_nonneg hx14 hbr0n,
            mul_nonneg hx14 hbr1n, mul_nonneg hy0 hy10, mul_nonneg hy0 hy11, mul_nonneg hy0 hbr11n,
            mul_nonneg hy2 hy12, mul_nonneg hy2 hbr11n, mul_nonneg hy8 hy10, mul_nonneg hy8 hbr11n,
            mul_nonneg hy10 hbr1n, mul_nonneg hy12 hbr10n, mul_nonneg hy13 hbr0n,
            mul_nonneg hbr0n hbr10n]
        · have hbr11n : (0 : ℝ) ≤ x0 - (1 / 2) := by linarith
          rcases le_total y1 (0 : ℝ) with hbr12 | hbr12
          · have hbr12n : (0 : ℝ) ≤ 0 - y1 := by linarith
            linarith [mul_nonneg hx0 hx14, mul_nonneg hx1 hx13, mul_nonneg hx1 hbr1n,
              mul_nonneg hx1 hbr12n, mul_nonneg hx4 hx8, mul_nonneg hx8 hy2, mul_nonneg hx8 hbr10n,
              mul_nonneg hx8 hbr11n, mul_nonneg hx10 hy10, mul_nonneg hx13 hy10,
              mul_nonneg hx13 hy11, mul_nonneg hx14 hy13, mul_nonneg hx14 hbr1n,
              mul_nonneg hx14 hbr11n, mul_nonneg hy1 hy10, mul_nonneg hy2 hy12,
              mul_nonneg hy8 hy11, mul_nonneg hy10 hbr1n, mul_nonneg hy10 hbr11n,
              mul_nonneg hy11 hbr1n, mul_nonneg hy11 hbr12n, mul_nonneg hy12 hy13,
              mul_nonneg hy12 hbr10n, mul_nonneg hy12 hbr11n]
          · have hbr12n : (0 : ℝ) ≤ y1 - (0) := by linarith
            linarith [mul_nonneg hx0 hx8, mul_nonneg hx1 hbr0n, mul_nonneg hx2 hx14,
              mul_nonneg hx2 hy10, mul_nonneg hx8 hy8, mul_nonneg hx8 hbr1n, mul_nonneg hx8 hbr11n,
              mul_nonneg hx8 hbr12n, mul_nonneg hx11 hbr10n, mul_nonneg hx11 hbr12n,
              mul_nonneg hx13 hy12, mul_nonneg hx13 hbr12n, mul_nonneg hx14 hbr0n,
              mul_nonneg hx14 hbr1n, mul_nonneg hy0 hy10, mul_nonneg hy0 hy12,
              mul_nonneg hy4 hbr10n, mul_nonneg hy4 hbr11n, mul_nonneg hy4 hbr12n,
              mul_nonneg hy10 hbr0n, mul_nonneg hy10 hbr1n, mul_nonneg hy12 hbr1n,
              mul_nonneg hy12 hbr11n]
      · have hbr10n : (0 : ℝ) ≤ x1 - (1 / 2) := by linarith
        rcases le_total x0 (1 / 2 : ℝ) with hbr13 | hbr13
        · have hbr13n : (0 : ℝ) ≤ 1 / 2 - x0 := by linarith
          rcases le_total y1 (0 : ℝ) with hbr14 | hbr14
          · have hbr14n : (0 : ℝ) ≤ 0 - y1 := by linarith
            rcases le_total x0 (0 : ℝ) with hbr15 | hbr15
            · have hbr15n : (0 : ℝ) ≤ 0 - x0 := by linarith
              linarith [mul_nonneg hx4 hx14, mul_nonneg hx4 hy13, mul_nonneg hx9 hx13,
                mul_nonneg hx9 hy5, mul_nonneg hx9 hy14, mul_nonneg hx9 hbr14n,
                mul_nonneg hx10 hx11, mul_nonneg hx11 hy11, mul_nonneg hx11 hbr1n,
                mul_nonneg hx11 hbr10n, mul_nonneg hx11 hbr15n, mul_nonneg hx12 hx14,
                mul_nonneg hx12 hy10, mul_nonneg hx12 hy13, mul_nonneg hx14 hy8,
                mul_nonneg hx14 hbr1n, mul_nonneg hy0 hy13, mul_nonneg hy1 hy13,
                mul_nonneg hy2 hy11, mul_nonneg hy2 hy12, mul_nonneg hy2 hy14,
                mul_nonneg hy2 hbr15n, mul_nonneg hy8 hy10, mul_nonneg hy10 hy14,
                mul_nonneg hy10 hbr1n, mul_nonneg hy13 hbr14n]
            · have hbr15n : (0 : ℝ) ≤ x0 - (0) := by linarith
              linarith [mul_nonneg hx0 hx14, mul_nonneg hx1 hy1, mul_nonneg hx1 hy8,
                mul_nonneg hx1 hbr15n, mul_nonneg hx2 hy13, mul_nonneg hx4 hy10,
                mul_nonneg hx9 hx13, mul_nonneg hx9 hy12, mul_nonneg hx9 hbr10n,
                mul_nonneg hx9 hbr13n, mul_nonneg hx9 hbr14n, mul_nonneg hx10 hx14,
                mul_nonneg hx10 hy10, mul_nonneg hx14 hy11, mul_nonneg hx14 hbr1n,
                mul_nonneg hx14 hbr10n, mul_nonneg hx14 hbr13n, mul_nonneg hx14 hbr14n,
                mul_nonneg hy2 hy11, mul_nonneg hy8 hy10, mul_nonneg hy10 hbr15n,
                mul_nonneg hy11 hbr15n, mul_nonneg hy13 hbr13n, mul_nonneg hy13 hbr14n]
          · have hbr14n : (0 : ℝ) ≤ y1 - (0) := by linarith
            linarith [mul_nonneg hx0 hx9, mul_nonneg hx0 hx11, mul_nonneg hx1 hx12,
              mul_nonneg hx1 hy8, mul_nonneg hx4 hx14, mul_nonneg hx9 hy12, mul_nonneg hx9 hbr10n,
              mul_nonneg hx11 hy12, mul_nonneg hx11 hbr13n, mul_nonneg hx12 hy10,
              mul_nonneg hx12 hy12, mul_nonneg hx13 hbr14n, mul_nonneg hx14 hy8,
              mul_nonneg hx14 hbr1n, mul_nonneg hy0 hy11, mul_nonneg hy0 hbr13n,
              mul_nonneg hy2 hy12, mul_nonneg hy2 hbr13n, mul_nonneg hy8 hy10,
              mul_nonneg hy10 hbr1n, mul_nonneg hy12 hbr14n, mul_nonneg hbr0n hbr14n,
              mul_nonneg hbr1n hbr14n, mul_nonneg hbr10n hbr14n]
        · have hbr13n : (0 : ℝ) ≤ x0 - (1 / 2) := by linarith
          linarith [mul_nonneg hx0 hx14, mul_nonneg hx0 hy10, mul_nonneg hx1 hx6,
            mul_nonneg hx1 hx10, mul_nonneg hx1 hy14, mul_nonneg hx1 hbr10n, mul_nonneg hx1 hbr13n,
            mul_nonneg hx8 hbr13n, mul_nonneg hx9 hbr10n, mul_nonneg hy0 hy10, mul_nonneg hy0 hy11,
            mul_nonneg hy1 hy10, mul_nonneg hy10 hbr1n, mul_nonneg hy11 hbr1n,
            mul_nonneg hy12 hy13, mul_nonneg hy12 hbr13n, mul_nonneg hy13 hbr10n,
            mul_nonneg hbr10n hbr13n]
  · have hbr0n : (0 : ℝ) ≤ y1 - (1 / 2) := by linarith
    rcases le_total x2 (1 / 2 : ℝ) with hbr16 | hbr16
    · have hbr16n : (0 : ℝ) ≤ 1 / 2 - x2 := by linarith
      rcases le_total y0 (1 / 2 : ℝ) with hbr17 | hbr17
      · have hbr17n : (0 : ℝ) ≤ 1 / 2 - y0 := by linarith
        rcases le_total x0 (1 / 2 : ℝ) with hbr18 | hbr18
        · have hbr18n : (0 : ℝ) ≤ 1 / 2 - x0 := by linarith
          linarith [mul_nonneg hx9 hx13, mul_nonneg hx11 hy9, mul_nonneg hx11 hy11,
            mul_nonneg hx11 hy12, mul_nonneg hx12 hy4, mul_nonneg hx12 hy12,
            mul_nonneg hx12 hbr18n, mul_nonneg hx13 hy0, mul_nonneg hx13 hbr0n,
            mul_nonneg hx13 hbr17n, mul_nonneg hx14 hy9, mul_nonneg hx14 hy14,
            mul_nonneg hx14 hbr16n, mul_nonneg hy0 hy9, mul_nonneg hy0 hy11, mul_nonneg hy0 hbr16n,
            mul_nonneg hy4 hy14, mul_nonneg hy4 hbr16n, mul_nonneg hy9 hy10, mul_nonneg hy9 hbr0n,
            mul_nonneg hy10 hbr16n, mul_nonneg hy12 hbr17n, mul_nonneg hy14 hbr18n,
            mul_nonneg hbr17n hbr18n]
        · have hbr18n : (0 : ℝ) ≤ x0 - (1 / 2) := by linarith
          rcases le_total y0 (0 : ℝ) with hbr19 | hbr19
          · have hbr19n : (0 : ℝ) ≤ 0 - y0 := by linarith
            rcases le_total x2 (0 : ℝ) with hbr20 | hbr20
            · have hbr20n : (0 : ℝ) ≤ 0 - x2 := by linarith
              linarith [mul_nonneg hx1 hx13, mul_nonneg hx5 hy12, mul_nonneg hx6 hy4,
                mul_nonneg hx8 hx12, mul_nonneg hx8 _hy3, mul_nonneg hx8 hy8, mul_nonneg hx8 hbr19n,
                mul_nonneg hx9 hx11, mul_nonneg hx11 hy11, mul_nonneg hx11 hy12,
                mul_nonneg hx11 hbr18n, mul_nonneg hx11 hbr20n, mul_nonneg hx13 hx14,
                mul_nonneg hx13 hy10, mul_nonneg hx13 hbr0n, mul_nonneg hx14 hy9,
                mul_nonneg hx14 hy12, mul_nonneg hy4 hy11, mul_nonneg hy4 hbr20n,
                mul_nonneg hy9 hy10, mul_nonneg hy12 hbr19n]
            · have hbr20n : (0 : ℝ) ≤ x2 - (0) := by linarith
              linarith [mul_nonneg hx0 hx13, mul_nonneg hx2 hy2, mul_nonneg hx2 hy10,
                mul_nonneg hx2 hbr20n, mul_nonneg hx4 hy12, mul_nonneg hx8 hx12,
                mul_nonneg hx8 hy9, mul_nonneg hx8 hy14, mul_nonneg hx8 hbr16n,
                mul_nonneg hx8 hbr18n, mul_nonneg hx8 hbr19n, mul_nonneg hx9 hy9,
                mul_nonneg hx13 hy11, mul_nonneg hx13 hy14, mul_nonneg hx13 hbr0n,
                mul_nonneg hx13 hbr18n, mul_nonneg hx13 hbr19n, mul_nonneg hy4 hy11,
                mul_nonneg hy9 hy10, mul_nonneg hy9 hbr20n, mul_nonneg hy11 hbr20n,
                mul_nonneg hy12 hbr16n, mul_nonneg hy12 hbr19n]
          · have hbr19n : (0 : ℝ) ≤ y0 - (0) := by linarith
            linarith [mul_nonneg hx0 hx8, mul_nonneg hx0 hx11, mul_nonneg hx1 hx13,
              mul_nonneg hx2 hx14, mul_nonneg hx2 hy10, mul_nonneg hx8 hy14, mul_nonneg hx8 hbr18n,
              mul_nonneg hx11 hy14, mul_nonneg hx11 hbr16n, mul_nonneg hx13 hy10,
              mul_nonneg hx13 hbr0n, mul_nonneg hx14 hy9, mul_nonneg hx14 hy14,
              mul_nonneg hy0 hy11, mul_nonneg hy0 hbr16n, mul_nonneg hy2 hbr19n,
              mul_nonneg hy4 hy11, mul_nonneg hy4 hy14, mul_nonneg hy4 hbr16n, mul_nonneg hy9 hy10,
              mul_nonneg hy9 hbr0n, mul_nonneg hbr0n hbr19n, mul_nonneg hbr17n hbr19n,
              mul_nonneg hbr18n hbr19n]
      · have hbr17n : (0 : ℝ) ≤ y0 - (1 / 2) := by linarith
        linarith [mul_nonneg hx0 hx11, mul_nonneg hx0 hy0, mul_nonneg hx0 hbr16n,
          mul_nonneg hx1 hx11, mul_nonneg hx1 hy1, mul_nonneg hx1 hbr16n, mul_nonneg hx8 hx12,
          mul_nonneg hx9 hx13, mul_nonneg hx12 hx13, mul_nonneg hx12 hy9, mul_nonneg hx12 hbr17n,
          mul_nonneg hx13 hy8, mul_nonneg hx13 hbr0n, mul_nonneg hx14 hy1, mul_nonneg hy0 hy1,
          mul_nonneg hy0 hy14, mul_nonneg hy0 hbr16n, mul_nonneg hy1 hbr0n, mul_nonneg hy1 hbr17n,
          mul_nonneg hy8 hy9, mul_nonneg hy8 hbr17n, mul_nonneg hy9 hbr0n]
    · have hbr16n : (0 : ℝ) ≤ x2 - (1 / 2) := by linarith
      rcases le_total y0 (1 / 2 : ℝ) with hbr21 | hbr21
      · have hbr21n : (0 : ℝ) ≤ 1 / 2 - y0 := by linarith
        rcases le_total x0 (1 / 2 : ℝ) with hbr22 | hbr22
        · have hbr22n : (0 : ℝ) ≤ 1 / 2 - x0 := by linarith
          rcases le_total y0 (0 : ℝ) with hbr23 | hbr23
          · have hbr23n : (0 : ℝ) ≤ 0 - y0 := by linarith
            linarith [mul_nonneg hx0 hx13, mul_nonneg hx2 hx12, mul_nonneg hx2 hbr0n,
              mul_nonneg hx2 hbr23n, mul_nonneg hx9 hy9, mul_nonneg hx10 hy4, mul_nonneg hx10 hy10,
              mul_nonneg hx10 hy12, mul_nonneg hx10 hbr16n, mul_nonneg hx10 hbr22n,
              mul_nonneg hx12 hy9, mul_nonneg hx12 hy11, mul_nonneg hx13 hy12,
              mul_nonneg hx13 hbr0n, mul_nonneg hx13 hbr16n, mul_nonneg hy2 hy9,
              mul_nonneg hy4 hy14, mul_nonneg hy9 hbr0n, mul_nonneg hy10 hy11,
              mul_nonneg hy11 hbr0n, mul_nonneg hy11 hbr23n, mul_nonneg hy12 hy14,
              mul_nonneg hy14 hbr16n, mul_nonneg hy14 hbr22n]
          · have hbr23n : (0 : ℝ) ≤ y0 - (0) := by linarith
            linarith [mul_nonneg hx0 hx10, mul_nonneg hx2 hbr21n, mul_nonneg hx4 hx13,
              mul_nonneg hx4 hy9, mul_nonneg hx10 hy10, mul_nonneg hx10 hbr0n,
              mul_nonneg hx10 hbr16n, mul_nonneg hx10 hbr23n, mul_nonneg hx11 hbr22n,
              mul_nonneg hx11 hbr23n, mul_nonneg hx12 hy14, mul_nonneg hx12 hbr23n,
              mul_nonneg hx13 hbr0n, mul_nonneg hx13 hbr21n, mul_nonneg hy0 hy9,
              mul_nonneg hy0 hy14, mul_nonneg hy1 hbr16n, mul_nonneg hy1 hbr22n,
              mul_nonneg hy1 hbr23n, mul_nonneg hy9 hbr0n, mul_nonneg hy9 hbr21n,
              mul_nonneg hy14 hbr0n, mul_nonneg hy14 hbr16n]
        · have hbr22n : (0 : ℝ) ≤ x0 - (1 / 2) := by linarith
          linarith [mul_nonneg hx0 hx13, mul_nonneg hx0 hy9, mul_nonneg hx2 hx5,
            mul_nonneg hx2 hx9, mul_nonneg hx2 hy13, mul_nonneg hx2 hbr0n, mul_nonneg hx8 hbr22n,
            mul_nonneg hx10 hbr16n, mul_nonneg hy0 hy11, mul_nonneg hy2 hy9, mul_nonneg hy9 hy10,
            mul_nonneg hy9 hbr0n, mul_nonneg hy9 hbr21n, mul_nonneg hy11 hbr0n,
            mul_nonneg hy12 hy14, mul_nonneg hy12 hbr22n, mul_nonneg hy14 hbr16n,
            mul_nonneg hbr16n hbr22n]
      · have hbr21n : (0 : ℝ) ≤ y0 - (1 / 2) := by linarith
        linarith [mul_nonneg hx0 hx10, mul_nonneg hx0 hx11, mul_nonneg hx1 hx10,
          mul_nonneg hx10 hy0, mul_nonneg hx10 hbr16n, mul_nonneg hx11 hbr16n,
          mul_nonneg hx12 hx13, mul_nonneg hx12 hbr21n, mul_nonneg hx13 hbr0n, mul_nonneg hx14 hy1,
          mul_nonneg hy0 hy14, mul_nonneg hy1 hy6, mul_nonneg hy1 hy10, mul_nonneg hy1 hbr16n,
          mul_nonneg hy8 hbr21n, mul_nonneg hy9 hbr0n, mul_nonneg hbr0n hbr21n]

set_option maxHeartbeats 1600000 in
-- the branch-and-certify case tree is large
theorem certC11 (x0 x1 x2 y0 y1 y2 : ℝ)
    (hx0 : (0 : ℝ) ≤ 3 / 2 - (x0 + x1 + x2)) (_hx1 : (0 : ℝ) ≤ 3 / 2 - (x0 + x1 - x2))
    (hx2 : (0 : ℝ) ≤ 3 / 2 - (x0 - x1 + x2)) (_hx3 : (0 : ℝ) ≤ 3 / 2 - (x0 - x1 - x2))
    (hx4 : (0 : ℝ) ≤ 3 / 2 - (-x0 + x1 + x2)) (hx5 : (0 : ℝ) ≤ 3 / 2 - (-x0 + x1 - x2))
    (hx6 : (0 : ℝ) ≤ 3 / 2 - (-x0 - x1 + x2)) (hx7 : (0 : ℝ) ≤ 3 / 2 - (-x0 - x1 - x2))
    (_hx8 : (0 : ℝ) ≤ 13 / 15 - x0) (hx9 : (0 : ℝ) ≤ 13 / 15 - x1)
    (hx10 : (0 : ℝ) ≤ 13 / 15 - x2) (hx11 : (0 : ℝ) ≤ 5 / 12 - (x0 + x1 + x2))
    (hx12 : (0 : ℝ) ≤ x1 - x0) (hx13 : (0 : ℝ) ≤ x2 - x0)
    (hy0 : (0 : ℝ) ≤ 3 / 2 - (y0 + y1 + y2)) (hy1 : (0 : ℝ) ≤ 3 / 2 - (y0 + y1 - y2))
    (_hy2 : (0 : ℝ) ≤ 3 / 2 - (y0 - y1 + y2)) (_hy3 : (0 : ℝ) ≤ 3 / 2 - (y0 - y1 - y2))
    (hy4 : (0 : ℝ) ≤ 3 / 2 - (-y0 + y1 + y2)) (hy5 : (0 : ℝ) ≤ 3 / 2 - (-y0 + y1 - y2))
    (hy6 : (0 : ℝ) ≤ 3 / 2 - (-y0 - y1 + y2)) (hy7 : (0 : ℝ) ≤ 3 / 2 - (-y0 - y1 - y2))
    (_hy8 : (0 : ℝ) ≤ 13 / 15 - y0) (hy9 : (0 : ℝ) ≤ 13 / 15 - y1)
    (hy10 : (0 : ℝ) ≤ 13 / 15 - y2) (hy11 : (0 : ℝ) ≤ 5 / 12 - (y0 + y1 + y2))
    (hy12 : (0 : ℝ) ≤ y1 - y0) (hy13 : (0 : ℝ) ≤ y2 - y0)
    :
    (x0 - y0) ^ 2 + (x1 - y1) ^ 2 + (x2 - y2) ^ 2 ≤ 149 / 50 := by
  rcases le_total y2 (0 : ℝ) with hbr0 | hbr0
  · have hbr0n : (0 : ℝ) ≤ 0 - y2 := by linarith
    rcases le_total x2 (0 : ℝ) with hbr1 | hbr1
    · have hbr1n : (0 : ℝ) ≤ 0 - x2 := by linarith
      rcases le_total y1 (0 : ℝ) with hbr2 | hbr2
      · have hbr2n : (0 : ℝ) ≤ 0 - y1 := by linarith
        linarith [mul_nonneg hx4 hx13, mul_nonneg hx4 hbr0n, mul_nonneg hx5 hx11,
          mul_nonneg hx5 hx13, mul_nonneg hx5 hy7, mul_nonneg hx5 hbr1n, mul_nonneg hx6 hx9,
          mul_nonneg hx6 hx13, mul_nonneg hx6 hy6, mul_nonneg hx6 hbr0n, mul_nonneg hx7 hx9,
          mul_nonneg hx7 hx11, mul_nonneg hx7 hy7, mul_nonneg hx9 hx12, mul_nonneg hx9 hbr2n,
          mul_nonneg hx12 hy12, mul_nonneg hx13 hy12, mul_nonneg hy5 hy12, mul_nonneg hy6 hy13,
          mul_nonneg hy6 hbr1n, mul_nonneg hy7 hbr0n, mul_nonneg hy7 hbr2n, mul_nonneg hy12 hbr1n]
      · have hbr2n : (0 : ℝ) ≤ y1 - (0) := by linarith
        rcases le_total y0 (-1 : ℝ) with hbr3 | hbr3
        · have hbr3n : (0 : ℝ) ≤ -1 - y0 := by linarith
          linarith [mul_nonneg hx4 hx13, mul_nonneg hx4 hy4, mul_nonneg hx4 hbr0n,
            mul_nonneg hx5 hx13, mul_nonneg hx5 hy5, mul_nonneg hx5 hbr1n, mul_nonneg hx6 hx11,
            mul_nonneg hx6 hx13, mul_nonneg hx6 hbr0n, mul_nonneg hx6 hbr2n, mul_nonneg hx7 hx11,
            mul_nonneg hx7 hy7, mul_nonneg hx7 hbr2n, mul_nonneg hx9 hx12, mul_nonneg hx9 hbr1n,
            mul_nonneg hx11 hx12, mul_nonneg hx11 hbr3n, mul_nonneg hx12 hbr2n,
            mul_nonneg hx13 hbr3n, mul_nonneg hy4 hy13, mul_nonneg hy4 hbr1n, mul_nonneg hy5 hy12,
            mul_nonneg hy5 hbr2n, mul_nonneg hy7 hbr0n, mul_nonneg hbr2n hbr3n]
        · have hbr3n : (0 : ℝ) ≤ y0 - (-1) := by linarith
          linarith [mul_nonneg hx5 hx12, mul_nonneg hx5 hy9, mul_nonneg hx6 hx11,
            mul_nonneg hx6 hbr2n, mul_nonneg hx6 hbr3n, mul_nonneg hx7 hx11, mul_nonneg hx7 hy7,
            mul_nonneg hx7 hbr2n, mul_nonneg hx7 hbr3n, mul_nonneg hx9 hy9, mul_nonneg hx12 hy12,
            mul_nonneg hx12 hy13, mul_nonneg hx12 hbr0n, mul_nonneg hx13 hy11,
            mul_nonneg hx13 hy13, mul_nonneg hx13 hbr1n, mul_nonneg hy4 hy13, mul_nonneg hy5 hy11,
            mul_nonneg hy9 hbr0n, mul_nonneg hy9 hbr2n, mul_nonneg hy11 hbr1n,
            mul_nonneg hy11 hbr3n, mul_nonneg hy13 hbr0n, mul_nonneg hy13 hbr3n,
            mul_nonneg hbr0n hbr1n]
    · have hbr1n : (0 : ℝ) ≤ x2 - (0) := by linarith
      rcases le_total y1 (0 : ℝ) with hbr4 | hbr4
      · have hbr4n : (0 : ℝ) ≤ 0 - y1 := by linarith
        rcases le_total x1 (0 : ℝ) with hbr5 | hbr5
        · have hbr5n : (0 : ℝ) ≤ 0 - x1 := by linarith
          linarith [mul_nonneg _hx1 hbr4n, mul_nonneg hx4 hx12, mul_nonneg hx4 hy5,
            mul_nonneg hx5 hx10, mul_nonneg hx5 hx12, mul_nonneg hx5 hbr4n, mul_nonneg hx6 hx11,
            mul_nonneg hx6 hy7, mul_nonneg hx7 hy7, mul_nonneg hx10 hy6, mul_nonneg hx10 hbr0n,
            mul_nonneg hx10 hbr1n, mul_nonneg hx11 hy1, mul_nonneg hx11 hy11, mul_nonneg hx11 hy13,
            mul_nonneg hx12 hy12, mul_nonneg hx12 hy13, mul_nonneg hx13 hy13, mul_nonneg hy5 hy12,
            mul_nonneg hy5 hbr5n, mul_nonneg hy6 hy13, mul_nonneg hy7 hy11, mul_nonneg hy7 hbr4n,
            mul_nonneg hy13 hbr0n]
        · have hbr5n : (0 : ℝ) ≤ x1 - (0) := by linarith
          linarith [mul_nonneg hx4 hx11, mul_nonneg hx4 hx12, mul_nonneg hx4 hx13,
            mul_nonneg hx4 hy4, mul_nonneg hx4 hy7, mul_nonneg hx5 hx11, mul_nonneg hx6 hx11,
            mul_nonneg hx7 hy7, mul_nonneg hx9 hbr4n, mul_nonneg hx9 hbr5n, mul_nonneg hx10 hbr0n,
            mul_nonneg hx10 hbr1n, mul_nonneg hx11 hy11, mul_nonneg hx11 hy12,
            mul_nonneg hx11 hy13, mul_nonneg hx12 hy12, mul_nonneg hx13 hy13, mul_nonneg hy4 hy7,
            mul_nonneg hy5 hy12, mul_nonneg hy6 hy13, mul_nonneg hy7 hy11, mul_nonneg hy7 hbr0n,
            mul_nonneg hy12 hbr4n, mul_nonneg hbr1n hbr5n]
      · have hbr4n : (0 : ℝ) ≤ y1 - (0) := by linarith
        rcases le_total x0 (-1 / 2 : ℝ) with hbr6 | hbr6
        · have hbr6n : (0 : ℝ) ≤ -1 / 2 - x0 := by linarith
          linarith [mul_nonneg hx4 hx12, mul_nonneg hx4 hy9, mul_nonneg hx5 hy5,
            mul_nonneg hx6 hx9, mul_nonneg hx6 hy6, mul_nonneg hx6 hbr0n, mul_nonneg hx6 hbr4n,
            mul_nonneg hx7 hy7, mul_nonneg hx7 hbr6n, mul_nonneg hx10 hy9, mul_nonneg hx10 hy11,
            mul_nonneg hx10 hbr0n, mul_nonneg hx10 hbr1n, mul_nonneg hx12 hy13,
            mul_nonneg hx12 hbr4n, mul_nonneg hy4 hy13, mul_nonneg hy5 hy11, mul_nonneg hy5 hbr1n,
            mul_nonneg hy6 hy13, mul_nonneg hy9 hbr4n, mul_nonneg hy11 hbr6n,
            mul_nonneg hy13 hbr1n, mul_nonneg hy13 hbr6n]
        · have hbr6n : (0 : ℝ) ≤ x0 - (-1 / 2) := by linarith
          rcases le_total y1 (1 / 2 : ℝ) with hbr7 | hbr7
          · have hbr7n : (0 : ℝ) ≤ 1 / 2 - y1 := by linarith
            linarith [mul_nonneg hx4 hx12, mul_nonneg hx5 hx12, mul_nonneg hx5 hy5,
              mul_nonneg hx6 hx11, mul_nonneg hx6 hy7, mul_nonneg hx6 hbr4n, mul_nonneg hx7 hy7,
              mul_nonneg hx10 hy4, mul_nonneg hx10 hy11, mul_nonneg hx10 hbr0n,
              mul_nonneg hx10 hbr1n, mul_nonneg hx11 hy13, mul_nonneg hx11 hbr7n,
              mul_nonneg hx12 hy13, mul_nonneg hx12 hbr4n, mul_nonneg hx13 hy13,
              mul_nonneg hy5 hy11, mul_nonneg hy5 hy12, mul_nonneg hy6 hy13, mul_nonneg hy7 hy11,
              mul_nonneg hy7 hbr6n, mul_nonneg hy7 hbr7n, mul_nonneg hy13 hbr0n]
          · have hbr7n : (0 : ℝ) ≤ y1 - (1 / 2) := by linarith
            linarith [mul_nonneg hx4 hx12, mul_nonneg hx5 hx12, mul_nonneg hx6 hx11,
              mul_nonneg hx6 hy6, mul_nonneg hx6 hbr1n, mul_nonneg hx6 hbr4n, mul_nonneg hx7 hy5,
              mul_nonneg hx10 hy11, mul_nonneg hx10 hbr1n, mul_nonneg hx10 hbr6n,
              mul_nonneg hx11 hy9, mul_nonneg hx12 hy12, mul_nonneg hx12 hy13,
              mul_nonneg hx12 hbr7n, mul_nonneg hx13 hy13, mul_nonneg hy4 hy13,
              mul_nonneg hy5 hy11, mul_nonneg hy5 hy12, mul_nonneg hy5 hbr0n, mul_nonneg hy5 hbr1n,
              mul_nonneg hy5 hbr6n, mul_nonneg hy7 hy9, mul_nonneg hy9 hbr4n, mul_nonneg hy9 hbr7n,
              mul_nonneg hy13 hbr1n, mul_nonneg hy13 hbr7n]
  · have hbr0n : (0 : ℝ) ≤ y2 - (0) := by linarith
    rcases le_total y0 (-1 / 2 : ℝ) with hbr8 | hbr8
    · have hbr8n : (0 : ℝ) ≤ -1 / 2 - y0 := by linarith
      rcases le_total x2 (0 : ℝ) with hbr9 | hbr9
      · have hbr9n : (0 : ℝ) ≤ 0 - x2 := by linarith
        rcases le_total x1 (0 : ℝ) with hbr10 | hbr10
        · have hbr10n : (0 : ℝ) ≤ 0 - x1 := by linarith
          linarith [mul_nonneg hx5 hx12, mul_nonneg hx5 hy4, mul_nonneg hx5 hy9,
            mul_nonneg hx6 hx13, mul_nonneg hx6 hy10, mul_nonneg hx7 hy4, mul_nonneg hx7 hy7,
            mul_nonneg hx7 hbr9n, mul_nonneg hx7 hbr10n, mul_nonneg hx12 hy6, mul_nonneg hx12 hy10,
            mul_nonneg hx12 hbr8n, mul_nonneg hx13 hy9, mul_nonneg hx13 hbr0n,
            mul_nonneg hx13 hbr8n, mul_nonneg hy4 hy12, mul_nonneg hy4 hbr8n, mul_nonneg hy5 hbr8n,
            mul_nonneg hy6 hy9, mul_nonneg hy7 hy11, mul_nonneg hy9 hbr10n, mul_nonneg hy10 hbr0n,
            mul_nonneg hy10 hbr9n, mul_nonneg hy11 hbr0n, mul_nonneg hy11 hbr10n]
        · have hbr10n : (0 : ℝ) ≤ x1 - (0) := by linarith
          linarith [mul_nonneg hx4 hx13, mul_nonneg hx5 hx11, mul_nonneg hx5 hy5,
            mul_nonneg hx5 hbr0n, mul_nonneg hx6 hx13, mul_nonneg hx6 hy6, mul_nonneg hx7 hy7,
            mul_nonneg hx9 hy4, mul_nonneg hx9 hy10, mul_nonneg hx9 hbr10n, mul_nonneg hx11 hy10,
            mul_nonneg hx11 hbr8n, mul_nonneg hx13 hy12, mul_nonneg hx13 hbr0n,
            mul_nonneg hx13 hbr8n, mul_nonneg hy4 hy12, mul_nonneg hy6 hy9, mul_nonneg hy6 hbr9n,
            mul_nonneg hy6 hbr10n, mul_nonneg hy7 hbr8n, mul_nonneg hy10 hbr0n,
            mul_nonneg hy10 hbr9n, mul_nonneg hy12 hbr10n]
      · have hbr9n : (0 : ℝ) ≤ x2 - (0) := by linarith
        linarith [mul_nonneg hx4 hx12, mul_nonneg hx4 hy4, mul_nonneg hx5 hx12, mul_nonneg hx5 hy5,
          mul_nonneg hx5 hbr0n, mul_nonneg hx6 hx11, mul_nonneg hx6 hy6, mul_nonneg hx6 hbr9n,
          mul_nonneg hx7 hx11, mul_nonneg hx7 hbr0n, mul_nonneg hx9 hy4, mul_nonneg hx11 hy9,
          mul_nonneg hx11 hbr8n, mul_nonneg hx12 hy6, mul_nonneg hx12 hy12, mul_nonneg hx13 hbr8n,
          mul_nonneg _hy2 hbr0n, mul_nonneg _hy3 hbr9n, mul_nonneg hy4 hy12, mul_nonneg hy5 hbr9n,
          mul_nonneg hy6 hy9, mul_nonneg hy6 hbr0n, mul_nonneg hy7 hy9, mul_nonneg hy7 hbr8n,
          mul_nonneg hy7 hbr9n, mul_nonneg hy11 hbr0n]
    · have hbr8n : (0 : ℝ) ≤ y0 - (-1 / 2) := by linarith
      rcases le_total x1 (0 : ℝ) with hbr11 | hbr11
      · have hbr11n : (0 : ℝ) ≤ 0 - x1 := by linarith
        rcases le_total y1 (0 : ℝ) with hbr12 | hbr12
        · have hbr12n : (0 : ℝ) ≤ 0 - y1 := by linarith
          linarith [mul_nonneg hx4 hy10, mul_nonneg hx5 hx11, mul_nonneg hx5 hx12,
            mul_nonneg hx5 hbr0n, mul_nonneg hx5 hbr8n, mul_nonneg hx6 hx13, mul_nonneg hx6 hy10,
            mul_nonneg hx7 hx10, mul_nonneg hx7 hx11, mul_nonneg hx7 hy7, mul_nonneg hx10 hy10,
            mul_nonneg hx12 hy11, mul_nonneg hx12 hy12, mul_nonneg hx12 hbr11n,
            mul_nonneg hx13 hy11, mul_nonneg hx13 hy13, mul_nonneg hx13 hbr12n,
            mul_nonneg hy5 hbr11n, mul_nonneg hy6 hy11, mul_nonneg hy10 hy13,
            mul_nonneg hy10 hbr0n, mul_nonneg hy11 hbr8n, mul_nonneg hy11 hbr11n,
            mul_nonneg hy12 hbr8n, mul_nonneg hy12 hbr12n]
        · have hbr12n : (0 : ℝ) ≤ y1 - (0) := by linarith
          linarith [mul_nonneg hx4 hbr8n, mul_nonneg hx5 hx12, mul_nonneg hx5 hy9,
            mul_nonneg hx6 hx13, mul_nonneg hx6 hy10, mul_nonneg hx7 hx10, mul_nonneg hx7 hx11,
            mul_nonneg hx7 hy7, mul_nonneg hx7 hbr0n, mul_nonneg hx7 hbr8n, mul_nonneg hx11 hy11,
            mul_nonneg hx12 hy11, mul_nonneg hx12 hy12, mul_nonneg hx12 hbr11n,
            mul_nonneg hx12 hbr12n, mul_nonneg hx13 hy11, mul_nonneg hx13 hy13,
            mul_nonneg hx13 hbr0n, mul_nonneg hy9 hbr11n, mul_nonneg hy11 hy13,
            mul_nonneg hy11 hbr0n, mul_nonneg hy11 hbr12n, mul_nonneg hy12 hbr8n,
            mul_nonneg hy13 hbr8n, mul_nonneg hbr0n hbr12n]
      · have hbr11n : (0 : ℝ) ≤ x1 - (0) := by linarith
        rcases le_total x0 (-1 / 2 : ℝ) with hbr13 | hbr13
        · have hbr13n : (0 : ℝ) ≤ -1 / 2 - x0 := by linarith
          linarith [mul_nonneg hx2 hx5, mul_nonneg hx4 hx13, mul_nonneg hx4 hy10,
            mul_nonneg hx5 hy9, mul_nonneg hx5 hbr0n, mul_nonneg hx5 hbr11n, mul_nonneg hx6 hx13,
            mul_nonneg hx7 hx11, mul_nonneg hx7 hbr0n, mul_nonneg hx7 hbr8n, mul_nonneg hx11 hy10,
            mul_nonneg hx11 hy11, mul_nonneg hx12 hy12, mul_nonneg hx13 hy12, mul_nonneg hx13 hy13,
            mul_nonneg hy6 hy11, mul_nonneg hy6 hbr11n, mul_nonneg hy9 hy12, mul_nonneg hy10 hbr0n,
            mul_nonneg hy11 hbr13n, mul_nonneg hy12 hbr8n, mul_nonneg hy12 hbr11n,
            mul_nonneg hy12 hbr13n, mul_nonneg hbr11n hbr13n]
        · have hbr13n : (0 : ℝ) ≤ x0 - (-1 / 2) := by linarith
          linarith [mul_nonneg hx4 hx13, mul_nonneg hx5 hx10, mul_nonneg hx5 hx11,
            mul_nonneg hx5 hx12, mul_nonneg hx5 hbr0n, mul_nonneg hx5 hbr8n, mul_nonneg hx9 hy11,
            mul_nonneg hx9 hbr11n, mul_nonneg hx9 hbr13n, mul_nonneg hx11 hy10,
            mul_nonneg hx12 hy12, mul_nonneg hx13 hy13, mul_nonneg hx13 hbr0n,
            mul_nonneg hx13 hbr13n, mul_nonneg hy1 hy6, mul_nonneg hy4 hy12, mul_nonneg hy6 hy11,
            mul_nonneg hy6 hy13, mul_nonneg hy6 hbr0n, mul_nonneg hy6 hbr11n,
            mul_nonneg hy6 hbr13n, mul_nonneg hy9 hy12, mul_nonneg hy10 hbr0n,
            mul_nonneg hy10 hbr8n, mul_nonneg hy12 hbr8n, mul_nonneg hy12 hbr11n]

set_option maxHeartbeats 1600000 in
-- the branch-and-certify case tree is large
theorem certC22 (x0 x1 x2 y0 y1 y2 : ℝ)
    (hx0 : (0 : ℝ) ≤ 3 / 2 - (x0 + x1 + x2)) (hx1 : (0 : ℝ) ≤ 3 / 2 - (x0 + x1 - x2))
    (hx2 : (0 : ℝ) ≤ 3 / 2 - (x0 - x1 + x2)) (_hx3 : (0 : ℝ) ≤ 3 / 2 - (x0 - x1 - x2))
    (hx4 : (0 : ℝ) ≤ 3 / 2 - (-x0 + x1 + x2)) (hx5 : (0 : ℝ) ≤ 3 / 2 - (-x0 + x1 - x2))
    (hx6 : (0 : ℝ) ≤ 3 / 2 - (-x0 - x1 + x2)) (hx7 : (0 : ℝ) ≤ 3 / 2 - (-x0 - x1 - x2))
    (_hx8 : (0 : ℝ) ≤ 13 / 15 - x0) (hx9 : (0 : ℝ) ≤ 13 / 15 - x1)
    (hx10 : (0 : ℝ) ≤ 13 / 15 - x2) (hx11 : (0 : ℝ) ≤ -(7 / 24) - x0)
    (hx12 : (0 : ℝ) ≤ x1 - x0) (hx13 : (0 : ℝ) ≤ x2 - x0)
    (hy0 : (0 : ℝ) ≤ 3 / 2 - (y0 + y1 + y2)) (hy1 : (0 : ℝ) ≤ 3 / 2 - (y0 + y1 - y2))
    (hy2 : (0 : ℝ) ≤ 3 / 2 - (y0 - y1 + y2)) (_hy3 : (0 : ℝ) ≤ 3 / 2 - (y0 - y1 - y2))
    (hy4 : (0 : ℝ) ≤ 3 / 2 - (-y0 + y1 + y2)) (hy5 : (0 : ℝ) ≤ 3 / 2 - (-y0 + y1 - y2))
    (hy6 : (0 : ℝ) ≤ 3 / 2 - (-y0 - y1 + y2)) (hy7 : (0 : ℝ) ≤ 3 / 2 - (-y0 - y1 - y2))
    (_hy8 : (0 : ℝ) ≤ 13 / 15 - y0) (hy9 : (0 : ℝ) ≤ 13 / 15 - y1)
    (hy10 : (0 : ℝ) ≤ 13 / 15 - y2) (hy11 : (0 : ℝ) ≤ -(7 / 24) - y0)
    (hy12 : (0 : ℝ) ≤ y1 - y0) (hy13 : (0 : ℝ) ≤ y2 - y0)
    :
    (x0 - y0) ^ 2 + (x1 - y1) ^ 2 + (x2 - y2) ^ 2 ≤ 149 / 50 := by
  rcases le_total y2 (0 : ℝ) with hbr0 | hbr0
  · have hbr0n : (0 : ℝ) ≤ 0 - y2 := by linarith
    rcases le_total x1 (0 : ℝ) with hbr1 | hbr1
    · have hbr1n : (0 : ℝ) ≤ 0 - x1 := by linarith
      rcases le_total x2 (0 : ℝ) with hbr2 | hbr2
      · have hbr2n : (0 : ℝ) ≤ 0 - x2 := by linarith
        linarith [mul_nonneg hx0 hx7, mul_nonneg hx1 hy9, mul_nonneg hx4 hx12, mul_nonneg hx5 hx12,
          mul_nonneg hx5 hbr2n, mul_nonneg hx6 hx13, mul_nonneg hx6 hy4, mul_nonneg hx6 hbr0n,
          mul_nonneg hx7 hy5, mul_nonneg hx7 hy7, mul_nonneg hx7 hbr1n, mul_nonneg hx12 hy11,
          mul_nonneg hx12 hy12, mul_nonneg hx12 hbr0n, mul_nonneg hx12 hbr1n, mul_nonneg hx13 hy11,
          mul_nonneg hx13 hy13, mul_nonneg hy2 hbr2n, mul_nonneg hy5 hy11, mul_nonneg hy6 hy9,
          mul_nonneg hy6 hbr2n, mul_nonneg hy7 hy9, mul_nonneg hy9 hbr1n, mul_nonneg hy13 hbr0n,
          mul_nonneg hbr0n hbr2n]
      · have hbr2n : (0 : ℝ) ≤ x2 - (0) := by linarith
        rcases le_total y1 (0 : ℝ) with hbr3 | hbr3
        · have hbr3n : (0 : ℝ) ≤ 0 - y1 := by linarith
          linarith [mul_nonneg hx0 hbr3n, mul_nonneg hx4 hy5, mul_nonneg hx4 hbr3n,
            mul_nonneg hx5 hx10, mul_nonneg hx5 hbr3n, mul_nonneg hx6 hx11, mul_nonneg hx6 hy7,
            mul_nonneg hx7 hx10, mul_nonneg hx7 hy7, mul_nonneg hx10 hy2, mul_nonneg hx10 hbr0n,
            mul_nonneg hx11 hy11, mul_nonneg hx11 hy13, mul_nonneg hx12 hy2, mul_nonneg hx12 hbr1n,
            mul_nonneg hx13 hy13, mul_nonneg hy0 hy7, mul_nonneg hy2 hy5, mul_nonneg hy4 hy13,
            mul_nonneg hy5 hy12, mul_nonneg hy5 hbr1n, mul_nonneg hy6 hy13, mul_nonneg hy7 hbr0n,
            mul_nonneg hy12 hbr3n]
        · have hbr3n : (0 : ℝ) ≤ y1 - (0) := by linarith
          rcases le_total y1 (1 / 2 : ℝ) with hbr4 | hbr4
          · have hbr4n : (0 : ℝ) ≤ 1 / 2 - y1 := by linarith
            linarith [mul_nonneg hx1 hy13, mul_nonneg hx5 hx10, mul_nonneg hx5 hy5,
              mul_nonneg hx6 hx11, mul_nonneg hx6 hy7, mul_nonneg hx6 hbr3n, mul_nonneg hx7 hx10,
              mul_nonneg hx7 hx11, mul_nonneg hx7 hy7, mul_nonneg hx7 hbr3n, mul_nonneg hx10 hy0,
              mul_nonneg hx10 hbr0n, mul_nonneg hx10 hbr2n, mul_nonneg hx10 hbr4n,
              mul_nonneg hx11 hy13, mul_nonneg hx12 hy12, mul_nonneg hx12 hbr1n,
              mul_nonneg hx12 hbr2n, mul_nonneg hx12 hbr3n, mul_nonneg hx13 hy13,
              mul_nonneg hy4 hy13, mul_nonneg hy5 hy11, mul_nonneg hy5 hbr0n, mul_nonneg hy6 hy13,
              mul_nonneg hy7 hbr4n, mul_nonneg hbr3n hbr4n]
          · have hbr4n : (0 : ℝ) ≤ y1 - (1 / 2) := by linarith
            linarith [mul_nonneg hx0 hy9, mul_nonneg hx1 hx6, mul_nonneg hx4 hx12,
              mul_nonneg hx5 hx12, mul_nonneg hx6 hx13, mul_nonneg hx6 hy4, mul_nonneg hx6 hy6,
              mul_nonneg hx6 hbr1n, mul_nonneg hx7 hx10, mul_nonneg hx7 hx11, mul_nonneg hx7 hy5,
              mul_nonneg hx7 hbr4n, mul_nonneg hx10 hy9, mul_nonneg hx12 hy0, mul_nonneg hx12 hy11,
              mul_nonneg hx12 hy12, mul_nonneg hx13 hy13, mul_nonneg hy5 hy9, mul_nonneg hy5 hy11,
              mul_nonneg hy5 hbr2n, mul_nonneg hy9 hbr1n, mul_nonneg hy9 hbr4n,
              mul_nonneg hy11 hbr4n, mul_nonneg hy13 hbr0n, mul_nonneg hy13 hbr2n,
              mul_nonneg hy13 hbr4n]
    · have hbr1n : (0 : ℝ) ≤ x1 - (0) := by linarith
      rcases le_total y1 (0 : ℝ) with hbr5 | hbr5
      · have hbr5n : (0 : ℝ) ≤ 0 - y1 := by linarith
        rcases le_total x2 (0 : ℝ) with hbr6 | hbr6
        · have hbr6n : (0 : ℝ) ≤ 0 - x2 := by linarith
          linarith [mul_nonneg hx0 hbr0n, mul_nonneg hx2 hbr0n, mul_nonneg _hx3 hx9,
            mul_nonneg hx5 hx11, mul_nonneg hx6 hx9, mul_nonneg hx6 hy6, mul_nonneg hx6 hbr0n,
            mul_nonneg hx7 hx9, mul_nonneg hx7 hx11, mul_nonneg hx7 hy7, mul_nonneg hx9 hy5,
            mul_nonneg hx9 hy9, mul_nonneg hx9 hbr5n, mul_nonneg hx11 hy11, mul_nonneg hx11 hy12,
            mul_nonneg hx12 hy12, mul_nonneg hx13 hy13, mul_nonneg hx13 hbr6n, mul_nonneg hy0 hy7,
            mul_nonneg hy4 hy12, mul_nonneg hy5 hy12, mul_nonneg hy6 hy13, mul_nonneg hy6 hbr5n,
            mul_nonneg hy7 hbr0n, mul_nonneg hy12 hbr6n, mul_nonneg hbr0n hbr6n]
        · have hbr6n : (0 : ℝ) ≤ x2 - (0) := by linarith
          rcases le_total x2 (1 / 2 : ℝ) with hbr7 | hbr7
          · have hbr7n : (0 : ℝ) ≤ 1 / 2 - x2 := by linarith
            linarith [mul_nonneg hx4 hx13, mul_nonneg hx4 hy4, mul_nonneg hx4 hbr6n,
              mul_nonneg hx6 hx9, mul_nonneg hx6 hbr0n, mul_nonneg hx7 hx11, mul_nonneg hx7 hy7,
              mul_nonneg hx9 hy1, mul_nonneg hx9 hy5, mul_nonneg hx9 hy13, mul_nonneg hx9 hbr1n,
              mul_nonneg hx9 hbr5n, mul_nonneg hx9 hbr7n, mul_nonneg hx11 hy11,
              mul_nonneg hx11 hy12, mul_nonneg hx11 hy13, mul_nonneg hx11 hbr6n,
              mul_nonneg hx12 hy12, mul_nonneg hy5 hy12, mul_nonneg hy6 hy13, mul_nonneg hy6 hbr7n,
              mul_nonneg hy7 hbr0n, mul_nonneg hy7 hbr5n, mul_nonneg hy12 hbr7n,
              mul_nonneg hbr0n hbr7n]
          · have hbr7n : (0 : ℝ) ≤ x2 - (1 / 2) := by linarith
            linarith [mul_nonneg hx4 hx6, mul_nonneg hx4 hx7, mul_nonneg hx4 hx12,
              mul_nonneg hx4 hy4, mul_nonneg hx4 hy5, mul_nonneg hx4 hbr1n, mul_nonneg hx4 hbr5n,
              mul_nonneg hx7 hx11, mul_nonneg hx7 hy7, mul_nonneg hx9 hx10, mul_nonneg hx9 hy5,
              mul_nonneg hx9 hy13, mul_nonneg hx9 hbr5n, mul_nonneg hx10 hy12,
              mul_nonneg hx10 hbr0n, mul_nonneg hx10 hbr6n, mul_nonneg hx11 hy13,
              mul_nonneg hx11 hbr1n, mul_nonneg hx11 hbr5n, mul_nonneg hy5 hy12,
              mul_nonneg hy5 hbr7n, mul_nonneg hy6 hy13, mul_nonneg hy7 hbr0n,
              mul_nonneg hy7 hbr5n, mul_nonneg hy13 hbr7n]
      · have hbr5n : (0 : ℝ) ≤ y1 - (0) := by linarith
        linarith [mul_nonneg hx1 hy13, mul_nonneg hx4 hy4, mul_nonneg hx4 hbr1n,
          mul_nonneg hx5 hx10, mul_nonneg hx5 hy5, mul_nonneg hx6 hx11, mul_nonneg hx6 hbr5n,
          mul_nonneg hx7 hy7, mul_nonneg hx9 hy13, mul_nonneg hx10 hbr0n, mul_nonneg hx11 hy0,
          mul_nonneg hx11 hy11, mul_nonneg hx13 hy5, mul_nonneg hx13 hy13, mul_nonneg hy4 hy13,
          mul_nonneg hy5 hy12, mul_nonneg hy5 hbr0n, mul_nonneg hy6 hy13, mul_nonneg hy7 hy9,
          mul_nonneg hy7 hy11, mul_nonneg hy7 hbr0n, mul_nonneg hy7 hbr1n, mul_nonneg hy9 hbr5n,
          mul_nonneg hbr1n hbr5n]
  · have hbr0n : (0 : ℝ) ≤ y2 - (0) := by linarith
    rcases le_total x1 (0 : ℝ) with hbr8 | hbr8
    · have hbr8n : (0 : ℝ) ≤ 0 - x1 := by linarith
      rcases le_total x2 (0 : ℝ) with hbr9 | hbr9
      · have hbr9n : (0 : ℝ) ≤ 0 - x2 := by linarith
        rcases le_total y1 (0 : ℝ) with hbr10 | hbr10
        · have hbr10n : (0 : ℝ) ≤ 0 - y1 := by linarith
          linarith [mul_nonneg hx2 hy12, mul_nonneg hx5 hx12, mul_nonneg hx5 hy4,
            mul_nonneg hx5 hbr10n, mul_nonneg hx6 hx13, mul_nonneg hx6 hy10, mul_nonneg hx7 hy7,
            mul_nonneg hx7 hbr8n, mul_nonneg hx7 hbr9n, mul_nonneg hx11 hy11, mul_nonneg hx12 hy12,
            mul_nonneg hx13 hy1, mul_nonneg hx13 hy11, mul_nonneg hx13 hy13, mul_nonneg hy1 hy10,
            mul_nonneg hy1 hbr8n, mul_nonneg hy5 hy10, mul_nonneg hy5 hbr8n, mul_nonneg hy6 hy11,
            mul_nonneg hy7 hy10, mul_nonneg hy7 hy11, mul_nonneg hy10 hbr9n,
            mul_nonneg hy12 hbr10n, mul_nonneg hbr8n hbr10n]
        · have hbr10n : (0 : ℝ) ≤ y1 - (0) := by linarith
          rcases le_total y2 (1 / 2 : ℝ) with hbr11 | hbr11
          · have hbr11n : (0 : ℝ) ≤ 1 / 2 - y2 := by linarith
            linarith [mul_nonneg hx0 hx7, mul_nonneg hx0 hy11, mul_nonneg hx4 hy4,
              mul_nonneg hx5 hx12, mul_nonneg hx5 hy9, mul_nonneg hx6 hx13, mul_nonneg hx6 hbr10n,
              mul_nonneg hx6 hbr11n, mul_nonneg hx7 hy7, mul_nonneg hx11 hy11, mul_nonneg hx12 hy2,
              mul_nonneg hx12 hy12, mul_nonneg hx12 hbr8n, mul_nonneg hx12 hbr10n,
              mul_nonneg hx13 hy11, mul_nonneg hx13 hbr9n, mul_nonneg hy4 hy13,
              mul_nonneg hy4 hbr0n, mul_nonneg hy4 hbr8n, mul_nonneg hy6 hy9, mul_nonneg hy7 hy11,
              mul_nonneg hy9 hbr8n, mul_nonneg hy9 hbr10n, mul_nonneg hy9 hbr11n,
              mul_nonneg hy11 hbr0n, mul_nonneg hbr9n hbr11n]
          · have hbr11n : (0 : ℝ) ≤ y2 - (1 / 2) := by linarith
            linarith [mul_nonneg hx0 hx7, mul_nonneg hx5 hx12, mul_nonneg hx5 hy4,
              mul_nonneg hx6 hx13, mul_nonneg hx6 hy10, mul_nonneg hx7 hy5, mul_nonneg hx7 hy7,
              mul_nonneg hx7 hbr8n, mul_nonneg hx7 hbr9n, mul_nonneg hx11 hy11,
              mul_nonneg hx12 hy10, mul_nonneg hx13 hy11, mul_nonneg hx13 hbr9n,
              mul_nonneg hx13 hbr11n, mul_nonneg hy4 hy7, mul_nonneg hy4 hy12,
              mul_nonneg hy4 hbr8n, mul_nonneg hy4 hbr10n, mul_nonneg hy5 hy10,
              mul_nonneg hy6 hy11, mul_nonneg hy7 hy11, mul_nonneg hy9 hy10, mul_nonneg hy9 hbr8n,
              mul_nonneg hy10 hbr11n, mul_nonneg hy11 hbr8n]
      · have hbr9n : (0 : ℝ) ≤ x2 - (0) := by linarith
        linarith [mul_nonneg hx0 hy11, mul_nonneg hx4 hx12, mul_nonneg hx4 hy4,
          mul_nonneg hx5 hx12, mul_nonneg hx6 hx13, mul_nonneg hx6 hy6, mul_nonneg hx6 hbr8n,
          mul_nonneg hx7 hx10, mul_nonneg hx7 hx11, mul_nonneg hx7 hy5, mul_nonneg hx7 hy7,
          mul_nonneg hx7 hbr0n, mul_nonneg hx10 hbr9n, mul_nonneg hx11 hy11, mul_nonneg hx12 hy10,
          mul_nonneg hx12 hy11, mul_nonneg hx12 hy12, mul_nonneg hy4 hy13, mul_nonneg hy4 hbr0n,
          mul_nonneg hy5 hy11, mul_nonneg hy5 hbr9n, mul_nonneg hy6 hy9, mul_nonneg hy9 hbr8n,
          mul_nonneg hy11 hbr0n, mul_nonneg hbr0n hbr9n]
    · have hbr8n : (0 : ℝ) ≤ x1 - (0) := by linarith
      rcases le_total y1 (0 : ℝ) with hbr12 | hbr12
      · have hbr12n : (0 : ℝ) ≤ 0 - y1 := by linarith
        rcases le_total x2 (0 : ℝ) with hbr13 | hbr13
        · have hbr13n : (0 : ℝ) ≤ 0 - x2 := by linarith
          rcases le_total y2 (1 / 2 : ℝ) with hbr14 | hbr14
          · have hbr14n : (0 : ℝ) ≤ 1 / 2 - y2 := by linarith
            linarith [mul_nonneg hx5 hx11, mul_nonneg hx5 hy7, mul_nonneg hx5 hbr0n,
              mul_nonneg hx6 hy6, mul_nonneg hx7 hx9, mul_nonneg hx7 hx11, mul_nonneg hx7 hy7,
              mul_nonneg hx7 hbr0n, mul_nonneg hx9 hy0, mul_nonneg hx9 hy11, mul_nonneg hx9 hbr8n,
              mul_nonneg hx9 hbr12n, mul_nonneg hx9 hbr14n, mul_nonneg hx11 hy12,
              mul_nonneg hx12 hy12, mul_nonneg hx13 hbr0n, mul_nonneg hx13 hbr8n,
              mul_nonneg hx13 hbr13n, mul_nonneg hy4 hy12, mul_nonneg hy5 hy12,
              mul_nonneg hy6 hy11, mul_nonneg hy6 hbr12n, mul_nonneg hy7 hbr14n,
              mul_nonneg hbr0n hbr14n]
          · have hbr14n : (0 : ℝ) ≤ y2 - (1 / 2) := by linarith
            linarith [mul_nonneg hx0 hx5, mul_nonneg hx0 hy10, mul_nonneg hx4 hx13,
              mul_nonneg hx4 hy10, mul_nonneg hx5 hy5, mul_nonneg hx5 hbr13n, mul_nonneg hx6 hx13,
              mul_nonneg hx7 hx11, mul_nonneg hx7 hy6, mul_nonneg hx7 hbr14n, mul_nonneg hx9 hy10,
              mul_nonneg hx9 hbr8n, mul_nonneg hx12 hy12, mul_nonneg hx13 hy0,
              mul_nonneg hx13 hy11, mul_nonneg hx13 hy13, mul_nonneg hy6 hy11,
              mul_nonneg hy6 hbr8n, mul_nonneg hy7 hy10, mul_nonneg hy10 hbr13n,
              mul_nonneg hy10 hbr14n, mul_nonneg hy11 hbr14n, mul_nonneg hy12 hbr8n,
              mul_nonneg hy12 hbr12n, mul_nonneg hy12 hbr14n]
        · have hbr13n : (0 : ℝ) ≤ x2 - (0) := by linarith
          linarith [mul_nonneg hx4 hy0, mul_nonneg hx4 hy4, mul_nonneg hx4 hbr12n,
            mul_nonneg hx4 hbr13n, mul_nonneg hx5 hx11, mul_nonneg hx5 hbr0n, mul_nonneg hx6 hx9,
            mul_nonneg hx6 hy6, mul_nonneg hx7 hbr0n, mul_nonneg hx9 hbr12n, mul_nonneg hx10 hy6,
            mul_nonneg hx10 hy12, mul_nonneg hx11 hy0, mul_nonneg hx11 hy11, mul_nonneg hx12 hy12,
            mul_nonneg hy0 hy6, mul_nonneg hy4 hy12, mul_nonneg hy5 hy12, mul_nonneg hy6 hy13,
            mul_nonneg hy6 hbr12n, mul_nonneg hy7 hy11, mul_nonneg hy7 hbr12n,
            mul_nonneg hy7 hbr13n, mul_nonneg hy10 hbr0n]
      · have hbr12n : (0 : ℝ) ≤ y1 - (0) := by linarith
        linarith [mul_nonneg hx0 hx7, mul_nonneg hx0 hy4, mul_nonneg hx2 hx5, mul_nonneg hx4 hx13,
          mul_nonneg hx4 hy10, mul_nonneg hx5 hx10, mul_nonneg hx5 hy5, mul_nonneg hx5 hbr0n,
          mul_nonneg hx6 hx13, mul_nonneg hx6 hy10, mul_nonneg hx7 hx11, mul_nonneg hx9 hbr8n,
          mul_nonneg hx10 hy10, mul_nonneg hx11 hy11, mul_nonneg hx13 hbr0n, mul_nonneg hy4 hbr12n,
          mul_nonneg hy5 hy10, mul_nonneg hy6 hy11, mul_nonneg hy7 hbr8n, mul_nonneg hy12 hbr8n,
          mul_nonneg hbr8n hbr12n]

set_option maxHeartbeats 1600000 in
-- the branch-and-certify case tree is large
theorem certC12 (x0 x1 x2 y0 y1 y2 : ℝ)
    (hx0 : (0 : ℝ) ≤ 3 / 2 - (x0 + x1 + x2)) (_hx1 : (0 : ℝ) ≤ 3 / 2 - (x0 + x1 - x2))
    (hx2 : (0 : ℝ) ≤ 3 / 2 - (x0 - x1 + x2)) (hx3 : (0 : ℝ) ≤ 3 / 2 - (x0 - x1 - x2))
    (hx4 : (0 : ℝ) ≤ 3 / 2 - (-x0 + x1 + x2)) (hx5 : (0 : ℝ) ≤ 3 / 2 - (-x0 + x1 - x2))
    (hx6 : (0 : ℝ) ≤ 3 / 2 - (-x0 - x1 + x2)) (hx7 : (0 : ℝ) ≤ 3 / 2 - (-x0 - x1 - x2))
    (_hx8 : (0 : ℝ) ≤ 13 / 15 - x0) (hx9 : (0 : ℝ) ≤ 13 / 15 - x1)
    (hx10 : (0 : ℝ) ≤ 13 / 15 - x2) (hx11 : (0 : ℝ) ≤ 5 / 12 - (x0 + x1 + x2))
    (hx12 : (0 : ℝ) ≤ x1 - x0) (hx13 : (0 : ℝ) ≤ x2 - x0)
    (hy0 : (0 : ℝ) ≤ 3 / 2 - (y0 + y1 + y2)) (hy1 : (0 : ℝ) ≤ 3 / 2 - (y0 + y1 - y2))
    (hy2 : (0 : ℝ) ≤ 3 / 2 - (y0 - y1 + y2)) (_hy3 : (0 : ℝ) ≤ 3 / 2 - (y0 - y1 - y2))
    (hy4 : (0 : ℝ) ≤ 3 / 2 - (-y0 + y1 + y2)) (hy5 : (0 : ℝ) ≤ 3 / 2 - (-y0 + y1 - y2))
    (hy6 : (0 : ℝ) ≤ 3 / 2 - (-y0 - y1 + y2)) (hy7 : (0 : ℝ) ≤ 3 / 2 - (-y0 - y1 - y2))
    (_hy8 : (0 : ℝ) ≤ 13 / 15 - y0) (hy9 : (0 : ℝ) ≤ 13 / 15 - y1)
    (hy10 : (0 : ℝ) ≤ 13 / 15 - y2) (hy11 : (0 : ℝ) ≤ -(7 / 24) - y0)
    (hy12 : (0 : ℝ) ≤ y1 - y0) (hy13 : (0 : ℝ) ≤ y2 - y0)
    :
    (x0 - y0) ^ 2 + (x1 - y1) ^ 2 + (x2 - y2) ^ 2 ≤ 149 / 50 := by
  rcases le_total y1 (0 : ℝ) with hbr0 | hbr0
  · have hbr0n : (0 : ℝ) ≤ 0 - y1 := by linarith
    rcases le_total x2 (0 : ℝ) with hbr1 | hbr1
    · have hbr1n : (0 : ℝ) ≤ 0 - x2 := by linarith
      rcases le_total y2 (0 : ℝ) with hbr2 | hbr2
      · have hbr2n : (0 : ℝ) ≤ 0 - y2 := by linarith
        linarith [mul_nonneg hx4 hx13, mul_nonneg hx4 hy6, mul_nonneg hx5 hx11,
          mul_nonneg hx5 hx13, mul_nonneg hx5 hy7, mul_nonneg hx5 hbr1n, mul_nonneg hx6 hx9,
          mul_nonneg hx6 hx13, mul_nonneg hx6 hy6, mul_nonneg hx6 hbr2n, mul_nonneg hx7 hx9,
          mul_nonneg hx7 hx11, mul_nonneg hx7 hy7, mul_nonneg hx9 hx12, mul_nonneg hx9 hbr0n,
          mul_nonneg hx12 hy12, mul_nonneg hx13 hy12, mul_nonneg hy5 hy12, mul_nonneg hy6 hy13,
          mul_nonneg hy6 hbr1n, mul_nonneg hy7 hbr0n, mul_nonneg hy7 hbr2n, mul_nonneg hy12 hbr1n]
      · have hbr2n : (0 : ℝ) ≤ y2 - (0) := by linarith
        rcases le_total x1 (0 : ℝ) with hbr3 | hbr3
        · have hbr3n : (0 : ℝ) ≤ 0 - x1 := by linarith
          linarith [mul_nonneg hx2 hy10, mul_nonneg hx4 hx13, mul_nonneg hx4 hy10,
            mul_nonneg hx5 hx12, mul_nonneg hx5 hy5, mul_nonneg hx5 hbr0n, mul_nonneg hx6 hx13,
            mul_nonneg hx6 hbr3n, mul_nonneg hx7 hx11, mul_nonneg hx7 hy6, mul_nonneg hx7 hy7,
            mul_nonneg hx12 hy11, mul_nonneg hx12 hy12, mul_nonneg hx13 hy11, mul_nonneg hx13 hy13,
            mul_nonneg hx13 hbr0n, mul_nonneg hx13 hbr1n, mul_nonneg hy1 hbr3n,
            mul_nonneg hy5 hy10, mul_nonneg hy5 hbr3n, mul_nonneg hy6 hy11, mul_nonneg hy7 hy10,
            mul_nonneg hy7 hy11, mul_nonneg hy10 hbr1n, mul_nonneg hy10 hbr2n,
            mul_nonneg hy12 hbr0n]
        · have hbr3n : (0 : ℝ) ≤ x1 - (0) := by linarith
          rcases le_total y2 (1 / 2 : ℝ) with hbr4 | hbr4
          · have hbr4n : (0 : ℝ) ≤ 1 / 2 - y2 := by linarith
            linarith [mul_nonneg hx4 hx13, mul_nonneg hx5 hx11, mul_nonneg hx5 hy7,
              mul_nonneg hx6 hx9, mul_nonneg hx6 hx13, mul_nonneg hx6 hy6, mul_nonneg hx7 hy7,
              mul_nonneg hx9 hy4, mul_nonneg hx9 hbr0n, mul_nonneg hx9 hbr3n, mul_nonneg hx9 hbr4n,
              mul_nonneg hx11 hy11, mul_nonneg hx11 hy12, mul_nonneg hx11 hbr4n,
              mul_nonneg hx12 hy12, mul_nonneg hx13 hy12, mul_nonneg hx13 hy13,
              mul_nonneg hx13 hbr2n, mul_nonneg hy4 hy12, mul_nonneg hy5 hy12, mul_nonneg hy6 hy13,
              mul_nonneg hy6 hbr0n, mul_nonneg hy6 hbr1n, mul_nonneg hy7 hy11,
              mul_nonneg hy7 hbr4n]
          · have hbr4n : (0 : ℝ) ≤ y2 - (1 / 2) := by linarith
            linarith [mul_nonneg hx2 hx5, mul_nonneg hx4 hx13, mul_nonneg hx5 hy5,
              mul_nonneg hx5 hbr0n, mul_nonneg hx6 hx13, mul_nonneg hx7 hx11, mul_nonneg hx7 hy6,
              mul_nonneg hx7 hbr4n, mul_nonneg hx9 hbr3n, mul_nonneg hx11 hy10,
              mul_nonneg hx12 hy12, mul_nonneg hx13 hy11, mul_nonneg hx13 hy13,
              mul_nonneg hx13 hbr0n, mul_nonneg hx13 hbr4n, mul_nonneg hy1 hy12,
              mul_nonneg hy5 hy12, mul_nonneg hy6 hy11, mul_nonneg hy6 hbr3n, mul_nonneg hy7 hy10,
              mul_nonneg hy7 hy11, mul_nonneg hy10 hbr1n, mul_nonneg hy10 hbr4n,
              mul_nonneg hy12 hbr0n, mul_nonneg hy12 hbr3n, mul_nonneg hy12 hbr4n]
    · have hbr1n : (0 : ℝ) ≤ x2 - (0) := by linarith
      rcases le_total x1 (0 : ℝ) with hbr5 | hbr5
      · have hbr5n : (0 : ℝ) ≤ 0 - x1 := by linarith
        rcases le_total y2 (0 : ℝ) with hbr6 | hbr6
        · have hbr6n : (0 : ℝ) ≤ 0 - y2 := by linarith
          linarith [mul_nonneg hx4 hx12, mul_nonneg hx4 hy5, mul_nonneg hx5 hx12,
            mul_nonneg hx5 hy5, mul_nonneg hx6 hx11, mul_nonneg hx6 hy7, mul_nonneg hx7 hy7,
            mul_nonneg hx10 hy4, mul_nonneg hx10 hy10, mul_nonneg hx10 hbr1n,
            mul_nonneg hx10 hbr6n, mul_nonneg hx11 hy11, mul_nonneg hx11 hy13,
            mul_nonneg hx12 hy13, mul_nonneg hx13 hy13, mul_nonneg hy0 hy7, mul_nonneg hy5 hy12,
            mul_nonneg hy5 hbr5n, mul_nonneg hy6 hy13, mul_nonneg hy7 hbr0n, mul_nonneg hy7 hbr6n,
            mul_nonneg hy12 hbr0n, mul_nonneg hbr0n hbr5n]
        · have hbr6n : (0 : ℝ) ≤ y2 - (0) := by linarith
          linarith [mul_nonneg hx4 hx12, mul_nonneg hx4 hy4, mul_nonneg hx4 hbr0n,
            mul_nonneg hx5 hbr6n, mul_nonneg hx6 hx12, mul_nonneg hx6 hy6, mul_nonneg hx6 hbr5n,
            mul_nonneg hx7 hx11, mul_nonneg hx7 hy7, mul_nonneg hx7 hbr6n, mul_nonneg hx10 hx13,
            mul_nonneg hx10 hbr1n, mul_nonneg hx10 hbr5n, mul_nonneg hx11 hy10,
            mul_nonneg hx11 hbr1n, mul_nonneg hx12 hy11, mul_nonneg hx12 hy12, mul_nonneg hy5 hy10,
            mul_nonneg hy5 hbr1n, mul_nonneg hy6 hy11, mul_nonneg hy7 hy10, mul_nonneg hy7 hy11,
            mul_nonneg hy10 hbr6n, mul_nonneg hy12 hbr0n, mul_nonneg hbr1n hbr6n]
      · have hbr5n : (0 : ℝ) ≤ x1 - (0) := by linarith
        linarith [mul_nonneg hx4 hx12, mul_nonneg hx4 hx13, mul_nonneg hx4 hy4, mul_nonneg hx5 hy5,
          mul_nonneg hx5 hy7, mul_nonneg hx6 hy6, mul_nonneg hx7 hx11, mul_nonneg hx7 hy7,
          mul_nonneg hx9 hbr0n, mul_nonneg hx10 hy6, mul_nonneg hx10 hbr1n, mul_nonneg hx11 hy11,
          mul_nonneg hx11 hbr1n, mul_nonneg hx11 hbr5n, mul_nonneg hx12 hy12, mul_nonneg hx13 hy13,
          mul_nonneg hy5 hbr1n, mul_nonneg hy6 hy13, mul_nonneg hy7 hy10, mul_nonneg hy7 hy11,
          mul_nonneg hy7 hbr1n, mul_nonneg hy12 hbr0n, mul_nonneg hy12 hbr5n,
          mul_nonneg hy13 hbr1n, mul_nonneg hbr1n hbr5n]
  · have hbr0n : (0 : ℝ) ≤ y1 - (0) := by linarith
    rcases le_total x2 (0 : ℝ) with hbr7 | hbr7
    · have hbr7n : (0 : ℝ) ≤ 0 - x2 := by linarith
      rcases le_total x1 (0 : ℝ) with hbr8 | hbr8
      · have hbr8n : (0 : ℝ) ≤ 0 - x1 := by linarith
        rcases le_total y2 (0 : ℝ) with hbr9 | hbr9
        · have hbr9n : (0 : ℝ) ≤ 0 - y2 := by linarith
          linarith [mul_nonneg _hx1 hy9, mul_nonneg hx4 hx12, mul_nonneg hx5 hx12,
            mul_nonneg hx5 hy9, mul_nonneg hx6 hx13, mul_nonneg hx6 hy4, mul_nonneg hx6 hy6,
            mul_nonneg hx6 hbr8n, mul_nonneg hx6 hbr9n, mul_nonneg hx7 hx11, mul_nonneg hx7 hy7,
            mul_nonneg hx11 hy11, mul_nonneg hx12 hy11, mul_nonneg hx12 hy12,
            mul_nonneg hx12 hbr9n, mul_nonneg hx13 hy13, mul_nonneg hx13 hbr7n,
            mul_nonneg hy0 hbr7n, mul_nonneg hy2 hbr7n, mul_nonneg hy5 hy11, mul_nonneg hy6 hy9,
            mul_nonneg hy6 hbr7n, mul_nonneg hy7 hy9, mul_nonneg hy9 hbr8n, mul_nonneg hy13 hbr9n]
        · have hbr9n : (0 : ℝ) ≤ y2 - (0) := by linarith
          rcases le_total y2 (1 / 2 : ℝ) with hbr10 | hbr10
          · have hbr10n : (0 : ℝ) ≤ 1 / 2 - y2 := by linarith
            linarith [mul_nonneg hx5 hx12, mul_nonneg hx6 hx13, mul_nonneg hx6 hy6,
              mul_nonneg hx6 hbr0n, mul_nonneg hx6 hbr10n, mul_nonneg hx7 hx11, mul_nonneg hx7 hy4,
              mul_nonneg hx7 hy5, mul_nonneg hx7 hy7, mul_nonneg hx7 hbr7n, mul_nonneg hx9 hy4,
              mul_nonneg hx11 hy11, mul_nonneg hx12 hy11, mul_nonneg hx12 hy12,
              mul_nonneg hx12 hbr8n, mul_nonneg hx12 hbr10n, mul_nonneg hx13 hy11,
              mul_nonneg hy4 hy7, mul_nonneg hy4 hy13, mul_nonneg hy4 hbr9n, mul_nonneg hy5 hy11,
              mul_nonneg hy6 hy9, mul_nonneg hy7 hy11, mul_nonneg hy9 hbr8n, mul_nonneg hy9 hbr10n,
              mul_nonneg hbr7n hbr10n]
          · have hbr10n : (0 : ℝ) ≤ y2 - (1 / 2) := by linarith
            linarith [mul_nonneg hx4 hx7, mul_nonneg hx5 hx12, mul_nonneg hx5 hy4,
              mul_nonneg hx6 hx13, mul_nonneg hx7 hx11, mul_nonneg hx7 hy5, mul_nonneg hx7 hy7,
              mul_nonneg _hx8 hy11, mul_nonneg hx9 hy4, mul_nonneg hx11 hy11, mul_nonneg hx12 hy10,
              mul_nonneg hx12 hy11, mul_nonneg hx13 hy11, mul_nonneg hx13 hbr10n,
              mul_nonneg hy4 hy6, mul_nonneg hy4 hy12, mul_nonneg hy4 hbr8n, mul_nonneg hy5 hy10,
              mul_nonneg hy6 hy11, mul_nonneg hy9 hbr8n, mul_nonneg hy10 hbr7n,
              mul_nonneg hy10 hbr9n, mul_nonneg hy10 hbr10n]
      · have hbr8n : (0 : ℝ) ≤ x1 - (0) := by linarith
        linarith [mul_nonneg hx4 hx13, mul_nonneg hx4 hy4, mul_nonneg hx4 hy10,
          mul_nonneg hx5 hx12, mul_nonneg hx5 hy5, mul_nonneg hx6 hx13, mul_nonneg hx7 hx11,
          mul_nonneg hx7 hy7, mul_nonneg hx7 hbr0n, mul_nonneg hx9 hbr8n, mul_nonneg hx11 hy11,
          mul_nonneg hx13 hy9, mul_nonneg hx13 hy11, mul_nonneg hx13 hy13, mul_nonneg hx13 hbr7n,
          mul_nonneg hy1 hy10, mul_nonneg hy4 hbr0n, mul_nonneg hy5 hy10, mul_nonneg hy6 hy11,
          mul_nonneg hy6 hbr8n, mul_nonneg hy7 hy11, mul_nonneg hy9 hy10, mul_nonneg hy10 hy13,
          mul_nonneg hy10 hbr7n, mul_nonneg hy12 hbr8n, mul_nonneg hbr0n hbr8n]
    · have hbr7n : (0 : ℝ) ≤ x2 - (0) := by linarith
      rcases le_total x0 (-1 / 2 : ℝ) with hbr11 | hbr11
      · have hbr11n : (0 : ℝ) ≤ -1 / 2 - x0 := by linarith
        rcases le_total y2 (0 : ℝ) with hbr12 | hbr12
        · have hbr12n : (0 : ℝ) ≤ 0 - y2 := by linarith
          linarith [mul_nonneg hx4 hx12, mul_nonneg hx4 hy9, mul_nonneg hx5 hy5,
            mul_nonneg hx6 hx9, mul_nonneg hx6 hy6, mul_nonneg hx7 hy5, mul_nonneg hx7 hy7,
            mul_nonneg hx7 hbr11n, mul_nonneg hx10 hy9, mul_nonneg hx10 hbr7n, mul_nonneg hx11 hy9,
            mul_nonneg hx12 hy13, mul_nonneg hx12 hbr0n, mul_nonneg hy5 hy11, mul_nonneg hy5 hbr7n,
            mul_nonneg hy6 hy9, mul_nonneg hy7 hy9, mul_nonneg hy7 hy11, mul_nonneg hy7 hbr7n,
            mul_nonneg hy9 hbr0n, mul_nonneg hy11 hbr11n, mul_nonneg hy13 hbr7n,
            mul_nonneg hy13 hbr12n, mul_nonneg hbr11n hbr12n]
        · have hbr12n : (0 : ℝ) ≤ y2 - (0) := by linarith
          linarith [mul_nonneg hx4 hx12, mul_nonneg hx4 hy9, mul_nonneg hx5 hx12,
            mul_nonneg hx6 hx9, mul_nonneg hx6 hx13, mul_nonneg hx6 hy6, mul_nonneg hx6 hbr0n,
            mul_nonneg hx6 hbr7n, mul_nonneg hx7 hx11, mul_nonneg hx7 hbr0n, mul_nonneg hx7 hbr12n,
            mul_nonneg hx11 hy4, mul_nonneg hx11 hy11, mul_nonneg hx12 hy11, mul_nonneg hx12 hy12,
            mul_nonneg hx12 hbr0n, mul_nonneg hy4 hbr12n, mul_nonneg hy5 hy11,
            mul_nonneg hy5 hbr7n, mul_nonneg hy6 hy9, mul_nonneg hy11 hbr11n,
            mul_nonneg hy13 hbr7n, mul_nonneg hbr7n hbr12n]
      · have hbr11n : (0 : ℝ) ≤ x0 - (-1 / 2) := by linarith
        rcases le_total x1 (0 : ℝ) with hbr13 | hbr13
        · have hbr13n : (0 : ℝ) ≤ 0 - x1 := by linarith
          linarith [mul_nonneg hx6 hx13, mul_nonneg hx6 hbr0n, mul_nonneg hx6 hbr13n,
            mul_nonneg hx10 hy4, mul_nonneg hx10 hy9, mul_nonneg hx10 hbr7n, mul_nonneg hx11 hx12,
            mul_nonneg hx11 hy9, mul_nonneg hx11 hy11, mul_nonneg hx11 hbr11n, mul_nonneg hx12 hy7,
            mul_nonneg hx12 hy12, mul_nonneg hx12 hy13, mul_nonneg hx12 hbr0n,
            mul_nonneg hx12 hbr11n, mul_nonneg hx12 hbr13n, mul_nonneg hx13 hy13,
            mul_nonneg hy4 hy5, mul_nonneg hy4 hy13, mul_nonneg hy5 hy11, mul_nonneg hy5 hbr7n,
            mul_nonneg hy5 hbr11n, mul_nonneg hy6 hy13, mul_nonneg hy7 hbr11n,
            mul_nonneg hy9 hbr0n, mul_nonneg hy13 hbr13n]
        · have hbr13n : (0 : ℝ) ≤ x1 - (0) := by linarith
          linarith [mul_nonneg hx9 hy5, mul_nonneg hx10 hx13, mul_nonneg hx10 hy4,
            mul_nonneg hx10 hy6, mul_nonneg hx11 hx13, mul_nonneg hx11 hy10, mul_nonneg hx11 hy11,
            mul_nonneg hx11 hbr7n, mul_nonneg hx11 hbr13n, mul_nonneg hx12 hy11,
            mul_nonneg hx12 hy13, mul_nonneg hx12 hbr11n, mul_nonneg hx13 hy13,
            mul_nonneg hx13 hbr13n, mul_nonneg hy4 hy13, mul_nonneg hy4 hbr11n,
            mul_nonneg hy5 hy10, mul_nonneg hy5 hbr7n, mul_nonneg hy5 hbr11n, mul_nonneg hy7 hy11,
            mul_nonneg hy7 hbr7n, mul_nonneg hy7 hbr11n, mul_nonneg hy9 hbr0n,
            mul_nonneg hbr0n hbr13n, mul_nonneg hbr7n hbr13n]
end Space.Cert

end Borsuk

namespace Borsuk

open Metric Set Real

namespace Space

/-- The truncated octahedron. -/
def TruncOct : Set E3 :=
  {y | |y 0| + |y 1| + |y 2| ≤ 3 / 2 ∧ y 0 ≤ 13 / 15 ∧ y 1 ≤ 13 / 15 ∧ y 2 ≤ 13 / 15}

/-- The cap piece of the dissection. -/
def pieceA : Set E3 :=
  {y ∈ TruncOct | 5 / 12 ≤ y 0 + y 1 + y 2 ∧
    -(7 / 24) ≤ y 0 ∧ -(7 / 24) ≤ y 1 ∧ -(7 / 24) ≤ y 2}

/-- The sector piece around the first axis. -/
def pieceB0 : Set E3 :=
  {y ∈ TruncOct | y 0 ≤ y 1 ∧ y 0 ≤ y 2 ∧
    (y 0 + y 1 + y 2 ≤ 5 / 12 ∨ y 0 ≤ -(7 / 24))}

/-- The sector piece around the second axis. -/
def pieceB1 : Set E3 :=
  {y ∈ TruncOct | y 1 ≤ y 0 ∧ y 1 ≤ y 2 ∧
    (y 0 + y 1 + y 2 ≤ 5 / 12 ∨ y 1 ≤ -(7 / 24))}

/-- The sector piece around the third axis. -/
def pieceB2 : Set E3 :=
  {y ∈ TruncOct | y 2 ≤ y 0 ∧ y 2 ≤ y 1 ∧
    (y 0 + y 1 + y 2 ≤ 5 / 12 ∨ y 2 ≤ -(7 / 24))}

/-- The four pieces cover the truncated octahedron. -/
theorem truncOct_subset_union :
    TruncOct ⊆ pieceA ∪ pieceB0 ∪ pieceB1 ∪ pieceB2 := by
  intro y hy
  by_cases hw0 : y 0 ≤ -(7 / 24)
  · rcases le_total (y 0) (y 1) with h01 | h01
    · rcases le_total (y 0) (y 2) with h02 | h02
      · exact Or.inl (Or.inl (Or.inr ⟨hy, h01, h02, Or.inr hw0⟩))
      · exact Or.inr ⟨hy, by linarith, by linarith, Or.inr (by linarith)⟩
    · rcases le_total (y 1) (y 2) with h12 | h12
      · exact Or.inl (Or.inr ⟨hy, h01, h12, Or.inr (by linarith)⟩)
      · exact Or.inr ⟨hy, by linarith, h12, Or.inr (by linarith)⟩
  · by_cases hw1 : y 1 ≤ -(7 / 24)
    · rcases le_total (y 1) (y 2) with h12 | h12
      · exact Or.inl (Or.inr ⟨hy, by linarith, h12, Or.inr hw1⟩)
      · exact Or.inr ⟨hy, by linarith, h12, Or.inr (by linarith)⟩
    · by_cases hw2 : y 2 ≤ -(7 / 24)
      · exact Or.inr ⟨hy, by linarith, by linarith, Or.inr hw2⟩
      · by_cases hs : 5 / 12 ≤ y 0 + y 1 + y 2
        · exact Or.inl (Or.inl (Or.inl ⟨hy, hs, by linarith, by linarith, by linarith⟩))
        · rcases le_total (y 0) (y 1) with h01 | h01
          · rcases le_total (y 0) (y 2) with h02 | h02
            · exact Or.inl (Or.inl (Or.inr ⟨hy, h01, h02, Or.inl (by linarith)⟩))
            · exact Or.inr ⟨hy, by linarith, by linarith, Or.inl (by linarith)⟩
          · rcases le_total (y 1) (y 2) with h12 | h12
            · exact Or.inl (Or.inr ⟨hy, h01, h12, Or.inl (by linarith)⟩)
            · exact Or.inr ⟨hy, by linarith, h12, Or.inl (by linarith)⟩

/-- Convert a certified squared-distance bound into a distance bound. -/
private theorem dist_le_of_sq {x y : E3}
    (h : (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 + (x 2 - y 2) ^ 2 ≤ 149 / 50) :
    dist x y ≤ 173 / 100 := by
  have hd2 : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 + (x 2 - y 2) ^ 2 := by
    rw [dist_eq_sqrt, Real.sq_sqrt (by positivity)]
  nlinarith [dist_nonneg (x := x) (y := y)]

/-- The cap piece has diameter at most `173/100`. -/
theorem dist_le_pieceA {x y : E3} (hx : x ∈ pieceA) (hy : y ∈ pieceA) :
    dist x y ≤ 173 / 100 := by
  obtain ⟨⟨hxl, hxt0, hxt1, hxt2⟩, hxs, hxw0, hxw1, hxw2⟩ := hx
  obtain ⟨⟨hyl, hyt0, hyt1, hyt2⟩, hys, hyw0, hyw1, hyw2⟩ := hy
  have ax0 := le_abs_self (x 0); have ax0' := neg_abs_le (x 0)
  have ax1 := le_abs_self (x 1); have ax1' := neg_abs_le (x 1)
  have ax2 := le_abs_self (x 2); have ax2' := neg_abs_le (x 2)
  have ay0 := le_abs_self (y 0); have ay0' := neg_abs_le (y 0)
  have ay1 := le_abs_self (y 1); have ay1' := neg_abs_le (y 1)
  have ay2 := le_abs_self (y 2); have ay2' := neg_abs_le (y 2)
  exact dist_le_of_sq (Cert.certAA (x 0) (x 1) (x 2) (y 0) (y 1) (y 2)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith))

section SectorBounds

set_option maxHeartbeats 800000 in
-- the certificate applications carry 28 linarith side goals each
/-- Distance bound between points of the two cells of a sector, stated for permuted
coordinates `(a, b, c)` of `x` and `(d, e, f)` of `y` in which the sector axis comes
first.  The four cell combinations reduce to the three generated certificates. -/
private theorem sector_sq_bound (a b c d e f : ℝ)
    (hxl1 : a + b + c ≤ 3 / 2) (hxl2 : a + b - c ≤ 3 / 2) (hxl3 : a - b + c ≤ 3 / 2)
    (hxl4 : a - b - c ≤ 3 / 2) (hxl5 : -a + b + c ≤ 3 / 2) (hxl6 : -a + b - c ≤ 3 / 2)
    (hxl7 : -a - b + c ≤ 3 / 2) (hxl8 : -a - b - c ≤ 3 / 2)
    (_hxt0 : a ≤ 13 / 15) (hxt1 : b ≤ 13 / 15) (hxt2 : c ≤ 13 / 15)
    (hxm1 : a ≤ b) (hxm2 : a ≤ c) (hxor : a + b + c ≤ 5 / 12 ∨ a ≤ -(7 / 24))
    (hyl1 : d + e + f ≤ 3 / 2) (hyl2 : d + e - f ≤ 3 / 2) (hyl3 : d - e + f ≤ 3 / 2)
    (hyl4 : d - e - f ≤ 3 / 2) (hyl5 : -d + e + f ≤ 3 / 2) (hyl6 : -d + e - f ≤ 3 / 2)
    (hyl7 : -d - e + f ≤ 3 / 2) (hyl8 : -d - e - f ≤ 3 / 2)
    (_hyt0 : d ≤ 13 / 15) (hyt1 : e ≤ 13 / 15) (hyt2 : f ≤ 13 / 15)
    (hym1 : d ≤ e) (hym2 : d ≤ f) (hyor : d + e + f ≤ 5 / 12 ∨ d ≤ -(7 / 24)) :
    (a - d) ^ 2 + (b - e) ^ 2 + (c - f) ^ 2 ≤ 149 / 50 := by
  rcases hxor with hxc | hxc
  · rcases hyor with hyc | hyc
    · exact Cert.certC11 a b c d e f
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith)
    · exact Cert.certC12 a b c d e f
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith)
  · rcases hyor with hyc | hyc
    · have h := Cert.certC12 d e f a b c
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith)
      have e1 : (a - d) ^ 2 = (d - a) ^ 2 := by ring
      have e2 : (b - e) ^ 2 = (e - b) ^ 2 := by ring
      have e3 : (c - f) ^ 2 = (f - c) ^ 2 := by ring
      linarith [h]
    · exact Cert.certC22 a b c d e f
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith)

/-- The first sector piece has diameter at most `173/100`. -/
theorem dist_le_pieceB0 {x y : E3} (hx : x ∈ pieceB0) (hy : y ∈ pieceB0) :
    dist x y ≤ 173 / 100 := by
  obtain ⟨⟨hxl, hxt0, hxt1, hxt2⟩, hxm1, hxm2, hxor⟩ := hx
  obtain ⟨⟨hyl, hyt0, hyt1, hyt2⟩, hym1, hym2, hyor⟩ := hy
  have ax0 := le_abs_self (x 0); have ax0' := neg_abs_le (x 0)
  have ax1 := le_abs_self (x 1); have ax1' := neg_abs_le (x 1)
  have ax2 := le_abs_self (x 2); have ax2' := neg_abs_le (x 2)
  have ay0 := le_abs_self (y 0); have ay0' := neg_abs_le (y 0)
  have ay1 := le_abs_self (y 1); have ay1' := neg_abs_le (y 1)
  have ay2 := le_abs_self (y 2); have ay2' := neg_abs_le (y 2)
  have h := sector_sq_bound (x 0) (x 1) (x 2) (y 0) (y 1) (y 2)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) hxt0 hxt1 hxt2 hxm1 hxm2 hxor
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) hyt0 hyt1 hyt2 hym1 hym2 hyor
  exact dist_le_of_sq h

/-- The second sector piece has diameter at most `173/100`. -/
theorem dist_le_pieceB1 {x y : E3} (hx : x ∈ pieceB1) (hy : y ∈ pieceB1) :
    dist x y ≤ 173 / 100 := by
  obtain ⟨⟨hxl, hxt0, hxt1, hxt2⟩, hxm1, hxm2, hxor⟩ := hx
  obtain ⟨⟨hyl, hyt0, hyt1, hyt2⟩, hym1, hym2, hyor⟩ := hy
  have ax0 := le_abs_self (x 0); have ax0' := neg_abs_le (x 0)
  have ax1 := le_abs_self (x 1); have ax1' := neg_abs_le (x 1)
  have ax2 := le_abs_self (x 2); have ax2' := neg_abs_le (x 2)
  have ay0 := le_abs_self (y 0); have ay0' := neg_abs_le (y 0)
  have ay1 := le_abs_self (y 1); have ay1' := neg_abs_le (y 1)
  have ay2 := le_abs_self (y 2); have ay2' := neg_abs_le (y 2)
  have h := sector_sq_bound (x 1) (x 0) (x 2) (y 1) (y 0) (y 2)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) hxt1 hxt0 hxt2 hxm1 hxm2
    (hxor.imp (fun h => by linarith) (fun h => h))
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) hyt1 hyt0 hyt2 hym1 hym2
    (hyor.imp (fun h => by linarith) (fun h => h))
  apply dist_le_of_sq
  linarith [h]

/-- The third sector piece has diameter at most `173/100`. -/
theorem dist_le_pieceB2 {x y : E3} (hx : x ∈ pieceB2) (hy : y ∈ pieceB2) :
    dist x y ≤ 173 / 100 := by
  obtain ⟨⟨hxl, hxt0, hxt1, hxt2⟩, hxm1, hxm2, hxor⟩ := hx
  obtain ⟨⟨hyl, hyt0, hyt1, hyt2⟩, hym1, hym2, hyor⟩ := hy
  have ax0 := le_abs_self (x 0); have ax0' := neg_abs_le (x 0)
  have ax1 := le_abs_self (x 1); have ax1' := neg_abs_le (x 1)
  have ax2 := le_abs_self (x 2); have ax2' := neg_abs_le (x 2)
  have ay0 := le_abs_self (y 0); have ay0' := neg_abs_le (y 0)
  have ay1 := le_abs_self (y 1); have ay1' := neg_abs_le (y 1)
  have ay2 := le_abs_self (y 2); have ay2' := neg_abs_le (y 2)
  have h := sector_sq_bound (x 2) (x 0) (x 1) (y 2) (y 0) (y 1)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) hxt2 hxt0 hxt1 hxm1 hxm2
    (hxor.imp (fun h => by linarith) (fun h => h))
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) hyt2 hyt0 hyt1 hym1 hym2
    (hyor.imp (fun h => by linarith) (fun h => h))
  apply dist_le_of_sq
  linarith [h]

end SectorBounds

/-- The bound `173/100` is strictly below `√3`. -/
theorem bound_lt_sqrt3 : (173 : ℝ) / 100 < Real.sqrt 3 := by
  have h : (173 : ℝ) / 100 = Real.sqrt ((173 / 100) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
  rw [h]
  apply Real.sqrt_lt_sqrt (by positivity)
  norm_num

end Space

end Borsuk

namespace Borsuk

open Metric Bornology Set Real
open scoped Pointwise ENNReal

namespace Space

/-- The truncated octahedron admits a four-piece Borsuk cover of anything inside it:
any set `K` inside `TruncOct` of diameter exactly `√3` has a Borsuk cover by four sets. -/
theorem hasBorsukCover_of_subset_truncOct {K : Set E3} (hKT : K ⊆ TruncOct)
    (hdiam : ediam K = ENNReal.ofReal (Real.sqrt 3)) : HasBorsukCover 4 K := by
  have hlt : ENNReal.ofReal (173 / 100) < ediam K := by
    rw [hdiam]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr bound_lt_sqrt3
  have hpiece : ∀ (P : Set E3), (∀ x ∈ P, ∀ y ∈ P, dist x y ≤ 173 / 100) →
      ediam (P ∩ K) < ediam K := by
    intro P hP
    refine lt_of_le_of_lt ?_ hlt
    apply Metric.ediam_le
    intro x hx y hy
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (hP x hx.1 y hy.1)
  refine ⟨![pieceA ∩ K, pieceB0 ∩ K, pieceB1 ∩ K, pieceB2 ∩ K], ?_, ?_⟩
  · intro y hy
    rcases truncOct_subset_union (hKT hy) with ((hA | hB0) | hB1) | hB2
    · exact mem_iUnion.mpr ⟨0, hA, hy⟩
    · exact mem_iUnion.mpr ⟨1, hB0, hy⟩
    · exact mem_iUnion.mpr ⟨2, hB1, hy⟩
    · exact mem_iUnion.mpr ⟨3, hB2, hy⟩
  · intro i
    fin_cases i
    · exact hpiece pieceA (fun x hx y hy => dist_le_pieceA hx hy)
    · exact hpiece pieceB0 (fun x hx y hy => dist_le_pieceB0 hx hy)
    · exact hpiece pieceB1 (fun x hx y hy => dist_le_pieceB1 hx hy)
    · exact hpiece pieceB2 (fun x hx y hy => dist_le_pieceB2 hx hy)

/-- **Borsuk's conjecture in dimension `3`** (Eggleston 1955, here via the
Gale–Grünbaum cover method): every bounded set in `ℝ³` with at least two points can be
divided into four parts of strictly smaller diameter. -/
theorem _root_.Borsuk.borsukConjecture_three : BorsukConjecture 3 := by
  intro s hbs hs
  -- the diameter is positive
  have hDpos : 0 < diam s := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hs
    have h1 : 0 < dist x y := dist_pos.mpr hxy
    have h2 : dist x y ≤ diam s := dist_le_diam_of_mem hbs hx hy
    linarith
  -- rescale to diameter √3
  set r : ℝ := Real.sqrt 3 / diam s with hrdef
  have hr : 0 < r := by positivity
  set s' : Set E3 := r • s with hs'def
  have hbs' : IsBounded s' := by
    obtain ⟨R, hR⟩ := hbs.subset_closedBall (0 : E3)
    apply (isBounded_closedBall (x := (0 : E3)) (r := r * R)).subset
    rintro y ⟨x, hx, rfl⟩
    have h1 := hR hx
    rw [mem_closedBall, dist_zero_right] at h1 ⊢
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left h1 hr.le
  have hnt' : s'.Nontrivial := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hs
    exact ⟨r • x, smul_mem_smul_set hx, r • y, smul_mem_smul_set hy,
      fun h => hxy (smul_right_injective E3 hr.ne' h)⟩
  have hdiam' : diam s' = Real.sqrt 3 := by
    rw [hs'def, diam_smul₀, Real.norm_eq_abs, abs_of_pos hr, hrdef]
    field_simp
  -- position inside the truncated octahedron
  obtain ⟨e, he⟩ :=
    exists_truncated_position hbs' hnt'.nonempty (le_of_eq hdiam')
  set K : Set E3 := ⇑e '' s' with hKdef
  have hKT : K ⊆ TruncOct := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hl1, ht0, ht1, ht2⟩ := he x hx
    exact ⟨hl1, ht0, ht1, ht2⟩
  have hediamK : ediam K = ENNReal.ofReal (Real.sqrt 3) := by
    rw [hKdef, e.isometry.ediam_image, ← hdiam', diam,
      ENNReal.ofReal_toReal hbs'.ediam_ne_top]
  -- the four-piece cover, transported back
  have hK := hasBorsukCover_of_subset_truncOct hKT hediamK
  have hs'cov : HasBorsukCover 4 s' := by
    have h2 := hK.image e.symm
    have h3 : ⇑e.symm '' K = s' := by
      rw [hKdef, Set.image_image]
      simp
    rwa [h3] at h2
  have hcov := HasBorsukCover.smul (r := r⁻¹) (by positivity) hs'cov
  have hss : r⁻¹ • s' = s := by
    rw [hs'def, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  rwa [hss] at hcov

end Space

end Borsuk

namespace Borsuk

open Metric Bornology Set

/-- Borsuk's conjecture holds vacuously in dimension `0`: the space is a single point, so
there is no bounded set with two distinct points. -/
theorem borsukConjecture_zero : BorsukConjecture 0 := by
  intro s _ hs
  obtain ⟨x, -, y, -, hxy⟩ := hs
  exact absurd (PiLp.ext fun i => i.elim0) hxy

section DimensionOne

/-- Every bounded set of reals with at least two points can be divided into two parts of
smaller diameter: split at the midpoint of `[sInf s, sSup s]`. -/
theorem Real.hasBorsukCover_two {s : Set ℝ} (hb : IsBounded s) (hs : s.Nontrivial) :
    HasBorsukCover 2 s := by
  set a := sInf s with ha
  set b := sSup s with hb'
  have hab : 0 < b - a := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hs
    have h₁ : a ≤ min x y := le_min (csInf_le hb.bddBelow hx) (csInf_le hb.bddBelow hy)
    have h₂ : max x y ≤ b := max_le (le_csSup hb.bddAbove hx) (le_csSup hb.bddAbove hy)
    have : min x y < max x y := min_lt_max.mpr hxy
    linarith
  have hdiam : ediam s = ENNReal.ofReal (b - a) := Real.ediam_eq hb
  have hmem : ∀ x ∈ s, x ∈ Icc a b := fun x hx =>
    ⟨csInf_le hb.bddBelow hx, le_csSup hb.bddAbove hx⟩
  set m := (a + b) / 2 with hm
  have hhalf : ENNReal.ofReal ((b - a) / 2) < ediam s := by
    rw [hdiam, ENNReal.ofReal_lt_ofReal_iff hab]
    linarith
  refine ⟨![s ∩ Iic m, s ∩ Ici m], fun x hx => ?_, fun i => ?_⟩
  · rcases le_total x m with h | h
    · exact mem_iUnion.mpr ⟨0, hx, h⟩
    · exact mem_iUnion.mpr ⟨1, hx, h⟩
  · fin_cases i
    · change ediam (s ∩ Iic m) < ediam s
      calc ediam (s ∩ Iic m)
          ≤ ediam (Icc a m) := ediam_mono fun x hx => ⟨(hmem x hx.1).1, hx.2⟩
        _ ≤ ENNReal.ofReal ((b - a) / 2) := by
            rw [Real.ediam_Icc]
            exact ENNReal.ofReal_le_ofReal (by rw [hm]; linarith)
        _ < ediam s := hhalf
    · change ediam (s ∩ Ici m) < ediam s
      calc ediam (s ∩ Ici m)
          ≤ ediam (Icc m b) := ediam_mono fun x hx => ⟨hx.2, (hmem x hx.1).2⟩
        _ ≤ ENNReal.ofReal ((b - a) / 2) := by
            rw [Real.ediam_Icc]
            exact ENNReal.ofReal_le_ofReal (by rw [hm]; linarith)
        _ < ediam s := hhalf

/-- The isometric equivalence between `ℝ` and one-dimensional Euclidean space. -/
noncomputable def IsometryEquiv.realEuclidean : ℝ ≃ᵢ EuclideanSpace ℝ (Fin 1) where
  toFun x := !₂[x]
  invFun x := x 0
  left_inv x := rfl
  right_inv x := PiLp.ext fun i => by fin_cases i; rfl
  isometry_toFun := Isometry.of_dist_eq fun x y => by
    rw [EuclideanSpace.dist_eq]
    simp

/-- Borsuk's conjecture holds in dimension `1`: a bounded set of reals with at least two
points splits at the midpoint of its smallest enclosing interval into two parts of smaller
diameter. -/
theorem borsukConjecture_one : BorsukConjecture 1 := by
  intro s hbs hs
  set e := IsometryEquiv.realEuclidean with he
  have hbt : IsBounded (⇑e.symm '' s) := e.symm.isometry.lipschitz.isBounded_image hbs
  have hnt : (⇑e.symm '' s).Nontrivial := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hs
    exact ⟨e.symm x, mem_image_of_mem _ hx, e.symm y, mem_image_of_mem _ hy,
      fun h => hxy (e.symm.injective h)⟩
  have h2 := (Real.hasBorsukCover_two hbt hnt).image e
  have himg : ⇑e '' (⇑e.symm '' s) = s := by
    rw [image_image]
    simp
  rwa [himg] at h2

end DimensionOne

end Borsuk

theorem OMA.solution : type_of% @Erdos505.erdos_505.small_dim := by
  intro n hn
  interval_cases n
  · exact Borsuk.borsukConjecture_zero
  · exact Borsuk.borsukConjecture_one
  · exact Borsuk.borsukConjecture_two
  · exact Borsuk.borsukConjecture_three
