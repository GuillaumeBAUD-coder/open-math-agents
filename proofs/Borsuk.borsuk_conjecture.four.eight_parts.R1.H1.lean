import OMAReductions.R_Borsuk_borsuk_conjecture_four_eight_parts_R1
import Mathlib

/-!
Eight-part Borsuk covering in four dimensions for the intermediate circumradius regime.
Normalisation and contact-simplex preliminaries are adapted from Logan R. Chalmers,
Lean formalisation of the four-dimensional six-part theorem (2026),
https://doi.org/10.5281/zenodo.23966881 (CC BY 4.0).
-/

noncomputable section

namespace BorsukEightH1

open Metric Bornology
open scoped BigOperators Pointwise InnerProductSpace

abbrev E4 := EuclideanSpace ℝ (Fin 4)

/- Normalisation and Contact Simplex -/

def radiusAt {E : Type*} [PseudoMetricSpace E] (K : Set E) (c : E) : ℝ :=
  sSup ((fun x => dist x c) '' K)

theorem radiusAt_attained {E : Type*} [PseudoMetricSpace E] {K : Set E}
    (hK : IsCompact K) (hne : K.Nonempty) (c : E) :
    ∃ x ∈ K, radiusAt K c = dist x c ∧ ∀ y ∈ K, dist y c ≤ radiusAt K c := by
  obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne
    (continuous_id.dist continuous_const).continuousOn
  have hg : IsGreatest ((fun y => dist y c) '' K) (dist x c) := by
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hmax hy
  have hr : radiusAt K c = dist x c := hg.csSup_eq
  exact ⟨x, hx, hr, fun y hy => hr ▸ hmax hy⟩

theorem dist_le_radiusAt {E : Type*} [PseudoMetricSpace E] {K : Set E}
    (hK : IsCompact K) (hne : K.Nonempty) {x : E} (hx : x ∈ K) (c : E) :
    dist x c ≤ radiusAt K c := (radiusAt_attained hK hne c).choose_spec.2.2 x hx

theorem radiusAt_nonneg {E : Type*} [PseudoMetricSpace E] {K : Set E}
    (hK : IsCompact K) (hne : K.Nonempty) (c : E) : 0 ≤ radiusAt K c := by
  obtain ⟨x, hx⟩ := hne
  exact dist_nonneg.trans (dist_le_radiusAt hK ⟨x, hx⟩ hx c)

theorem radiusAt_lipschitz {E : Type*} [PseudoMetricSpace E] {K : Set E}
    (hK : IsCompact K) (hne : K.Nonempty) : LipschitzWith 1 (radiusAt K) := by
  apply LipschitzWith.of_le_add
  intro c d
  obtain ⟨x, hx, hr, _⟩ := radiusAt_attained hK hne c
  rw [hr]
  exact (dist_triangle_right x c d).trans
    (add_le_add (dist_le_radiusAt hK hne hx d) le_rfl)

theorem exists_minimum_center {E : Type*} [MetricSpace E] [ProperSpace E]
    {K : Set E} (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ c : E, ∀ d : E, radiusAt K c ≤ radiusAt K d := by
  obtain ⟨p, hp⟩ := hne
  have hpball : p ∈ Metric.closedBall p (radiusAt K p) := by
    simpa using radiusAt_nonneg hK ⟨p, hp⟩ p
  obtain ⟨c, _, hmin⟩ := (isCompact_closedBall p (radiusAt K p)).exists_isMinOn
    ⟨p, hpball⟩ (radiusAt_lipschitz hK ⟨p, hp⟩).continuous.continuousOn
  refine ⟨c, fun d => ?_⟩
  by_cases hd : d ∈ Metric.closedBall p (radiusAt K p)
  · exact hmin hd
  · have hout : radiusAt K p < dist p d := by
      simpa only [Metric.mem_closedBall, not_le, dist_comm] using hd
    exact (hmin hpball).trans (hout.le.trans (dist_le_radiusAt hK ⟨p, hp⟩ hp d))

theorem radiusAt_translate (K : Set E4) (c d : E4) :
    radiusAt ((fun x => x - c) '' K) d = radiusAt K (d + c) := by
  unfold radiusAt
  congr 1
  rw [Set.image_image]
  congr 1
  funext x
  simp only [dist_eq_norm]
  congr 1
  abel

theorem subtract_isometry (c : E4) : Isometry (fun x : E4 => x - c) := by
  apply Isometry.of_dist_eq
  intro x y
  simp only [dist_eq_norm]
  congr 1
  abel

theorem exists_compact_centered_normalization {S : Set E4}
    (hS : IsCompact S) (hD : 0 < diam S) :
    ∃ c : E4, let K := (fun x => x - c) '' ((diam S)⁻¹ • S)
      IsCompact K ∧ diam K = 1 ∧ ∀ d : E4, radiusAt K 0 ≤ radiusAt K d := by
  let S1 := (diam S)⁻¹ • S
  have hS1 : IsCompact S1 := hS.image (continuous_const_smul ((diam S)⁻¹))
  have hd1 : diam S1 = 1 := by
    rw [diam_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hD), inv_mul_cancel₀ hD.ne']
  have hne : S1.Nonempty := by
    by_contra h
    have he : S1 = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    simp [he] at hd1
  obtain ⟨c, hc⟩ := exists_minimum_center hS1 hne
  refine ⟨c, hS1.image (subtract_isometry c).continuous,
    (subtract_isometry c).diam_image S1 |>.trans hd1, ?_⟩
  intro d
  rw [radiusAt_translate, radiusAt_translate, zero_add]
  exact hc (d + c)

def combinations (n : ℕ) (K : Set E4) : Set E4 :=
  (fun wz : (Fin n → ℝ) × (Fin n → E4) => ∑ i, wz.1 i • wz.2 i) ''
    (stdSimplex ℝ (Fin n) ×ˢ {z : Fin n → E4 | ∀ i, z i ∈ K})

theorem combinations_isCompact (n : ℕ) {K : Set E4} (hK : IsCompact K) :
    IsCompact (combinations n K) := by
  apply ((isCompact_stdSimplex ℝ (Fin n)).prod
    (isCompact_pi_infinite (fun _ => hK))).image
  fun_prop

theorem combinations_subset_hull (n : ℕ) (K : Set E4) :
    combinations n K ⊆ convexHull ℝ K := by
  rintro _ ⟨⟨w, z⟩, ⟨hw, hz⟩, rfl⟩
  exact (convex_convexHull ℝ K).sum_mem (fun i _ => hw.1 i) hw.2
    (fun i _ => subset_convexHull ℝ K (hz i))

theorem affineIndependent_card_le_five {ι : Type} [Fintype ι] {z : ι → E4}
    (hz : AffineIndependent ℝ z) : Fintype.card ι ≤ 5 := by
  have h := hz.card_le_finrank_succ
  have hdim := Submodule.finrank_le (vectorSpan ℝ (Set.range z))
  have he : Module.finrank ℝ E4 = 4 := finrank_euclideanSpace_fin
  omega

theorem convexHull_eq_five_combinations (K : Set E4) :
    convexHull ℝ K = ⋃ n : Fin 6, combinations n.val K := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨ι, hι, z, w, hzK, hz, hwpos, hwsum, hwz⟩ :=
      eq_pos_convex_span_of_mem_convexHull hx
    let _ := hι
    let n : Fin 6 := ⟨Fintype.card ι, by have := affineIndependent_card_le_five hz; omega⟩
    let e : Fin n.val ≃ ι := (Fintype.equivFin ι).symm
    apply Set.mem_iUnion.mpr
    refine ⟨n, ⟨(w ∘ e, z ∘ e), ⟨?_, ?_⟩, ?_⟩⟩
    · exact ⟨fun i => (hwpos (e i)).le, (e.sum_comp w).trans hwsum⟩
    · intro i; exact hzK ⟨e i, rfl⟩
    · exact (e.sum_comp (fun i => w i • z i)).trans hwz
  · apply Set.iUnion_subset
    intro n; exact combinations_subset_hull n.val K

theorem convexHull_isCompact {K : Set E4} (hK : IsCompact K) :
    IsCompact (convexHull ℝ K) := by
  rw [convexHull_eq_five_combinations]
  exact isCompact_iUnion (fun n => combinations_isCompact n.val hK)

def contacts (K : Set E4) : Set E4 := {x | x ∈ K ∧ ‖x‖ = radiusAt K 0}

theorem contacts_isCompact {K : Set E4} (hK : IsCompact K) : IsCompact (contacts K) :=
  hK.inter_right (isClosed_eq continuous_norm continuous_const)

theorem contacts_nonempty {K : Set E4} (hK : IsCompact K) (hne : K.Nonempty) :
    (contacts K).Nonempty := by
  obtain ⟨x, hx, hr, _⟩ := radiusAt_attained hK hne 0
  exact ⟨x, hx, by simpa using hr.symm⟩

theorem exists_improved_center_of_contact_direction {K : Set E4}
    (hK : IsCompact K) (hne : K.Nonempty) (v : E4) (a : ℝ) (ha : 0 < a)
    (hcontact : ∀ x ∈ contacts K, a < inner ℝ v x) :
    ∃ c : E4, radiusAt K c < radiusAt K 0 := by
  let R := radiusAt K 0
  have hnorm (x : E4) (hx : x ∈ K) : ‖x‖ ≤ R := by
    simpa [R] using dist_le_radiusAt hK hne hx 0
  have hR : 0 < R := by
    by_contra hn
    have hrzero : R = 0 := le_antisymm (le_of_not_gt hn) (radiusAt_nonneg hK hne 0)
    obtain ⟨x, hx⟩ := contacts_nonempty hK hne
    have hxzero : x = 0 := norm_eq_zero.mp (hx.2.trans hrzero)
    have := hcontact x hx
    simp only [hxzero, inner_zero_right] at this
    linarith
  let B : Set E4 := {x | x ∈ K ∧ inner ℝ v x ≤ a / 2}
  have hB : IsCompact B :=
    hK.inter_right (isClosed_le (show Continuous (fun x : E4 => inner ℝ v x) by fun_prop) continuous_const)
  have hbad : ∃ r : ℝ, 0 ≤ r ∧ r < R ∧ ∀ x ∈ K, inner ℝ v x ≤ a / 2 → ‖x‖ ≤ r := by
    rcases B.eq_empty_or_nonempty with he | hneB
    · refine ⟨0, le_rfl, hR, fun x hx hv => ?_⟩
      have : x ∈ B := ⟨hx, hv⟩
      simp [he] at this
    · obtain ⟨z, hz, hmax⟩ := hB.exists_isMaxOn hneB continuous_norm.continuousOn
      have hlt : ‖z‖ < R := lt_of_le_of_ne (hnorm z hz.1) (fun he => by
        have hc := hcontact z ⟨hz.1, he⟩; linarith [hz.2])
      exact ⟨‖z‖, norm_nonneg _, hlt, fun x hx hv => hmax ⟨hx, hv⟩⟩
  obtain ⟨r, _, hrR, hbad⟩ := hbad
  have hdena : 0 < ‖v‖ ^ 2 + 1 := by positivity
  have hdenb : 0 < ‖v‖ + 1 := by positivity
  obtain ⟨t, ht, htmin⟩ := exists_between (lt_min
    (div_pos ha hdena) (div_pos (sub_pos.mpr hrR) hdenb))
  have hta : t * (‖v‖ ^ 2 + 1) < a := (lt_div_iff₀ hdena).mp (lt_min_iff.mp htmin).1
  have htb : t * (‖v‖ + 1) < R - r := (lt_div_iff₀ hdenb).mp (lt_min_iff.mp htmin).2
  have himprove : ∀ x ∈ K, dist x (t • v) < R := by
    intro x hx
    rw [dist_eq_norm]
    by_cases hb : inner ℝ v x ≤ a / 2
    · calc
        ‖x - t • v‖ ≤ ‖x‖ + ‖t • v‖ := norm_sub_le _ _
        _ ≤ r + t * ‖v‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
          exact add_le_add (hbad x hx hb) le_rfl
        _ < R := by nlinarith
    · have hxn : ‖x‖ ^ 2 ≤ R ^ 2 := (sq_le_sq₀ (norm_nonneg _) hR.le).mpr (hnorm x hx)
      have hdir : t * (t * ‖v‖ ^ 2) < t * (2 * inner ℝ v x) :=
        mul_lt_mul_of_pos_left (by nlinarith) ht
      have hs : ‖x - t • v‖ ^ 2 < R ^ 2 := by
        rw [norm_sub_sq_real, real_inner_smul_right, ← real_inner_comm x v,
          norm_smul, Real.norm_eq_abs, abs_of_pos ht]
        nlinarith
      nlinarith [norm_nonneg (x - t • v)]
  obtain ⟨x, hx, he, _⟩ := radiusAt_attained hK hne (t • v)
  exact ⟨t • v, he ▸ himprove x hx⟩

theorem zero_mem_convexHull_contacts {K : Set E4} (hK : IsCompact K)
    (hne : K.Nonempty) (hmin : ∀ c : E4, radiusAt K 0 ≤ radiusAt K c) :
    (0 : E4) ∈ convexHull ℝ (contacts K) := by
  by_contra hout
  obtain ⟨f, a, ha, hsep⟩ := geometric_hahn_banach_point_closed
    (convex_convexHull ℝ (contacts K))
    (convexHull_isCompact (contacts_isCompact hK)).isClosed hout
  have ha0 : 0 < a := by simpa using ha
  let v := (InnerProductSpace.toDual ℝ E4).symm f
  have hdir : ∀ x ∈ contacts K, a < inner ℝ v x := fun x hx => by
    simpa [v] using hsep x (subset_convexHull ℝ (contacts K) hx)
  obtain ⟨c, hc⟩ := exists_improved_center_of_contact_direction hK hne v a ha0 hdir
  exact (not_lt_of_ge (hmin c)) hc

theorem exists_positive_contact_simplex {K : Set E4} (hK : IsCompact K)
    (hne : K.Nonempty) (hmin : ∀ c : E4, radiusAt K 0 ≤ radiusAt K c) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ 5 ∧ ∃ (p : Fin n → E4) (w : Fin n → ℝ),
      (∀ i, p i ∈ K ∧ ‖p i‖ = radiusAt K 0) ∧ AffineIndependent ℝ p ∧
      (∀ i, 0 < w i) ∧ (∑ i, w i) = 1 ∧ (∑ i, w i • p i) = 0 := by
  obtain ⟨ι, hι, z, w, hzK, hz, hwpos, hwsum, hwz⟩ :=
    eq_pos_convex_span_of_mem_convexHull (zero_mem_convexHull_contacts hK hne hmin)
  let _ := hι
  have hn : 1 ≤ Fintype.card ι := by
    by_contra h
    have he : Fintype.card ι = 0 := by omega
    have _ : IsEmpty ι := Fintype.card_eq_zero_iff.mp he
    simp at hwsum
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, hn, affineIndependent_card_le_five hz,
    z ∘ e, w ∘ e, fun i => hzK ⟨e i, rfl⟩, hz.comp_embedding e.toEmbedding,
    fun i => hwpos (e i), (e.sum_comp w).trans hwsum,
    (e.sum_comp (fun i => w i • z i)).trans hwz⟩

theorem contact_weighted_distance_identity {n : ℕ} (p : Fin n → E4) (w : Fin n → ℝ)
    (R : ℝ) (hnorm : ∀ i, ‖p i‖ = R) (hw : ∑ i, w i = 1)
    (hbary : ∑ i, w i • p i = 0) (c : E4) :
    (∑ i, w i * ‖p i - c‖ ^ 2) = R ^ 2 + ‖c‖ ^ 2 := by
  have hi : (∑ i, w i * inner ℝ (p i) c) = 0 := by
    simp only [← real_inner_smul_left, ← sum_inner, hbary, inner_zero_left]
  calc
    (∑ i, w i * ‖p i - c‖ ^ 2) =
      (∑ i, w i * R ^ 2) - 2 * (∑ i, w i * inner ℝ (p i) c) + (∑ i, w i * ‖c‖ ^ 2) := by
      simp only [norm_sub_sq_real, hnorm, mul_add, mul_sub,
        Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
      congr 2; apply Finset.sum_congr rfl; intro i _; ring
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul, hw, hi]; ring

theorem contact_pair_variance {n : ℕ} (p : Fin n → E4) (w : Fin n → ℝ)
    (R : ℝ) (hnorm : ∀ i, ‖p i‖ = R) (hw : ∑ i, w i = 1)
    (hbary : ∑ i, w i • p i = 0) :
    (∑ i, ∑ j, w i * w j * dist (p i) (p j) ^ 2) = 2 * R ^ 2 := by
  have hrow (i : Fin n) : (∑ j, w j * dist (p i) (p j) ^ 2) = 2 * R ^ 2 := by
    simp_rw [dist_comm (p i), dist_eq_norm]
    rw [contact_weighted_distance_identity p w R hnorm hw hbary, hnorm i]; ring
  calc
    (∑ i, ∑ j, w i * w j * dist (p i) (p j) ^ 2) =
        ∑ i, w i * (∑ j, w j * dist (p i) (p j) ^ 2) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ i, w i * (2 * R ^ 2) := by simp_rw [hrow]
    _ = 2 * R ^ 2 := by rw [← Finset.sum_mul, hw, one_mul]

theorem contact_jung_bound {n : ℕ} (hn : 0 < n)
    (p : Fin n → E4) (w : Fin n → ℝ) (R : ℝ)
    (hnorm : ∀ i, ‖p i‖ = R) (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1)
    (hbary : ∑ i, w i • p i = 0) (hd : ∀ i j, dist (p i) (p j) ≤ 1) :
    R ^ 2 ≤ ((n : ℝ) - 1) / (2 * (n : ℝ)) := by
  have hrow (i : Fin n) : (∑ j, w j * dist (p i) (p j) ^ 2) ≤ 1 - w i := by
    calc
      (∑ j, w j * dist (p i) (p j) ^ 2) ≤ ∑ j, (w j - if j = i then w i else 0) := by
        apply Finset.sum_le_sum; intro j _
        by_cases hji : j = i
        · simp [hji]
        · simp only [hji, ↓reduceIte, sub_zero]
          have hs : dist (p i) (p j) ^ 2 ≤ 1 := by
            nlinarith [hd i j, dist_nonneg (x := p i) (y := p j)]
          simpa using mul_le_mul_of_nonneg_left hs (hw0 j)
      _ = 1 - w i := by simp [Finset.sum_sub_distrib, hw]
  have hweight : 2 * R ^ 2 ≤ 1 - ∑ i, w i ^ 2 := by
    rw [← contact_pair_variance p w R hnorm hw hbary]
    calc
      _ = ∑ i, w i * (∑ j, w j * dist (p i) (p j) ^ 2) := by simp only [Finset.mul_sum, mul_assoc]
      _ ≤ ∑ i, w i * (1 - w i) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hrow i) (hw0 i))
      _ = 1 - ∑ i, w i ^ 2 := by simp [mul_sub, Finset.sum_sub_distrib, hw, pow_two]
  have hcs : 1 ≤ (n : ℝ) * ∑ i, w i ^ 2 := by
    simpa [hw] using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := w))
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  apply (le_div_iff₀ (mul_pos (by norm_num) hnreal)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hweight hnreal.le]

/- Nearest-Facet Contact Reduction -/

theorem drop_one_contact {n : ℕ} {q : Fin (n + 3) → E4} {w : Fin (n + 3) → ℝ} {ρ₀ : ℝ}
    (hρ : 0 < ρ₀) (hnorm : ∀ i, ‖q i‖ ^ 2 = ρ₀) (haff : AffineIndependent ℝ q)
    (hwpos : ∀ i, 0 < w i) (hwsum : ∑ i, w i = 1) (hbary : ∑ i, w i • q i = 0) :
    ∃ (i : Fin (n + 3)) (c : E4) (μ : Fin (n + 2) → ℝ),
      (∀ k, 0 < μ k) ∧ (∑ k, μ k = 1) ∧ (∑ k, μ k • q (i.succAbove k) = c) ∧
      (∀ k, ‖q (i.succAbove k) - c‖ ^ 2 = ρ₀ - ‖c‖ ^ 2) ∧
      ((1 - 1 / ((n : ℝ) + 2) ^ 2) * ρ₀ ≤ ρ₀ - ‖c‖ ^ 2) := by
  let face (i : Fin (n + 3)) : Fin (n + 2) → E4 := q ∘ i.succAbove
  obtain ⟨c, hc_orth, hc_comb⟩ : ∃ c : Fin (n + 3) → E4,
      (∀ i k, inner ℝ (c i) (face i k - c i) = 0) ∧
      (∀ i, ∃ μ : Fin (n + 2) → ℝ, (∑ k, μ k = 1) ∧ (∑ k, μ k • face i k = c i)) := by
    let V (i : Fin (n + 3)) : Submodule ℝ E4 :=
      Submodule.span ℝ (Set.range (fun k : Fin (n + 1) => face i k.succ - face i 0))
    refine ⟨fun i => face i 0 - (V i).starProjection (face i 0), ?_, ?_⟩
    · intro i k
      have hmem0 : face i 0 - (V i).starProjection (face i 0) ∈ (V i)ᗮ :=
        Submodule.sub_starProjection_mem_orthogonal _
      have hv : (V i).starProjection (face i 0) ∈ V i :=
        ((V i).orthogonalProjectionOnto (face i 0)).2
      have hdiff : face i k - (face i 0 - (V i).starProjection (face i 0)) ∈ V i := by
        refine Fin.cases ?_ (fun k' => ?_) k
        · simpa only [sub_sub_cancel] using hv
        · have h1 : face i k'.succ - face i 0 ∈ V i := Submodule.subset_span ⟨k', rfl⟩
          have h2 : (V i).starProjection (face i 0) ∈ V i := hv
          have heq : face i k'.succ - (face i 0 - (V i).starProjection (face i 0)) =
              (face i k'.succ - face i 0) + (V i).starProjection (face i 0) := by abel
          rw [heq]
          exact (V i).add_mem h1 h2
      exact (Submodule.mem_orthogonal' (V i) _).mp hmem0 _ hdiff
    · intro i
      have hv : (V i).starProjection (face i 0) ∈ V i :=
        ((V i).orthogonalProjectionOnto (face i 0)).2
      obtain ⟨α, hα⟩ := Submodule.mem_span_range_iff_exists_fun ℝ |>.mp hv
      let μ : Fin (n + 2) → ℝ := Fin.cons (1 + ∑ k, α k) (fun k => -α k)
      refine ⟨μ, ?_, ?_⟩
      · simp only [μ, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Finset.sum_neg_distrib]
        ring
      · simp only [μ, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, neg_smul,
          Finset.sum_neg_distrib, ← hα, smul_sub, Finset.sum_sub_distrib,
          ← Finset.sum_smul, add_smul, one_smul]
        abel
  have hc_inner (i : Fin (n + 3)) (k : Fin (n + 2)) :
      inner ℝ (c i) (face i k) = ‖c i‖ ^ 2 := by
    have h := hc_orth i k
    rw [inner_sub_right, real_inner_self_eq_norm_sq] at h
    linarith
  have hc_dist (i : Fin (n + 3)) (k : Fin (n + 2)) :
      ‖face i k - c i‖ ^ 2 = ρ₀ - ‖c i‖ ^ 2 := by
    rw [norm_sub_sq_real]
    have hin : inner ℝ (face i k) (c i) = ‖c i‖ ^ 2 := by
      rw [real_inner_comm, hc_inner i k]
    have hn := hnorm (i.succAbove k)
    change ‖face i k‖ ^ 2 = ρ₀ at hn
    linarith
  have hc_ne (i : Fin (n + 3)) : c i ≠ 0 := by
    intro h0
    obtain ⟨μ, hμ1, hμc⟩ := hc_comb i
    rw [h0] at hμc
    let μ' : Fin (n + 3) → ℝ := i.insertNth 0 μ
    have hμ'sum : ∑ j, μ' j = 1 := by
      rw [Fin.sum_univ_succAbove _ i]
      simp [μ', hμ1]
    have hμ'bary : ∑ j, μ' j • q j = 0 := by
      rw [Fin.sum_univ_succAbove _ i]
      simpa [μ', face] using hμc
    have hweq : μ' = w := by
      have hws : ∑ j ∈ Finset.univ, (μ' - w) j = 0 := by
        simp [Pi.sub_apply, Finset.sum_sub_distrib, hμ'sum, hwsum]
      have hwv : Finset.univ.weightedVSub q (μ' - w) = 0 := by
        rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ hws (0 : E4)]
        simp [Finset.weightedVSubOfPoint_apply, vsub_eq_sub, sub_smul,
          Finset.sum_sub_distrib, hμ'bary, hbary]
      have hdiff0 := haff Finset.univ (μ' - w) hws hwv
      funext j
      have hj := hdiff0 j (Finset.mem_univ j)
      simp only [Pi.sub_apply] at hj
      linarith
    have hi0 : μ' i = 0 := by simp [μ']
    linarith [hwpos i, congrFun hweq i]
  have hc_opp (i : Fin (n + 3)) :
      w i * inner ℝ (c i) (q i) = -(1 - w i) * ‖c i‖ ^ 2 := by
    have h0 : inner ℝ (c i) (∑ j, w j • q j) = 0 := by rw [hbary, inner_zero_right]
    rw [inner_sum, Fin.sum_univ_succAbove _ i] at h0
    have hrest : ∑ k : Fin (n + 2), inner ℝ (c i) (w (i.succAbove k) • q (i.succAbove k)) =
        (∑ k : Fin (n + 2), w (i.succAbove k)) * ‖c i‖ ^ 2 := by
      simp_rw [inner_smul_right]
      have : ∀ k, inner ℝ (c i) (q (i.succAbove k)) = ‖c i‖ ^ 2 := hc_inner i
      simp_rw [this, ← Finset.sum_mul]
    have hw_rest : w i + ∑ k : Fin (n + 2), w (i.succAbove k) = 1 := by
      rw [← Fin.sum_univ_succAbove w i, hwsum]
    rw [inner_smul_right, hrest] at h0
    nlinarith
  have hw_lt_one (i : Fin (n + 3)) : w i < 1 := by
    have hw_rest : w i + ∑ k : Fin (n + 2), w (i.succAbove k) = 1 := by
      rw [← Fin.sum_univ_succAbove w i, hwsum]
    have hpos_rest : 0 < ∑ k : Fin (n + 2), w (i.succAbove k) :=
      Finset.sum_pos (fun k _ => hwpos (i.succAbove k)) Finset.univ_nonempty
    linarith
  have hc_bound (i : Fin (n + 3)) :
      (1 - w i) ^ 2 * ‖c i‖ ^ 2 ≤ (w i) ^ 2 * ρ₀ := by
    have hcs : |inner ℝ (c i) (q i)| ≤ ‖c i‖ * ‖q i‖ := abs_real_inner_le_norm _ _
    have hsq := pow_le_pow_left₀ (abs_nonneg _) hcs 2
    rw [sq_abs, mul_pow, hnorm i] at hsq
    have hopp : (w i) ^ 2 * (inner ℝ (c i) (q i)) ^ 2 = (1 - w i) ^ 2 * (‖c i‖ ^ 2) ^ 2 := by
      calc
        (w i) ^ 2 * (inner ℝ (c i) (q i)) ^ 2 = (w i * inner ℝ (c i) (q i)) ^ 2 := by ring
        _ = (-(1 - w i) * ‖c i‖ ^ 2) ^ 2 := by rw [hc_opp i]
        _ = (1 - w i) ^ 2 * (‖c i‖ ^ 2) ^ 2 := by ring
    have hwi2 : 0 < (w i) ^ 2 := sq_pos_of_pos (hwpos i)
    have hmul := mul_le_mul_of_nonneg_left hsq hwi2.le
    by_cases hc0 : ‖c i‖ ^ 2 = 0
    · rw [hc0, mul_zero]; positivity
    · have hcpos : 0 < ‖c i‖ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hc0)
      nlinarith
  obtain ⟨i₀, _, hi₀⟩ := Finset.exists_min_image Finset.univ w Finset.univ_nonempty
  have hwi₀ : ((n : ℝ) + 3) * w i₀ ≤ 1 := by
    have hsum_ge : ((n : ℝ) + 3) * w i₀ ≤ ∑ j : Fin (n + 3), w j := by
      calc
        ((n : ℝ) + 3) * w i₀ = ∑ _j : Fin (n + 3), w i₀ := by simp
        _ ≤ ∑ j : Fin (n + 3), w j := Finset.sum_le_sum (fun j _ => hi₀ j (Finset.mem_univ j))
    linarith
  have hci₀ : ((n : ℝ) + 2) ^ 2 * ‖c i₀‖ ^ 2 ≤ ρ₀ := by
    have hb := hc_bound i₀
    have h1 : ((n : ℝ) + 2) * w i₀ ≤ 1 - w i₀ := by linarith
    have hnn : 0 ≤ ((n : ℝ) + 2) * w i₀ := mul_nonneg (by positivity) (hwpos i₀).le
    have h2 : (((n : ℝ) + 2) * w i₀) ^ 2 ≤ (1 - w i₀) ^ 2 := pow_le_pow_left₀ hnn h1 2
    have h3 := mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖c i₀‖)
    have hwi2 : 0 < (w i₀) ^ 2 := sq_pos_of_pos (hwpos i₀)
    nlinarith
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ (fun j => ‖c j‖) Finset.univ_nonempty
  obtain ⟨μ, hμ1, hμc⟩ := hc_comb i
  refine ⟨i, c i, μ, ?_, hμ1, hμc, hc_dist i, ?_⟩
  · intro k
    let j := i.succAbove k
    have hij : j ≠ i := i.succAbove_ne k
    have hcj_pos : 0 < ‖c j‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (hc_ne j))
    have hci_le : ‖c i‖ ≤ ‖c j‖ := hi j (Finset.mem_univ j)
    have hneq_c : c j ≠ c i := by
      intro heq
      have h1 : inner ℝ (c j) (q j) = ‖c i‖ ^ 2 := by
        rw [heq]; exact hc_inner i k
      have h2 := hc_opp j
      have h3 : 0 < ‖c i‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (hc_ne i))
      have h4 : 0 < 1 - w j := sub_pos.mpr (hw_lt_one j)
      nlinarith [hwpos j]
    have hdiff_pos : 0 < ‖c j - c i‖ ^ 2 :=
      sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hneq_c))
    have hinner_lt : inner ℝ (c j) (c i) < ‖c j‖ ^ 2 := by
      rw [norm_sub_sq_real] at hdiff_pos
      have hsq_le : ‖c i‖ ^ 2 ≤ ‖c j‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hci_le 2
      linarith
    have hexp : w j * inner ℝ (c j) (c i) = (w j - μ k) * ‖c j‖ ^ 2 := by
      rw [← hμc, inner_sum]
      simp_rw [inner_smul_right]
      have hterm (l : Fin (n + 2)) :
          w j * (μ l * inner ℝ (c j) (face i l)) =
            (w j * μ l - if l = k then μ k else 0) * ‖c j‖ ^ 2 := by
        by_cases hlk : l = k
        · subst hlk
          simp only [↓reduceIte]
          change w j * (μ l * inner ℝ (c j) (q j)) = _
          have hopp := hc_opp j
          calc
            w j * (μ l * inner ℝ (c j) (q j)) = μ l * (w j * inner ℝ (c j) (q j)) := by ring
            _ = μ l * (-(1 - w j) * ‖c j‖ ^ 2) := by rw [hopp]
            _ = (w j * μ l - μ l) * ‖c j‖ ^ 2 := by ring
        · simp only [hlk, ↓reduceIte, sub_zero]
          have hne_jl : i.succAbove l ≠ j := fun h => hlk (i.succAbove_right_injective h)
          obtain ⟨m, hm⟩ := Fin.exists_succAbove_eq hne_jl
          have hin : inner ℝ (c j) (face i l) = ‖c j‖ ^ 2 := by
            change inner ℝ (c j) (q (i.succAbove l)) = ‖c j‖ ^ 2
            rw [← hm]; exact hc_inner j m
          rw [hin]; ring
      calc
        w j * ∑ l, μ l * inner ℝ (c j) (face i l)
          = ∑ l, w j * (μ l * inner ℝ (c j) (face i l)) := Finset.mul_sum _ _ _
        _ = ∑ l, (w j * μ l - if l = k then μ k else 0) * ‖c j‖ ^ 2 := by simp_rw [hterm]
        _ = (∑ l, (w j * μ l - if l = k then μ k else 0)) * ‖c j‖ ^ 2 := (Finset.sum_mul _ _ _).symm
        _ = (w j - μ k) * ‖c j‖ ^ 2 := by
          simp [Finset.sum_sub_distrib, ← Finset.mul_sum, hμ1]
    nlinarith [hwpos j]
  · have hle : ‖c i‖ ^ 2 ≤ ‖c i₀‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hi i₀ (Finset.mem_univ i₀)) 2
    have hden : 0 < ((n : ℝ) + 2) ^ 2 := by positivity
    have hci_div : ‖c i‖ ^ 2 ≤ ρ₀ / ((n : ℝ) + 2) ^ 2 := (le_div_iff₀ hden).mpr (by nlinarith)
    have hid : (1 - 1 / ((n : ℝ) + 2) ^ 2) * ρ₀ = ρ₀ - ρ₀ / ((n : ℝ) + 2) ^ 2 := by ring
    linarith


theorem sort_three_sides (P : Fin 3 → E4) :
    ∃ σ : Equiv.Perm (Fin 3),
      dist (P (σ 1)) (P (σ 2)) ≤ dist (P (σ 0)) (P (σ 2)) ∧
      dist (P (σ 0)) (P (σ 2)) ≤ dist (P (σ 0)) (P (σ 1)) := by
  have eval_perm (σ : Equiv.Perm (Fin 3)) (a b c : Fin 3)
      (h0 : σ 0 = a) (h1 : σ 1 = b) (h2 : σ 2 = c)
      (hlo : dist (P b) (P c) ≤ dist (P a) (P c))
      (hhi : dist (P a) (P c) ≤ dist (P a) (P b)) :
      dist (P (σ 1)) (P (σ 2)) ≤ dist (P (σ 0)) (P (σ 2)) ∧
      dist (P (σ 0)) (P (σ 2)) ≤ dist (P (σ 0)) (P (σ 1)) := by
    rw [h0, h1, h2]; exact ⟨hlo, hhi⟩
  by_cases c01_02 : dist (P 0) (P 2) ≤ dist (P 0) (P 1)
  · by_cases c12_02 : dist (P 1) (P 2) ≤ dist (P 0) (P 2)
    · exact ⟨1, eval_perm 1 0 1 2 (by decide) (by decide) (by decide) c12_02 c01_02⟩
    · by_cases c12_01 : dist (P 1) (P 2) ≤ dist (P 0) (P 1)
      · exact ⟨Equiv.swap 0 1, eval_perm _ 1 0 2 (by decide) (by decide) (by decide)
          (by linarith)
          (by rw [dist_comm (P 1) (P 0)]; exact c12_01)⟩
      · exact ⟨Equiv.swap 0 2 * Equiv.swap 0 1, eval_perm _ 1 2 0 (by decide) (by decide) (by decide)
          (by rw [dist_comm (P 2) (P 0), dist_comm (P 1) (P 0)]; exact c01_02)
          (by rw [dist_comm (P 1) (P 0)]; linarith)⟩
  · by_cases c12_01 : dist (P 1) (P 2) ≤ dist (P 0) (P 1)
    · exact ⟨Equiv.swap 1 2, eval_perm _ 0 2 1 (by decide) (by decide) (by decide)
        (by rw [dist_comm (P 2) (P 1)]; exact c12_01) (by linarith)⟩
    · by_cases c12_02 : dist (P 1) (P 2) ≤ dist (P 0) (P 2)
      · exact ⟨Equiv.swap 0 1 * Equiv.swap 0 2, eval_perm _ 2 0 1 (by decide) (by decide) (by decide)
          (by rw [dist_comm (P 2) (P 1)]; linarith)
          (by rw [dist_comm (P 2) (P 1), dist_comm (P 2) (P 0)]; exact c12_02)⟩
      · exact ⟨Equiv.swap 0 2, eval_perm _ 2 1 0 (by decide) (by decide) (by decide)
          (by rw [dist_comm (P 1) (P 0), dist_comm (P 2) (P 0)]; linarith)
          (by rw [dist_comm (P 2) (P 0), dist_comm (P 2) (P 1)]; linarith)⟩

theorem exists_rotated_contact_coords {P : Fin 3 → E4} {μ : Fin 3 → ℝ} {c_Δ : E4} {r τ : ℝ}
    (haff : AffineIndependent ℝ P)
    (hPnorm : ∀ i, ‖P i‖ ^ 2 = r)
    (hPdiam : ∀ i j, dist (P i) (P j) ≤ 1)
    (hμpos : ∀ i, 0 < μ i) (hμsum : ∑ i, μ i = 1) (hμbary : ∑ i, μ i • P i = c_Δ)
    (hτdist : ∀ i, ‖P i - c_Δ‖ ^ 2 = τ)
    (hτlo : (5 / 6 : ℝ) * r ≤ τ) (hτhi : τ ≤ 1 / 3) (hr_pos : 0 < r) :
    ∃ (b : OrthonormalBasis (Fin 4) ℝ E4) (σ : Equiv.Perm (Fin 3))
      (s h x2 y2 x3 y3 : ℝ),
      0 < s ∧ 0 ≤ h ∧ s ^ 2 + h ^ 2 = r ∧ 5 * h ^ 2 ≤ s ^ 2 ∧ 3 * s ^ 2 ≤ 1 ∧
      2 * s ^ 2 - 1 ≤ 2 * s * x2 ∧ x2 ≤ x3 ∧ x3 ≤ 0 ∧ s * (s + x2) ≤ 2 * x3 ^ 2 ∧
      0 ≤ y2 ∧ y2 ^ 2 = s ^ 2 - x2 ^ 2 ∧ y3 ≤ 0 ∧ y3 ^ 2 = s ^ 2 - x3 ^ 2 ∧
      b.repr (P (σ 0)) 0 = s  ∧ b.repr (P (σ 0)) 1 = 0  ∧ b.repr (P (σ 0)) 2 = h ∧ b.repr (P (σ 0)) 3 = 0 ∧
      b.repr (P (σ 1)) 0 = x2 ∧ b.repr (P (σ 1)) 1 = y2 ∧ b.repr (P (σ 1)) 2 = h ∧ b.repr (P (σ 1)) 3 = 0 ∧
      b.repr (P (σ 2)) 0 = x3 ∧ b.repr (P (σ 2)) 1 = y3 ∧ b.repr (P (σ 2)) 2 = h ∧ b.repr (P (σ 2)) 3 = 0 := by
  obtain ⟨σ, hd12, hd02⟩ := sort_three_sides P
  obtain ⟨Q, hQdef⟩ : ∃ Q : Fin 3 → E4, Q = P ∘ σ := ⟨P ∘ σ, rfl⟩
  obtain ⟨ν, hνdef⟩ : ∃ ν : Fin 3 → ℝ, ν = μ ∘ σ := ⟨μ ∘ σ, rfl⟩
  have hQ_apply (i : Fin 3) : Q i = P (σ i) := by rw [hQdef]; rfl
  have hν_apply (i : Fin 3) : ν i = μ (σ i) := by rw [hνdef]; rfl
  rw [← hQ_apply 0, ← hQ_apply 1, ← hQ_apply 2] at hd12 hd02
  have hQaff : AffineIndependent ℝ Q := by rw [hQdef]; exact haff.comp_embedding σ.toEmbedding
  have hνpos (i : Fin 3) : 0 < ν i := by rw [hν_apply]; exact hμpos (σ i)
  have hνsum : ∑ i, ν i = 1 := by rw [hνdef]; exact (Equiv.sum_comp σ μ).trans hμsum
  have hνbary : ∑ i, ν i • Q i = c_Δ := by
    simp_rw [hQ_apply, hν_apply]
    exact (Equiv.sum_comp σ (fun i => μ i • P i)).trans hμbary
  have hQnorm (i : Fin 3) : ‖Q i‖ ^ 2 = r := by rw [hQ_apply]; exact hPnorm (σ i)
  have hQτ (i : Fin 3) : ‖Q i - c_Δ‖ ^ 2 = τ := by rw [hQ_apply]; exact hτdist (σ i)
  have hQdiam (i j : Fin 3) : dist (Q i) (Q j) ≤ 1 := by rw [hQ_apply, hQ_apply]; exact hPdiam _ _
  have hPyth : τ + ‖c_Δ‖ ^ 2 = r ∧ ∀ i, inner ℝ c_Δ (Q i - c_Δ) = 0 := by
    have hrow (i : Fin 3) : 2 * inner ℝ c_Δ (Q i) = r + ‖c_Δ‖ ^ 2 - τ := by
      have hd := hQτ i
      rw [norm_sub_sq_real, hQnorm i, real_inner_comm c_Δ (Q i)] at hd
      linarith
    have havg : 2 * ‖c_Δ‖ ^ 2 = r + ‖c_Δ‖ ^ 2 - τ := by
      calc
        2 * ‖c_Δ‖ ^ 2 = 2 * inner ℝ c_Δ c_Δ := by rw [real_inner_self_eq_norm_sq]
        _ = 2 * inner ℝ c_Δ (∑ i, ν i • Q i) := by rw [hνbary]
        _ = ∑ i, ν i * (2 * inner ℝ c_Δ (Q i)) := by
          rw [inner_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro i _; rw [inner_smul_right]; ring
        _ = ∑ i, ν i * (r + ‖c_Δ‖ ^ 2 - τ) := by simp_rw [hrow]
        _ = r + ‖c_Δ‖ ^ 2 - τ := by rw [← Finset.sum_mul, hνsum, one_mul]
    refine ⟨by linarith, fun i => ?_⟩
    rw [inner_sub_right, real_inner_self_eq_norm_sq]
    linarith [hrow i]
  have hτ_pos : 0 < τ := by linarith
  obtain ⟨s, hs_pos, hs_sq⟩ : ∃ s : ℝ, 0 < s ∧ s ^ 2 = τ :=
    ⟨Real.sqrt τ, Real.sqrt_pos.mpr hτ_pos, Real.sq_sqrt hτ_pos.le⟩
  obtain ⟨h, hh_def⟩ : ∃ h : ℝ, h = ‖c_Δ‖ := ⟨‖c_Δ‖, rfl⟩
  have hh_nn : 0 ≤ h := by rw [hh_def]; exact norm_nonneg _
  have hsh_r : s ^ 2 + h ^ 2 = r := by rw [hh_def, hs_sq]; exact hPyth.1
  -- Build e0, e1 and coordinates x2, y2, x3, y3 opaquely!
  obtain ⟨e0, e1, x2, y2, x3, y3, he0_unit, he1_unit, he01_orth, hy2_pos, hy3_neg,
          hv0_eq, hv1_eq, hv2_eq, he0_orth_c, he1_orth_c⟩ :
      ∃ (e0 e1 : E4) (x2 y2 x3 y3 : ℝ),
        ‖e0‖ = 1 ∧ ‖e1‖ = 1 ∧ inner ℝ e0 e1 = 0 ∧ 0 < y2 ∧ y3 < 0 ∧
        Q 0 - c_Δ = s • e0 ∧
        Q 1 - c_Δ = x2 • e0 + y2 • e1 ∧
        Q 2 - c_Δ = x3 • e0 + y3 • e1 ∧
        inner ℝ e0 c_Δ = 0 ∧ inner ℝ e1 c_Δ = 0 := by
    let v0 := Q 0 - c_Δ
    let v1 := Q 1 - c_Δ
    let v2 := Q 2 - c_Δ
    have hv0_norm : ‖v0‖ = s :=
      (sq_eq_sq₀ (norm_nonneg v0) hs_pos.le).mp (by rw [hs_sq]; exact hQτ 0)
    let e0 : E4 := s⁻¹ • v0
    have he0_unit : ‖e0‖ = 1 := by
      simp [e0, norm_smul, Real.norm_eq_abs, abs_of_pos hs_pos, hv0_norm, hs_pos.ne']
    have hv0_eq : v0 = s • e0 := by simp [e0, smul_smul, hs_pos.ne']
    let x2 : ℝ := inner ℝ e0 v1
    let u1 : E4 := v1 - x2 • e0
    have hu1_orth : inner ℝ e0 u1 = 0 := by
      simp [u1, inner_sub_right, inner_smul_right, he0_unit, x2]
    have hv_bary : ν 0 • v0 + ν 1 • v1 + ν 2 • v2 = 0 := by
      have : ∑ i : Fin 3, ν i • (Q i - c_Δ) = (∑ i, ν i • Q i) - (∑ i, ν i) • c_Δ := by
        simp [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
      rw [hνbary, hνsum, one_smul, sub_self] at this
      simpa [Fin.sum_univ_three, v0, v1, v2] using this
    have hu1_ne : u1 ≠ 0 := by
      intro hu0
      let α1 := x2 / s
      have hv1_col : v1 = α1 • v0 := by
        calc
          v1 = x2 • e0 := sub_eq_zero.mp hu0
          _ = (x2 * s⁻¹) • v0 := by simp [e0, smul_smul]
          _ = α1 • v0 := by dsimp [α1]; rw [div_eq_mul_inv]
      let α2 := -(ν 0 + ν 1 * α1) / ν 2
      have hv2_col : v2 = α2 • v0 := by
        have hν2 : ν 2 ≠ 0 := (hνpos 2).ne'
        have hsub : ν 2 • v2 = -(ν 0 + ν 1 * α1) • v0 := by
          rw [hv1_col] at hv_bary
          calc
            ν 2 • v2 = -(ν 0 • v0 + ν 1 • (α1 • v0)) := eq_neg_of_add_eq_zero_right hv_bary
            _ = -(ν 0 + ν 1 * α1) • v0 := by rw [smul_smul, ← add_smul, ← neg_smul]
        calc
          v2 = (ν 2)⁻¹ • (ν 2 • v2) := by rw [inv_smul_smul₀ hν2]
          _ = α2 • v0 := by rw [hsub, smul_smul]; congr 1; dsimp [α2]; field_simp
      let c1 := α2 - 1
      let c2 := -(α1 - 1)
      let c0 := -c1 - c2
      let wt : Fin 3 → ℝ := ![c0, c1, c2]
      have hwt_sum : ∑ i ∈ Finset.univ, wt i = 0 := by simp [Fin.sum_univ_three, wt, c0]; ring
      have hwt_vsub : Finset.univ.weightedVSub Q wt = 0 := by
        rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ hwt_sum c_Δ]
        simp only [Finset.weightedVSubOfPoint_apply, vsub_eq_sub, Fin.sum_univ_three, wt]
        change c0 • v0 + c1 • v1 + c2 • v2 = 0
        rw [hv1_col, hv2_col, smul_smul, smul_smul, ← add_smul, ← add_smul]
        have : c0 + c1 * α1 + c2 * α2 = 0 := by dsimp [c0, c1, c2]; ring
        rw [this, zero_smul]
      have hwt0 := hQaff Finset.univ wt hwt_sum hwt_vsub
      have hc2_0 : c2 = 0 := by simpa [wt] using hwt0 2 (Finset.mem_univ 2)
      have hα1 : α1 = 1 := by dsimp [c2] at hc2_0; linarith
      have hQ10 : Q 1 = Q 0 := by
        have : v1 = v0 := by rw [hv1_col, hα1, one_smul]
        exact sub_left_inj.mp this
      exact absurd (hQaff.injective hQ10) (by decide)
    let y2 : ℝ := ‖u1‖
    have hy2_pos : 0 < y2 := norm_pos_iff.mpr hu1_ne
    let e1 : E4 := y2⁻¹ • u1
    have he1_unit : ‖e1‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hy2_pos), inv_mul_cancel₀ hy2_pos.ne']
    have he01_orth : inner ℝ e0 e1 = 0 := by simp [e1, inner_smul_right, hu1_orth]
    have hv1_eq : v1 = x2 • e0 + y2 • e1 := by
      have : u1 = y2 • e1 := by simp [e1, smul_smul, hy2_pos.ne']
      exact eq_add_of_sub_eq' this
    let x3 : ℝ := -(ν 0 * s + ν 1 * x2) / ν 2
    let y3 : ℝ := -(ν 1 * y2) / ν 2
    have hv2_eq : v2 = x3 • e0 + y3 • e1 := by
      have hν2 : ν 2 ≠ 0 := (hνpos 2).ne'
      have hsub : ν 2 • v2 = -(ν 0 * s + ν 1 * x2) • e0 + (-(ν 1 * y2)) • e1 := by
        calc
          ν 2 • v2 = -(ν 0 • v0 + ν 1 • v1) := eq_neg_of_add_eq_zero_right hv_bary
          _ = -(ν 0 • (s • e0) + ν 1 • (x2 • e0 + y2 • e1)) := by rw [hv0_eq, hv1_eq]
          _ = _ := by rw [smul_add, smul_smul, smul_smul, smul_smul]; module
      calc
        v2 = (ν 2)⁻¹ • (ν 2 • v2) := by rw [inv_smul_smul₀ hν2]
        _ = _ := by
          have hx3_eq : (ν 2)⁻¹ * -(ν 0 * s + ν 1 * x2) = x3 := by dsimp [x3]; field_simp
          have hy3_eq : (ν 2)⁻¹ * -(ν 1 * y2) = y3 := by dsimp [y3]; field_simp
          rw [hsub, smul_add, smul_smul (ν 2)⁻¹, smul_smul (ν 2)⁻¹, hx3_eq, hy3_eq]
    have hy3_neg : y3 < 0 :=
      div_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos (hνpos 1) hy2_pos)) (hνpos 2)
    have hv_orth (i : Fin 3) : inner ℝ (Q i - c_Δ) c_Δ = 0 := by
      rw [real_inner_comm, hPyth.2 i]
    have he0_orth_c : inner ℝ e0 c_Δ = 0 := by
      rw [show e0 = s⁻¹ • (Q 0 - c_Δ) from rfl, real_inner_smul_left, hv_orth 0, mul_zero]
    have he1_orth_c : inner ℝ e1 c_Δ = 0 := by
      rw [show e1 = y2⁻¹ • ((Q 1 - c_Δ) - x2 • e0) from rfl,
        real_inner_smul_left, inner_sub_left, real_inner_smul_left, hv_orth 1, he0_orth_c]
      ring
    exact ⟨e0, e1, x2, y2, x3, y3, he0_unit, he1_unit, he01_orth, hy2_pos, hy3_neg,
      hv0_eq, hv1_eq, hv2_eq, he0_orth_c, he1_orth_c⟩
  have he0_self : inner ℝ e0 e0 = 1 := by rw [real_inner_self_eq_norm_sq, he0_unit]; norm_num
  have he1_self : inner ℝ e1 e1 = 1 := by rw [real_inner_self_eq_norm_sq, he1_unit]; norm_num
  have he10_orth : inner ℝ e1 e0 = 0 := by rw [real_inner_comm, he01_orth]
  have hy2_sq : y2 ^ 2 = s ^ 2 - x2 ^ 2 := by
    have hn1 : ‖Q 1 - c_Δ‖ ^ 2 = s ^ 2 := by rw [hs_sq]; exact hQτ 1
    rw [hv1_eq, norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      he0_unit, he1_unit, mul_one, mul_one, sq_abs, sq_abs, inner_smul_left, inner_smul_right,
      he01_orth] at hn1
    linarith
  have hy3_sq : y3 ^ 2 = s ^ 2 - x3 ^ 2 := by
    have hn2 : ‖Q 2 - c_Δ‖ ^ 2 = s ^ 2 := by rw [hs_sq]; exact hQτ 2
    rw [hv2_eq, norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      he0_unit, he1_unit, mul_one, mul_one, sq_abs, sq_abs, inner_smul_left, inner_smul_right,
      he01_orth] at hn2
    linarith
  have hdist01 : dist (Q 0) (Q 1) ^ 2 = 2 * s ^ 2 - 2 * s * x2 := by
    have hsub : Q 0 - Q 1 = (Q 0 - c_Δ) - (Q 1 - c_Δ) := by abel
    rw [dist_eq_norm, hsub, norm_sub_sq_real, hQτ 0, hQτ 1, ← hs_sq]
    have hin : inner ℝ (Q 0 - c_Δ) (Q 1 - c_Δ) = s * x2 := by
      rw [hv0_eq, hv1_eq, inner_add_right, real_inner_smul_left, real_inner_smul_left,
        real_inner_smul_right, real_inner_smul_right, he0_self, he01_orth]
      ring
    linarith
  have hdist02 : dist (Q 0) (Q 2) ^ 2 = 2 * s ^ 2 - 2 * s * x3 := by
    have hsub : Q 0 - Q 2 = (Q 0 - c_Δ) - (Q 2 - c_Δ) := by abel
    rw [dist_eq_norm, hsub, norm_sub_sq_real, hQτ 0, hQτ 2, ← hs_sq]
    have hin : inner ℝ (Q 0 - c_Δ) (Q 2 - c_Δ) = s * x3 := by
      rw [hv0_eq, hv2_eq, inner_add_right, real_inner_smul_left, real_inner_smul_left,
        real_inner_smul_right, real_inner_smul_right, he0_self, he01_orth]
      ring
    linarith
  have hdist12 : dist (Q 1) (Q 2) ^ 2 = 2 * s ^ 2 - 2 * (x2 * x3 + y2 * y3) := by
    have hsub : Q 1 - Q 2 = (Q 1 - c_Δ) - (Q 2 - c_Δ) := by abel
    rw [dist_eq_norm, hsub, norm_sub_sq_real, hQτ 1, hQτ 2, ← hs_sq]
    have hin : inner ℝ (Q 1 - c_Δ) (Q 2 - c_Δ) = x2 * x3 + y2 * y3 := by
      rw [hv1_eq, hv2_eq, inner_add_left, inner_add_right, inner_add_right]
      simp [inner_smul_left, inner_smul_right, he0_unit, he1_unit, he01_orth, he10_orth]
      ring
    linarith
  have hside1 : 2 * s ^ 2 - 1 ≤ 2 * s * x2 := by
    have hsq : dist (Q 0) (Q 1) ^ 2 ≤ 1 := pow_le_one₀ dist_nonneg (hQdiam 0 1)
    linarith
  have hx2_le_x3 : x2 ≤ x3 := by
    have hsq : dist (Q 0) (Q 2) ^ 2 ≤ dist (Q 0) (Q 1) ^ 2 := pow_le_pow_left₀ dist_nonneg hd02 2
    exact le_of_mul_le_mul_left (by linarith : s * x2 ≤ s * x3) hs_pos
  have hx2_lt_s : x2 < s := by
    have h1 : x2 ^ 2 < s ^ 2 := by linarith [sq_pos_of_pos hy2_pos]
    exact lt_of_abs_lt ((sq_lt_sq.mp h1).trans_le (le_of_eq (abs_of_pos hs_pos)))
  have hs_sub_x2 : 0 < s - x2 := sub_pos.mpr hx2_lt_s
  have hx3_neg : x3 ≤ 0 := by
    have hsq : dist (Q 1) (Q 2) ^ 2 ≤ dist (Q 0) (Q 2) ^ 2 := pow_le_pow_left₀ dist_nonneg hd12 2
    have h1 : (s - x2) * x3 ≤ y2 * y3 := by rw [sub_mul]; linarith
    have hyy : y2 * y3 < 0 := mul_neg_of_pos_of_neg hy2_pos hy3_neg
    exact (neg_of_mul_neg_right (h1.trans_lt hyy) hs_sub_x2.le).le
  have hside23 : s * (s + x2) ≤ 2 * x3 ^ 2 := by
    have hsq : dist (Q 1) (Q 2) ^ 2 ≤ dist (Q 0) (Q 2) ^ 2 := pow_le_pow_left₀ dist_nonneg hd12 2
    have h1 : 0 ≤ -y2 * y3 := by
      rw [neg_mul]; exact neg_nonneg.mpr (mul_neg_of_pos_of_neg hy2_pos hy3_neg).le
    have h2 : -y2 * y3 ≤ (s - x2) * (-x3) := by
      have : (s - x2) * (-x3) = -(s * x3 - x2 * x3) := by ring
      linarith
    have h3 : (-y2 * y3) ^ 2 ≤ ((s - x2) * (-x3)) ^ 2 := pow_le_pow_left₀ h1 h2 2
    have h4 : (s - x2) * ((s + x2) * (s ^ 2 - x3 ^ 2)) ≤ (s - x2) * ((s - x2) * x3 ^ 2) := by
      calc
        (s - x2) * ((s + x2) * (s ^ 2 - x3 ^ 2)) = y2 ^ 2 * y3 ^ 2 := by rw [hy2_sq, hy3_sq]; ring
        _ = (-y2 * y3) ^ 2 := by ring
        _ ≤ ((s - x2) * (-x3)) ^ 2 := h3
        _ = (s - x2) * ((s - x2) * x3 ^ 2) := by ring
    have h5 : (s + x2) * (s ^ 2 - x3 ^ 2) ≤ (s - x2) * x3 ^ 2 :=
      le_of_mul_le_mul_left h4 hs_sub_x2
    have h6 : s * (s * (s + x2)) ≤ s * (2 * x3 ^ 2) := by
      have : s * (2 * x3 ^ 2) - s * (s * (s + x2)) =
        (s - x2) * x3 ^ 2 - (s + x2) * (s ^ 2 - x3 ^ 2) := by ring
      linarith
    exact le_of_mul_le_mul_left h6 hs_pos
  obtain ⟨b, hb0, hb1, hbc⟩ : ∃ b : OrthonormalBasis (Fin 4) ℝ E4,
      b 0 = e0 ∧ b 1 = e1 ∧ c_Δ = h • b 2 := by
    by_cases hc0 : c_Δ = 0
    · have hh0 : h = 0 := by rw [hh_def, hc0, norm_zero]
      let S_idx : Set (Fin 4) := {0, 1}
      let vec : Fin 4 → E4 := ![e0, e1, 0, 0]
      have horth : Orthonormal ℝ (S_idx.domRestrict vec) := by
        rw [orthonormal_iff_ite]
        rintro ⟨i, hi⟩ ⟨j, hj⟩
        rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
          simp [Set.domRestrict, vec, Subtype.ext_iff, he0_unit, he1_unit, he01_orth, he10_orth]
      obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq
        (show Module.finrank ℝ E4 = Fintype.card (Fin 4) by simp)
      refine ⟨b, hb 0 (by simp [S_idx]), hb 1 (by simp [S_idx]), ?_⟩
      rw [hc0, hh0, zero_smul]
    · have hh_pos : 0 < h := by rw [hh_def]; exact norm_pos_iff.mpr hc0
      let e2 : E4 := h⁻¹ • c_Δ
      have he2_unit : ‖e2‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hh_pos), ← hh_def,
          inv_mul_cancel₀ hh_pos.ne']
      have he02 : inner ℝ e0 e2 = 0 := by simp [e2, inner_smul_right, he0_orth_c]
      have he20 : inner ℝ e2 e0 = 0 := by rw [real_inner_comm, he02]
      have he12 : inner ℝ e1 e2 = 0 := by simp [e2, inner_smul_right, he1_orth_c]
      have he21 : inner ℝ e2 e1 = 0 := by rw [real_inner_comm, he12]
      let S_idx : Set (Fin 4) := {0, 1, 2}
      let vec : Fin 4 → E4 := ![e0, e1, e2, 0]
      have horth : Orthonormal ℝ (S_idx.domRestrict vec) := by
        rw [orthonormal_iff_ite]
        rintro ⟨i, hi⟩ ⟨j, hj⟩
        rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
          simp [Set.domRestrict, vec, Subtype.ext_iff, he0_unit, he1_unit, he2_unit,
            he01_orth, he10_orth, he02, he20, he12, he21]
      obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq
        (show Module.finrank ℝ E4 = Fintype.card (Fin 4) by simp)
      refine ⟨b, hb 0 (by simp [S_idx]), hb 1 (by simp [S_idx]), ?_⟩
      rw [hb 2 (by simp [S_idx])]
      simp [vec, e2, smul_smul, hh_pos.ne']
  have hQ0 : Q 0 = s • b 0 + h • b 2 := by
    calc Q 0 = (Q 0 - c_Δ) + c_Δ := by abel
      _ = s • b 0 + h • b 2 := by rw [hv0_eq, hb0, hbc]
  have hQ1 : Q 1 = x2 • b 0 + y2 • b 1 + h • b 2 := by
    calc Q 1 = (Q 1 - c_Δ) + c_Δ := by abel
      _ = x2 • b 0 + y2 • b 1 + h • b 2 := by rw [hv1_eq, hb0, hb1, hbc]
  have hQ2 : Q 2 = x3 • b 0 + y3 • b 1 + h • b 2 := by
    calc Q 2 = (Q 2 - c_Δ) + c_Δ := by abel
      _ = x3 • b 0 + y3 • b 1 + h • b 2 := by rw [hv2_eq, hb0, hb1, hbc]
  have hrepr0 (j : Fin 4) : b.repr (Q 0) j = if j = 0 then s else if j = 2 then h else 0 := by
    rw [hQ0, map_add, map_smul, map_smul, b.repr_self, b.repr_self]
    fin_cases j <;> simp
  have hrepr1 (j : Fin 4) : b.repr (Q 1) j = if j = 0 then x2 else if j = 1 then y2 else if j = 2 then h else 0 := by
    rw [hQ1, map_add, map_add, map_smul, map_smul, map_smul, b.repr_self, b.repr_self, b.repr_self]
    fin_cases j <;> simp
  have hrepr2 (j : Fin 4) : b.repr (Q 2) j = if j = 0 then x3 else if j = 1 then y3 else if j = 2 then h else 0 := by
    rw [hQ2, map_add, map_add, map_smul, map_smul, map_smul, b.repr_self, b.repr_self, b.repr_self]
    fin_cases j <;> simp
  refine ⟨b, σ, s, h, x2, y2, x3, y3, hs_pos, hh_nn, hsh_r,
    by linarith [hs_sq, hsh_r, hτlo], by linarith [hs_sq, hτhi],
    hside1, hx2_le_x3, hx3_neg, hside23,
    hy2_pos.le, hy2_sq, hy3_neg.le, hy3_sq, ?_⟩
  rw [hQ_apply 0] at hrepr0
  rw [hQ_apply 1] at hrepr1
  rw [hQ_apply 2] at hrepr2
  refine ⟨by simpa using hrepr0 0, by simpa using hrepr0 1, by simpa using hrepr0 2, by simpa using hrepr0 3,
          by simpa using hrepr1 0, by simpa using hrepr1 1, by simpa using hrepr1 2, by simpa using hrepr1 3,
          by simpa using hrepr2 0, by simpa using hrepr2 1, by simpa using hrepr2 2, by simpa using hrepr2 3⟩


structure SInt where
  p : Nat
  n : Nat

def sNorm (x : SInt) : SInt :=
  match Nat.ble x.n x.p with
  | true  => ⟨Nat.sub x.p x.n, 0⟩
  | false => ⟨0, Nat.sub x.n x.p⟩

def sAdd (x y : SInt) : SInt := ⟨Nat.add x.p y.p, Nat.add x.n y.n⟩
def sSub (x y : SInt) : SInt := ⟨Nat.add x.p y.n, Nat.add x.n y.p⟩
def sNeg (x : SInt) : SInt := ⟨x.n, x.p⟩
def sMul (x y : SInt) : SInt :=
  sNorm ⟨Nat.add (Nat.mul x.p y.p) (Nat.mul x.n y.n),
         Nat.add (Nat.mul x.p y.n) (Nat.mul x.n y.p)⟩

def sLt (x y : SInt) : Bool :=
  Nat.ble (Nat.add (Nat.add x.p y.n) 1) (Nat.add y.p x.n)

def sEq (x y : SInt) : Bool :=
  Bool.and (Nat.ble (Nat.add x.p y.n) (Nat.add y.p x.n))
           (Nat.ble (Nat.add y.p x.n) (Nat.add x.p y.n))

def ofInt (z : Int) : SInt :=
  match z with
  | Int.ofNat m   => ⟨m, 0⟩
  | Int.negSucc m => ⟨0, Nat.add m 1⟩

def toR (x : SInt) : ℝ := (x.p : ℝ) - (x.n : ℝ)

@[simp] lemma toR_sNorm (x : SInt) : toR (sNorm x) = toR x := by
  unfold sNorm toR
  cases h : Nat.ble x.n x.p
  · have hle : ¬ x.n ≤ x.p := by rw [← Nat.ble_eq]; simp [h]
    have hlt : x.p ≤ x.n := by omega
    simp [Nat.cast_sub hlt]
  · have hle : x.n ≤ x.p := by rw [← Nat.ble_eq]; exact h
    simp [Nat.cast_sub hle]

@[simp] lemma toR_sAdd (x y : SInt) : toR (sAdd x y) = toR x + toR y := by
  unfold sAdd toR; simp [Nat.add_eq]; ring

@[simp] lemma toR_sSub (x y : SInt) : toR (sSub x y) = toR x - toR y := by
  unfold sSub toR; simp [Nat.add_eq]; ring

@[simp] lemma toR_sNeg (x : SInt) : toR (sNeg x) = -toR x := by
  unfold sNeg toR; ring

@[simp] lemma toR_sMul (x y : SInt) : toR (sMul x y) = toR x * toR y := by
  unfold sMul; rw [toR_sNorm]; unfold toR; simp [Nat.add_eq, Nat.mul_eq]; ring

@[simp] lemma toR_zero : toR ⟨0, 0⟩ = 0 := by unfold toR; ring

@[simp] lemma toR_ofInt (z : Int) : toR (ofInt z) = (z : ℝ) := by
  cases z with
  | ofNat m => simp [ofInt, toR]
  | negSucc m => simp [ofInt, toR, Nat.add_eq]

lemma sLt_iff (x y : SInt) : sLt x y = true ↔ toR x < toR y := by
  unfold sLt toR
  rw [Nat.ble_eq]
  simp only [Nat.add_eq]
  constructor
  · intro h
    have hr : ((x.p + y.n + 1 : ℕ) : ℝ) ≤ ((y.p + x.n : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at hr; linarith
  · intro h
    have hr : (((x.p : ℤ) - (x.n : ℤ) : ℤ) : ℝ) < (((y.p : ℤ) - (y.n : ℤ) : ℤ) : ℝ) := by
      push_cast; exact h
    have hz : (x.p : ℤ) - (x.n : ℤ) < (y.p : ℤ) - (y.n : ℤ) := by exact_mod_cast hr
    omega

lemma sLt_false_iff (x y : SInt) : sLt x y = false ↔ toR y ≤ toR x := by
  rw [← Bool.not_eq_true, sLt_iff, not_lt]

lemma sEq_iff (x y : SInt) : sEq x y = true ↔ toR x = toR y := by
  unfold sEq toR
  rw [Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq]
  simp only [Nat.add_eq]
  constructor
  · rintro ⟨h1, h2⟩
    have hr1 : ((x.p + y.n : ℕ) : ℝ) ≤ ((y.p + x.n : ℕ) : ℝ) := by exact_mod_cast h1
    have hr2 : ((y.p + x.n : ℕ) : ℝ) ≤ ((x.p + y.n : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at hr1 hr2; linarith
  · intro h
    have hr : (((x.p : ℤ) - (x.n : ℤ) : ℤ) : ℝ) = (((y.p : ℤ) - (y.n : ℤ) : ℤ) : ℝ) := by
      push_cast; exact h
    have hz : (x.p : ℤ) - (x.n : ℤ) = (y.p : ℤ) - (y.n : ℤ) := by exact_mod_cast hr
    omega

structure Row5S where
  a0 : SInt
  a1 : SInt
  a2 : SInt
  a3 : SInt
  a4 : Bool
  d  : SInt

structure Row4S where
  a0 : SInt
  a1 : SInt
  a2 : SInt
  a3 : SInt
  d  : SInt

structure Sol4S where
  den : SInt
  n0  : SInt
  n1  : SInt
  n2  : SInt
  n3  : SInt

def det2S (a b c d : SInt) : SInt := sNorm (sSub (sMul a d) (sMul b c))

def lin6S (p0 q0 p1 q1 p2 q2 p3 q3 p4 q4 p5 q5 : SInt) : SInt :=
  sNorm (sAdd
    (sAdd (sSub (sMul p0 q0) (sMul p1 q1)) (sAdd (sMul p2 q2) (sMul p3 q3)))
    (sSub (sMul p5 q5) (sMul p4 q4)))

def solve4Raw (u0 u1 u2 u3 : Row4S) : Sol4S :=
  let p01 := det2S u0.a0 u0.a1 u1.a0 u1.a1
  let p02 := det2S u0.a0 u0.a2 u1.a0 u1.a2
  let p03 := det2S u0.a0 u0.a3 u1.a0 u1.a3
  let p12 := det2S u0.a1 u0.a2 u1.a1 u1.a2
  let p13 := det2S u0.a1 u0.a3 u1.a1 u1.a3
  let p23 := det2S u0.a2 u0.a3 u1.a2 u1.a3
  let q01 := det2S u2.a0 u2.a1 u3.a0 u3.a1
  let q02 := det2S u2.a0 u2.a2 u3.a0 u3.a2
  let q03 := det2S u2.a0 u2.a3 u3.a0 u3.a3
  let q12 := det2S u2.a1 u2.a2 u3.a1 u3.a2
  let q13 := det2S u2.a1 u2.a3 u3.a1 u3.a3
  let q23 := det2S u2.a2 u2.a3 u3.a2 u3.a3
  let det := lin6S p01 q23 p02 q13 p03 q12 p12 q03 p13 q02 p23 q01
  let p04 := det2S u0.a0 u0.d u1.a0 u1.d
  let p14 := det2S u0.a1 u0.d u1.a1 u1.d
  let p24 := det2S u0.a2 u0.d u1.a2 u1.d
  let p34 := det2S u0.a3 u0.d u1.a3 u1.d
  let q04 := det2S u2.a0 u2.d u3.a0 u3.d
  let q14 := det2S u2.a1 u2.d u3.a1 u3.d
  let q24 := det2S u2.a2 u2.d u3.a2 u3.d
  let q34 := det2S u2.a3 u2.d u3.a3 u3.d
  let n0 := sNeg (lin6S p12 q34 p13 q24 p14 q23 p23 q14 p24 q13 p34 q12)
  let n1 :=       lin6S p02 q34 p03 q24 p04 q23 p23 q04 p24 q03 p34 q02
  let n2 := sNeg (lin6S p01 q34 p03 q14 p04 q13 p13 q04 p14 q03 p34 q01)
  let n3 :=       lin6S p01 q24 p02 q14 p04 q12 p12 q04 p14 q02 p24 q01
  ⟨det, n0, n1, n2, n3⟩

def solve4S (u0 u1 u2 u3 : Row4S) : Sol4S :=
  let s := solve4Raw u0 u1 u2 u3
  match sLt s.den ⟨0, 0⟩ with
  | true  => ⟨sNeg s.den, sNeg s.n0, sNeg s.n1, sNeg s.n2, sNeg s.n3⟩
  | false => s

def evalRow4S (a0 a1 a2 a3 n0 n1 n2 n3 : SInt) : SInt :=
  sNorm (sAdd (sAdd (sMul a0 n0) (sMul a1 n1)) (sAdd (sMul a2 n2) (sMul a3 n3)))

def anyViolatedS : List Row5S → SInt → SInt → SInt → SInt → SInt → SInt → Bool
  | [], _, _, _, _, _, _ => false
  | r :: rs, den, n0, n1, n2, n3, n4 =>
    let dot4 := evalRow4S r.a0 r.a1 r.a2 r.a3 n0 n1 n2 n3
    let lhs := match r.a4 with | true => sAdd dot4 n4 | false => sSub dot4 n4
    match sLt (sMul r.d den) lhs with
    | true  => true
    | false => anyViolatedS rs den n0 n1 n2 n3 n4

def norm2S (n0 n1 n2 n3 : SInt) : SInt :=
  sAdd (sAdd (sMul n0 n0) (sMul n1 n1)) (sAdd (sMul n2 n2) (sMul n3 n3))

def toRow4ZeroS (r : Row5S) : Row4S := ⟨r.a0, r.a1, r.a2, r.a3, r.d⟩
def toRow4TopS (r_hi : SInt) (r : Row5S) : Row4S :=
  ⟨r.a0, r.a1, r.a2, r.a3, sNorm (match r.a4 with | true => sSub r.d r_hi | false => sAdd r.d r_hi)⟩

def elimRow4S (p r : Row5S) : Row4S :=
  match r.a4 == p.a4 with
  | true  => ⟨sNorm (sSub r.a0 p.a0), sNorm (sSub r.a1 p.a1), sNorm (sSub r.a2 p.a2), sNorm (sSub r.a3 p.a3), sNorm (sSub r.d p.d)⟩
  | false => ⟨sNorm (sAdd r.a0 p.a0), sNorm (sAdd r.a1 p.a1), sNorm (sAdd r.a2 p.a2), sNorm (sAdd r.a3 p.a3), sNorm (sAdd r.d p.d)⟩

def checkSolZS (rem : List Row5S) : Sol4S → Bool
  | ⟨den, n0, n1, n2, n3⟩ =>
    match sLt ⟨0, 0⟩ den with
    | false => false
    | true  => anyViolatedS rem den n0 n1 n2 n3 ⟨0, 0⟩

def checkSolTS (r_hi : SInt) (rem : List Row5S) : Sol4S → Bool
  | ⟨den, n0, n1, n2, n3⟩ =>
    match sLt ⟨0, 0⟩ den with
    | false => false
    | true  =>
      let n4 := sMul r_hi den
      match sLt (norm2S n0 n1 n2 n3) (sMul n4 den) with
      | true  => true
      | false => anyViolatedS rem den n0 n1 n2 n3 n4

def checkSolMS (r_hi : SInt) (mids : List Row5S) (p : Row5S) : Sol4S → Bool
  | ⟨den, n0, n1, n2, n3⟩ =>
    match sLt ⟨0, 0⟩ den with
    | false => false
    | true  =>
      let diff := sSub (sMul p.d den) (evalRow4S p.a0 p.a1 p.a2 p.a3 n0 n1 n2 n3)
      let n4 := sNorm (match p.a4 with | true => diff | false => sNeg diff)
      match sLt n4 ⟨0, 0⟩ with
      | true  => true
      | false =>
        match sLt (sMul r_hi den) n4 with
        | true  => true
        | false =>
          match sLt (norm2S n0 n1 n2 n3) (sMul n4 den) with
          | true  => true
          | false => anyViolatedS mids den n0 n1 n2 n3 n4

def ch1Z (rem : List Row5S) (u0 u1 u2 : Row4S) : List Row4S → Bool
  | [] => true | u3 :: us => Bool.and (checkSolZS rem (solve4S u0 u1 u2 u3)) (ch1Z rem u0 u1 u2 us)
def ch2Z (rem : List Row5S) (u0 u1 : Row4S) : List Row4S → Bool
  | [] => true | u2 :: us => Bool.and (ch1Z rem u0 u1 u2 us) (ch2Z rem u0 u1 us)
def ch3Z (rem : List Row5S) (u0 : Row4S) : List Row4S → Bool
  | [] => true | u1 :: us => Bool.and (ch2Z rem u0 u1 us) (ch3Z rem u0 us)
def ch4Z (rem : List Row5S) : List Row4S → Bool
  | [] => true | u0 :: us => Bool.and (ch3Z rem u0 us) (ch4Z rem us)

def ch1T (r_hi : SInt) (rem : List Row5S) (u0 u1 u2 : Row4S) : List Row4S → Bool
  | [] => true | u3 :: us => Bool.and (checkSolTS r_hi rem (solve4S u0 u1 u2 u3)) (ch1T r_hi rem u0 u1 u2 us)
def ch2T (r_hi : SInt) (rem : List Row5S) (u0 u1 : Row4S) : List Row4S → Bool
  | [] => true | u2 :: us => Bool.and (ch1T r_hi rem u0 u1 u2 us) (ch2T r_hi rem u0 u1 us)
def ch3T (r_hi : SInt) (rem : List Row5S) (u0 : Row4S) : List Row4S → Bool
  | [] => true | u1 :: us => Bool.and (ch2T r_hi rem u0 u1 us) (ch3T r_hi rem u0 us)
def ch4T (r_hi : SInt) (rem : List Row5S) : List Row4S → Bool
  | [] => true | u0 :: us => Bool.and (ch3T r_hi rem u0 us) (ch4T r_hi rem us)

def ch1M (r_hi : SInt) (mids : List Row5S) (p r1 r2 r3 : Row5S) : List Row5S → Bool
  | [] => true | r4 :: rs => Bool.and (checkSolMS r_hi mids p (solve4S (elimRow4S p r1) (elimRow4S p r2) (elimRow4S p r3) (elimRow4S p r4))) (ch1M r_hi mids p r1 r2 r3 rs)
def ch2M (r_hi : SInt) (mids : List Row5S) (p r1 r2 : Row5S) : List Row5S → Bool
  | [] => true | r3 :: rs => Bool.and (ch1M r_hi mids p r1 r2 r3 rs) (ch2M r_hi mids p r1 r2 rs)
def ch3M (r_hi : SInt) (mids : List Row5S) (p r1 : Row5S) : List Row5S → Bool
  | [] => true | r2 :: rs => Bool.and (ch2M r_hi mids p r1 r2 rs) (ch3M r_hi mids p r1 rs)
def ch4M (r_hi : SInt) (mids : List Row5S) (p : Row5S) : List Row5S → Bool
  | [] => true | r1 :: rs => Bool.and (ch3M r_hi mids p r1 rs) (ch4M r_hi mids p rs)
def ch5M (r_hi : SInt) (mids : List Row5S) : List Row5S → Bool
  | [] => true | p :: rs => Bool.and (ch4M r_hi mids p rs) (ch5M r_hi mids rs)

def mkRowAS (a : Int × Int × Int × Int) (b : Int) : Row5S :=
  ⟨ofInt (-2*a.1), ofInt (-2*a.2.1), ofInt (-2*a.2.2.1), ofInt (-2*a.2.2.2), true, ofInt b⟩

def mkRowCS (c : Int × Int × Int × Int) : Row5S :=
  let (x0, x1, x2, x3) := c
  ⟨ofInt (2*x0), ofInt (2*x1), ofInt (2*x2), ofInt (2*x3), false, ofInt (x0*x0 + x1*x1 + x2*x2 + x3*x3 - 998001)⟩

def pickC (c0 c1 c2 c3 c4 c5 c6 c7 : Int × Int × Int × Int) : Nat → Int × Int × Int × Int
  | 0 => c0 | 1 => c1 | 2 => c2 | 3 => c3 | 4 => c4 | 5 => c5 | 6 => c6 | _ => c7

def mkHomRow4 (c : Int × Int × Int × Int) : Row4S :=
  ⟨ofInt c.1, ofInt c.2.1, ofInt c.2.2.1, ofInt c.2.2.2, ⟨0, 0⟩⟩

def lin5S (w0 p0 w1 p1 w2 p2 w3 p3 w4 p4 : SInt) : SInt :=
  sAdd (sAdd (sAdd (sMul w0 p0) (sMul w1 p1)) (sAdd (sMul w2 p2) (sMul w3 p3))) (sMul w4 p4)

def checkSimplex (c0 c1 c2 c3 c4 c5 c6 c7 : Int × Int × Int × Int)
    (si0 si1 si2 si3 si4 : Nat) (sw0 sw1 sw2 sw3 sw4 : Int) : Bool :=
  let p0 := pickC c0 c1 c2 c3 c4 c5 c6 c7 si0
  let p1 := pickC c0 c1 c2 c3 c4 c5 c6 c7 si1
  let p2 := pickC c0 c1 c2 c3 c4 c5 c6 c7 si2
  let p3 := pickC c0 c1 c2 c3 c4 c5 c6 c7 si3
  let p4 := pickC c0 c1 c2 c3 c4 c5 c6 c7 si4
  let w0 := ofInt sw0; let w1 := ofInt sw1; let w2 := ofInt sw2; let w3 := ofInt sw3; let w4 := ofInt sw4
  Bool.and (Nat.ble (Nat.add si0 1) 8)
  (Bool.and (Nat.ble (Nat.add si1 1) 8)
  (Bool.and (Nat.ble (Nat.add si2 1) 8)
  (Bool.and (Nat.ble (Nat.add si3 1) 8)
  (Bool.and (Nat.ble (Nat.add si4 1) 8)
  (Bool.and (sLt ⟨0, 0⟩ w0)
  (Bool.and (sLt ⟨0, 0⟩ w1)
  (Bool.and (sLt ⟨0, 0⟩ w2)
  (Bool.and (sLt ⟨0, 0⟩ w3)
  (Bool.and (sLt ⟨0, 0⟩ w4)
  (Bool.and (sEq (lin5S w0 (ofInt p0.1) w1 (ofInt p1.1) w2 (ofInt p2.1) w3 (ofInt p3.1) w4 (ofInt p4.1)) ⟨0, 0⟩)
  (Bool.and (sEq (lin5S w0 (ofInt p0.2.1) w1 (ofInt p1.2.1) w2 (ofInt p2.2.1) w3 (ofInt p3.2.1) w4 (ofInt p4.2.1)) ⟨0, 0⟩)
  (Bool.and (sEq (lin5S w0 (ofInt p0.2.2.1) w1 (ofInt p1.2.2.1) w2 (ofInt p2.2.2.1) w3 (ofInt p3.2.2.1) w4 (ofInt p4.2.2.1)) ⟨0, 0⟩)
  (Bool.and (sEq (lin5S w0 (ofInt p0.2.2.2) w1 (ofInt p1.2.2.2) w2 (ofInt p2.2.2.2) w3 (ofInt p3.2.2.2) w4 (ofInt p4.2.2.2)) ⟨0, 0⟩)
            (sLt ⟨0, 0⟩ (solve4S (mkHomRow4 p1) (mkHomRow4 p2) (mkHomRow4 p3) (mkHomRow4 p4)).den))))))))))))))

def checkBoxFull (r_hi : Int) (a0 a1 a2 : Int × Int × Int × Int) (b0 b1 b2 : Int)
    (c0 c1 c2 c3 c4 c5 c6 c7 : Int × Int × Int × Int)
    (si0 si1 si2 si3 si4 : Nat) (sw0 sw1 sw2 sw3 sw4 : Int) : Bool :=
  let r_hiS := ofInt r_hi
  Bool.and (sLt ⟨0, 0⟩ r_hiS)
  (Bool.and (sEq (ofInt a0.2.2.2) ⟨0, 0⟩)
  (Bool.and (sEq (ofInt a1.2.2.2) ⟨0, 0⟩)
  (Bool.and (sEq (ofInt a2.2.2.2) ⟨0, 0⟩)
  (Bool.and (sEq (ofInt a1.2.2.1) (ofInt a0.2.2.1))
  (Bool.and (sEq (ofInt a2.2.2.1) (ofInt a0.2.2.1))
  (Bool.and (checkSimplex c0 c1 c2 c3 c4 c5 c6 c7 si0 si1 si2 si3 si4 sw0 sw1 sw2 sw3 sw4)
  (let r2 := mkRowAS a0 b0; let r3 := mkRowAS a1 b1; let r4 := mkRowAS a2 b2
   let cs : List Row5S := [mkRowCS c0, mkRowCS c1, mkRowCS c2, mkRowCS c3, mkRowCS c4, mkRowCS c5, mkRowCS c6, mkRowCS c7]
   let mids := r2 :: r3 :: r4 :: cs
   let z2 := toRow4ZeroS r2; let z3 := toRow4ZeroS r3; let z4 := toRow4ZeroS r4
   let zcs := cs.map toRow4ZeroS
   let okZ :=
     Bool.and (if sEq (ofInt a0.2.2.1) ⟨0, 0⟩ then true else ch1Z mids z2 z3 z4 zcs)
     (Bool.and (ch2Z mids z2 z3 zcs) (Bool.and (ch2Z mids z2 z4 zcs) (Bool.and (ch2Z mids z3 z4 zcs)
     (Bool.and (ch3Z mids z2 zcs) (Bool.and (ch3Z mids z3 zcs) (Bool.and (ch3Z mids z4 zcs) (ch4Z mids zcs)))))))
   let t2 := toRow4TopS r_hiS r2; let t3 := toRow4TopS r_hiS r3; let t4 := toRow4TopS r_hiS r4
   let tcs := cs.map (toRow4TopS r_hiS)
   let okT :=
     Bool.and (if sEq (ofInt a0.2.2.1) ⟨0, 0⟩ then true else ch1T r_hiS mids t2 t3 t4 tcs)
     (Bool.and (ch2T r_hiS mids t2 t3 tcs) (Bool.and (ch2T r_hiS mids t2 t4 tcs) (Bool.and (ch2T r_hiS mids t3 t4 tcs)
     (Bool.and (ch3T r_hiS mids t2 tcs) (Bool.and (ch3T r_hiS mids t3 tcs) (Bool.and (ch3T r_hiS mids t4 tcs) (ch4T r_hiS mids tcs)))))))
   Bool.and okZ (Bool.and okT (ch5M r_hiS mids mids)))))))))

def row4Val (u : Row4S) (x0 x1 x2 x3 : ℝ) : ℝ :=
  toR u.a0 * x0 + toR u.a1 * x1 + toR u.a2 * x2 + toR u.a3 * x3

def row5Val (r : Row5S) (z : Fin 5 → ℝ) : ℝ :=
  toR r.a0 * z 0 + toR r.a1 * z 1 + toR r.a2 * z 2 + toR r.a3 * z 3 +
    (if r.a4 then 1 else -1) * z 4

theorem solve4Raw_cramer {u0 u1 u2 u3 : Row4S} {x0 x1 x2 x3 : ℝ}
    (h0 : row4Val u0 x0 x1 x2 x3 = toR u0.d) (h1 : row4Val u1 x0 x1 x2 x3 = toR u1.d)
    (h2 : row4Val u2 x0 x1 x2 x3 = toR u2.d) (h3 : row4Val u3 x0 x1 x2 x3 = toR u3.d) :
    let s := solve4Raw u0 u1 u2 u3
    toR s.den * x0 = toR s.n0 ∧
    toR s.den * x1 = toR s.n1 ∧
    toR s.den * x2 = toR s.n2 ∧
    toR s.den * x3 = toR s.n3 := by
  dsimp only [solve4Raw]
  unfold row4Val at h0 h1 h2 h3
  simp only [lin6S, det2S, toR_sNorm, toR_sAdd, toR_sSub, toR_sNeg, toR_sMul,
    ← h0, ← h1, ← h2, ← h3]
  exact ⟨by ring, by ring, by ring, by ring⟩

theorem solve4S_cramer {u0 u1 u2 u3 : Row4S} {x0 x1 x2 x3 : ℝ}
    (h0 : row4Val u0 x0 x1 x2 x3 = toR u0.d) (h1 : row4Val u1 x0 x1 x2 x3 = toR u1.d)
    (h2 : row4Val u2 x0 x1 x2 x3 = toR u2.d) (h3 : row4Val u3 x0 x1 x2 x3 = toR u3.d) :
    let s := solve4S u0 u1 u2 u3
    toR s.den * x0 = toR s.n0 ∧
    toR s.den * x1 = toR s.n1 ∧
    toR s.den * x2 = toR s.n2 ∧
    toR s.den * x3 = toR s.n3 := by
  obtain ⟨e0, e1, e2, e3⟩ := solve4Raw_cramer h0 h1 h2 h3
  dsimp only [solve4S]
  cases sLt (solve4Raw u0 u1 u2 u3).den ⟨0, 0⟩
  · exact ⟨e0, e1, e2, e3⟩
  · simp only [toR_sNeg]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem solve4S_real_bound (u0 u1 u2 u3 : Row4S)
    (hden : sLt ⟨0, 0⟩ (solve4S u0 u1 u2 u3).den = true) (M : ℝ) (hM : 0 ≤ M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x0 x1 x2 x3 : ℝ,
      |row4Val u0 x0 x1 x2 x3| ≤ M →
      |row4Val u1 x0 x1 x2 x3| ≤ M →
      |row4Val u2 x0 x1 x2 x3| ≤ M →
      |row4Val u3 x0 x1 x2 x3| ≤ M →
      |x0| ≤ K ∧ |x1| ≤ K ∧ |x2| ≤ K ∧ |x3| ≤ K := by
  have hd_pos : 0 < toR (solve4S u0 u1 u2 u3).den := by simpa using (sLt_iff _ _).mp hden
  obtain ⟨D, hD_def⟩ : ∃ D : ℝ, D = toR (solve4Raw u0 u1 u2 u3).den := ⟨_, rfl⟩
  have hraw_ne : D ≠ 0 := by
    rw [hD_def]
    dsimp only [solve4S] at hd_pos
    cases hs : sLt (solve4Raw u0 u1 u2 u3).den ⟨0, 0⟩ <;> rw [hs] at hd_pos
    · linarith
    · simp only [toR_sNeg] at hd_pos; linarith
  have hD_pos : 0 < |D| := abs_pos.mpr hraw_ne
  obtain ⟨p01, hp01⟩ : ∃ v : ℝ, v = toR (det2S u0.a0 u0.a1 u1.a0 u1.a1) := ⟨_, rfl⟩
  obtain ⟨p02, hp02⟩ : ∃ v : ℝ, v = toR (det2S u0.a0 u0.a2 u1.a0 u1.a2) := ⟨_, rfl⟩
  obtain ⟨p03, hp03⟩ : ∃ v : ℝ, v = toR (det2S u0.a0 u0.a3 u1.a0 u1.a3) := ⟨_, rfl⟩
  obtain ⟨p12, hp12⟩ : ∃ v : ℝ, v = toR (det2S u0.a1 u0.a2 u1.a1 u1.a2) := ⟨_, rfl⟩
  obtain ⟨p13, hp13⟩ : ∃ v : ℝ, v = toR (det2S u0.a1 u0.a3 u1.a1 u1.a3) := ⟨_, rfl⟩
  obtain ⟨p23, hp23⟩ : ∃ v : ℝ, v = toR (det2S u0.a2 u0.a3 u1.a2 u1.a3) := ⟨_, rfl⟩
  obtain ⟨q01, hq01⟩ : ∃ v : ℝ, v = toR (det2S u2.a0 u2.a1 u3.a0 u3.a1) := ⟨_, rfl⟩
  obtain ⟨q02, hq02⟩ : ∃ v : ℝ, v = toR (det2S u2.a0 u2.a2 u3.a0 u3.a2) := ⟨_, rfl⟩
  obtain ⟨q03, hq03⟩ : ∃ v : ℝ, v = toR (det2S u2.a0 u2.a3 u3.a0 u3.a3) := ⟨_, rfl⟩
  obtain ⟨q12, hq12⟩ : ∃ v : ℝ, v = toR (det2S u2.a1 u2.a2 u3.a1 u3.a2) := ⟨_, rfl⟩
  obtain ⟨q13, hq13⟩ : ∃ v : ℝ, v = toR (det2S u2.a1 u2.a3 u3.a1 u3.a3) := ⟨_, rfl⟩
  obtain ⟨q23, hq23⟩ : ∃ v : ℝ, v = toR (det2S u2.a2 u2.a3 u3.a2 u3.a3) := ⟨_, rfl⟩
  let S_box : Set (Fin 4 → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (-M) M)
  have hcomp : IsCompact S_box := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hne : S_box.Nonempty := ⟨fun _ => 0, fun _ _ => ⟨by linarith, by linarith⟩⟩
  let poly0 (d : Fin 4 → ℝ) : ℝ :=
    -((p12 * (toR u2.a3 * d 3 - d 2 * toR u3.a3) - p13 * (toR u2.a2 * d 3 - d 2 * toR u3.a2) +
       (toR u0.a1 * d 1 - d 0 * toR u1.a1) * q23 + p23 * (toR u2.a1 * d 3 - d 2 * toR u3.a1) -
       (toR u0.a2 * d 1 - d 0 * toR u1.a2) * q13 + (toR u0.a3 * d 1 - d 0 * toR u1.a3) * q12))
  let poly1 (d : Fin 4 → ℝ) : ℝ :=
     (p02 * (toR u2.a3 * d 3 - d 2 * toR u3.a3) - p03 * (toR u2.a2 * d 3 - d 2 * toR u3.a2) +
      (toR u0.a0 * d 1 - d 0 * toR u1.a0) * q23 + p23 * (toR u2.a0 * d 3 - d 2 * toR u3.a0) -
      (toR u0.a2 * d 1 - d 0 * toR u1.a2) * q03 + (toR u0.a3 * d 1 - d 0 * toR u1.a3) * q02)
  let poly2 (d : Fin 4 → ℝ) : ℝ :=
    -((p01 * (toR u2.a3 * d 3 - d 2 * toR u3.a3) - p03 * (toR u2.a1 * d 3 - d 2 * toR u3.a1) +
       (toR u0.a0 * d 1 - d 0 * toR u1.a0) * q13 + p13 * (toR u2.a0 * d 3 - d 2 * toR u3.a0) -
       (toR u0.a1 * d 1 - d 0 * toR u1.a1) * q03 + (toR u0.a3 * d 1 - d 0 * toR u1.a3) * q01))
  let poly3 (d : Fin 4 → ℝ) : ℝ :=
     (p01 * (toR u2.a2 * d 3 - d 2 * toR u3.a2) - p02 * (toR u2.a1 * d 3 - d 2 * toR u3.a1) +
      (toR u0.a0 * d 1 - d 0 * toR u1.a0) * q12 + p12 * (toR u2.a0 * d 3 - d 2 * toR u3.a0) -
      (toR u0.a1 * d 1 - d 0 * toR u1.a1) * q02 + (toR u0.a2 * d 1 - d 0 * toR u1.a2) * q01)
  let bigF (d : Fin 4 → ℝ) : ℝ := (|poly0 d| + |poly1 d| + |poly2 d| + |poly3 d|) / |D|
  have hcont : Continuous bigF := by dsimp [bigF, poly0, poly1, poly2, poly3]; fun_prop
  obtain ⟨d_max, _, hmax⟩ := hcomp.exists_isMaxOn hne hcont.continuousOn
  have hbigF_nn : 0 ≤ bigF d_max :=
    div_nonneg (add_nonneg (add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)) (abs_nonneg _)) hD_pos.le
  refine ⟨bigF d_max, hbigF_nn, fun x0 x1 x2 x3 hb0 hb1 hb2 hb3 => ?_⟩
  let dv : Fin 4 → ℝ := fun i =>
    match i with
    | 0 => row4Val u0 x0 x1 x2 x3
    | 1 => row4Val u1 x0 x1 x2 x3
    | 2 => row4Val u2 x0 x1 x2 x3
    | 3 => row4Val u3 x0 x1 x2 x3
  have hdv_mem : dv ∈ S_box := by
    intro i _; fin_cases i <;> simpa [dv] using abs_le.mp (by assumption)
  have hle : bigF dv ≤ bigF d_max := hmax hdv_mem
  have hid0 : D * x0 = poly0 dv := by
    rw [hD_def]
    dsimp [solve4Raw, poly0, dv, lin6S, det2S, row4Val]
    simp only [hp12, hp13, hp23, hq12, hq13, hq23, det2S, toR_sNorm, toR_sAdd, toR_sSub, toR_sMul]
    ring
  have hid1 : D * x1 = poly1 dv := by
    rw [hD_def]
    dsimp [solve4Raw, poly1, dv, lin6S, det2S, row4Val]
    simp only [hp02, hp03, hp23, hq02, hq03, hq23, det2S, toR_sNorm, toR_sAdd, toR_sSub, toR_sMul]
    ring
  have hid2 : D * x2 = poly2 dv := by
    rw [hD_def]
    dsimp [solve4Raw, poly2, dv, lin6S, det2S, row4Val]
    simp only [hp01, hp03, hp13, hq01, hq03, hq13, det2S, toR_sNorm, toR_sAdd, toR_sSub, toR_sMul]
    ring
  have hid3 : D * x3 = poly3 dv := by
    rw [hD_def]
    dsimp [solve4Raw, poly3, dv, lin6S, det2S, row4Val]
    simp only [hp01, hp02, hp12, hq01, hq02, hq12, det2S, toR_sNorm, toR_sAdd, toR_sSub, toR_sMul]
    ring
  have hx0 : |x0| ≤ |poly0 dv| / |D| := by rw [le_div_iff₀ hD_pos, mul_comm, ← abs_mul, hid0]
  have hx1 : |x1| ≤ |poly1 dv| / |D| := by rw [le_div_iff₀ hD_pos, mul_comm, ← abs_mul, hid1]
  have hx2 : |x2| ≤ |poly2 dv| / |D| := by rw [le_div_iff₀ hD_pos, mul_comm, ← abs_mul, hid2]
  have hx3 : |x3| ≤ |poly3 dv| / |D| := by rw [le_div_iff₀ hD_pos, mul_comm, ← abs_mul, hid3]
  have hp0 : 0 ≤ |poly0 dv| / |D| := div_nonneg (abs_nonneg _) hD_pos.le
  have hp1 : 0 ≤ |poly1 dv| / |D| := div_nonneg (abs_nonneg _) hD_pos.le
  have hp2 : 0 ≤ |poly2 dv| / |D| := div_nonneg (abs_nonneg _) hD_pos.le
  have hp3 : 0 ≤ |poly3 dv| / |D| := div_nonneg (abs_nonneg _) hD_pos.le
  have hsum : |poly0 dv| / |D| + |poly1 dv| / |D| + |poly2 dv| / |D| + |poly3 dv| / |D| = bigF dv := by
    dsimp [bigF]; ring
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/- Rank-Nullity Helper on Fin n → ℝ -/

theorem exists_nonzero_in_common_ker {n : ℕ} (eqs : List ((Fin n → ℝ) →ₗ[ℝ] ℝ))
    (hlen : eqs.length < n) :
    ∃ v : Fin n → ℝ, v ≠ 0 ∧ ∀ f ∈ eqs, f v = 0 := by
  let F : (Fin n → ℝ) →ₗ[ℝ] (Fin eqs.length → ℝ) :=
    LinearMap.pi (fun i : Fin eqs.length => eqs.get i)
  have hker : LinearMap.ker F ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective F := LinearMap.ker_eq_bot.mp hbot
    have hfr := LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_fin_fun ℝ, Module.finrank_fin_fun ℝ] at hfr
    omega
  obtain ⟨v, hv_mem, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨v, hv_ne, fun f hf => ?_⟩
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hf
  exact congrFun (LinearMap.mem_ker.mp hv_mem) i

def row5Lin (r : Row5S) : (Fin 5 → ℝ) →ₗ[ℝ] ℝ :=
  toR r.a0 • LinearMap.proj 0 + toR r.a1 • LinearMap.proj 1 +
  toR r.a2 • LinearMap.proj 2 + toR r.a3 • LinearMap.proj 3 +
  (if r.a4 then (1 : ℝ) else -1) • LinearMap.proj 4

lemma row5Lin_apply (r : Row5S) (z : Fin 5 → ℝ) : row5Lin r z = row5Val r z := by
  cases hb : r.a4 <;> simp [row5Lin, row5Val, hb]

def row4Lin (r : Row5S) : (Fin 4 → ℝ) →ₗ[ℝ] ℝ :=
  toR r.a0 • LinearMap.proj 0 + toR r.a1 • LinearMap.proj 1 +
  toR r.a2 • LinearMap.proj 2 + toR r.a3 • LinearMap.proj 3

lemma row4Lin_apply (r : Row5S) (x : Fin 4 → ℝ) :
    row4Lin r x = row4Val ⟨r.a0, r.a1, r.a2, r.a3, r.d⟩ (x 0) (x 1) (x 2) (x 3) := by
  simp [row4Lin, row4Val]

/- Polytope Compactness from checkSimplex -/

lemma pickC_mem_cs (c0 c1 c2 c3 c4 c5 c6 c7 : Int × Int × Int × Int) {si : Nat}
    (hsi : Nat.ble (Nat.add si 1) 8 = true) :
    mkRowCS (pickC c0 c1 c2 c3 c4 c5 c6 c7 si) ∈
      [mkRowCS c0, mkRowCS c1, mkRowCS c2, mkRowCS c3, mkRowCS c4, mkRowCS c5, mkRowCS c6, mkRowCS c7] := by
  rw [Nat.ble_eq] at hsi; simp only [Nat.add_eq] at hsi
  rcases si with _ | _ | _ | _ | _ | _ | _ | _ | n
  · simp [pickC]
  · simp [pickC]
  · simp [pickC]
  · simp [pickC]
  · simp [pickC]
  · simp [pickC]
  · simp [pickC]
  · simp [pickC]
  · omega

def polySet (r_hi : SInt) (mids : List Row5S) : Set (Fin 5 → ℝ) :=
  {z | 0 ≤ z 4 ∧ z 4 ≤ toR r_hi ∧ ∀ r ∈ mids, row5Val r z ≤ toR r.d}

lemma polySet_isClosed (r_hi : SInt) (mids : List Row5S) : IsClosed (polySet r_hi mids) := by
  have hlist : ∀ L : List Row5S, IsClosed {z : Fin 5 → ℝ | ∀ r ∈ L, row5Val r z ≤ toR r.d} := by
    intro L
    induction L with
    | nil =>
      convert isClosed_univ
      ext z; simp
    | cons r rs ih =>
      have heq : {z : Fin 5 → ℝ | ∀ q ∈ r :: rs, row5Val q z ≤ toR q.d} =
          {z | row5Val r z ≤ toR r.d} ∩ {z | ∀ q ∈ rs, row5Val q z ≤ toR q.d} := by
        ext z; simp [List.mem_cons]
      rw [heq]
      refine IsClosed.inter ?_ ih
      exact isClosed_le (by unfold row5Val; fun_prop) continuous_const
  have heq : polySet r_hi mids =
      ({z : Fin 5 → ℝ | 0 ≤ z 4} ∩ {z : Fin 5 → ℝ | z 4 ≤ toR r_hi}) ∩
      {z : Fin 5 → ℝ | ∀ r ∈ mids, row5Val r z ≤ toR r.d} := by
    ext z; simp [polySet, and_assoc]
  rw [heq]
  exact ((isClosed_le continuous_const (continuous_apply 4)).inter
    (isClosed_le (continuous_apply 4) continuous_const)).inter (hlist mids)

theorem polySet_isCompact (r_hi : SInt) (hr_hi : sLt ⟨0, 0⟩ r_hi = true)
    (r2 r3 r4 : Row5S) (c0 c1 c2 c3 c4 c5 c6 c7 : Int × Int × Int × Int)
    (si0 si1 si2 si3 si4 : Nat) (sw0 sw1 sw2 sw3 sw4 : Int)
    (hsimp : checkSimplex c0 c1 c2 c3 c4 c5 c6 c7 si0 si1 si2 si3 si4 sw0 sw1 sw2 sw3 sw4 = true) :
    let cs := [mkRowCS c0, mkRowCS c1, mkRowCS c2, mkRowCS c3, mkRowCS c4, mkRowCS c5, mkRowCS c6, mkRowCS c7]
    IsCompact (polySet r_hi (r2 :: r3 :: r4 :: cs)) := by
  intro cs
  let mids := r2 :: r3 :: r4 :: cs
  unfold checkSimplex at hsimp
  simp only [Bool.and_eq_true] at hsimp
  rcases hsimp with ⟨hsi0, hsi1, hsi2, hsi3, hsi4, hw0, hw1, hw2, hw3, hw4, he0, he1, he2, he3, hden⟩
  let p0 := pickC c0 c1 c2 c3 c4 c5 c6 c7 si0
  let p1 := pickC c0 c1 c2 c3 c4 c5 c6 c7 si1
  let p2 := pickC c0 c1 c2 c3 c4 c5 c6 c7 si2
  let p3 := pickC c0 c1 c2 c3 c4 c5 c6 c7 si3
  let p4 := pickC c0 c1 c2 c3 c4 c5 c6 c7 si4
  have hr_pos : 0 < toR r_hi := by simpa using (sLt_iff _ _).mp hr_hi
  have hw0p : 0 < (sw0 : ℝ) := by simpa using (sLt_iff _ _).mp hw0
  have hw1p : 0 < (sw1 : ℝ) := by simpa using (sLt_iff _ _).mp hw1
  have hw2p : 0 < (sw2 : ℝ) := by simpa using (sLt_iff _ _).mp hw2
  have hw3p : 0 < (sw3 : ℝ) := by simpa using (sLt_iff _ _).mp hw3
  have hw4p : 0 < (sw4 : ℝ) := by simpa using (sLt_iff _ _).mp hw4
  have hlin0 : (sw0 : ℝ) * p0.1 + sw1 * p1.1 + sw2 * p2.1 + sw3 * p3.1 + sw4 * p4.1 = 0 := by
    have := (sEq_iff _ _).mp he0; simp [lin5S] at this; linarith
  have hlin1 : (sw0 : ℝ) * p0.2.1 + sw1 * p1.2.1 + sw2 * p2.2.1 + sw3 * p3.2.1 + sw4 * p4.2.1 = 0 := by
    have := (sEq_iff _ _).mp he1; simp [lin5S] at this; linarith
  have hlin2 : (sw0 : ℝ) * p0.2.2.1 + sw1 * p1.2.2.1 + sw2 * p2.2.2.1 + sw3 * p3.2.2.1 + sw4 * p4.2.2.1 = 0 := by
    have := (sEq_iff _ _).mp he2; simp [lin5S] at this; linarith
  have hlin3 : (sw0 : ℝ) * p0.2.2.2 + sw1 * p1.2.2.2 + sw2 * p2.2.2.2 + sw3 * p3.2.2.2 + sw4 * p4.2.2.2 = 0 := by
    have := (sEq_iff _ _).mp he3; simp [lin5S] at this; linarith
  have hmem_c : ∀ p, mkRowCS p ∈ cs → ∀ z ∈ polySet r_hi mids,
      row4Val (mkHomRow4 p) (z 0) (z 1) (z 2) (z 3) ≤ (|toR (mkRowCS p).d| + toR r_hi) / 2 := by
    intro p hp z ⟨_, hz4_hi, hzmids⟩
    have hzr : row5Val (mkRowCS p) z ≤ toR (mkRowCS p).d :=
      hzmids _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp)))
    have hval : row5Val (mkRowCS p) z = 2 * row4Val (mkHomRow4 p) (z 0) (z 1) (z 2) (z 3) - z 4 := by
      rcases p with ⟨x0, x1, x2, x3⟩
      simp [mkRowCS, mkHomRow4, row5Val, row4Val]
      ring
    have hd_le : toR (mkRowCS p).d ≤ |toR (mkRowCS p).d| := le_abs_self _
    linarith
  let U (p : Int × Int × Int × Int) : ℝ := (|toR (mkRowCS p).d| + toR r_hi) / 2
  have hU_pos (p : Int × Int × Int × Int) : 0 ≤ U p := by dsimp [U]; positivity
  let S_up : ℝ := sw0 * U p0 + sw1 * U p1 + sw2 * U p2 + sw3 * U p3 + sw4 * U p4
  have hS_pos : 0 ≤ S_up := by dsimp [S_up]; positivity
  let w_min : ℝ := min (sw1 : ℝ) (min (sw2 : ℝ) (min (sw3 : ℝ) (sw4 : ℝ)))
  have hw_min_pos : 0 < w_min := by
    dsimp [w_min]; exact lt_min hw1p (lt_min hw2p (lt_min hw3p hw4p))
  let M : ℝ := max (U p1 + U p2 + U p3 + U p4) (S_up / w_min)
  have hM_nn : 0 ≤ M := le_max_of_le_left (by positivity)
  obtain ⟨K, hK_nn, hK⟩ := solve4S_real_bound (mkHomRow4 p1) (mkHomRow4 p2) (mkHomRow4 p3) (mkHomRow4 p4) hden M hM_nn
  let B : ℝ := max K (toR r_hi)
  refine IsCompact.of_isClosed_subset (isCompact_univ_pi (fun _ : Fin 5 => isCompact_Icc (a := -B) (b := B)))
    (polySet_isClosed r_hi mids) ?_
  intro z hz
  have hu0 : row4Val (mkHomRow4 p0) (z 0) (z 1) (z 2) (z 3) ≤ U p0 := hmem_c p0 (pickC_mem_cs _ _ _ _ _ _ _ _ hsi0) z hz
  have hu1 : row4Val (mkHomRow4 p1) (z 0) (z 1) (z 2) (z 3) ≤ U p1 := hmem_c p1 (pickC_mem_cs _ _ _ _ _ _ _ _ hsi1) z hz
  have hu2 : row4Val (mkHomRow4 p2) (z 0) (z 1) (z 2) (z 3) ≤ U p2 := hmem_c p2 (pickC_mem_cs _ _ _ _ _ _ _ _ hsi2) z hz
  have hu3 : row4Val (mkHomRow4 p3) (z 0) (z 1) (z 2) (z 3) ≤ U p3 := hmem_c p3 (pickC_mem_cs _ _ _ _ _ _ _ _ hsi3) z hz
  have hu4 : row4Val (mkHomRow4 p4) (z 0) (z 1) (z 2) (z 3) ≤ U p4 := hmem_c p4 (pickC_mem_cs _ _ _ _ _ _ _ _ hsi4) z hz
  have hsum0 : (sw0 : ℝ) * row4Val (mkHomRow4 p0) (z 0) (z 1) (z 2) (z 3) +
               sw1 * row4Val (mkHomRow4 p1) (z 0) (z 1) (z 2) (z 3) +
               sw2 * row4Val (mkHomRow4 p2) (z 0) (z 1) (z 2) (z 3) +
               sw3 * row4Val (mkHomRow4 p3) (z 0) (z 1) (z 2) (z 3) +
               sw4 * row4Val (mkHomRow4 p4) (z 0) (z 1) (z 2) (z 3) = 0 := by
    simp only [mkHomRow4, row4Val, toR_ofInt]
    calc
      _ = ((sw0 : ℝ) * p0.1 + sw1 * p1.1 + sw2 * p2.1 + sw3 * p3.1 + sw4 * p4.1) * z 0 +
          ((sw0 : ℝ) * p0.2.1 + sw1 * p1.2.1 + sw2 * p2.2.1 + sw3 * p3.2.1 + sw4 * p4.2.1) * z 1 +
          ((sw0 : ℝ) * p0.2.2.1 + sw1 * p1.2.2.1 + sw2 * p2.2.2.1 + sw3 * p3.2.2.1 + sw4 * p4.2.2.1) * z 2 +
          ((sw0 : ℝ) * p0.2.2.2 + sw1 * p1.2.2.2 + sw2 * p2.2.2.2 + sw3 * p3.2.2.2 + sw4 * p4.2.2.2) * z 3 := by ring
      _ = 0 := by rw [hlin0, hlin1, hlin2, hlin3]; ring
  have habs_bound : ∀ (w v : ℝ), w_min ≤ w → v ≤ U p1 + U p2 + U p3 + U p4 → -S_up ≤ w * v → |v| ≤ M := by
    intro w v hw_ge hv_le hwv
    have hw_pos : 0 < w := lt_of_lt_of_le hw_min_pos hw_ge
    rw [abs_le]
    refine ⟨?_, hv_le.trans (le_max_left _ _)⟩
    have h1 : -(S_up / w) ≤ v := by
      have h1' : -S_up / w ≤ v := (div_le_iff₀ hw_pos).mpr (by linarith)
      rwa [neg_div] at h1'
    have h2 : S_up / w ≤ S_up / w_min := div_le_div_of_nonneg_left hS_pos hw_min_pos hw_ge
    have h3 : -(S_up / w_min) ≤ v := by linarith
    have h4 : S_up / w_min ≤ M := le_max_right _ _
    linarith
  have h0u := mul_le_mul_of_nonneg_left hu0 hw0p.le
  have h1u := mul_le_mul_of_nonneg_left hu1 hw1p.le
  have h2u := mul_le_mul_of_nonneg_left hu2 hw2p.le
  have h3u := mul_le_mul_of_nonneg_left hu3 hw3p.le
  have h4u := mul_le_mul_of_nonneg_left hu4 hw4p.le
  have hb1 : |row4Val (mkHomRow4 p1) (z 0) (z 1) (z 2) (z 3)| ≤ M :=
    habs_bound sw1 _ (min_le_left _ _)
      (by linarith [hU_pos p2, hU_pos p3, hU_pos p4]) (by dsimp [S_up]; linarith [mul_nonneg hw1p.le (hU_pos p1)])
  have hb2 : |row4Val (mkHomRow4 p2) (z 0) (z 1) (z 2) (z 3)| ≤ M :=
    habs_bound sw2 _ ((min_le_right _ _).trans (min_le_left _ _))
      (by linarith [hU_pos p1, hU_pos p3, hU_pos p4]) (by dsimp [S_up]; linarith [mul_nonneg hw2p.le (hU_pos p2)])
  have hb3 : |row4Val (mkHomRow4 p3) (z 0) (z 1) (z 2) (z 3)| ≤ M :=
    habs_bound sw3 _ ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
      (by linarith [hU_pos p1, hU_pos p2, hU_pos p4]) (by dsimp [S_up]; linarith [mul_nonneg hw3p.le (hU_pos p3)])
  have hb4 : |row4Val (mkHomRow4 p4) (z 0) (z 1) (z 2) (z 3)| ≤ M :=
    habs_bound sw4 _ ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
      (by linarith [hU_pos p1, hU_pos p2, hU_pos p3]) (by dsimp [S_up]; linarith [mul_nonneg hw4p.le (hU_pos p4)])
  obtain ⟨hz0, hz1, hz2, hz3⟩ := hK (z 0) (z 1) (z 2) (z 3) hb1 hb2 hb3 hb4
  have hKB : K ≤ B := le_max_left _ _
  have hrB : toR r_hi ≤ B := le_max_right _ _
  have hz4_nn : 0 ≤ z 4 := hz.1
  have hz4_lo : -B ≤ z 4 := by linarith [hK_nn, hKB, hz4_nn]
  have hz4_hi : z 4 ≤ B := hz.2.1.trans hrB
  intro i _
  fin_cases i
  · exact abs_le.mp (hz0.trans hKB)
  · exact abs_le.mp (hz1.trans hKB)
  · exact abs_le.mp (hz2.trans hKB)
  · exact abs_le.mp (hz3.trans hKB)
  · exact ⟨hz4_lo, hz4_hi⟩

/- Paraboloid Maximizer Active Kernel = 0 -/

def paraG (z : Fin 5 → ℝ) : ℝ :=
  (z 0) ^ 2 + (z 1) ^ 2 + (z 2) ^ 2 + (z 3) ^ 2 - z 4

lemma list_step_feasible (L : List Row5S) (z v : Fin 5 → ℝ)
    (hfeas : ∀ r ∈ L, row5Val r z ≤ toR r.d)
    (hact : ∀ r ∈ L, row5Val r z = toR r.d → row5Val r v = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| ≤ δ → ∀ r ∈ L, row5Val r (z + t • v) ≤ toR r.d := by
  induction L with
  | nil => exact ⟨1, zero_lt_one, fun _ _ r hr => False.elim (List.not_mem_nil hr)⟩
  | cons r₀ rs ih =>
    obtain ⟨δ_rs, hδ_rs, hstep_rs⟩ := ih
      (fun q hq => hfeas q (List.mem_cons_of_mem _ hq))
      (fun q hq => hact q (List.mem_cons_of_mem _ hq))
    have hlin : ∀ t : ℝ, row5Val r₀ (z + t • v) = row5Val r₀ z + t * row5Val r₀ v := by
      intro t; cases hb : r₀.a4 <;> simp [row5Val, hb] <;> ring
    by_cases heq : row5Val r₀ z = toR r₀.d
    · have hv0 : row5Val r₀ v = 0 := hact r₀ List.mem_cons_self heq
      refine ⟨δ_rs, hδ_rs, fun t ht q hq => ?_⟩
      rcases List.mem_cons.mp hq with hqr | hq'
      · rw [hqr, hlin, heq, hv0]; linarith
      · exact hstep_rs t ht q hq'
    · have hlt : row5Val r₀ z < toR r₀.d := lt_of_le_of_ne (hfeas r₀ List.mem_cons_self) heq
      have hgap : 0 < toR r₀.d - row5Val r₀ z := sub_pos.mpr hlt
      have hden : 0 < |row5Val r₀ v| + 1 := by positivity
      refine ⟨min δ_rs ((toR r₀.d - row5Val r₀ z) / (|row5Val r₀ v| + 1)),
        lt_min hδ_rs (div_pos hgap hden), fun t ht q hq => ?_⟩
      rcases List.mem_cons.mp hq with hqr | hq'
      · rw [hqr, hlin]
        have ht1 : |t| ≤ (toR r₀.d - row5Val r₀ z) / (|row5Val r₀ v| + 1) := ht.trans (min_le_right _ _)
        have hmul1 : |t| * (|row5Val r₀ v| + 1) ≤ toR r₀.d - row5Val r₀ z := (le_div_iff₀ hden).mp ht1
        have hmul2 : t * row5Val r₀ v ≤ |t| * |row5Val r₀ v| := by
          rw [← abs_mul]; exact le_abs_self _
        have hmul3 : |t| * |row5Val r₀ v| ≤ |t| * (|row5Val r₀ v| + 1) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (abs_nonneg t)
        linarith
      · exact hstep_rs t (ht.trans (min_le_left _ _)) q hq'

theorem ker_active_eq_zero {r_hi : SInt} {mids : List Row5S} {z v : Fin 5 → ℝ}
    (hz : z ∈ polySet r_hi mids)
    (hmax : ∀ w ∈ polySet r_hi mids, paraG w ≤ paraG z)
    (hv0 : z 4 = 0 → v 4 = 0)
    (hvhi : z 4 = toR r_hi → v 4 = 0)
    (hvact : ∀ r ∈ mids, row5Val r z = toR r.d → row5Val r v = 0) :
    v = 0 := by
  obtain ⟨δ_L, hδ_L, hstep_L⟩ := list_step_feasible mids z v hz.2.2 hvact
  have hstep_4 : ∃ δ_4 : ℝ, 0 < δ_4 ∧ ∀ t : ℝ, |t| ≤ δ_4 →
      0 ≤ (z + t • v) 4 ∧ (z + t • v) 4 ≤ toR r_hi := by
    by_cases h40 : z 4 = 0
    · refine ⟨1, zero_lt_one, fun t _ => ?_⟩
      simp [h40, hv0 h40, hz.1.trans hz.2.1]
    · by_cases h4hi : z 4 = toR r_hi
      · refine ⟨1, zero_lt_one, fun t _ => ?_⟩
        simp [h4hi, hvhi h4hi]; exact h4hi ▸ hz.1
      · have hp1 : 0 < z 4 := lt_of_le_of_ne hz.1 (Ne.symm h40)
        have hp2 : 0 < toR r_hi - z 4 := sub_pos.mpr (lt_of_le_of_ne hz.2.1 h4hi)
        let g4 := min (z 4) (toR r_hi - z 4)
        let d4 := |v 4| + 1
        have hd4 : 0 < d4 := by dsimp [d4]; positivity
        refine ⟨g4 / d4, div_pos (lt_min hp1 hp2) hd4, fun t ht => ?_⟩
        have hm1 : |t| * d4 ≤ g4 := (le_div_iff₀ hd4).mp ht
        have hm2 : |t * v 4| ≤ |t| * d4 := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (by dsimp [d4]; linarith) (abs_nonneg t)
        obtain ⟨hl, hr⟩ := abs_le.mp (hm2.trans hm1)
        have hg1 : g4 ≤ z 4 := min_le_left _ _
        have hg2 : g4 ≤ toR r_hi - z 4 := min_le_right _ _
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact ⟨by linarith, by linarith⟩
  obtain ⟨δ_4, hδ_4, hstep_4⟩ := hstep_4
  let t := min δ_L δ_4
  have ht_pos : 0 < t := lt_min hδ_L hδ_4
  have hmem_plus : z + t • v ∈ polySet r_hi mids := by
    have ha : |t| ≤ δ_L := by rw [abs_of_pos ht_pos]; exact min_le_left _ _
    have hb : |t| ≤ δ_4 := by rw [abs_of_pos ht_pos]; exact min_le_right _ _
    exact ⟨(hstep_4 t hb).1, (hstep_4 t hb).2, hstep_L t ha⟩
  have hmem_minus : z + (-t) • v ∈ polySet r_hi mids := by
    have ha : |-t| ≤ δ_L := by rw [abs_neg, abs_of_pos ht_pos]; exact min_le_left _ _
    have hb : |-t| ≤ δ_4 := by rw [abs_neg, abs_of_pos ht_pos]; exact min_le_right _ _
    exact ⟨(hstep_4 (-t) hb).1, (hstep_4 (-t) hb).2, hstep_L (-t) ha⟩
  have hgp := hmax _ hmem_plus
  have hgm := hmax _ hmem_minus
  have hid : paraG (z + t • v) + paraG (z + (-t) • v) - 2 * paraG z =
      2 * t ^ 2 * ((v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2) := by
    unfold paraG; simp; ring
  have hsum_sq_le : (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2 ≤ 0 := by
    have hle0 : 2 * t ^ 2 * ((v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2) ≤ 0 := by linarith
    have ht2 : 0 < 2 * t ^ 2 := by positivity
    exact nonpos_of_mul_nonpos_right hle0 ht2
  have hv0_0 : v 0 = 0 := sq_eq_zero_iff.mp (le_antisymm (by linarith [sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3)]) (sq_nonneg _))
  have hv1_0 : v 1 = 0 := sq_eq_zero_iff.mp (le_antisymm (by linarith [sq_nonneg (v 0), sq_nonneg (v 2), sq_nonneg (v 3)]) (sq_nonneg _))
  have hv2_0 : v 2 = 0 := sq_eq_zero_iff.mp (le_antisymm (by linarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 3)]) (sq_nonneg _))
  have hv3_0 : v 3 = 0 := sq_eq_zero_iff.mp (le_antisymm (by linarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]) (sq_nonneg _))
  have hgp4 : paraG (z + t • v) = paraG z - t * v 4 := by
    unfold paraG; simp [hv0_0, hv1_0, hv2_0, hv3_0]; ring
  have hgm4 : paraG (z + (-t) • v) = paraG z + t * v 4 := by
    unfold paraG; simp [hv0_0, hv1_0, hv2_0, hv3_0]; ring
  have htv0 : t * v 4 = 0 := by linarith
  have hv4_0 : v 4 = 0 := (mul_eq_zero.mp htv0).resolve_left ht_pos.ne'
  funext i
  fin_cases i <;> assumption

/- Sublist & Solver Soundness -/

lemma anyViolatedS_sound {rs : List Row5S} {den n0 n1 n2 n3 n4 : SInt} {z : Fin 5 → ℝ}
    (hv : anyViolatedS rs den n0 n1 n2 n3 n4 = true)
    (hden : 0 < toR den)
    (hx0 : toR den * z 0 = toR n0) (hx1 : toR den * z 1 = toR n1)
    (hx2 : toR den * z 2 = toR n2) (hx3 : toR den * z 3 = toR n3)
    (hx4 : toR den * z 4 = toR n4)
    (hfeas : ∀ r ∈ rs, row5Val r z ≤ toR r.d) : False := by
  induction rs with
  | nil => simp [anyViolatedS] at hv
  | cons r rs ih =>
    unfold anyViolatedS at hv
    dsimp only at hv
    cases hs : sLt (sMul r.d den) (match r.a4 with | true => sAdd (evalRow4S r.a0 r.a1 r.a2 r.a3 n0 n1 n2 n3) n4 | false => sSub (evalRow4S r.a0 r.a1 r.a2 r.a3 n0 n1 n2 n3) n4)
    · rw [hs] at hv
      exact ih hv (fun q hq => hfeas q (List.mem_cons_of_mem _ hq))
    · have hlt := (sLt_iff _ _).mp hs
      have hlhs : toR (match r.a4 with | true => sAdd (evalRow4S r.a0 r.a1 r.a2 r.a3 n0 n1 n2 n3) n4 | false => sSub (evalRow4S r.a0 r.a1 r.a2 r.a3 n0 n1 n2 n3) n4) =
          toR den * row5Val r z := by
        cases hb : r.a4 <;> simp [hb, evalRow4S, row5Val, ← hx0, ← hx1, ← hx2, ← hx3, ← hx4] <;> ring
      rw [toR_sMul, hlhs] at hlt
      have hr_le := mul_le_mul_of_nonneg_left (hfeas r List.mem_cons_self) hden.le
      linarith

lemma checkSolZS_sound {mids : List Row5S} {m0 m1 m2 m3 : Row5S} {z : Fin 5 → ℝ}
    (hchk : checkSolZS mids (solve4S (toRow4ZeroS m0) (toRow4ZeroS m1) (toRow4ZeroS m2) (toRow4ZeroS m3)) = true)
    (hz4 : z 4 = 0)
    (hfeas : ∀ r ∈ mids, row5Val r z ≤ toR r.d)
    (ha0 : row5Val m0 z = toR m0.d) (ha1 : row5Val m1 z = toR m1.d)
    (ha2 : row5Val m2 z = toR m2.d) (ha3 : row5Val m3 z = toR m3.d) : False := by
  have h4 (m : Row5S) (hm : row5Val m z = toR m.d) :
      row4Val (toRow4ZeroS m) (z 0) (z 1) (z 2) (z 3) = toR (toRow4ZeroS m).d := by
    simp [toRow4ZeroS, row4Val, row5Val, hz4] at hm ⊢; exact hm
  obtain ⟨e0, e1, e2, e3⟩ := solve4S_cramer (h4 m0 ha0) (h4 m1 ha1) (h4 m2 ha2) (h4 m3 ha3)
  rcases hsol : solve4S (toRow4ZeroS m0) (toRow4ZeroS m1) (toRow4ZeroS m2) (toRow4ZeroS m3) with ⟨den, n0, n1, n2, n3⟩
  rw [hsol] at hchk e0 e1 e2 e3
  dsimp only [checkSolZS] at hchk e0 e1 e2 e3
  cases hd : sLt ⟨0, 0⟩ den
  · rw [hd] at hchk; simp at hchk
  · rw [hd] at hchk
    have hden : 0 < toR den := by simpa using (sLt_iff _ _).mp hd
    exact anyViolatedS_sound hchk hden e0 e1 e2 e3 (by simp [hz4]) hfeas

lemma checkSolTS_sound {r_hi : SInt} {mids : List Row5S} {m0 m1 m2 m3 : Row5S} {z : Fin 5 → ℝ}
    (hchk : checkSolTS r_hi mids (solve4S (toRow4TopS r_hi m0) (toRow4TopS r_hi m1) (toRow4TopS r_hi m2) (toRow4TopS r_hi m3)) = true)
    (hz4 : z 4 = toR r_hi) (hG : 0 ≤ paraG z)
    (hfeas : ∀ r ∈ mids, row5Val r z ≤ toR r.d)
    (ha0 : row5Val m0 z = toR m0.d) (ha1 : row5Val m1 z = toR m1.d)
    (ha2 : row5Val m2 z = toR m2.d) (ha3 : row5Val m3 z = toR m3.d) : False := by
  have h4 (m : Row5S) (hm : row5Val m z = toR m.d) :
      row4Val (toRow4TopS r_hi m) (z 0) (z 1) (z 2) (z 3) = toR (toRow4TopS r_hi m).d := by
    cases hb : m.a4 <;> simp [toRow4TopS, row4Val, row5Val, hz4, hb] at hm ⊢ <;> linarith
  obtain ⟨e0, e1, e2, e3⟩ := solve4S_cramer (h4 m0 ha0) (h4 m1 ha1) (h4 m2 ha2) (h4 m3 ha3)
  rcases hsol : solve4S (toRow4TopS r_hi m0) (toRow4TopS r_hi m1) (toRow4TopS r_hi m2) (toRow4TopS r_hi m3) with ⟨den, n0, n1, n2, n3⟩
  rw [hsol] at hchk e0 e1 e2 e3
  dsimp only [checkSolTS] at hchk e0 e1 e2 e3
  cases hd : sLt ⟨0, 0⟩ den
  · rw [hd] at hchk; simp at hchk
  · rw [hd] at hchk; dsimp only at hchk
    have hden : 0 < toR den := by simpa using (sLt_iff _ _).mp hd
    cases hn : sLt (norm2S n0 n1 n2 n3) (sMul (sMul r_hi den) den)
    · rw [hn] at hchk
      exact anyViolatedS_sound hchk hden e0 e1 e2 e3 (by simp [hz4, mul_comm]) hfeas
    · have hlt := (sLt_iff _ _).mp hn
      simp only [norm2S, toR_sAdd, toR_sMul, ← e0, ← e1, ← e2, ← e3, ← hz4] at hlt
      have hgle : toR den ^ 2 * paraG z < 0 := by unfold paraG; nlinarith
      have hge : 0 ≤ toR den ^ 2 * paraG z := mul_nonneg (sq_nonneg _) hG
      linarith

lemma checkSolMS_sound {r_hi : SInt} {mids : List Row5S} {p r1 r2 r3 r4 : Row5S} {z : Fin 5 → ℝ}
    (hchk : checkSolMS r_hi mids p (solve4S (elimRow4S p r1) (elimRow4S p r2) (elimRow4S p r3) (elimRow4S p r4)) = true)
    (hz : z ∈ polySet r_hi mids) (hG : 0 ≤ paraG z)
    (hp : row5Val p z = toR p.d)
    (ha1 : row5Val r1 z = toR r1.d) (ha2 : row5Val r2 z = toR r2.d)
    (ha3 : row5Val r3 z = toR r3.d) (ha4 : row5Val r4 z = toR r4.d) : False := by
  have helim (r : Row5S) (hr : row5Val r z = toR r.d) :
      row4Val (elimRow4S p r) (z 0) (z 1) (z 2) (z 3) = toR (elimRow4S p r).d := by
    unfold elimRow4S
    cases hb1 : r.a4 <;> cases hb2 : p.a4 <;>
      simp [row4Val, row5Val, hb1, hb2] at hp hr ⊢ <;> linarith
  obtain ⟨e0, e1, e2, e3⟩ := solve4S_cramer (helim r1 ha1) (helim r2 ha2) (helim r3 ha3) (helim r4 ha4)
  rcases hsol : solve4S (elimRow4S p r1) (elimRow4S p r2) (elimRow4S p r3) (elimRow4S p r4) with ⟨den, n0, n1, n2, n3⟩
  rw [hsol] at hchk e0 e1 e2 e3
  dsimp only [checkSolMS] at hchk e0 e1 e2 e3
  cases hd : sLt ⟨0, 0⟩ den
  · rw [hd] at hchk; simp at hchk
  · rw [hd] at hchk; dsimp only at hchk
    have hden : 0 < toR den := by simpa using (sLt_iff _ _).mp hd
    let diff := sSub (sMul p.d den) (evalRow4S p.a0 p.a1 p.a2 p.a3 n0 n1 n2 n3)
    let n4 := sNorm (match p.a4 with | true => diff | false => sNeg diff)
    have he4 : toR den * z 4 = toR n4 := by
      have hp_mul : toR den * row5Val p z = toR den * toR p.d := congrArg (toR den * ·) hp
      cases hpa : p.a4
      · dsimp only [n4, diff, evalRow4S, row5Val] at hp_mul ⊢
        simp only [hpa, Bool.false_eq_true, ↓reduceIte, toR_sNorm, toR_sNeg, toR_sSub, toR_sAdd, toR_sMul,
          ← e0, ← e1, ← e2, ← e3] at hp_mul ⊢
        linarith [show toR den * (toR p.a0 * z 0 + toR p.a1 * z 1 + toR p.a2 * z 2 + toR p.a3 * z 3 + -1 * z 4) =
            toR p.a0 * (toR den * z 0) + toR p.a1 * (toR den * z 1) +
            (toR p.a2 * (toR den * z 2) + toR p.a3 * (toR den * z 3)) - toR den * z 4 by ring,
          mul_comm (toR p.d) (toR den)]
      · dsimp only [n4, diff, evalRow4S, row5Val] at hp_mul ⊢
        simp only [hpa, ↓reduceIte, toR_sNorm, toR_sSub, toR_sAdd, toR_sMul,
          ← e0, ← e1, ← e2, ← e3] at hp_mul ⊢
        linarith [show toR den * (toR p.a0 * z 0 + toR p.a1 * z 1 + toR p.a2 * z 2 + toR p.a3 * z 3 + 1 * z 4) =
            toR p.a0 * (toR den * z 0) + toR p.a1 * (toR den * z 1) +
            (toR p.a2 * (toR den * z 2) + toR p.a3 * (toR den * z 3)) + toR den * z 4 by ring,
          mul_comm (toR p.d) (toR den)]
    cases hc1 : sLt n4 ⟨0, 0⟩
    · rw [hc1] at hchk
      cases hc2 : sLt (sMul r_hi den) n4
      · rw [hc2] at hchk
        cases hc3 : sLt (norm2S n0 n1 n2 n3) (sMul n4 den)
        · rw [hc3] at hchk
          exact anyViolatedS_sound hchk hden e0 e1 e2 e3 he4 hz.2.2
        · have hlt := (sLt_iff _ _).mp hc3
          simp only [norm2S, toR_sAdd, toR_sMul, ← e0, ← e1, ← e2, ← e3, ← he4] at hlt
          have hgle : toR den ^ 2 * paraG z < 0 := by unfold paraG; nlinarith
          have hge : 0 ≤ toR den ^ 2 * paraG z := mul_nonneg (sq_nonneg _) hG
          linarith
      · have hlt := (sLt_iff _ _).mp hc2
        rw [toR_sMul, ← he4] at hlt
        have hhi := mul_le_mul_of_nonneg_left hz.2.1 hden.le
        linarith
    · have hlt := (sLt_iff _ _).mp hc1
      rw [toR_zero, ← he4] at hlt
      have hlo := mul_nonneg hden.le hz.1
      linarith

open scoped List

lemma ch1Z_sub {rem : List Row5S} {u0 u1 u2 v3 : Row4S} {us : List Row4S}
    (h : ch1Z rem u0 u1 u2 us = true) (hs : [v3] <+ us) :
    checkSolZS rem (solve4S u0 u1 u2 v3) = true := by
  induction us with
  | nil => cases hs
  | cons x xs ih =>
    simp only [ch1Z, Bool.and_eq_true] at h
    cases hs with
    | cons _ h' => exact ih h.2 h'
    | cons_cons _ _ => exact h.1

lemma ch2Z_sub {rem : List Row5S} {u0 u1 v2 v3 : Row4S} {us : List Row4S}
    (h : ch2Z rem u0 u1 us = true) (hs : [v2, v3] <+ us) :
    checkSolZS rem (solve4S u0 u1 v2 v3) = true := by
  induction us with
  | nil => cases hs
  | cons x xs ih =>
    simp only [ch2Z, Bool.and_eq_true] at h
    cases hs with
    | cons _ h' => exact ih h.2 h'
    | cons_cons _ h' => exact ch1Z_sub h.1 h'

lemma ch3Z_sub {rem : List Row5S} {u0 v1 v2 v3 : Row4S} {us : List Row4S}
    (h : ch3Z rem u0 us = true) (hs : [v1, v2, v3] <+ us) :
    checkSolZS rem (solve4S u0 v1 v2 v3) = true := by
  induction us with
  | nil => cases hs
  | cons x xs ih =>
    simp only [ch3Z, Bool.and_eq_true] at h
    cases hs with
    | cons _ h' => exact ih h.2 h'
    | cons_cons _ h' => exact ch2Z_sub h.1 h'

lemma ch4Z_sub {rem : List Row5S} {v0 v1 v2 v3 : Row4S} {us : List Row4S}
    (h : ch4Z rem us = true) (hs : [v0, v1, v2, v3] <+ us) :
    checkSolZS rem (solve4S v0 v1 v2 v3) = true := by
  induction us with
  | nil => cases hs
  | cons x xs ih =>
    simp only [ch4Z, Bool.and_eq_true] at h
    cases hs with
    | cons _ h' => exact ih h.2 h'
    | cons_cons _ h' => exact ch3Z_sub h.1 h'

lemma ch1T_sub {r_hi : SInt} {rem : List Row5S} {u0 u1 u2 v3 : Row4S} {us : List Row4S}
    (h : ch1T r_hi rem u0 u1 u2 us = true) (hs : [v3] <+ us) :
    checkSolTS r_hi rem (solve4S u0 u1 u2 v3) = true := by
  induction us with
  | nil => cases hs
  | cons x xs ih =>
    simp only [ch1T, Bool.and_eq_true] at h
    cases hs with
    | cons _ h' => exact ih h.2 h'
    | cons_cons _ _ => exact h.1

lemma ch2T_sub {r_hi : SInt} {rem : List Row5S} {u0 u1 v2 v3 : Row4S} {us : List Row4S}
    (h : ch2T r_hi rem u0 u1 us = true) (hs : [v2, v3] <+ us) :
    checkSolTS r_hi rem (solve4S u0 u1 v2 v3) = true := by
  induction us with
  | nil => cases hs
  | cons x xs ih =>
    simp only [ch2T, Bool.and_eq_true] at h
    cases hs with
    | cons _ h' => exact ih h.2 h'
    | cons_cons _ h' => exact ch1T_sub h.1 h'

lemma ch3T_sub {r_hi : SInt} {rem : List Row5S} {u0 v1 v2 v3 : Row4S} {us : List Row4S}
    (h : ch3T r_hi rem u0 us = true) (hs : [v1, v2, v3] <+ us) :
    checkSolTS r_hi rem (solve4S u0 v1 v2 v3) = true := by
  induction us with
  | nil => cases hs
  | cons x xs ih =>
    simp only [ch3T, Bool.and_eq_true] at h
    cases hs with
    | cons _ h' => exact ih h.2 h'
    | cons_cons _ h' => exact ch2T_sub h.1 h'

lemma ch4T_sub {r_hi : SInt} {rem : List Row5S} {v0 v1 v2 v3 : Row4S} {us : List Row4S}
    (h : ch4T r_hi rem us = true) (hs : [v0, v1, v2, v3] <+ us) :
    checkSolTS r_hi rem (solve4S v0 v1 v2 v3) = true := by
  induction us with
  | nil => cases hs
  | cons x xs ih =>
    simp only [ch4T, Bool.and_eq_true] at h
    cases hs with
    | cons _ h' => exact ih h.2 h'
    | cons_cons _ h' => exact ch3T_sub h.1 h'

lemma ch1M_sub {r_hi : SInt} {mids : List Row5S} {p r1 r2 r3 v4 : Row5S} {rs : List Row5S}
    (h : ch1M r_hi mids p r1 r2 r3 rs = true) (hs : [v4] <+ rs) :
    checkSolMS r_hi mids p (solve4S (elimRow4S p r1) (elimRow4S p r2) (elimRow4S p r3) (elimRow4S p v4)) = true := by
  induction rs with
  | nil => cases hs
  | cons x xs ih =>
    simp only [ch1M, Bool.and_eq_true] at h
    cases hs with
    | cons _ h' => exact ih h.2 h'
    | cons_cons _ _ => exact h.1

lemma ch2M_sub {r_hi : SInt} {mids : List Row5S} {p r1 r2 v3 v4 : Row5S} {rs : List Row5S}
    (h : ch2M r_hi mids p r1 r2 rs = true) (hs : [v3, v4] <+ rs) :
    checkSolMS r_hi mids p (solve4S (elimRow4S p r1) (elimRow4S p r2) (elimRow4S p v3) (elimRow4S p v4)) = true := by
  induction rs with
  | nil => cases hs
  | cons x xs ih =>
    simp only [ch2M, Bool.and_eq_true] at h
    cases hs with
    | cons _ h' => exact ih h.2 h'
    | cons_cons _ h' => exact ch1M_sub h.1 h'

lemma ch3M_sub {r_hi : SInt} {mids : List Row5S} {p r1 v2 v3 v4 : Row5S} {rs : List Row5S}
    (h : ch3M r_hi mids p r1 rs = true) (hs : [v2, v3, v4] <+ rs) :
    checkSolMS r_hi mids p (solve4S (elimRow4S p r1) (elimRow4S p v2) (elimRow4S p v3) (elimRow4S p v4)) = true := by
  induction rs with
  | nil => cases hs
  | cons x xs ih =>
    simp only [ch3M, Bool.and_eq_true] at h
    cases hs with
    | cons _ h' => exact ih h.2 h'
    | cons_cons _ h' => exact ch2M_sub h.1 h'

lemma ch4M_sub {r_hi : SInt} {mids : List Row5S} {p v1 v2 v3 v4 : Row5S} {rs : List Row5S}
    (h : ch4M r_hi mids p rs = true) (hs : [v1, v2, v3, v4] <+ rs) :
    checkSolMS r_hi mids p (solve4S (elimRow4S p v1) (elimRow4S p v2) (elimRow4S p v3) (elimRow4S p v4)) = true := by
  induction rs with
  | nil => cases hs
  | cons x xs ih =>
    simp only [ch4M, Bool.and_eq_true] at h
    cases hs with
    | cons _ h' => exact ih h.2 h'
    | cons_cons _ h' => exact ch3M_sub h.1 h'

lemma ch5M_sub {r_hi : SInt} {mids : List Row5S} {v0 v1 v2 v3 v4 : Row5S} {rs : List Row5S}
    (h : ch5M r_hi mids rs = true) (hs : [v0, v1, v2, v3, v4] <+ rs) :
    checkSolMS r_hi mids v0 (solve4S (elimRow4S v0 v1) (elimRow4S v0 v2) (elimRow4S v0 v3) (elimRow4S v0 v4)) = true := by
  induction rs with
  | nil => cases hs
  | cons x xs ih =>
    simp only [ch5M, Bool.and_eq_true] at h
    cases hs with
    | cons _ h' => exact ih h.2 h'
    | cons_cons _ h' => exact ch4M_sub h.1 h'

/- Master Box Soundness Theorem -/

theorem checkBoxFull_sound
    {r_hi : Int} {a0 a1 a2 : Int × Int × Int × Int} {b0 b1 b2 : Int}
    {c0 c1 c2 c3 c4 c5 c6 c7 : Int × Int × Int × Int}
    {si0 si1 si2 si3 si4 : Nat} {sw0 sw1 sw2 sw3 sw4 : Int}
    (hchk : checkBoxFull r_hi a0 a1 a2 b0 b1 b2 c0 c1 c2 c3 c4 c5 c6 c7 si0 si1 si2 si3 si4 sw0 sw1 sw2 sw3 sw4 = true)
    (z₀ : Fin 5 → ℝ)
    (hz₀ : z₀ ∈ polySet (ofInt r_hi)
      (mkRowAS a0 b0 :: mkRowAS a1 b1 :: mkRowAS a2 b2 ::
        [mkRowCS c0, mkRowCS c1, mkRowCS c2, mkRowCS c3, mkRowCS c4, mkRowCS c5, mkRowCS c6, mkRowCS c7]))
    (hG₀ : 0 ≤ paraG z₀) : False := by
  let r_hiS := ofInt r_hi
  let r2 := mkRowAS a0 b0; let r3 := mkRowAS a1 b1; let r4 := mkRowAS a2 b2
  let cs : List Row5S := [mkRowCS c0, mkRowCS c1, mkRowCS c2, mkRowCS c3, mkRowCS c4, mkRowCS c5, mkRowCS c6, mkRowCS c7]
  let mids := r2 :: r3 :: r4 :: cs
  unfold checkBoxFull at hchk
  simp only [Bool.and_eq_true] at hchk
  rcases hchk with ⟨hr_hi, ha0_3, ha1_3, ha2_3, ha1_2, ha2_2, hsimp, hokZ, hokT, hokM⟩
  have hcomp := polySet_isCompact r_hiS hr_hi r2 r3 r4 c0 c1 c2 c3 c4 c5 c6 c7 si0 si1 si2 si3 si4 sw0 sw1 sw2 sw3 sw4 hsimp
  have hG_cont : Continuous paraG := by unfold paraG; fun_prop
  obtain ⟨z, hz, hmax⟩ := hcomp.exists_isMaxOn ⟨z₀, hz₀⟩ hG_cont.continuousOn
  have hGz : 0 ≤ paraG z := hG₀.trans (hmax hz₀)
  let actPred (r : Row5S) : Bool := @decide (row5Val r z = toR r.d) (Classical.propDecidable _)
  let act := mids.filter actPred
  have hact_sub : act <+ mids := List.filter_sublist
  have hact_eq : ∀ r ∈ act, row5Val r z = toR r.d := by
    intro r hr
    have := (List.mem_filter.mp hr).2
    simpa [actPred] using this
  have hmem_act : ∀ r ∈ mids, row5Val r z = toR r.d → r ∈ act := by
    intro r hrm heq
    exact List.mem_filter.mpr ⟨hrm, by simpa [actPred] using heq⟩
  -- Helper for boundary 4-tuple selection (handles degenerate [r2, r3, r4, cj] when a0.2.2.1 = 0!):
  have hbound_4 : (z 4 = 0 ∨ z 4 = toR r_hiS) →
      ∃ m0 m1 m2 m3 : Row5S, [m0, m1, m2, m3] <+ act ∧
        (sEq (ofInt a0.2.2.1) ⟨0, 0⟩ = true → ¬ (m0 = r2 ∧ m1 = r3 ∧ m2 = r4)) := by
    intro hz4_bd
    have hno_ker4 : ∀ x : Fin 4 → ℝ, (∀ r ∈ act, row4Lin r x = 0) → x = 0 := by
      intro x hx
      let v : Fin 5 → ℝ := fun i =>
        match i with | 0 => x 0 | 1 => x 1 | 2 => x 2 | 3 => x 3 | 4 => 0
      have hv_eq0 : v = 0 := by
        refine ker_active_eq_zero hz hmax (fun _ => rfl) (fun _ => rfl) (fun r hrm heq => ?_)
        have hrx := hx r (hmem_act r hrm heq)
        rw [row4Lin_apply] at hrx
        cases hb : r.a4 <;> simp [row5Val, row4Val, v, hb] at hrx ⊢ <;> linarith
      funext i
      fin_cases i
      · simpa [v] using congrFun hv_eq0 0
      · simpa [v] using congrFun hv_eq0 1
      · simpa [v] using congrFun hv_eq0 2
      · simpa [v] using congrFun hv_eq0 3
    have hlen4 : 4 ≤ act.length := by
      by_contra hlt
      rw [not_le] at hlt
      obtain ⟨x, hx_ne, hx_ker⟩ := exists_nonzero_in_common_ker (act.map row4Lin) (by simpa using hlt)
      exact hx_ne (hno_ker4 x (fun r hr => hx_ker (row4Lin r) (List.mem_map_of_mem hr)))
    rcases hact_def : act with _ | ⟨q0, _ | ⟨q1, _ | ⟨q2, _ | ⟨q3, qrest⟩⟩⟩⟩
    · simp [hact_def] at hlen4
    · simp [hact_def] at hlen4
    · simp [hact_def] at hlen4
    · simp [hact_def] at hlen4
    · rcases qrest with _ | ⟨q4, qtail⟩
      · -- act has exact length 4: [q0, q1, q2, q3]
        refine ⟨q0, q1, q2, q3, by simp, fun ha_zero hdeg => ?_⟩
        rcases hdeg with ⟨rfl, rfl, rfl⟩
        -- Here act = [r2, r3, r4, q3] and a0.2.2.1 = 0!
        have ha02 : (a0.2.2.1 : ℝ) = 0 := by simpa using (sEq_iff _ _).mp ha_zero
        have ha12 : (a1.2.2.1 : ℝ) = 0 := by
          have := (sEq_iff _ _).mp ha1_2; simp only [toR_ofInt] at this; linarith [ha02]
        have ha22 : (a2.2.2.1 : ℝ) = 0 := by
          have := (sEq_iff _ _).mp ha2_2; simp only [toR_ofInt] at this; linarith [ha02]
        have ha03 : (a0.2.2.2 : ℝ) = 0 := by simpa using (sEq_iff _ _).mp ha0_3
        have ha13 : (a1.2.2.2 : ℝ) = 0 := by simpa using (sEq_iff _ _).mp ha1_3
        have ha23 : (a2.2.2.2 : ℝ) = 0 := by simpa using (sEq_iff _ _).mp ha2_3
        let eqs3 : List ((Fin 4 → ℝ) →ₗ[ℝ] ℝ) := [LinearMap.proj 0, LinearMap.proj 1, row4Lin q3]
        obtain ⟨x, hx_ne, hx_ker⟩ := exists_nonzero_in_common_ker eqs3 (by simp [eqs3])
        have hx0 : x 0 = 0 := hx_ker (LinearMap.proj 0) (by simp [eqs3])
        have hx1 : x 1 = 0 := hx_ker (LinearMap.proj 1) (by simp [eqs3])
        have hxq3 : row4Lin q3 x = 0 := hx_ker (row4Lin q3) (by simp [eqs3])
        refine hx_ne (hno_ker4 x (fun r hr => ?_))
        rw [hact_def] at hr
        rcases List.mem_cons.mp hr with rfl | hr1
        · simp [row4Lin, r2, mkRowAS, hx0, hx1, ha02, ha03]
        · rcases List.mem_cons.mp hr1 with rfl | hr2
          · simp [row4Lin, r3, mkRowAS, hx0, hx1, ha12, ha13]
          · rcases List.mem_cons.mp hr2 with rfl | hr3
            · simp [row4Lin, r4, mkRowAS, hx0, hx1, ha22, ha23]
            · rcases List.mem_cons.mp hr3 with rfl | hr4
              · exact hxq3
              · cases hr4
      · -- act has ≥ 5 elements: q0 :: q1 :: q2 :: q3 :: q4 :: qtail!
        -- Notice q0 :: q1 :: q2 :: q3 :: q4 :: qtail <+ r2 :: r3 :: r4 :: cs,
        -- so if q0=r2, q1=r3, q2=r4, picking [q0, q1, q3, q4] avoids m2=r4 unless q3=r4!
        -- Even better: q2 :: q3 :: q4 :: qtail <+ r4 :: cs -> q3 :: q4 :: qtail <+ cs,
        -- wait: can q3 = r4 in Lean without NoDup? Wait: q0..q4 is a sublist of r2 :: r3 :: r4 :: cs!
        -- Let's check: in r2 :: r3 :: r4 :: cs, can r4 appear in cs? r4.a4 = true, while every x ∈ cs has x.a4 = false!!
        -- YES!! r2.a4 = r3.a4 = r4.a4 = true, whereas ∀ c ∈ cs, c.a4 = false!!
        have h_sub5 : [q0, q1, q2, q3, q4] <+ mids := by
          have hp : [q0, q1, q2, q3, q4] <+ q0 :: q1 :: q2 :: q3 :: q4 :: qtail := by
            repeat apply List.Sublist.cons_cons
            exact List.nil_sublist _
          rw [← hact_def] at hp
          exact hp.trans hact_sub
        have hq3_a4 : q3.a4 = false := by
          -- Any 5-element sublist of r2 :: r3 :: r4 :: cs has its 4th and 5th elements in cs!
          change [q0, q1, q2, q3, q4] <+ r2 :: r3 :: r4 :: cs at h_sub5
          have hcs_false : ∀ c ∈ cs, c.a4 = false := by
            intro c hc; simp [cs, mkRowCS] at hc
            rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
          have h3_in_cs : q3 ∈ cs := by
            cases h_sub5 with
            | cons _ h1 =>
              cases h1 with
              | cons _ h2 =>
                cases h2 with
                | cons _ h3 => exact h3.subset (by simp)
                | cons_cons _ h3 => exact h3.subset (by simp)
              | cons_cons _ h2 =>
                cases h2 with
                | cons _ h3 => exact h3.subset (by simp)
                | cons_cons _ h3 => exact h3.subset (by simp)
            | cons_cons _ h1 =>
              cases h1 with
              | cons _ h2 =>
                cases h2 with
                | cons _ h3 => exact h3.subset (by simp)
                | cons_cons _ h3 => exact h3.subset (by simp)
              | cons_cons _ h2 =>
                cases h2 with
                | cons _ h3 => exact h3.subset (by simp)
                | cons_cons _ h3 => exact h3.subset (by simp)
          exact hcs_false q3 h3_in_cs
        refine ⟨q0, q1, q3, q4, ?_, fun _ hdeg => ?_⟩
        · apply List.Sublist.cons_cons; apply List.Sublist.cons_cons; apply List.Sublist.cons
          apply List.Sublist.cons_cons; apply List.Sublist.cons_cons; exact List.nil_sublist _
        · have hr4_true : r4.a4 = true := rfl
          rw [hdeg.2.2] at hq3_a4; simp [hr4_true] at hq3_a4
  by_cases hz4_zero : z 4 = 0
  · obtain ⟨m0, m1, m2, m3, hsub_act, hnondeg⟩ := hbound_4 (Or.inl hz4_zero)
    have hsub_mids : [m0, m1, m2, m3] <+ r2 :: r3 :: r4 :: cs := hsub_act.trans hact_sub
    have ha_m (m : Row5S) (hm : m ∈ [m0, m1, m2, m3]) : row5Val m z = toR m.d :=
      hact_eq m (hsub_act.subset hm)
    rcases hokZ with ⟨hz123, hz12, hz13, hz23, hz1, hz2, hz3, hz0⟩
    have hsol_true : checkSolZS mids (solve4S (toRow4ZeroS m0) (toRow4ZeroS m1) (toRow4ZeroS m2) (toRow4ZeroS m3)) = true := by
      cases hsub_mids with
      | cons_cons _ h1 =>
        cases h1 with
        | cons_cons _ h2 =>
          cases h2 with
          | cons_cons _ h3 =>
            cases hs_eq : sEq (ofInt a0.2.2.1) ⟨0, 0⟩
            · rw [hs_eq] at hz123
              exact ch1Z_sub hz123 (h3.map toRow4ZeroS)
            · exact False.elim (hnondeg hs_eq ⟨rfl, rfl, rfl⟩)
          | cons _ h3 => exact ch2Z_sub hz12 (h3.map toRow4ZeroS)
        | cons _ h2 =>
          cases h2 with
          | cons_cons _ h3 => exact ch2Z_sub hz13 (h3.map toRow4ZeroS)
          | cons _ h3 => exact ch3Z_sub hz1 (h3.map toRow4ZeroS)
      | cons _ h1 =>
        cases h1 with
        | cons_cons _ h2 =>
          cases h2 with
          | cons_cons _ h3 => exact ch2Z_sub hz23 (h3.map toRow4ZeroS)
          | cons _ h3 => exact ch3Z_sub hz2 (h3.map toRow4ZeroS)
        | cons _ h2 =>
          cases h2 with
          | cons_cons _ h3 => exact ch3Z_sub hz3 (h3.map toRow4ZeroS)
          | cons _ h3 => exact ch4Z_sub hz0 (h3.map toRow4ZeroS)
    exact checkSolZS_sound hsol_true hz4_zero hz.2.2
      (ha_m m0 (by simp)) (ha_m m1 (by simp)) (ha_m m2 (by simp)) (ha_m m3 (by simp))
  · by_cases hz4_top : z 4 = toR r_hiS
    · obtain ⟨m0, m1, m2, m3, hsub_act, hnondeg⟩ := hbound_4 (Or.inr hz4_top)
      have hsub_mids : [m0, m1, m2, m3] <+ r2 :: r3 :: r4 :: cs := hsub_act.trans hact_sub
      have ha_m (m : Row5S) (hm : m ∈ [m0, m1, m2, m3]) : row5Val m z = toR m.d :=
        hact_eq m (hsub_act.subset hm)
      rcases hokT with ⟨ht123, ht12, ht13, ht23, ht1, ht2, ht3, ht0⟩
      have hsol_true : checkSolTS r_hiS mids (solve4S (toRow4TopS r_hiS m0) (toRow4TopS r_hiS m1) (toRow4TopS r_hiS m2) (toRow4TopS r_hiS m3)) = true := by
        cases hsub_mids with
        | cons_cons _ h1 =>
          cases h1 with
          | cons_cons _ h2 =>
            cases h2 with
            | cons_cons _ h3 =>
              cases hs_eq : sEq (ofInt a0.2.2.1) ⟨0, 0⟩
              · rw [hs_eq] at ht123
                exact ch1T_sub ht123 (h3.map (toRow4TopS r_hiS))
              · exact False.elim (hnondeg hs_eq ⟨rfl, rfl, rfl⟩)
            | cons _ h3 => exact ch2T_sub ht12 (h3.map (toRow4TopS r_hiS))
          | cons _ h2 =>
            cases h2 with
            | cons_cons _ h3 => exact ch2T_sub ht13 (h3.map (toRow4TopS r_hiS))
            | cons _ h3 => exact ch3T_sub ht1 (h3.map (toRow4TopS r_hiS))
        | cons _ h1 =>
          cases h1 with
          | cons_cons _ h2 =>
            cases h2 with
            | cons_cons _ h3 => exact ch2T_sub ht23 (h3.map (toRow4TopS r_hiS))
            | cons _ h3 => exact ch3T_sub ht2 (h3.map (toRow4TopS r_hiS))
          | cons _ h2 =>
            cases h2 with
            | cons_cons _ h3 => exact ch3T_sub ht3 (h3.map (toRow4TopS r_hiS))
            | cons _ h3 => exact ch4T_sub ht0 (h3.map (toRow4TopS r_hiS))
      exact checkSolTS_sound hsol_true hz4_top hGz hz.2.2
        (ha_m m0 (by simp)) (ha_m m1 (by simp)) (ha_m m2 (by simp)) (ha_m m3 (by simp))
    · -- Interior case: z 4 ≠ 0 and z 4 ≠ toR r_hiS -> 5 ≤ act.length!
      have hlen5 : 5 ≤ act.length := by
        by_contra hlt
        rw [not_le] at hlt
        obtain ⟨v, hv_ne, hv_ker⟩ := exists_nonzero_in_common_ker (act.map row5Lin) (by simpa using hlt)
        refine hv_ne (ker_active_eq_zero hz hmax (fun h => absurd h hz4_zero) (fun h => absurd h hz4_top) ?_)
        intro r hrm heq
        have := hv_ker (row5Lin r) (List.mem_map_of_mem (hmem_act r hrm heq))
        rwa [row5Lin_apply] at this
      rcases hact_def : act with _ | ⟨p, _ | ⟨q1, _ | ⟨q2, _ | ⟨q3, _ | ⟨q4, qtail⟩⟩⟩⟩⟩
      · simp [hact_def] at hlen5
      · simp [hact_def] at hlen5
      · simp [hact_def] at hlen5
      · simp [hact_def] at hlen5
      · simp [hact_def] at hlen5
      · have hsub_act : [p, q1, q2, q3, q4] <+ act := by
          rw [hact_def]
          repeat apply List.Sublist.cons_cons
          exact List.nil_sublist _
        have hsub_mids : [p, q1, q2, q3, q4] <+ mids := hsub_act.trans hact_sub
        have ha_m (m : Row5S) (hm : m ∈ [p, q1, q2, q3, q4]) : row5Val m z = toR m.d :=
          hact_eq m (hsub_act.subset hm)
        have hsol_true := ch5M_sub hokM hsub_mids
        exact checkSolMS_sound hsol_true hz hGz
          (ha_m p (by simp)) (ha_m q1 (by simp)) (ha_m q2 (by simp)) (ha_m q3 (by simp)) (ha_m q4 (by simp))


/- Glue Section: Acute Contact Triangle, Enclosure Tree Soundness, and OMA.solution -/

def sLe (x y : SInt) : Bool :=
  Nat.ble (Nat.add x.p y.n) (Nat.add y.p x.n)

lemma sLe_iff (x y : SInt) : sLe x y = true ↔ toR x ≤ toR y := by
  unfold sLe toR
  rw [Nat.ble_eq]
  simp only [Nat.add_eq]
  constructor
  · intro h
    have hr : ((x.p + y.n : ℕ) : ℝ) ≤ ((y.p + x.n : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at hr; linarith
  · intro h
    have hr : (((x.p : ℤ) - (x.n : ℤ) : ℤ) : ℝ) ≤ (((y.p : ℤ) - (y.n : ℤ) : ℤ) : ℝ) := by
      push_cast; exact h
    have hz : (x.p : ℤ) - (x.n : ℤ) ≤ (y.p : ℤ) - (y.n : ℤ) := by exact_mod_cast hr
    omega

theorem inner_eq_sum {ι : Type*} [Fintype ι]
    (n x : EuclideanSpace ℝ ι) : inner ℝ n x = ∑ i, n i * x i := by
  simp [PiLp.inner_apply, mul_comm]

theorem e4_norm_sq (v : E4) : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_sum, Fin.sum_univ_four]
  ring

theorem e4_dist_sq (u v : E4) :
    dist u v ^ 2 = (u 0 - v 0) ^ 2 + (u 1 - v 1) ^ 2 + (u 2 - v 2) ^ 2 + (u 3 - v 3) ^ 2 := by
  rw [dist_eq_norm, e4_norm_sq]
  simp

lemma cs4_sq (u0 u1 u2 u3 v0 v1 v2 v3 : ℝ) :
    (u0 * v0 + u1 * v1 + u2 * v2 + u3 * v3) ^ 2 ≤
      (u0 ^ 2 + u1 ^ 2 + u2 ^ 2 + u3 ^ 2) * (v0 ^ 2 + v1 ^ 2 + v2 ^ 2 + v3 ^ 2) := by
  have h : 0 ≤ (u0 * v1 - u1 * v0) ^ 2 + (u0 * v2 - u2 * v0) ^ 2 + (u0 * v3 - u3 * v0) ^ 2 +
               (u1 * v2 - u2 * v1) ^ 2 + (u1 * v3 - u3 * v1) ^ 2 + (u2 * v3 - u3 * v2) ^ 2 := by
    positivity
  have hid : (u0 ^ 2 + u1 ^ 2 + u2 ^ 2 + u3 ^ 2) * (v0 ^ 2 + v1 ^ 2 + v2 ^ 2 + v3 ^ 2) -
      (u0 * v0 + u1 * v1 + u2 * v2 + u3 * v3) ^ 2 =
      (u0 * v1 - u1 * v0) ^ 2 + (u0 * v2 - u2 * v0) ^ 2 + (u0 * v3 - u3 * v0) ^ 2 +
      (u1 * v2 - u2 * v1) ^ 2 + (u1 * v3 - u3 * v1) ^ 2 + (u2 * v3 - u3 * v2) ^ 2 := by ring
  linarith

lemma triangle_jung_upper {P : Fin 3 → E4} {μ : Fin 3 → ℝ} {c_Δ : E4} {τ : ℝ}
    (hPdiam : ∀ i j, dist (P i) (P j) ≤ 1)
    (hμpos : ∀ i, 0 < μ i) (hμsum : ∑ i, μ i = 1) (hμbary : ∑ i, μ i • P i = c_Δ)
    (hτ_nn : 0 ≤ τ) (hτdist : ∀ i, ‖P i - c_Δ‖ ^ 2 = τ) :
    τ ≤ 1 / 3 := by
  let q (i : Fin 3) : E4 := P i - c_Δ
  let R' : ℝ := Real.sqrt τ
  have hq_norm (i : Fin 3) : ‖q i‖ = R' := by
    dsimp [q, R']
    rw [← Real.sqrt_sq (norm_nonneg _), hτdist i]
  have hq_bary : ∑ i, μ i • q i = 0 := by
    have : ∑ i : Fin 3, μ i • (P i - c_Δ) = (∑ i, μ i • P i) - (∑ i, μ i) • c_Δ := by
      simp [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
    rw [hμbary, hμsum, one_smul, sub_self] at this
    exact this
  have hq_diam (i j : Fin 3) : dist (q i) (q j) ≤ 1 := by
    have : q i - q j = P i - P j := by dsimp [q]; abel
    rw [dist_eq_norm, this, ← dist_eq_norm]
    exact hPdiam i j
  have hj := contact_jung_bound (by decide : 0 < 3) q μ R' hq_norm
    (fun i => (hμpos i).le) hμsum hq_bary hq_diam
  rw [Real.sq_sqrt hτ_nn] at hj
  linarith

theorem exists_acute_contact_triangle {S : Set E4}
    (hS : IsCompact S) (hSne : S.Nonempty) (hdiam : diam S = 1)
    (hmin : ∀ d : E4, radiusAt S 0 ≤ radiusAt S d)
    (hr_lo : 16 / 49 < (radiusAt S 0) ^ 2) :
    let r := (radiusAt S 0) ^ 2
    ∃ (P : Fin 3 → E4) (μ : Fin 3 → ℝ) (c_Δ : E4) (τ : ℝ),
      (∀ i, P i ∈ S) ∧ AffineIndependent ℝ P ∧
      (∀ i, ‖P i‖ ^ 2 = r) ∧ (∀ i j, dist (P i) (P j) ≤ 1) ∧
      (∀ i, 0 < μ i) ∧ (∑ i, μ i = 1) ∧ (∑ i, μ i • P i = c_Δ) ∧
      (∀ i, ‖P i - c_Δ‖ ^ 2 = τ) ∧ (5 / 6 : ℝ) * r ≤ τ ∧ τ ≤ 1 / 3 := by
  let R := radiusAt S 0
  let r := R ^ 2
  have hr_pos : 0 < r := by linarith
  have hSdiam (x : E4) (hx : x ∈ S) (y : E4) (hy : y ∈ S) : dist x y ≤ 1 :=
    hdiam ▸ dist_le_diam_of_mem hS.isBounded hx hy
  obtain ⟨k, hk1, hk5, p, w, hpS, haff, hwpos, hwsum, hwbary⟩ :=
    exists_positive_contact_simplex hS hSne hmin
  have hk_cases : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
  rcases hk_cases with rfl | rfl | rfl | rfl | rfl
  · have hj := contact_jung_bound (by decide) p w R (fun i => (hpS i).2)
      (fun i => (hwpos i).le) hwsum hwbary (fun i j => hSdiam _ (hpS i).1 _ (hpS j).1)
    dsimp [R] at hj; norm_num at hj; rw [hj] at hr_lo; norm_num at hr_lo
  · have hj := contact_jung_bound (by decide) p w R (fun i => (hpS i).2)
      (fun i => (hwpos i).le) hwsum hwbary (fun i j => hSdiam _ (hpS i).1 _ (hpS j).1)
    dsimp [R] at hj; norm_num at hj; linarith
  · have hPnorm (i : Fin 3) : ‖p i‖ ^ 2 = r := by dsimp [r, R]; rw [(hpS i).2]
    have hPdiam (i j : Fin 3) : dist (p i) (p j) ≤ 1 := hSdiam _ (hpS i).1 _ (hpS j).1
    have hτdist (i : Fin 3) : ‖p i - 0‖ ^ 2 = r := by simp [hPnorm i]
    refine ⟨p, w, 0, r, fun i => (hpS i).1, haff, hPnorm, hPdiam, hwpos, hwsum, hwbary,
      hτdist, by linarith, triangle_jung_upper hPdiam hwpos hwsum hwbary hr_pos.le hτdist⟩
  · have hpnorm2 (i : Fin 4) : ‖p i‖ ^ 2 = r := by dsimp [r, R]; rw [(hpS i).2]
    obtain ⟨i₁, c_Δ, μ, hμpos, hμsum, hμbary, hcdist, hclo⟩ :=
      drop_one_contact (n := 1) hr_pos hpnorm2 haff hwpos hwsum hwbary
    let P : Fin 3 → E4 := p ∘ i₁.succAbove
    let τ : ℝ := r - ‖c_Δ‖ ^ 2
    have hPaff : AffineIndependent ℝ P :=
      haff.comp_embedding ⟨i₁.succAbove, i₁.succAbove_right_injective⟩
    have hPS (i : Fin 3) : P i ∈ S := (hpS (i₁.succAbove i)).1
    have hPnorm (i : Fin 3) : ‖P i‖ ^ 2 = r := hpnorm2 (i₁.succAbove i)
    have hPdiam (i j : Fin 3) : dist (P i) (P j) ≤ 1 := hSdiam _ (hPS i) _ (hPS j)
    have hτ_lo : (5 / 6 : ℝ) * r ≤ τ := by dsimp [τ]; norm_num at hclo; linarith
    have hτ_nn : 0 ≤ τ := by linarith
    exact ⟨P, μ, c_Δ, τ, hPS, hPaff, hPnorm, hPdiam, hμpos, hμsum, hμbary,
      hcdist, hτ_lo, triangle_jung_upper hPdiam hμpos hμsum hμbary hτ_nn hcdist⟩
  · have hpnorm2 (i : Fin 5) : ‖p i‖ ^ 2 = r := by dsimp [r, R]; rw [(hpS i).2]
    obtain ⟨i₁, c₁, μ₁, hμ₁pos, hμ₁sum, hμ₁bary, hc₁dist, hc₁lo⟩ :=
      drop_one_contact (n := 2) hr_pos hpnorm2 haff hwpos hwsum hwbary
    let q₁ : Fin 4 → E4 := p ∘ i₁.succAbove
    let ρ₁ : ℝ := r - ‖c₁‖ ^ 2
    have hρ₁_lo : (15 / 16 : ℝ) * r ≤ ρ₁ := by dsimp [ρ₁]; norm_num at hc₁lo; linarith
    have hρ₁_pos : 0 < ρ₁ := by linarith
    let q₁' : Fin 4 → E4 := fun k => q₁ k - c₁
    have haff_q₁ : AffineIndependent ℝ q₁ :=
      haff.comp_embedding ⟨i₁.succAbove, i₁.succAbove_right_injective⟩
    have haff₁ : AffineIndependent ℝ q₁' := by
      intro s wt hws hwv
      rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ hws (0 : E4)] at hwv
      have hwv0 : s.weightedVSub q₁ wt = 0 := by
        rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ hws c₁]
        simpa [Finset.weightedVSubOfPoint_apply, vsub_eq_sub, q₁'] using hwv
      exact haff_q₁ s wt hws hwv0
    have hbary₁ : ∑ k, μ₁ k • q₁' k = 0 := by
      have : ∑ k : Fin 4, μ₁ k • (q₁ k - c₁) = (∑ k, μ₁ k • q₁ k) - (∑ k, μ₁ k) • c₁ := by
        simp [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
      change ∑ k, μ₁ k • q₁ k = c₁ at hμ₁bary
      rw [hμ₁bary, hμ₁sum, one_smul, sub_self] at this
      exact this
    obtain ⟨i₂, c₂, μ, hμpos, hμsum, hμbary, hc₂dist, hc₂lo⟩ :=
      drop_one_contact (n := 1) hρ₁_pos hc₁dist haff₁ hμ₁pos hμ₁sum hbary₁
    let P : Fin 3 → E4 := q₁ ∘ i₂.succAbove
    let c_Δ : E4 := c₁ + c₂
    let τ : ℝ := ρ₁ - ‖c₂‖ ^ 2
    have hPaff : AffineIndependent ℝ P :=
      haff_q₁.comp_embedding ⟨i₂.succAbove, i₂.succAbove_right_injective⟩
    have hPS (i : Fin 3) : P i ∈ S := (hpS (i₁.succAbove (i₂.succAbove i))).1
    have hPnorm (i : Fin 3) : ‖P i‖ ^ 2 = r := hpnorm2 (i₁.succAbove (i₂.succAbove i))
    have hPdiam (i j : Fin 3) : dist (P i) (P j) ≤ 1 := hSdiam _ (hPS i) _ (hPS j)
    have hPbary : ∑ i, μ i • P i = c_Δ := by
      have hdecomp (i : Fin 3) : P i = q₁' (i₂.succAbove i) + c₁ := by
        dsimp [P, q₁']; abel
      simp_rw [hdecomp, smul_add]
      change ∑ i, μ i • q₁' (i₂.succAbove i) = c₂ at hμbary
      rw [Finset.sum_add_distrib, ← Finset.sum_smul, hμbary, hμsum, one_smul]
      dsimp [c_Δ]; abel
    have hτdist (i : Fin 3) : ‖P i - c_Δ‖ ^ 2 = τ := by
      have hsub : P i - c_Δ = q₁' (i₂.succAbove i) - c₂ := by dsimp [P, q₁', c_Δ]; abel
      rw [hsub]; exact hc₂dist i
    have hτ_lo : (5 / 6 : ℝ) * r ≤ τ := by
      have h89 : (8 / 9 : ℝ) * ρ₁ ≤ τ := by dsimp [τ]; norm_num at hc₂lo; linarith
      linarith
    have hτ_nn : 0 ≤ τ := by linarith
    exact ⟨P, μ, c_Δ, τ, hPS, hPaff, hPnorm, hPdiam, hμpos, hμsum, hPbary,
      hτdist, hτ_lo, triangle_jung_upper hPdiam hμpos hμsum hPbary hτ_nn hτdist⟩

/- Certificate Structures and Enclosure Tree -/

structure Box4 where
  s0  : Int
  s1  : Int
  h0  : Int
  h1  : Int
  x20 : Int
  x21 : Int
  x30 : Int
  x31 : Int

structure CoverCert where
  r_lo : Int
  r_hi : Int
  y20  : Int
  y21  : Int
  ny30 : Int
  ny31 : Int
  rt0  : Int
  rt1  : Int
  rt2  : Int
  b0   : Int
  b1   : Int
  b2   : Int
  a0   : Int × Int × Int × Int
  e0   : Int × Int × Int × Int
  a1   : Int × Int × Int × Int
  e1   : Int × Int × Int × Int
  a2   : Int × Int × Int × Int
  e2   : Int × Int × Int × Int
  c0   : Int × Int × Int × Int
  c1   : Int × Int × Int × Int
  c2   : Int × Int × Int × Int
  c3   : Int × Int × Int × Int
  c4   : Int × Int × Int × Int
  c5   : Int × Int × Int × Int
  c6   : Int × Int × Int × Int
  c7   : Int × Int × Int × Int
  si0  : Nat
  si1  : Nat
  si2  : Nat
  si3  : Nat
  si4  : Nat
  sw0  : Int
  sw1  : Int
  sw2  : Int
  sw3  : Int
  sw4  : Int

def checkCert (c : CoverCert) : Bool :=
  checkBoxFull c.r_hi c.a0 c.a1 c.a2 c.b0 c.b1 c.b2
    c.c0 c.c1 c.c2 c.c3 c.c4 c.c5 c.c6 c.c7
    c.si0 c.si1 c.si2 c.si3 c.si4 c.sw0 c.sw1 c.sw2 c.sw3 c.sw4

structure VerifiedCert where
  c  : CoverCert
  ok : checkCert c = true

inductive PTree where
  | split (axis : Nat) (mid : Int) (left right : PTree)
  | inf (reason : Nat)
  | leaf (vc : VerifiedCert)

def splitBoxL (Q : Box4) (axis : Nat) (mid : Int) : Box4 :=
  match axis with
  | 0 => { Q with s1 := mid }
  | 1 => { Q with h1 := mid }
  | 2 => { Q with x21 := mid }
  | _ => { Q with x31 := mid }

def splitBoxR (Q : Box4) (axis : Nat) (mid : Int) : Box4 :=
  match axis with
  | 0 => { Q with s0 := mid }
  | 1 => { Q with h0 := mid }
  | 2 => { Q with x20 := mid }
  | _ => { Q with x30 := mid }

def checkInfeasible (Q : Box4) (reason : Nat) : Bool :=
  let s0 := ofInt Q.s0; let s1 := ofInt Q.s1; let h0 := ofInt Q.h0; let h1 := ofInt Q.h1
  let x20 := ofInt Q.x20; let x21 := ofInt Q.x21; let x30 := ofInt Q.x30; let x31 := ofInt Q.x31
  match reason with
  | 0 => Bool.and (sLe ⟨0, 0⟩ s1) (Bool.and (sLe ⟨0, 0⟩ h1)
           (sLe (sMul ⟨49, 0⟩ (sAdd (sMul s1 s1) (sMul h1 h1))) ⟨64000000, 0⟩))
  | 1 => Bool.and (sLe ⟨0, 0⟩ s0) (Bool.and (sLe ⟨0, 0⟩ h0)
           (sLt ⟨1572516, 0⟩ (sAdd (sMul s0 s0) (sMul h0 h0))))
  | 2 => Bool.and (sLe ⟨0, 0⟩ h0) (Bool.and (sLe ⟨0, 0⟩ s1)
           (sLt (sMul s1 s1) (sMul ⟨5, 0⟩ (sMul h0 h0))))
  | 3 => Bool.and (sLe ⟨0, 0⟩ s0) (sLt ⟨4000000, 0⟩ (sMul ⟨3, 0⟩ (sMul s0 s0)))
  | 4 => Bool.and (sLt ⟨0, 0⟩ s0)
           (sLt (sMul ⟨2, 0⟩ (sMul s0 x21)) (sSub (sMul ⟨2, 0⟩ (sMul s0 s0)) ⟨4000000, 0⟩))
  | 5 => sLt x31 x20
  | _ => Bool.and (sLt ⟨0, 0⟩ s0) (Bool.and (sLt ⟨0, 0⟩ (sAdd s0 x20))
           (Bool.and (sLe x31 ⟨0, 0⟩) (sLt (sMul ⟨2, 0⟩ (sMul x30 x30)) (sMul s0 (sAdd s0 x20)))))

def checkMidRad (lo hi m e : SInt) : Bool :=
  Bool.and (sLe ⟨0, 0⟩ e) (Bool.and (sLe (sSub m e) lo) (sLe hi (sAdd m e)))

def checkContactRow (lo0 hi0 lo1 hi1 lo2 hi2 lo3 hi3 : SInt)
    (a e : Int × Int × Int × Int) (r_lo r_hi rt b : SInt) : Bool :=
  let ea0 := ofInt e.1; let ea1 := ofInt e.2.1; let ea2 := ofInt e.2.2.1; let ea3 := ofInt e.2.2.2
  Bool.and (checkMidRad lo0 hi0 (ofInt a.1) ea0)
  (Bool.and (checkMidRad lo1 hi1 (ofInt a.2.1) ea1)
  (Bool.and (checkMidRad lo2 hi2 (ofInt a.2.2.1) ea2)
  (Bool.and (checkMidRad lo3 hi3 (ofInt a.2.2.2) ea3)
  (Bool.and (sLe ⟨0, 0⟩ rt)
  (Bool.and (sLe (sMul (norm2S ea0 ea1 ea2 ea3) r_hi) (sMul rt rt))
            (sLe (sAdd (sSub ⟨4000000, 0⟩ r_lo) (sMul ⟨2, 0⟩ rt)) b))))))

def checkEnclosure (Q : Box4) (c : CoverCert) : Bool :=
  let s0 := ofInt Q.s0; let s1 := ofInt Q.s1; let h0 := ofInt Q.h0; let h1 := ofInt Q.h1
  let x20 := ofInt Q.x20; let x21 := ofInt Q.x21; let x30 := ofInt Q.x30; let x31 := ofInt Q.x31
  let r_lo := ofInt c.r_lo; let r_hi := ofInt c.r_hi
  let y20 := ofInt c.y20; let y21 := ofInt c.y21; let ny30 := ofInt c.ny30; let ny31 := ofInt c.ny31
  Bool.and (sLe ⟨0, 0⟩ s0)
  (Bool.and (sLe ⟨0, 0⟩ h0)
  (Bool.and (sLe x21 ⟨0, 0⟩)
  (Bool.and (sLe x31 ⟨0, 0⟩)
  (Bool.and (Bool.or (sLe r_lo (sAdd (sMul s0 s0) (sMul h0 h0))) (sLe r_lo ⟨1306122, 0⟩))
  (Bool.and (Bool.or (sLe (sAdd (sMul s1 s1) (sMul h1 h1)) r_hi) (sLe ⟨1572516, 0⟩ r_hi))
  (Bool.and (sLe ⟨0, 0⟩ y20)
  (Bool.and (Bool.or (sEq y20 ⟨0, 0⟩) (sLe (sMul y20 y20) (sSub (sMul s0 s0) (sMul x20 x20))))
  (Bool.and (sLe ⟨0, 0⟩ y21)
  (Bool.and (sLe (sSub (sMul s1 s1) (sMul x21 x21)) (sMul y21 y21))
  (Bool.and (sLe ⟨0, 0⟩ ny30)
  (Bool.and (Bool.or (sEq ny30 ⟨0, 0⟩) (sLe (sMul ny30 ny30) (sSub (sMul s0 s0) (sMul x30 x30))))
  (Bool.and (sLe ⟨0, 0⟩ ny31)
  (Bool.and (sLe (sSub (sMul s1 s1) (sMul x31 x31)) (sMul ny31 ny31))
  (Bool.and (checkContactRow s0 s1 ⟨0, 0⟩ ⟨0, 0⟩ h0 h1 ⟨0, 0⟩ ⟨0, 0⟩ c.a0 c.e0 r_lo r_hi (ofInt c.rt0) (ofInt c.b0))
  (Bool.and (checkContactRow x20 x21 y20 y21 h0 h1 ⟨0, 0⟩ ⟨0, 0⟩ c.a1 c.e1 r_lo r_hi (ofInt c.rt1) (ofInt c.b1))
            (checkContactRow x30 x31 (sNeg ny31) (sNeg ny30) h0 h1 ⟨0, 0⟩ ⟨0, 0⟩ c.a2 c.e2 r_lo r_hi (ofInt c.rt2) (ofInt c.b2)))))))))))))))))

def checkEnclosureTree (Q : Box4) : PTree → Bool
  | .split axis mid l r =>
    Bool.and (checkEnclosureTree (splitBoxL Q axis mid) l)
             (checkEnclosureTree (splitBoxR Q axis mid) r)
  | .inf reason => checkInfeasible Q reason
  | .leaf vc => checkEnclosure Q vc.c

/- Soundness of Enclosure Tree -/

structure ParamState where
  ss      : ℝ
  hh      : ℝ
  xx2     : ℝ
  yy2     : ℝ
  xx3     : ℝ
  yy3     : ℝ
  rr      : ℝ
  hss_pos : 0 < ss
  hhh_nn  : 0 ≤ hh
  hsh_rr  : ss ^ 2 + hh ^ 2 = rr
  hrr_lo  : 64000000 < 49 * rr
  hrr_hi  : rr ≤ 1572516
  h5h     : 5 * hh ^ 2 ≤ ss ^ 2
  h3s     : 3 * ss ^ 2 ≤ 4000000
  hside1  : 2 * ss ^ 2 - 4000000 ≤ 2 * ss * xx2
  hx23    : xx2 ≤ xx3
  hx30    : xx3 ≤ 0
  hside23 : ss * (ss + xx2) ≤ 2 * xx3 ^ 2
  hyy2_nn : 0 ≤ yy2
  hyy2_sq : yy2 ^ 2 = ss ^ 2 - xx2 ^ 2
  hyy3_np : yy3 ≤ 0
  hyy3_sq : yy3 ^ 2 = ss ^ 2 - xx3 ^ 2

def inBox (Q : Box4) (P : ParamState) : Prop :=
  (Q.s0 : ℝ) ≤ P.ss ∧ P.ss ≤ (Q.s1 : ℝ) ∧
  (Q.h0 : ℝ) ≤ P.hh ∧ P.hh ≤ (Q.h1 : ℝ) ∧
  (Q.x20 : ℝ) ≤ P.xx2 ∧ P.xx2 ≤ (Q.x21 : ℝ) ∧
  (Q.x30 : ℝ) ≤ P.xx3 ∧ P.xx3 ≤ (Q.x31 : ℝ)

theorem inBox_root_bounds (P : ParamState) :
    inBox ⟨1043, 1155, 0, 512, -874, -521, -874, 0⟩ P := by
  have h147 : 160000000 < 147 * P.ss ^ 2 := by linarith [P.hsh_rr, P.hrr_lo, P.h5h]
  have hss_tight : (104328 / 100 : ℝ) < P.ss := by
    have hsq : (104328 / 100 : ℝ) ^ 2 < P.ss ^ 2 := by linarith
    by_contra hle; rw [not_lt] at hle
    have := pow_le_pow_left₀ P.hss_pos.le hle 2
    linarith
  have hss_lo : (1043 : ℝ) ≤ P.ss := by linarith
  have hss_hi : P.ss ≤ 1155 := by
    by_contra hlt; rw [not_le] at hlt
    have : (1155 : ℝ) ^ 2 ≤ P.ss ^ 2 := pow_le_pow_left₀ (by norm_num) hlt.le 2
    linarith [P.h3s]
  have hhh_hi : P.hh ≤ 512 := by
    by_contra hlt; rw [not_le] at hlt
    have : (512 : ℝ) ^ 2 ≤ P.hh ^ 2 := pow_le_pow_left₀ (by norm_num) hlt.le 2
    linarith [P.hsh_rr, P.hrr_hi, P.h5h]
  have hxx2_lo : (-874 : ℝ) ≤ P.xx2 := by
    have h1 : (104328 / 100 : ℝ) ^ 2 ≤ P.ss ^ 2 := pow_le_pow_left₀ (by norm_num) hss_tight.le 2
    have h2 : 2000000 < P.ss ^ 2 + 874 * P.ss := by linarith
    have h3 : 2 * P.ss * (-874) < 2 * P.ss * P.xx2 := by linarith [P.hside1]
    have h4 : (-874 : ℝ) < P.xx2 := lt_of_mul_lt_mul_left h3 (by linarith [P.hss_pos])
    exact h4.le
  have hxx2_hi : P.xx2 ≤ -521 := by
    have hx3_sq_le : P.xx3 ^ 2 ≤ P.xx2 ^ 2 := by
      have : (-P.xx3) ^ 2 ≤ (-P.xx2) ^ 2 := pow_le_pow_left₀ (by linarith [P.hx30]) (by linarith [P.hx23]) 2
      linarith
    have hprod : 0 ≤ (P.ss - P.xx2) * (-(2 * P.xx2 + P.ss)) := by
      have hid : (P.ss - P.xx2) * (-(2 * P.xx2 + P.ss)) = 2 * P.xx2 ^ 2 - P.ss * (P.ss + P.xx2) := by ring
      linarith [P.hside23]
    have hpos : 0 < P.ss - P.xx2 := by linarith [P.hss_pos, P.hx23, P.hx30]
    have hneg : 0 ≤ -(2 * P.xx2 + P.ss) := nonneg_of_mul_nonneg_right hprod hpos
    linarith
  dsimp [inBox]
  norm_num
  exact ⟨hss_lo, hss_hi, P.hhh_nn, hhh_hi, hxx2_lo, hxx2_hi, hxx2_lo.trans P.hx23, P.hx30⟩

lemma inBox_split (Q : Box4) (axis : Nat) (mid : Int) (P : ParamState) (hQ : inBox Q P) :
    inBox (splitBoxL Q axis mid) P ∨ inBox (splitBoxR Q axis mid) P := by
  rcases hQ with ⟨hs0, hs1, hh0, hh1, hx20, hx21, hx30, hx31⟩
  rcases axis with _ | _ | _ | n
  · rcases le_total P.ss (mid : ℝ) with h | h
    · exact Or.inl ⟨hs0, h, hh0, hh1, hx20, hx21, hx30, hx31⟩
    · exact Or.inr ⟨h, hs1, hh0, hh1, hx20, hx21, hx30, hx31⟩
  · rcases le_total P.hh (mid : ℝ) with h | h
    · exact Or.inl ⟨hs0, hs1, hh0, h, hx20, hx21, hx30, hx31⟩
    · exact Or.inr ⟨hs0, hs1, h, hh1, hx20, hx21, hx30, hx31⟩
  · rcases le_total P.xx2 (mid : ℝ) with h | h
    · exact Or.inl ⟨hs0, hs1, hh0, hh1, hx20, h, hx30, hx31⟩
    · exact Or.inr ⟨hs0, hs1, hh0, hh1, h, hx21, hx30, hx31⟩
  · rcases le_total P.xx3 (mid : ℝ) with h | h
    · exact Or.inl ⟨hs0, hs1, hh0, hh1, hx20, hx21, hx30, h⟩
    · exact Or.inr ⟨hs0, hs1, hh0, hh1, hx20, hx21, h, hx31⟩

theorem checkInfeasible_sound {Q : Box4} {reason : Nat}
    (h : checkInfeasible Q reason = true) {P : ParamState} (hQ : inBox Q P) : False := by
  rcases hQ with ⟨hs0, hs1, hh0, hh1, hx20, hx21, hx30, hx31⟩
  unfold checkInfeasible at h
  rcases reason with _ | _ | _ | _ | _ | _ | n
  · simp only [Bool.and_eq_true, sLe_iff, toR_zero, toR_ofInt, toR_sMul, toR_sAdd] at h
    have h1 : P.ss ^ 2 ≤ (Q.s1 : ℝ) ^ 2 := pow_le_pow_left₀ P.hss_pos.le hs1 2
    have h2 : P.hh ^ 2 ≤ (Q.h1 : ℝ) ^ 2 := pow_le_pow_left₀ P.hhh_nn hh1 2
    have h3 : (49 : ℝ) = toR ⟨49, 0⟩ := by unfold toR; norm_num
    have h4 : (64000000 : ℝ) = toR ⟨64000000, 0⟩ := by unfold toR; norm_num
    rw [← h3, ← h4] at h
    linarith [P.hsh_rr, P.hrr_lo, sq_abs (Q.s1 : ℝ)]
  · simp only [Bool.and_eq_true, sLe_iff, sLt_iff, toR_zero, toR_ofInt, toR_sMul, toR_sAdd] at h
    have h1 : (Q.s0 : ℝ) ^ 2 ≤ P.ss ^ 2 := pow_le_pow_left₀ h.1 hs0 2
    have h2 : (Q.h0 : ℝ) ^ 2 ≤ P.hh ^ 2 := pow_le_pow_left₀ h.2.1 hh0 2
    have h3 : (1572516 : ℝ) = toR ⟨1572516, 0⟩ := by unfold toR; norm_num
    rw [← h3] at h
    linarith [P.hsh_rr, P.hrr_hi]
  · simp only [Bool.and_eq_true, sLe_iff, sLt_iff, toR_zero, toR_ofInt, toR_sMul] at h
    have h1 : (Q.h0 : ℝ) ^ 2 ≤ P.hh ^ 2 := pow_le_pow_left₀ h.1 hh0 2
    have h2 : P.ss ^ 2 ≤ (Q.s1 : ℝ) ^ 2 := pow_le_pow_left₀ P.hss_pos.le hs1 2
    have h3 : (5 : ℝ) = toR ⟨5, 0⟩ := by unfold toR; norm_num
    rw [← h3] at h
    linarith [P.h5h]
  · simp only [Bool.and_eq_true, sLe_iff, sLt_iff, toR_zero, toR_ofInt, toR_sMul] at h
    have h1 : (Q.s0 : ℝ) ^ 2 ≤ P.ss ^ 2 := pow_le_pow_left₀ h.1 hs0 2
    have h2 : (4000000 : ℝ) = toR ⟨4000000, 0⟩ := by unfold toR; norm_num
    have h3 : (3 : ℝ) = toR ⟨3, 0⟩ := by unfold toR; norm_num
    rw [← h2, ← h3] at h
    linarith [P.h3s]
  · simp only [Bool.and_eq_true, sLt_iff, toR_zero, toR_ofInt, toR_sMul, toR_sSub] at h
    have hc2 : (2 : ℝ) = toR ⟨2, 0⟩ := by unfold toR; norm_num
    have hc4 : (4000000 : ℝ) = toR ⟨4000000, 0⟩ := by unfold toR; norm_num
    rw [← hc2, ← hc4] at h
    have h1 : 2 * P.ss * P.xx2 ≤ 2 * P.ss * (Q.x21 : ℝ) :=
      mul_le_mul_of_nonneg_left hx21 (by linarith [P.hss_pos])
    have h2 : (Q.s0 : ℝ) * (2 * P.ss ^ 2 - 4000000 - 2 * P.ss * (Q.x21 : ℝ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos h.1.le (by linarith [P.hside1, h1])
    have h3 : 0 < P.ss * (2 * (Q.s0 : ℝ) * (Q.s0 : ℝ) - 4000000 - 2 * ((Q.s0 : ℝ) * (Q.x21 : ℝ))) :=
      mul_pos P.hss_pos (by linarith [h.2])
    have h4 : 0 ≤ (P.ss - (Q.s0 : ℝ)) * (2 * (Q.s0 : ℝ) * P.ss + 4000000) :=
      mul_nonneg (by linarith) (by have := mul_pos h.1 P.hss_pos; linarith)
    have hid : (Q.s0 : ℝ) * (2 * P.ss ^ 2 - 4000000 - 2 * P.ss * (Q.x21 : ℝ)) -
        P.ss * (2 * (Q.s0 : ℝ) * (Q.s0 : ℝ) - 4000000 - 2 * ((Q.s0 : ℝ) * (Q.x21 : ℝ))) =
        (P.ss - (Q.s0 : ℝ)) * (2 * (Q.s0 : ℝ) * P.ss + 4000000) := by ring
    linarith
  · simp only [sLt_iff, toR_ofInt] at h
    linarith [P.hx23]
  · simp only [Bool.and_eq_true, sLt_iff, sLe_iff, toR_zero, toR_ofInt, toR_sAdd, toR_sMul] at h
    have hc2 : (2 : ℝ) = toR ⟨2, 0⟩ := by unfold toR; norm_num
    rw [← hc2] at h
    rcases h with ⟨hs0_pos, hsx_pos, _, hviol⟩
    have h1 : (Q.s0 : ℝ) * ((Q.s0 : ℝ) + (Q.x20 : ℝ)) ≤ P.ss * ((Q.s0 : ℝ) + (Q.x20 : ℝ)) :=
      mul_le_mul_of_nonneg_right hs0 hsx_pos.le
    have h2 : P.ss * ((Q.s0 : ℝ) + (Q.x20 : ℝ)) ≤ P.ss * (P.ss + P.xx2) :=
      mul_le_mul_of_nonneg_left (by linarith) P.hss_pos.le
    have h3 : (-P.xx3) ^ 2 ≤ (-(Q.x30 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by linarith [P.hx30]) (by linarith) 2
    have h4 : P.xx3 ^ 2 ≤ (Q.x30 : ℝ) * (Q.x30 : ℝ) := by linarith [show (-P.xx3)^2 = P.xx3^2 by ring, show (-(Q.x30 : ℝ))^2 = (Q.x30 : ℝ) * (Q.x30 : ℝ) by ring]
    linarith [P.hside23]

def mkCenterE4 (b : OrthonormalBasis (Fin 4) ℝ E4) (c : Int × Int × Int × Int) : E4 :=
  ((c.1 : ℝ) / 2000) • b 0 + ((c.2.1 : ℝ) / 2000) • b 1 +
  ((c.2.2.1 : ℝ) / 2000) • b 2 + ((c.2.2.2 : ℝ) / 2000) • b 3

lemma repr_mkCenterE4 (b : OrthonormalBasis (Fin 4) ℝ E4) (c : Int × Int × Int × Int) :
    b.repr (mkCenterE4 b c) 0 = (c.1 : ℝ) / 2000 ∧
    b.repr (mkCenterE4 b c) 1 = (c.2.1 : ℝ) / 2000 ∧
    b.repr (mkCenterE4 b c) 2 = (c.2.2.1 : ℝ) / 2000 ∧
    b.repr (mkCenterE4 b c) 3 = (c.2.2.2 : ℝ) / 2000 := by
  have h (j : Fin 4) : b.repr (mkCenterE4 b c) j =
      if j = 0 then (c.1 : ℝ) / 2000 else if j = 1 then (c.2.1 : ℝ) / 2000 else
      if j = 2 then (c.2.2.1 : ℝ) / 2000 else (c.2.2.2 : ℝ) / 2000 := by
    unfold mkCenterE4
    simp only [map_add, map_smul, b.repr_self]
    fin_cases j <;> simp
  exact ⟨by simpa using h 0, by simpa using h 1, by simpa using h 2, by simpa using h 3⟩

lemma checkMidRad_sound {lo hi m e : SInt} {t : ℝ}
    (hchk : checkMidRad lo hi m e = true) (hlo : toR lo ≤ t) (hhi : t ≤ toR hi) :
    (t - toR m) ^ 2 ≤ (toR e) ^ 2 := by
  unfold checkMidRad at hchk
  simp only [Bool.and_eq_true, sLe_iff, toR_zero, toR_sSub, toR_sAdd] at hchk
  have habs : |t - toR m| ≤ toR e := abs_le.mpr ⟨by linarith, by linarith⟩
  have hsq := pow_le_pow_left₀ (abs_nonneg _) habs 2
  rwa [sq_abs] at hsq

lemma checkContactRow_sound
    {lo0 hi0 lo1 hi1 lo2 hi2 lo3 hi3 : SInt}
    {a e : Int × Int × Int × Int} {r_lo r_hi : SInt} {rt b_int : Int}
    (hchk : checkContactRow lo0 hi0 lo1 hi1 lo2 hi2 lo3 hi3 a e r_lo r_hi (ofInt rt) (ofInt b_int) = true)
    {qq0 qq1 qq2 qq3 rr : ℝ} {Y : Fin 5 → ℝ}
    (hq0 : toR lo0 ≤ qq0 ∧ qq0 ≤ toR hi0)
    (hq1 : toR lo1 ≤ qq1 ∧ qq1 ≤ toR hi1)
    (hq2 : toR lo2 ≤ qq2 ∧ qq2 ≤ toR hi2)
    (hq3 : toR lo3 ≤ qq3 ∧ qq3 ≤ toR hi3)
    (hq_norm : qq0 ^ 2 + qq1 ^ 2 + qq2 ^ 2 + qq3 ^ 2 = rr)
    (hY_norm : (Y 0) ^ 2 + (Y 1) ^ 2 + (Y 2) ^ 2 + (Y 3) ^ 2 = Y 4)
    (hY_dist : (Y 0 - qq0) ^ 2 + (Y 1 - qq1) ^ 2 + (Y 2 - qq2) ^ 2 + (Y 3 - qq3) ^ 2 ≤ 4000000)
    (hr_lo : toR r_lo ≤ rr) (hY4_hi : Y 4 ≤ toR r_hi) (hY4_nn : 0 ≤ Y 4) :
    row5Val (mkRowAS a b_int) Y ≤ toR (mkRowAS a b_int).d := by
  unfold checkContactRow at hchk
  simp only [Bool.and_eq_true] at hchk
  rcases hchk with ⟨hm0, hm1, hm2, hm3, hrt_nn, hrt_sq, hb_ge⟩
  have he0 := checkMidRad_sound hm0 hq0.1 hq0.2
  have he1 := checkMidRad_sound hm1 hq1.1 hq1.2
  have he2 := checkMidRad_sound hm2 hq2.1 hq2.2
  have he3 := checkMidRad_sound hm3 hq3.1 hq3.2
  simp only [toR_ofInt] at he0 he1 he2 he3
  have hcs := cs4_sq (qq0 - a.1) (qq1 - a.2.1) (qq2 - a.2.2.1) (qq3 - a.2.2.2) (Y 0) (Y 1) (Y 2) (Y 3)
  have hsum_e : (qq0 - a.1) ^ 2 + (qq1 - a.2.1) ^ 2 + (qq2 - a.2.2.1) ^ 2 + (qq3 - a.2.2.2) ^ 2 ≤
      toR (norm2S (ofInt e.1) (ofInt e.2.1) (ofInt e.2.2.1) (ofInt e.2.2.2)) := by
    simp only [norm2S, toR_sAdd, toR_sMul, toR_ofInt]
    linarith
  have hrt_nnR : 0 ≤ (rt : ℝ) := by simpa using (sLe_iff _ _).mp hrt_nn
  have hrt_sqR : toR (norm2S (ofInt e.1) (ofInt e.2.1) (ofInt e.2.2.1) (ofInt e.2.2.2)) * toR r_hi ≤ (rt : ℝ) ^ 2 := by
    have := (sLe_iff _ _).mp hrt_sq
    simp only [toR_sMul, toR_ofInt] at this
    linarith
  have hprod_le : ((qq0 - a.1) ^ 2 + (qq1 - a.2.1) ^ 2 + (qq2 - a.2.2.1) ^ 2 + (qq3 - a.2.2.2) ^ 2) *
      ((Y 0) ^ 2 + (Y 1) ^ 2 + (Y 2) ^ 2 + (Y 3) ^ 2) ≤ (rt : ℝ) ^ 2 := by
    rw [hY_norm]
    have h1 := mul_le_mul_of_nonneg_right hsum_e hY4_nn
    have hnn_norm : 0 ≤ toR (norm2S (ofInt e.1) (ofInt e.2.1) (ofInt e.2.2.1) (ofInt e.2.2.2)) :=
      (by positivity : 0 ≤ (qq0 - a.1) ^ 2 + (qq1 - a.2.1) ^ 2 + (qq2 - a.2.2.1) ^ 2 + (qq3 - a.2.2.2) ^ 2).trans hsum_e
    have h2 := mul_le_mul_of_nonneg_left hY4_hi hnn_norm
    linarith
  have hdot_le : (qq0 - a.1) * Y 0 + (qq1 - a.2.1) * Y 1 + (qq2 - a.2.2.1) * Y 2 + (qq3 - a.2.2.2) * Y 3 ≤ (rt : ℝ) := by
    by_contra hlt; rw [not_le] at hlt
    have := pow_lt_pow_left₀ hlt hrt_nnR (by decide : 2 ≠ 0)
    linarith
  have hb_geR : 4000000 - toR r_lo + 2 * (rt : ℝ) ≤ (b_int : ℝ) := by
    have := (sLe_iff _ _).mp hb_ge
    simp only [toR_sAdd, toR_sSub, toR_sMul, toR_ofInt] at this
    have hc4 : toR ⟨4000000, 0⟩ = 4000000 := by unfold toR; norm_num
    have hc2 : toR ⟨2, 0⟩ = 2 := by unfold toR; norm_num
    rw [hc4, hc2] at this
    linarith
  simp only [mkRowAS, row5Val, toR_ofInt, ↓reduceIte]
  have hid : (-2 * (a.1 : ℝ)) * Y 0 + (-2 * (a.2.1 : ℝ)) * Y 1 +
      (-2 * (a.2.2.1 : ℝ)) * Y 2 + (-2 * (a.2.2.2 : ℝ)) * Y 3 + 1 * Y 4 =
      ((Y 0 - qq0) ^ 2 + (Y 1 - qq1) ^ 2 + (Y 2 - qq2) ^ 2 + (Y 3 - qq3) ^ 2 -
        (qq0 ^ 2 + qq1 ^ 2 + qq2 ^ 2 + qq3 ^ 2)) +
      (Y 4 - ((Y 0) ^ 2 + (Y 1) ^ 2 + (Y 2) ^ 2 + (Y 3) ^ 2)) +
      2 * ((qq0 - a.1) * Y 0 + (qq1 - a.2.1) * Y 1 + (qq2 - a.2.2.1) * Y 2 + (qq3 - a.2.2.2) * Y 3) := by
    ring
  push_cast
  linarith

lemma ball_miss_row5 {b : OrthonormalBasis (Fin 4) ℝ E4} {x : E4} {c : Int × Int × Int × Int}
    {Y : Fin 5 → ℝ}
    (hmiss : x ∉ Metric.closedBall (mkCenterE4 b c) (999 / 2000))
    (hY0 : Y 0 = 2000 * b.repr x 0) (hY1 : Y 1 = 2000 * b.repr x 1)
    (hY2 : Y 2 = 2000 * b.repr x 2) (hY3 : Y 3 = 2000 * b.repr x 3)
    (hY_norm : (Y 0) ^ 2 + (Y 1) ^ 2 + (Y 2) ^ 2 + (Y 3) ^ 2 = Y 4) :
    row5Val (mkRowCS c) Y ≤ toR (mkRowCS c).d := by
  have hgt : (999 / 2000 : ℝ) < dist x (mkCenterE4 b c) := by
    simpa only [Metric.mem_closedBall, not_le] using hmiss
  have hsq : (999 / 2000 : ℝ) ^ 2 < dist (b.repr x) (b.repr (mkCenterE4 b c)) ^ 2 := by
    rw [b.repr.isometry.dist_eq]
    exact pow_lt_pow_left₀ hgt (by norm_num) (by decide : 2 ≠ 0)
  obtain ⟨hc0, hc1, hc2, hc3⟩ := repr_mkCenterE4 b c
  rw [e4_dist_sq, hc0, hc1, hc2, hc3] at hsq
  rcases c with ⟨cx0, cx1, cx2, cx3⟩
  simp only [mkRowCS, row5Val, toR_ofInt, Bool.false_eq_true, ↓reduceIte]
  push_cast
  have hid : 4000000 * ((b.repr x 0 - (cx0 : ℝ) / 2000) ^ 2 + (b.repr x 1 - (cx1 : ℝ) / 2000) ^ 2 +
      (b.repr x 2 - (cx2 : ℝ) / 2000) ^ 2 + (b.repr x 3 - (cx3 : ℝ) / 2000) ^ 2) =
      ((Y 0) ^ 2 + (Y 1) ^ 2 + (Y 2) ^ 2 + (Y 3) ^ 2) -
      (2 * (cx0 : ℝ) * Y 0 + 2 * (cx1 : ℝ) * Y 1 + 2 * (cx2 : ℝ) * Y 2 + 2 * (cx3 : ℝ) * Y 3) +
      ((cx0 : ℝ) ^ 2 + (cx1 : ℝ) ^ 2 + (cx2 : ℝ) ^ 2 + (cx3 : ℝ) ^ 2) := by
    rw [hY0, hY1, hY2, hY3]; ring
  linarith

theorem checkEnclosure_sound
    {S : Set E4} {b : OrthonormalBasis (Fin 4) ℝ E4} {q : Fin 3 → E4} {r : ℝ}
    (hSdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ 1)
    (hSnorm : ∀ x ∈ S, ‖x‖ ^ 2 ≤ r)
    (hqS : ∀ i, q i ∈ S)
    {P : ParamState} (hrr : P.rr = 4000000 * r)
    (hq0 : b.repr (q 0) 0 = P.ss / 2000 ∧ b.repr (q 0) 1 = 0 ∧ b.repr (q 0) 2 = P.hh / 2000 ∧ b.repr (q 0) 3 = 0)
    (hq1 : b.repr (q 1) 0 = P.xx2 / 2000 ∧ b.repr (q 1) 1 = P.yy2 / 2000 ∧ b.repr (q 1) 2 = P.hh / 2000 ∧ b.repr (q 1) 3 = 0)
    (hq2 : b.repr (q 2) 0 = P.xx3 / 2000 ∧ b.repr (q 2) 1 = P.yy3 / 2000 ∧ b.repr (q 2) 2 = P.hh / 2000 ∧ b.repr (q 2) 3 = 0)
    {Q : Box4} (hQ : inBox Q P) {vc : VerifiedCert} (henc : checkEnclosure Q vc.c = true) :
    ∃ D : Fin 8 → Set E4, (∀ j, IsClosed (D j)) ∧ S ⊆ ⋃ j, D j ∧
      ∀ j, ∀ x ∈ D j, ∀ y ∈ D j, dist x y ≤ 999 / 1000 := by
  let c := vc.c
  let center (j : Fin 8) : E4 :=
    mkCenterE4 b (pickC c.c0 c.c1 c.c2 c.c3 c.c4 c.c5 c.c6 c.c7 j.val)
  let D (j : Fin 8) : Set E4 := Metric.closedBall (center j) (999 / 2000)
  refine ⟨D, fun _ => Metric.isClosed_closedBall, ?_, ?_⟩
  · intro x hxS
    by_contra hout
    have hmiss (j : Fin 8) : x ∉ D j := fun hj => hout (Set.mem_iUnion.mpr ⟨j, hj⟩)
    rcases hQ with ⟨hs0, hs1, hh0, hh1, hx20, hx21, hx30, hx31⟩
    unfold checkEnclosure at henc
    simp only [Bool.and_eq_true] at henc
    rcases henc with ⟨hs0_nn, hh0_nn, hx21_np, hx31_np, hr_lo_or, hr_hi_or,
      hy20_nn, hy20_or, hy21_nn, hy21_hi, hny30_nn, hny30_or, hny31_nn, hny31_hi,
      hrow0, hrow1, hrow2⟩
    have hs0R : 0 ≤ (Q.s0 : ℝ) := by simpa using (sLe_iff _ _).mp hs0_nn
    have hh0R : 0 ≤ (Q.h0 : ℝ) := by simpa using (sLe_iff _ _).mp hh0_nn
    have hx21R : (Q.x21 : ℝ) ≤ 0 := by simpa using (sLe_iff _ _).mp hx21_np
    have hx31R : (Q.x31 : ℝ) ≤ 0 := by simpa using (sLe_iff _ _).mp hx31_np
    have hrr_loR : (vc.c.r_lo : ℝ) ≤ P.rr := by
      rcases Bool.or_eq_true_iff.mp hr_lo_or with h1 | h2
      · have hle := (sLe_iff _ _).mp h1
        simp only [toR_sAdd, toR_sMul, toR_ofInt, ← sq] at hle
        have hsq1 := pow_le_pow_left₀ hs0R hs0 2
        have hsq2 := pow_le_pow_left₀ hh0R hh0 2
        linarith [P.hsh_rr]
      · have hle := (sLe_iff _ _).mp h2
        have hc13 : toR ⟨1306122, 0⟩ = 1306122 := by unfold toR; norm_num
        simp only [toR_ofInt, hc13] at hle; linarith [P.hrr_lo]
    have hrr_lo : toR (ofInt c.r_lo) ≤ P.rr := by dsimp [c]; simpa only [toR_ofInt] using hrr_loR
    have hrr_hiR : P.rr ≤ (vc.c.r_hi : ℝ) := by
      rcases Bool.or_eq_true_iff.mp hr_hi_or with h1 | h2
      · have hle := (sLe_iff _ _).mp h1
        simp only [toR_sAdd, toR_sMul, toR_ofInt, ← sq] at hle
        have hsq1 := pow_le_pow_left₀ P.hss_pos.le hs1 2
        have hsq2 := pow_le_pow_left₀ P.hhh_nn hh1 2
        linarith [P.hsh_rr]
      · have hle := (sLe_iff _ _).mp h2
        have hc15 : toR ⟨1572516, 0⟩ = 1572516 := by unfold toR; norm_num
        simp only [toR_ofInt, hc15] at hle; linarith [P.hrr_hi]
    have hrr_hi : P.rr ≤ toR (ofInt c.r_hi) := by dsimp [c]; simpa only [toR_ofInt] using hrr_hiR
    have hyy2_lo : (c.y20 : ℝ) ≤ P.yy2 := by
      have hnn : 0 ≤ (c.y20 : ℝ) := by simpa using (sLe_iff _ _).mp hy20_nn
      rcases Bool.or_eq_true_iff.mp hy20_or with h0 | hsq
      · have heq : (c.y20 : ℝ) = 0 := by simpa using (sEq_iff _ _).mp h0
        linarith [P.hyy2_nn]
      · have hle := (sLe_iff _ _).mp hsq
        simp only [toR_sMul, toR_sSub, toR_ofInt, ← sq] at hle
        have hs_sq : (Q.s0 : ℝ) ^ 2 ≤ P.ss ^ 2 := pow_le_pow_left₀ hs0R hs0 2
        have hx_sq : P.xx2 ^ 2 ≤ (Q.x20 : ℝ) ^ 2 := by
          have : (-P.xx2) ^ 2 ≤ (-(Q.x20 : ℝ)) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
          linarith
        have hy_sq : (c.y20 : ℝ) ^ 2 ≤ P.yy2 ^ 2 := by linarith [P.hyy2_sq]
        by_contra hlt; rw [not_le] at hlt
        have := pow_lt_pow_left₀ hlt P.hyy2_nn (by decide : 2 ≠ 0)
        linarith
    have hyy2_hi : P.yy2 ≤ (c.y21 : ℝ) := by
      have hnn : 0 ≤ (c.y21 : ℝ) := by simpa using (sLe_iff _ _).mp hy21_nn
      have hle := (sLe_iff _ _).mp hy21_hi
      simp only [toR_sMul, toR_sSub, toR_ofInt, ← sq] at hle
      have hs_sq : P.ss ^ 2 ≤ (Q.s1 : ℝ) ^ 2 := pow_le_pow_left₀ P.hss_pos.le hs1 2
      have hx_sq : (Q.x21 : ℝ) ^ 2 ≤ P.xx2 ^ 2 := by
        have : (-(Q.x21 : ℝ)) ^ 2 ≤ (-P.xx2) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
        linarith
      have hy_sq : P.yy2 ^ 2 ≤ (c.y21 : ℝ) ^ 2 := by linarith [P.hyy2_sq]
      by_contra hlt; rw [not_le] at hlt
      have := pow_lt_pow_left₀ hlt hnn (by decide : 2 ≠ 0)
      linarith
    have hny3_lo : (c.ny30 : ℝ) ≤ -P.yy3 := by
      have hnn : 0 ≤ (c.ny30 : ℝ) := by simpa using (sLe_iff _ _).mp hny30_nn
      rcases Bool.or_eq_true_iff.mp hny30_or with h0 | hsq
      · have heq : (c.ny30 : ℝ) = 0 := by simpa using (sEq_iff _ _).mp h0
        linarith [P.hyy3_np]
      · have hle := (sLe_iff _ _).mp hsq
        simp only [toR_sMul, toR_sSub, toR_ofInt, ← sq] at hle
        have hs_sq : (Q.s0 : ℝ) ^ 2 ≤ P.ss ^ 2 := pow_le_pow_left₀ hs0R hs0 2
        have hx_sq : P.xx3 ^ 2 ≤ (Q.x30 : ℝ) ^ 2 := by
          have : (-P.xx3) ^ 2 ≤ (-(Q.x30 : ℝ)) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
          linarith
        have hy_sq : (c.ny30 : ℝ) ^ 2 ≤ (-P.yy3) ^ 2 := by linarith [P.hyy3_sq]
        by_contra hlt; rw [not_le] at hlt
        have := pow_lt_pow_left₀ hlt (by linarith [P.hyy3_np]) (by decide : 2 ≠ 0)
        linarith
    have hny3_hi : -P.yy3 ≤ (c.ny31 : ℝ) := by
      have hnn : 0 ≤ (c.ny31 : ℝ) := by simpa using (sLe_iff _ _).mp hny31_nn
      have hle := (sLe_iff _ _).mp hny31_hi
      simp only [toR_sMul, toR_sSub, toR_ofInt, ← sq] at hle
      have hs_sq : P.ss ^ 2 ≤ (Q.s1 : ℝ) ^ 2 := pow_le_pow_left₀ P.hss_pos.le hs1 2
      have hx_sq : (Q.x31 : ℝ) ^ 2 ≤ P.xx3 ^ 2 := by
        have : (-(Q.x31 : ℝ)) ^ 2 ≤ (-P.xx3) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
        linarith
      have hy_sq : (-P.yy3) ^ 2 ≤ (c.ny31 : ℝ) ^ 2 := by linarith [P.hyy3_sq]
      by_contra hlt; rw [not_le] at hlt
      have := pow_lt_pow_left₀ hlt hnn (by decide : 2 ≠ 0)
      linarith
    obtain ⟨Y, hY0, hY1, hY2, hY3, hY4_def⟩ : ∃ Y : Fin 5 → ℝ,
        Y 0 = 2000 * b.repr x 0 ∧ Y 1 = 2000 * b.repr x 1 ∧
        Y 2 = 2000 * b.repr x 2 ∧ Y 3 = 2000 * b.repr x 3 ∧ Y 4 = 4000000 * ‖x‖ ^ 2 :=
      ⟨fun k => match k with
        | 0 => 2000 * b.repr x 0 | 1 => 2000 * b.repr x 1
        | 2 => 2000 * b.repr x 2 | 3 => 2000 * b.repr x 3 | 4 => 4000000 * ‖x‖ ^ 2,
       rfl, rfl, rfl, rfl, rfl⟩
    have hY_norm : (Y 0) ^ 2 + (Y 1) ^ 2 + (Y 2) ^ 2 + (Y 3) ^ 2 = Y 4 := by
      rw [hY0, hY1, hY2, hY3, hY4_def]
      have hn : ‖b.repr x‖ ^ 2 = ‖x‖ ^ 2 := by rw [b.repr.norm_map]
      rw [e4_norm_sq] at hn
      linarith
    have hY4_nn : 0 ≤ Y 4 := by rw [hY4_def]; positivity
    have hY4_hi : Y 4 ≤ toR (ofInt c.r_hi) := by
      have : Y 4 ≤ P.rr := by rw [hY4_def]; linarith [hSnorm x hxS, hrr]
      exact this.trans hrr_hi
    have hdist_q (i : Fin 3) :
        (Y 0 - 2000 * b.repr (q i) 0) ^ 2 + (Y 1 - 2000 * b.repr (q i) 1) ^ 2 +
        (Y 2 - 2000 * b.repr (q i) 2) ^ 2 + (Y 3 - 2000 * b.repr (q i) 3) ^ 2 ≤ 4000000 := by
      have hd1 : dist (b.repr x) (b.repr (q i)) ^ 2 ≤ 1 := by
        rw [b.repr.isometry.dist_eq]
        exact pow_le_one₀ dist_nonneg (hSdiam x hxS (q i) (hqS i))
      rw [e4_dist_sq] at hd1
      rw [hY0, hY1, hY2, hY3]
      linarith [show (2000 * b.repr x 0 - 2000 * b.repr (q i) 0) ^ 2 +
          (2000 * b.repr x 1 - 2000 * b.repr (q i) 1) ^ 2 +
          (2000 * b.repr x 2 - 2000 * b.repr (q i) 2) ^ 2 +
          (2000 * b.repr x 3 - 2000 * b.repr (q i) 3) ^ 2 =
          4000000 * ((b.repr x 0 - b.repr (q i) 0) ^ 2 + (b.repr x 1 - b.repr (q i) 1) ^ 2 +
          (b.repr x 2 - b.repr (q i) 2) ^ 2 + (b.repr x 3 - b.repr (q i) 3) ^ 2) by ring]
    have hr2_ok : row5Val (mkRowAS c.a0 c.b0) Y ≤ toR (mkRowAS c.a0 c.b0).d := by
      refine checkContactRow_sound hrow0 (qq0 := P.ss) (qq1 := 0) (qq2 := P.hh) (qq3 := 0) (rr := P.rr)
        ⟨by simpa using hs0, by simpa using hs1⟩ ⟨by simp, by simp⟩
        ⟨by simpa using hh0, by simpa using hh1⟩ ⟨by simp, by simp⟩
        (by linarith [P.hsh_rr]) hY_norm ?_ hrr_lo hY4_hi hY4_nn
      have hd0 := hdist_q 0
      rw [hq0.1, hq0.2.1, hq0.2.2.1, hq0.2.2.2] at hd0
      linarith [show 2000 * (P.ss / 2000) = P.ss by ring, show 2000 * (P.hh / 2000) = P.hh by ring, show (2000 : ℝ) * 0 = 0 by ring]
    have hr3_ok : row5Val (mkRowAS c.a1 c.b1) Y ≤ toR (mkRowAS c.a1 c.b1).d := by
      refine checkContactRow_sound hrow1 (qq0 := P.xx2) (qq1 := P.yy2) (qq2 := P.hh) (qq3 := 0) (rr := P.rr)
        ⟨by simpa using hx20, by simpa using hx21⟩ ⟨by simpa using hyy2_lo, by simpa using hyy2_hi⟩
        ⟨by simpa using hh0, by simpa using hh1⟩ ⟨by simp, by simp⟩
        (by linarith [P.hyy2_sq, P.hsh_rr]) hY_norm ?_ hrr_lo hY4_hi hY4_nn
      have hd1 := hdist_q 1
      rw [hq1.1, hq1.2.1, hq1.2.2.1, hq1.2.2.2] at hd1
      linarith [show 2000 * (P.xx2 / 2000) = P.xx2 by ring, show 2000 * (P.yy2 / 2000) = P.yy2 by ring,
                show 2000 * (P.hh / 2000) = P.hh by ring, show (2000 : ℝ) * 0 = 0 by ring]
    have hr4_ok : row5Val (mkRowAS c.a2 c.b2) Y ≤ toR (mkRowAS c.a2 c.b2).d := by
      refine checkContactRow_sound hrow2 (qq0 := P.xx3) (qq1 := P.yy3) (qq2 := P.hh) (qq3 := 0) (rr := P.rr)
        ⟨by simpa using hx30, by simpa using hx31⟩
        ⟨by simp; linarith, by simp; linarith⟩
        ⟨by simpa using hh0, by simpa using hh1⟩ ⟨by simp, by simp⟩
        (by linarith [P.hyy3_sq, P.hsh_rr]) hY_norm ?_ hrr_lo hY4_hi hY4_nn
      have hd2 := hdist_q 2
      rw [hq2.1, hq2.2.1, hq2.2.2.1, hq2.2.2.2] at hd2
      linarith [show 2000 * (P.xx3 / 2000) = P.xx3 by ring, show 2000 * (P.yy3 / 2000) = P.yy3 by ring,
                show 2000 * (P.hh / 2000) = P.hh by ring, show (2000 : ℝ) * 0 = 0 by ring]
    have hmiss_c (m : Nat) (cc : Int × Int × Int × Int) (hlt : m < 8)
        (hp : pickC c.c0 c.c1 c.c2 c.c3 c.c4 c.c5 c.c6 c.c7 m = cc) :
        row5Val (mkRowCS cc) Y ≤ toR (mkRowCS cc).d := by
      have hm : x ∉ Metric.closedBall (mkCenterE4 b (pickC c.c0 c.c1 c.c2 c.c3 c.c4 c.c5 c.c6 c.c7 m)) (999 / 2000) :=
        hmiss ⟨m, hlt⟩
      rw [hp] at hm
      exact ball_miss_row5 hm hY0 hY1 hY2 hY3 hY_norm
    have hc0_ok := hmiss_c 0 c.c0 (by decide) rfl
    have hc1_ok := hmiss_c 1 c.c1 (by decide) rfl
    have hc2_ok := hmiss_c 2 c.c2 (by decide) rfl
    have hc3_ok := hmiss_c 3 c.c3 (by decide) rfl
    have hc4_ok := hmiss_c 4 c.c4 (by decide) rfl
    have hc5_ok := hmiss_c 5 c.c5 (by decide) rfl
    have hc6_ok := hmiss_c 6 c.c6 (by decide) rfl
    have hc7_ok := hmiss_c 7 c.c7 (by decide) rfl
    have hY_poly : Y ∈ polySet (ofInt c.r_hi)
        (mkRowAS c.a0 c.b0 :: mkRowAS c.a1 c.b1 :: mkRowAS c.a2 c.b2 ::
          [mkRowCS c.c0, mkRowCS c.c1, mkRowCS c.c2, mkRowCS c.c3, mkRowCS c.c4, mkRowCS c.c5, mkRowCS c.c6, mkRowCS c.c7]) := by
      refine ⟨hY4_nn, hY4_hi, fun row hrow => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
      rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hr2_ok
      · exact hr3_ok
      · exact hr4_ok
      · exact hc0_ok
      · exact hc1_ok
      · exact hc2_ok
      · exact hc3_ok
      · exact hc4_ok
      · exact hc5_ok
      · exact hc6_ok
      · exact hc7_ok
    have hGY : 0 ≤ paraG Y := by unfold paraG; linarith [hY_norm]
    exact checkBoxFull_sound vc.ok Y hY_poly hGY
  · intro j x hx y hy
    have htri := dist_triangle_right x y (center j)
    linarith [Metric.mem_closedBall.mp hx, Metric.mem_closedBall.mp hy]

theorem checkEnclosureTree_sound
    {S : Set E4} {b : OrthonormalBasis (Fin 4) ℝ E4} {q : Fin 3 → E4} {r : ℝ}
    (hSdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ 1)
    (hSnorm : ∀ x ∈ S, ‖x‖ ^ 2 ≤ r)
    (hqS : ∀ i, q i ∈ S)
    {P : ParamState} (hrr : P.rr = 4000000 * r)
    (hq0 : b.repr (q 0) 0 = P.ss / 2000 ∧ b.repr (q 0) 1 = 0 ∧ b.repr (q 0) 2 = P.hh / 2000 ∧ b.repr (q 0) 3 = 0)
    (hq1 : b.repr (q 1) 0 = P.xx2 / 2000 ∧ b.repr (q 1) 1 = P.yy2 / 2000 ∧ b.repr (q 1) 2 = P.hh / 2000 ∧ b.repr (q 1) 3 = 0)
    (hq2 : b.repr (q 2) 0 = P.xx3 / 2000 ∧ b.repr (q 2) 1 = P.yy3 / 2000 ∧ b.repr (q 2) 2 = P.hh / 2000 ∧ b.repr (q 2) 3 = 0)
    (t : PTree) :
    ∀ {Q : Box4}, inBox Q P → checkEnclosureTree Q t = true →
      ∃ D : Fin 8 → Set E4, (∀ j, IsClosed (D j)) ∧ S ⊆ ⋃ j, D j ∧
        ∀ j, ∀ x ∈ D j, ∀ y ∈ D j, dist x y ≤ 999 / 1000 := by
  induction t with
  | split axis mid l r ihl ihr =>
    intro Q hQ hchk
    simp only [checkEnclosureTree, Bool.and_eq_true] at hchk
    rcases inBox_split Q axis mid P hQ with hL | hR
    · exact ihl hL hchk.1
    · exact ihr hR hchk.2
  | inf reason =>
    intro Q hQ hchk
    exact False.elim (checkInfeasible_sound hchk hQ)
  | leaf vc =>
    intro Q hQ hchk
    exact checkEnclosure_sound hSdiam hSnorm hqS hrr hq0 hq1 hq2 hQ hchk


private def cert_0 : CoverCert := ⟨1306122, 1350409, 666, 921, 666, 951, 81179, 195228, 221789, 2856236, 3084334, 3137456, (1127, 0, 64, 0), (28, 0, 64, 0), (-786, 793, 64, 0), (88, 128, 64, 0), (-765, -809, 64, 0), (109, 143, 64, 0), (603, -132, 202, 98), (-206, 537, -22, -50), (-257, -562, 12, 10), (-100, 93, 534, 406), (65, 19, 595, -366), (22, 29, -199, 653), (48, -39, -204, -653), (88, 14, -652, -18), 0, 1, 2, 4, 7, 65267972910, 100594196664, 81519864126, 4842400244, 22746203552⟩
private def cert_1 : CoverCert := ⟨1306122, 1350409, 775, 1031, 569, 951, 98824, 195840, 266158, 2891526, 3085558, 3226194, (1099, 0, 64, 0), (56, 0, 64, 0), (-610, 903, 64, 0), (89, 128, 64, 0), (-765, -760, 64, 0), (109, 191, 64, 0), (581, 119, 200, -30), (-216, 583, 12, -31), (-233, -466, 27, 90), (70, 19, 325, 589), (-42, -95, 584, -161), (46, -5, -416, 411), (36, -16, 24, -619), (68, -7, -541, -259), 0, 1, 2, 3, 7, 56698603134, 63133635666, 93223709772, 5224845775, 30152383171⟩
private def cert_2 : CoverCert := ⟨1306122, 1335665, 666, 885, 666, 917, 75715, 178818, 206265, 2845308, 3051514, 3106408, (1113, 0, 192, 0), (14, 0, 64, 0), (-786, 775, 192, 0), (88, 110, 64, 0), (-765, -792, 192, 0), (109, 126, 64, 0), (539, 99, 269, -185), (-305, 568, 140, 18), (-194, -494, -151, 107), (0, -157, 568, 253), (-111, -133, 317, -535), (87, 60, 66, 605), (75, 55, -398, -490), (151, 95, -532, 288), 0, 1, 2, 4, 7, 53953196758, 55682694304, 76579214694, 13847481316, 28449581370⟩
private def cert_3 : CoverCert := ⟨1306122, 1399561, 848, 1031, 789, 951, 82643, 169306, 138380, 2859164, 3032490, 2970638, (1127, 0, 192, 0), (28, 0, 64, 0), (-610, 939, 192, 0), (89, 92, 64, 0), (-711, -870, 192, 0), (55, 81, 64, 0), (628, -83, 170, -28), (-273, 572, -88, 97), (-249, -624, 158, -129), (-40, 65, 620, 311), (-45, 46, 442, -470), (58, -103, -3, 657), (88, 18, -275, -631), (5, -94, -675, 130), 0, 1, 2, 4, 7, 82885159240, 111452344803, 87066570599, 1903790316, 27971354374⟩
private def cert_4 : CoverCert := ⟨1306122, 1350409, 569, 921, 810, 1070, 98824, 240457, 211408, 2891526, 3174792, 3116694, (1099, 0, 64, 0), (56, 0, 64, 0), (-786, 745, 64, 0), (88, 176, 64, 0), (-547, -940, 64, 0), (110, 130, 64, 0), (620, 92, 116, -43), (-221, 524, 140, -91), (-110, -567, 19, 34), (-10, -2, 435, 455), (-12, -143, 560, -354), (3, 39, -261, 570), (-26, -42, -195, -579), (14, 10, -624, -48), 0, 1, 2, 3, 7, 47705038484, 90143380982, 91790204722, 20553528726, 46215795973⟩
private def cert_5 : CoverCert := ⟨1306122, 1350409, 775, 1031, 810, 1070, 98824, 195840, 211408, 2891526, 3085558, 3116694, (1099, 0, 64, 0), (56, 0, 64, 0), (-610, 903, 64, 0), (89, 128, 64, 0), (-547, -940, 64, 0), (110, 130, 64, 0), (615, 66, 58, -57), (-290, 468, 47, 12), (-187, -578, 10, 32), (61, 24, 600, 329), (-4, -31, 523, -408), (46, -18, -68, 642), (-5, 36, -258, -582), (43, 33, -609, 114), 0, 1, 2, 4, 7, 47267061722, 64614302156, 58294228767, 3667706649, 13595262145⟩
private def cert_6 : CoverCert := ⟨1306122, 1399561, 666, 921, 881, 1070, 82643, 198750, 187879, 2859164, 3091378, 3069636, (1127, 0, 192, 0), (28, 0, 64, 0), (-786, 793, 192, 0), (88, 128, 64, 0), (-547, -976, 192, 0), (110, 95, 64, 0), (642, -97, 164, -91), (-258, 537, 2, -41), (-283, -573, 134, 69), (8, 15, 714, -131), (56, -43, 114, -685), (67, 54, 357, 576), (29, -88, -607, -304), (77, 5, -447, 463), 0, 1, 2, 4, 7, 70853472920, 107173137428, 86414088008, 34171853804, 61094843312⟩
private def cert_7 : CoverCert := ⟨1306122, 1399561, 848, 1031, 881, 1070, 82643, 169306, 187879, 2859164, 3032490, 3069636, (1127, 0, 192, 0), (28, 0, 64, 0), (-610, 939, 192, 0), (89, 92, 64, 0), (-547, -976, 192, 0), (110, 95, 64, 0), (649, 34, 118, -61), (-327, 546, 50, -23), (-266, -596, 114, 54), (48, 64, 386, 598), (22, -2, 713, -89), (56, -39, -434, 530), (21, -31, 133, -718), (8, -15, -620, -312), 0, 1, 2, 3, 7, 84378484484, 96659413460, 95758448284, 37486283172, 64799677824⟩
private def cert_8 : CoverCert := ⟨1306122, 1350409, 569, 921, 947, 1135, 98824, 240457, 183052, 2891526, 3174792, 3059982, (1099, 0, 64, 0), (56, 0, 64, 0), (-786, 745, 64, 0), (88, 176, 64, 0), (-328, -1041, 64, 0), (109, 94, 64, 0), (629, 144, 73, 104), (-366, 492, 57, -46), (-165, -578, 21, 50), (9, -10, 646, 267), (72, -65, 460, -492), (36, -13, -63, 691), (47, -60, -294, -584), (32, 19, -649, 103), 0, 1, 2, 4, 7, 79578073717, 99148932268, 102570293853, 26264032900, 39593404970⟩
private def cert_9 : CoverCert := ⟨1306122, 1350409, 775, 1031, 947, 1135, 98824, 195840, 183052, 2891526, 3085558, 3059982, (1099, 0, 64, 0), (56, 0, 64, 0), (-610, 903, 64, 0), (89, 128, 64, 0), (-328, -1041, 64, 0), (109, 94, 64, 0), (626, 67, -36, 8), (-341, 499, 57, -29), (-210, -583, 83, 36), (49, 49, 620, 331), (59, -18, 481, -448), (18, -12, -86, 675), (-10, -37, -306, -609), (-3, -9, -640, 93), 0, 1, 2, 4, 7, 73504792905, 85741680459, 81355694571, 6181412064, 18698257959⟩
private def cert_10 : CoverCert := ⟨1306122, 1399561, 666, 921, 1008, 1135, 82643, 198750, 167611, 2859164, 3091378, 3029100, (1127, 0, 192, 0), (28, 0, 64, 0), (-786, 793, 192, 0), (88, 128, 64, 0), (-328, -1072, 192, 0), (109, 64, 64, 0), (642, 179, 116, 76), (-400, 506, 61, -58), (-157, -623, 72, 41), (1, 21, 656, 295), (34, -54, 533, -457), (1, -5, -36, 701), (38, -60, -286, -630), (35, -20, -673, 107), 0, 1, 2, 4, 7, 82989991817, 99864643453, 101348351603, 22375909798, 51919797235⟩
private def cert_11 : CoverCert := ⟨1306122, 1355257, 569, 849, 569, 882, 81325, 206421, 234646, 2856528, 3106720, 3163170, (1071, 0, 320, 0), (28, 0, 64, 0), (-786, 709, 320, 0), (88, 140, 64, 0), (-765, -726, 320, 0), (109, 157, 64, 0), (404, -139, 321, 402), (-231, 421, 381, 340), (-146, -410, 436, -301), (-269, -439, -56, 425), (496, 199, 274, -346), (174, 248, -519, 311), (-315, 443, 18, -402), (75, -220, -455, -408), 0, 1, 2, 3, 7, 69035063075, 158464657610, 19511505555, 12375063065, 198569896015⟩
private def cert_12 : CoverCert := ⟨1306122, 1417585, 666, 885, 666, 917, 78002, 184220, 212496, 2849882, 3062318, 3118870, (1113, 0, 320, 0), (14, 0, 64, 0), (-786, 775, 320, 0), (88, 110, 64, 0), (-765, -792, 320, 0), (109, 126, 64, 0), (635, 118, 210, 29), (-221, 552, 259, 21), (-35, -266, 598, -181), (-100, -199, 383, 521), (-31, -20, 142, -636), (60, 240, -294, 577), (105, 235, -564, -305), (-139, -502, -298, 11), 0, 1, 2, 6, 7, 66107616648, 108895374976, 9697926504, 12940315552, 136199743936⟩
private def cert_13 : CoverCert := ⟨1306122, 1355257, 775, 968, 708, 882, 81325, 170405, 141099, 2856528, 3034688, 2976076, (1071, 0, 320, 0), (28, 0, 64, 0), (-610, 871, 320, 0), (89, 97, 64, 0), (-711, -795, 320, 0), (55, 87, 64, 0), (582, -293, 148, -31), (-352, 546, -110, 20), (-281, -132, 585, -213), (14, 33, 236, 633), (203, 429, 399, -203), (115, 37, -590, 247), (-5, -67, -214, -664), (-212, -610, -52, 128), 0, 1, 2, 5, 6, 57025947912, 48288025203, 99258653558, 101950828166, 4876080524⟩
private def cert_14 : CoverCert := ⟨1306122, 1417585, 848, 1000, 789, 917, 78002, 158818, 126100, 2849882, 3011514, 2946078, (1113, 0, 320, 0), (14, 0, 64, 0), (-610, 924, 320, 0), (89, 76, 64, 0), (-711, -853, 320, 0), (55, 64, 64, 0), (633, -134, 198, 48), (-282, 511, -160, -36), (-192, -663, 175, -103), (-93, 192, 612, 123), (-61, 112, 354, -547), (-31, -8, 178, 604), (128, -177, -325, -576), (32, -122, -589, 305), 0, 1, 2, 3, 7, 82254432558, 129441264693, 80990955891, 9104925164, 26012575173⟩
private def cert_15 : CoverCert := ⟨1335665, 1436425, 884, 1031, 827, 951, 41863, 143926, 106479, 2748061, 2952187, 2877293, (1141, 0, 288, 0), (14, 0, 32, 0), (-610, 957, 288, 0), (89, 74, 32, 0), (-711, -889, 288, 0), (55, 62, 32, 0), (610, -183, 250, 137), (-252, 565, -93, -18), (-315, -629, 192, -25), (-97, 137, 609, 383), (5, 69, 546, -508), (76, -82, -205, 696), (141, -26, -206, -660), (46, -147, -701, -22), 0, 1, 2, 4, 7, 129353114998, 183843012651, 113710420506, 19815730488, 68320496657⟩
private def cert_16 : CoverCert := ⟨1372529, 1481481, 884, 1031, 827, 951, 42514, 146166, 108136, 2712499, 2919803, 2843743, (1141, 0, 352, 0), (14, 0, 32, 0), (-610, 957, 352, 0), (89, 74, 32, 0), (-711, -889, 352, 0), (55, 62, 32, 0), (592, -208, 260, 179), (-264, 611, -246, -64), (-232, -549, 374, -90), (-134, 244, 554, 399), (22, 186, 456, -483), (24, -133, -200, 670), (157, -198, -175, -667), (8, -214, -626, 33), 0, 1, 2, 4, 7, 99111115712, 137750629972, 98146136188, 3483470048, 48206633208⟩
private def cert_17 : CoverCert := ⟨1306122, 1408505, 569, 769, 569, 790, 50464, 135109, 151847, 2794806, 2964096, 2997572, (1071, 0, 416, 0), (28, 0, 32, 0), (-830, 669, 416, 0), (44, 100, 32, 0), (-820, -680, 416, 0), (55, 111, 32, 0), (357, -180, 233, -494), (-188, 486, 158, 422), (-193, -406, 470, 250), (499, 141, 381, 291), (-235, 294, 427, -446), (-11, -311, -419, 473), (136, 392, -480, -187), (-270, -423, -215, -410), 0, 1, 2, 3, 6, 14448680832, 2723470127, 108851739514, 1303272618, 115528573652⟩
private def cert_18 : CoverCert := ⟨1306122, 1409185, 569, 728, 569, 750, 41464, 114848, 131816, 2776806, 2923574, 2957510, (1057, 0, 480, 0), (14, 0, 32, 0), (-830, 648, 480, 0), (44, 80, 32, 0), (-820, -660, 480, 0), (55, 91, 32, 0), (264, -64, 176, 611), (-252, 442, 485, 113), (-132, -460, 509, -129), (-327, -288, -94, 534), (524, 8, 291, -249), (54, 422, -481, 217), (-160, 250, 74, -611), (34, -388, -456, -313), 0, 1, 4, 5, 7, 73835963460, 162837208660, 26218869880, 20799223340, 196483422100⟩
private def cert_19 : CoverCert := ⟨1347745, 1469945, 619, 769, 619, 790, 42348, 112337, 129706, 2736951, 2876929, 2911667, (1085, 0, 480, 0), (14, 0, 32, 0), (-830, 694, 480, 0), (44, 75, 32, 0), (-820, -705, 480, 0), (55, 86, 32, 0), (527, -10, 430, -95), (-182, 695, 149, 55), (-317, -75, 657, -21), (71, -14, 286, 670), (-8, 17, 209, -702), (22, -26, -455, 420), (-21, 3, -507, -370), (-185, -669, 93, 13), 0, 1, 2, 3, 6, 49061495814, 12296743610, 90433473360, 143028494204, 243095856682⟩
private def cert_20 : CoverCert := ⟨1306122, 1408505, 685, 849, 569, 790, 50464, 116791, 151847, 2794806, 2927460, 2997572, (1071, 0, 416, 0), (28, 0, 32, 0), (-742, 767, 416, 0), (44, 82, 32, 0), (-820, -680, 416, 0), (55, 111, 32, 0), (533, 30, 426, -44), (-270, 540, 281, 4), (-204, -396, 470, -283), (-153, -241, 353, 511), (80, 58, -23, -699), (139, 223, -157, 644), (114, 271, -573, -135), (-138, -445, -347, 32), 0, 1, 2, 3, 6, 43707051939, 25522609294, 107187308076, 117103376333, 205072572389⟩
private def cert_21 : CoverCert := ⟨1306122, 1409185, 685, 813, 569, 750, 41464, 99716, 131816, 2776806, 2893310, 2957510, (1057, 0, 480, 0), (14, 0, 32, 0), (-742, 749, 480, 0), (44, 64, 32, 0), (-820, -660, 480, 0), (55, 91, 32, 0), (516, 98, 269, -265), (27, 302, -550, 262), (-210, -378, 516, -214), (-226, 462, 403, 343), (-206, 496, 101, -474), (282, -130, 252, 530), (23, -340, -384, -485), (-390, -399, -171, 419), 0, 1, 2, 3, 5, 63385952704, 205257344720, 182643230356, 2482996608, 2365729452⟩
private def cert_22 : CoverCert := ⟨1347745, 1469945, 727, 849, 619, 790, 42348, 99100, 129706, 2736951, 2850455, 2911667, (1085, 0, 480, 0), (14, 0, 32, 0), (-742, 788, 480, 0), (44, 61, 32, 0), (-820, -705, 480, 0), (55, 86, 32, 0), (509, -105, 440, -29), (-82, 423, -396, 109), (-288, -580, 294, -147), (-146, 233, 410, 449), (-152, 375, 482, -285), (87, -185, 35, 686), (61, 44, -100, -684), (108, -364, -525, 59), 0, 1, 2, 4, 7, 34671690974, 67878182723, 42327449900, 1140508039, 2609102506⟩
private def cert_23 : CoverCert := ⟨1306122, 1408505, 569, 769, 708, 882, 50464, 135109, 127922, 2794806, 2964096, 2949722, (1071, 0, 416, 0), (28, 0, 32, 0), (-830, 669, 416, 0), (44, 100, 32, 0), (-711, -795, 416, 0), (55, 87, 32, 0), (543, -167, 331, 16), (-152, 554, -169, 38), (-344, -547, 198, -74), (-93, 167, 493, 453), (-85, 240, 521, -313), (112, -127, -103, 633), (98, -36, -45, -655), (70, -184, -660, -17), 0, 1, 2, 3, 7, 86222506719, 125331675324, 88095798432, 2306949807, 39301349907⟩
private def cert_24 : CoverCert := ⟨1306122, 1409185, 569, 728, 708, 847, 41464, 114848, 112298, 2776806, 2923574, 2918474, (1057, 0, 480, 0), (14, 0, 32, 0), (-830, 648, 480, 0), (44, 80, 32, 0), (-711, -778, 480, 0), (55, 70, 32, 0), (539, 134, 328, -201), (34, 379, -532, 209), (-132, -469, 517, -126), (-311, 438, 446, 264), (-276, 353, 133, -560), (251, -80, 184, 622), (66, -310, -345, -488), (-284, -413, -226, 421), 0, 1, 2, 3, 6, 25436239215, 116290461485, 103088530725, 17781774175, 22330442375⟩
private def cert_25 : CoverCert := ⟨1347745, 1469945, 619, 769, 749, 882, 42348, 112337, 112029, 2736951, 2876929, 2876313, (1085, 0, 480, 0), (14, 0, 32, 0), (-830, 694, 480, 0), (44, 75, 32, 0), (-711, -816, 480, 0), (55, 67, 32, 0), (529, 42, 414, -60), (-270, 687, 138, -36), (-313, -93, 610, 39), (114, 36, 288, 638), (73, -60, 244, -698), (-5, 14, -497, 430), (2, -18, -472, -376), (-226, -701, 130, 46), 0, 1, 2, 3, 6, 28471487952, 9202917024, 87539553168, 126207370488, 217805187912⟩
private def cert_26 : CoverCert := ⟨1306122, 1408505, 685, 849, 708, 882, 50464, 116791, 127922, 2794806, 2927460, 2949722, (1071, 0, 416, 0), (28, 0, 32, 0), (-742, 767, 416, 0), (44, 82, 32, 0), (-711, -795, 416, 0), (55, 87, 32, 0), (524, -48, 424, 126), (-168, 500, -140, -42), (-233, -549, 233, 1), (-115, 222, 485, 412), (-127, 204, 534, -381), (26, -58, -219, 601), (117, -54, -13, -636), (114, -201, -599, -141), 0, 1, 2, 3, 7, 40354749370, 73446791730, 52584793352, 8188419616, 38483310944⟩
private def cert_27 : CoverCert := ⟨1306122, 1409185, 685, 813, 708, 847, 41464, 99716, 112298, 2776806, 2893310, 2918474, (1057, 0, 480, 0), (14, 0, 32, 0), (-742, 749, 480, 0), (44, 64, 32, 0), (-711, -778, 480, 0), (55, 70, 32, 0), (578, -105, 363, 21), (-136, 413, -362, -109), (-341, -472, 371, 73), (-134, 408, 292, 452), (-112, 374, 517, -334), (93, -148, -155, 653), (70, -159, -37, -700), (81, -333, -522, -45), 0, 1, 2, 3, 7, 75800802996, 123108251922, 81017712000, 16479898821, 34138325478⟩
private def cert_28 : CoverCert := ⟨1347745, 1469945, 727, 849, 749, 882, 42348, 99100, 112029, 2736951, 2850455, 2876313, (1085, 0, 480, 0), (14, 0, 32, 0), (-742, 788, 480, 0), (44, 61, 32, 0), (-711, -816, 480, 0), (55, 67, 32, 0), (586, -37, 369, -38), (-215, 534, -290, 38), (-169, -625, 340, -24), (-154, 235, 458, 429), (-114, 270, 594, -333), (106, -173, -95, 654), (-51, -49, -110, -684), (63, -255, -611, -13), 0, 1, 2, 3, 7, 69347972865, 126557592450, 90883442865, 1021477479, 33152057997⟩
private def cert_29 : CoverCert := ⟨1306122, 1408505, 775, 968, 708, 882, 50464, 160785, 127922, 2794806, 3015448, 2949722, (1071, 0, 416, 0), (28, 0, 32, 0), (-610, 871, 416, 0), (89, 97, 32, 0), (-711, -795, 416, 0), (55, 87, 32, 0), (577, -39, 317, 5), (-213, 504, -288, 5), (-343, -491, 353, -57), (-70, 201, 481, 444), (-135, 305, 423, -430), (116, -176, -131, 607), (116, -144, -102, -659), (126, -329, -562, -13), 0, 1, 2, 3, 7, 90482728846, 126070342502, 91167504324, 10815683254, 52952382696⟩
private def cert_30 : CoverCert := ⟨1306122, 1409185, 775, 936, 708, 847, 41464, 147821, 112298, 2776806, 2989520, 2918474, (1057, 0, 480, 0), (14, 0, 32, 0), (-610, 855, 480, 0), (89, 81, 32, 0), (-711, -778, 480, 0), (55, 70, 32, 0), (582, -100, 351, -28), (-207, 492, -243, 25), (-312, -566, 245, -22), (-137, 323, 508, -345), (84, -68, -30, -735), (-133, 281, 494, 383), (71, -176, -594, -24), (102, -112, -18, 653), 0, 1, 2, 4, 7, 27154098024, 66462505548, 36738691164, 47437850634, 53252409690⟩
private def cert_31 : CoverCert := ⟨1347745, 1438201, 812, 968, 749, 882, 25497, 143214, 105712, 2703249, 2938683, 2863679, (1085, 0, 464, 0), (14, 0, 16, 0), (-610, 890, 464, 0), (89, 78, 16, 0), (-711, -816, 464, 0), (55, 67, 16, 0), (608, -141, 368, -121), (-121, 463, -306, 119), (-313, -506, 385, -72), (-115, 346, 513, 326), (-138, 338, 410, -520), (90, -119, 65, 653), (13, -130, -290, -629), (136, -317, -484, 199), 0, 1, 2, 4, 7, 49730546530, 102885651304, 66680742936, 18667678104, 41619144374⟩
private def cert_32 : CoverCert := ⟨1377441, 1469945, 812, 968, 749, 882, 25777, 144786, 106872, 2674113, 2912131, 2836303, (1085, 0, 496, 0), (14, 0, 16, 0), (-610, 890, 496, 0), (89, 78, 16, 0), (-711, -816, 496, 0), (55, 67, 16, 0), (562, -123, 307, -114), (-185, 584, -355, 97), (-283, -503, 405, -119), (-110, 246, 528, 347), (-106, 322, 441, -496), (89, -102, 99, 660), (96, -106, -325, -589), (-12, -349, -449, 220), 0, 1, 2, 4, 7, 50422600832, 70730292208, 52030094160, 1885309488, 27336513008⟩
private def cert_33 : CoverCert := ⟨1355257, 1470833, 666, 885, 666, 828, 42361, 175196, 124923, 2729465, 2995135, 2894589, (1113, 0, 416, 0), (14, 0, 32, 0), (-786, 775, 416, 0), (88, 110, 32, 0), (-820, -747, 416, 0), (55, 81, 32, 0), (498, -148, 298, -162), (-245, 563, -323, 62), (-281, -603, 285, 52), (-100, 295, 632, 229), (-132, 231, 397, -563), (128, -18, 156, 658), (-27, -213, -300, -646), (29, -203, -586, 235), 0, 1, 2, 4, 7, 86861793294, 101670195206, 66869528958, 1393812000, 21598123664⟩
private def cert_34 : CoverCert := ⟨1355257, 1470833, 768, 885, 789, 917, 42361, 97333, 109453, 2729465, 2839409, 2863649, (1113, 0, 416, 0), (14, 0, 32, 0), (-742, 826, 416, 0), (44, 59, 32, 0), (-711, -853, 416, 0), (55, 64, 32, 0), (581, 89, 383, -46), (-295, 531, 377, 95), (-178, -401, 601, -53), (29, -89, 247, 681), (-59, 68, 193, -721), (12, 191, -446, 421), (40, 238, -437, -401), (-158, -537, -247, -85), 0, 1, 2, 5, 6, 48531668499, 10110288207, 184108481997, 160332729981, 140823816471⟩
private def cert_35 : CoverCert := ⟨1408505, 1532273, 768, 885, 789, 917, 43237, 99345, 111716, 2677969, 2790185, 2814927, (1113, 0, 480, 0), (14, 0, 32, 0), (-742, 826, 480, 0), (44, 59, 32, 0), (-711, -853, 480, 0), (55, 64, 32, 0), (616, -140, 282, 34), (-240, 618, -191, 117), (-244, -602, 342, -166), (-163, 279, 645, 15), (38, 138, 258, -704), (10, -32, 348, 591), (-1, -30, -515, -397), (-56, -264, -344, 537), 0, 1, 2, 4, 7, 45337401236, 69018390200, 37131248272, 75206915696, 92165423776⟩
private def cert_36 : CoverCert := ⟨1355257, 1470833, 848, 1000, 789, 917, 42361, 147147, 109453, 2729465, 2939037, 2863649, (1113, 0, 416, 0), (14, 0, 32, 0), (-610, 924, 416, 0), (89, 76, 32, 0), (-711, -853, 416, 0), (55, 64, 32, 0), (546, -153, 405, 111), (-227, 526, -264, -48), (-298, -637, 247, -110), (-151, 228, 486, 398), (-72, 238, 534, -387), (7, -128, -70, 629), (130, -170, -79, -728), (146, -116, -650, 19), 0, 1, 2, 3, 7, 90658176028, 130504131888, 82132754340, 11102653992, 42994077900⟩
private def cert_37 : CoverCert := ⟨1417585, 1507081, 884, 1031, 827, 951, 26100, 143444, 103625, 2634615, 2869303, 2789665, (1141, 0, 400, 0), (14, 0, 16, 0), (-610, 957, 400, 0), (89, 74, 16, 0), (-711, -889, 400, 0), (55, 62, 16, 0), (578, -225, 289, -124), (-248, 609, -109, 137), (-246, -649, 230, -52), (-106, 223, 637, 176), (-62, 90, 442, -639), (155, -116, 193, 666), (9, 13, -388, -579), (37, -130, -523, 372), 0, 1, 2, 4, 7, 57435975567, 83819170117, 50036561732, 46988334487, 75984627988⟩
private def cert_38 : CoverCert := ⟨1443185, 1534729, 884, 1031, 827, 951, 26339, 144754, 104571, 2609493, 2846323, 2765957, (1141, 0, 432, 0), (14, 0, 16, 0), (-610, 957, 432, 0), (89, 74, 16, 0), (-711, -889, 432, 0), (55, 62, 16, 0), (584, -198, 397, -145), (-219, 600, -236, 64), (-232, -582, 362, -40), (-82, 264, 534, 381), (-113, 259, 470, -558), (127, -203, 18, 688), (-3, -150, -276, -620), (98, -132, -602, 185), 0, 1, 2, 4, 7, 69505256410, 115901015598, 86287633911, 8610703194, 59010134702⟩
private def cert_39 : CoverCert := ⟨1408505, 1500529, 848, 1000, 789, 917, 26044, 144696, 105212, 2643583, 2880887, 2801919, (1113, 0, 464, 0), (14, 0, 16, 0), (-610, 924, 464, 0), (89, 76, 16, 0), (-711, -853, 464, 0), (55, 64, 16, 0), (679, -105, 302, -51), (-272, 567, -58, 57), (-216, -636, 328, -104), (-155, 241, 667, -163), (22, 72, 11, -771), (-3, 16, 392, 580), (85, -162, -569, -258), (43, -197, -353, 624), 0, 1, 2, 4, 7, 83316318708, 160602575208, 98223934824, 105984184068, 139461347124⟩
private def cert_40 : CoverCert := ⟨1438201, 1500913, 848, 984, 789, 900, 21396, 138612, 98140, 2604591, 2839023, 2758079, (1106, 0, 496, 0), (7, 0, 16, 0), (-610, 916, 496, 0), (89, 68, 16, 0), (-711, -845, 496, 0), (55, 56, 16, 0), (583, -107, 394, -76), (-261, 578, -327, 106), (-227, -643, 328, -127), (-167, 198, 614, 373), (-110, 379, 523, -354), (84, -105, 91, 684), (33, -20, -138, -702), (75, -275, -477, 150), 0, 1, 2, 4, 7, 35748297819, 53442711063, 35385140592, 5474459925, 23225432868⟩
private def cert_41 : CoverCert := ⟨1469169, 1532273, 866, 948, 808, 917, 21619, 77036, 98299, 2574069, 2684903, 2727429, (1120, 0, 496, 0), (7, 0, 16, 0), (-654, 907, 496, 0), (44, 41, 16, 0), (-711, -863, 496, 0), (55, 55, 16, 0), (661, -124, 340, 64), (-234, 632, -114, 139), (-123, -626, 257, -162), (-134, 189, 668, 253), (-85, 176, 469, -550), (-33, -144, 150, 706), (70, 33, -248, -671), (-10, -133, -603, 242), 0, 1, 2, 4, 7, 55326242600, 95387414412, 80176720429, 42196726865, 80153298990⟩
private def cert_42 : CoverCert := ⟨1470833, 1572516, 884, 981, 827, 951, 43801, 91817, 111409, 2616769, 2712801, 2751985, (1141, 0, 480, 0), (14, 0, 32, 0), (-654, 932, 480, 0), (44, 49, 32, 0), (-711, -889, 480, 0), (55, 62, 32, 0), (649, -66, 278, 61), (-271, 603, -179, 60), (-186, -566, 458, -123), (-167, 323, 687, -14), (22, 123, 241, -773), (-45, -22, 337, 708), (-33, -226, -536, -398), (-77, -266, -414, 569), 0, 1, 2, 4, 7, 77188270388, 109250775452, 65301424784, 106280715212, 138705689080⟩
private def cert_43 : CoverCert := ⟨1306122, 1355257, 569, 849, 810, 1009, 81325, 206421, 188421, 2856528, 3106720, 3070720, (1071, 0, 320, 0), (28, 0, 64, 0), (-786, 709, 320, 0), (88, 140, 64, 0), (-547, -910, 320, 0), (110, 100, 64, 0), (565, 4, 252, -87), (-194, 409, -232, 18), (-222, -563, 230, 43), (-30, 167, 398, 468), (-108, 252, 510, -284), (87, -144, -185, 584), (11, -103, -84, -620), (173, -180, -602, -79), 0, 1, 2, 3, 7, 61630656786, 107172857446, 74418841972, 3016381274, 14923049806⟩
private def cert_44 : CoverCert := ⟨1306122, 1372529, 666, 885, 881, 1039, 40921, 169240, 163031, 2775720, 3032358, 3019940, (1113, 0, 288, 0), (14, 0, 32, 0), (-786, 775, 288, 0), (88, 110, 32, 0), (-547, -960, 288, 0), (110, 79, 32, 0), (615, -57, 256, -27), (-213, 556, -144, 14), (-240, -606, 151, 18), (-6, 5, 271, 605), (-101, 231, 645, -52), (138, -70, -446, 404), (12, 25, 203, -633), (106, -118, -553, -319), 0, 1, 2, 3, 7, 70452818507, 116056905363, 92993194939, 16643112021, 35942103000⟩
private def cert_45 : CoverCert := ⟨1310201, 1417585, 666, 885, 881, 1039, 41587, 171995, 165686, 2772973, 3033789, 3021171, (1113, 0, 352, 0), (14, 0, 32, 0), (-786, 775, 352, 0), (88, 110, 32, 0), (-547, -960, 352, 0), (110, 79, 32, 0), (653, 136, 230, 31), (-216, 547, 341, 92), (-79, -330, 608, -138), (-44, -159, 250, 612), (5, -22, 181, -621), (48, 214, -458, 451), (52, 235, -456, -412), (-152, -494, -249, -57), 0, 1, 2, 3, 6, 6930045288, 6748000074, 91407902184, 169664150079, 223436448441⟩
private def cert_46 : CoverCert := ⟨1306122, 1355257, 775, 968, 810, 1009, 81325, 170405, 188421, 2856528, 3034688, 3070720, (1071, 0, 320, 0), (28, 0, 64, 0), (-610, 871, 320, 0), (89, 97, 64, 0), (-547, -910, 320, 0), (110, 100, 64, 0), (610, -100, 193, 25), (-174, 480, -129, 51), (-295, -501, 257, -61), (-119, 340, 576, 115), (10, 86, 252, -610), (19, -11, 194, 621), (90, -95, -480, -430), (90, -157, -513, 321), 0, 1, 2, 4, 7, 55485330570, 97273898250, 72370397232, 27459717876, 46158629472⟩
private def cert_47 : CoverCert := ⟨1306122, 1372529, 848, 1000, 881, 1039, 40921, 142145, 163031, 2775720, 2978168, 3019940, (1113, 0, 288, 0), (14, 0, 32, 0), (-610, 924, 288, 0), (89, 76, 32, 0), (-547, -960, 288, 0), (110, 79, 32, 0), (646, -38, 203, -49), (-230, 554, 71, 42), (-235, -596, 82, 36), (-44, 86, 685, 174), (-33, 11, 453, -575), (52, -32, 113, 679), (-9, 5, -365, -581), (112, 15, -619, 238), 0, 1, 2, 4, 7, 59983520421, 102169723293, 93641035785, 37787729661, 71449291551⟩
private def cert_48 : CoverCert := ⟨1310201, 1417585, 848, 1000, 881, 1039, 41587, 144459, 165686, 2772973, 2978717, 3021171, (1113, 0, 352, 0), (14, 0, 32, 0), (-610, 924, 352, 0), (89, 76, 32, 0), (-547, -960, 352, 0), (110, 79, 32, 0), (599, 103, 274, -13), (-279, 619, 177, -88), (-93, -190, 640, 49), (27, -15, 215, 627), (2, -80, 223, -655), (52, 142, -481, 411), (181, 141, -555, -357), (-231, -519, -132, 28), 0, 1, 3, 6, 7, 82309159430, 95484326326, 38229457310, 51839523140, 143195707746⟩
private def cert_49 : CoverCert := ⟨1335665, 1436425, 884, 1031, 916, 1070, 41863, 143926, 165434, 2748061, 2952187, 2995203, (1141, 0, 288, 0), (14, 0, 32, 0), (-610, 957, 288, 0), (89, 74, 32, 0), (-547, -993, 288, 0), (110, 77, 32, 0), (715, 57, -28, -16), (-276, 595, 143, 96), (-231, -628, 7, -24), (35, -4, 616, -265), (-14, 14, 46, -704), (30, -18, 595, 347), (-76, 105, -723, -150), (-11, -17, -233, 680), 0, 1, 2, 3, 6, 94310904042, 125794848628, 132895093054, 10184866308, 31192394658⟩
private def cert_50 : CoverCert := ⟨1372529, 1449337, 884, 1016, 916, 1002, 39436, 138844, 92457, 2706343, 2905159, 2812385, (1134, 0, 352, 0), (7, 0, 32, 0), (-610, 950, 352, 0), (89, 66, 32, 0), (-602, -959, 352, 0), (55, 43, 32, 0), (631, -21, 308, 83), (-181, 519, -245, 39), (-129, -560, 270, -220), (-137, 195, 559, 382), (-103, 185, 488, -495), (-24, -250, -1, 690), (116, -134, -286, -614), (126, -222, -576, 264), 0, 1, 2, 3, 7, 74157493866, 176058531114, 146531334804, 16269962958, 49243989025⟩
private def cert_51 : CoverCert := ⟨1404281, 1481481, 902, 1031, 933, 1018, 39871, 139683, 93477, 2675461, 2875085, 2782673, (1148, 0, 352, 0), (7, 0, 32, 0), (-610, 966, 352, 0), (89, 65, 32, 0), (-602, -976, 352, 0), (55, 43, 32, 0), (695, -124, 151, -59), (-349, 628, -110, 6), (-182, -630, 322, 80), (-40, 133, 674, 230), (-86, 60, 448, -548), (82, -47, 60, 744), (-10, -130, -342, -591), (-16, -167, -648, 303), 0, 1, 2, 4, 7, 92167294736, 122552221608, 88122483360, 46731562108, 76771136720⟩
private def cert_52 : CoverCert := ⟨1372529, 1425785, 884, 1016, 985, 1054, 20854, 133677, 80154, 2669179, 2894825, 2787779, (1134, 0, 336, 0), (7, 0, 16, 0), (-610, 950, 336, 0), (89, 66, 16, 0), (-492, -1020, 336, 0), (55, 35, 16, 0), (699, -59, 107, 25), (-334, 530, 93, -45), (-233, -613, 191, -25), (3, -14, 639, 363), (77, 81, 626, -450), (3, 68, -99, 746), (24, -49, -272, -678), (27, -107, -669, 169), 0, 1, 2, 4, 7, 64445579660, 94253754480, 67528062800, 9922513040, 51974034900⟩
private def cert_53 : CoverCert := ⟨1394033, 1449337, 884, 1016, 985, 1054, 21025, 134776, 80813, 2648017, 2875519, 2767593, (1134, 0, 368, 0), (7, 0, 16, 0), (-610, 950, 368, 0), (89, 66, 16, 0), (-492, -1020, 368, 0), (55, 35, 16, 0), (678, 10, 248, -6), (-335, 544, -70, -36), (-170, -605, 325, 23), (-13, 66, 419, 638), (-91, 163, 688, -223), (62, -135, -408, 560), (44, -60, 134, -745), (54, -145, -576, -322), 0, 1, 2, 3, 7, 72709512831, 118080854100, 87583527714, 59551389570, 109692670368⟩
private def cert_54 : CoverCert := ⟨1404281, 1481481, 902, 1031, 1001, 1070, 39871, 139683, 88394, 2675461, 2875085, 2772507, (1148, 0, 352, 0), (7, 0, 32, 0), (-610, 966, 352, 0), (89, 65, 32, 0), (-492, -1036, 352, 0), (55, 35, 32, 0), (755, -36, 216, -53), (-323, 579, 30, 81), (-249, -649, 265, -24), (-8, 31, 716, -236), (-68, 23, 29, -789), (36, -12, 480, 575), (49, -141, -629, -318), (61, -105, -407, 595), 0, 1, 2, 4, 7, 112890533011, 171293843848, 124764867503, 129107922307, 162972948602⟩
private def cert_55 : CoverCert := ⟨1306122, 1408505, 569, 849, 810, 954, 50464, 199892, 114039, 2794806, 3093662, 2921956, (1071, 0, 416, 0), (28, 0, 32, 0), (-786, 709, 416, 0), (88, 140, 32, 0), (-602, -882, 416, 0), (55, 72, 32, 0), (611, 31, 270, -47), (-282, 500, -271, 15), (-203, -521, 384, -35), (-79, 247, 503, 406), (-143, 247, 406, -404), (61, -160, -60, 605), (38, -151, -201, -614), (89, -303, -547, 85), 0, 1, 2, 3, 7, 87347346946, 131417067970, 102197692248, 3061311642, 52565835164⟩
private def cert_56 : CoverCert := ⟨1306122, 1409185, 569, 813, 810, 921, 41464, 182566, 100624, 2776806, 3059010, 2895126, (1057, 0, 480, 0), (14, 0, 32, 0), (-786, 691, 480, 0), (88, 122, 32, 0), (-602, -866, 480, 0), (55, 56, 32, 0), (513, -11, 427, 68), (-235, 488, -324, -17), (-245, -636, 205, -40), (-218, 245, 435, 394), (-199, 307, 434, -341), (119, -143, -141, 616), (117, -104, 31, -679), (200, -221, -578, -107), 0, 1, 2, 3, 7, 63318861774, 88813886171, 61205819131, 5274134199, 22669370513⟩
private def cert_57 : CoverCert := ⟨1347745, 1469945, 619, 849, 846, 954, 42348, 179802, 101184, 2736951, 3011859, 2854623, (1085, 0, 480, 0), (14, 0, 32, 0), (-786, 734, 480, 0), (88, 115, 32, 0), (-602, -900, 480, 0), (55, 54, 32, 0), (584, -100, 273, 36), (-248, 481, -395, -6), (-249, -553, 427, 40), (-140, 271, 344, 556), (-130, 324, 577, -297), (150, -263, -263, 564), (35, -52, 54, -695), (31, -359, -502, -187), 0, 1, 2, 4, 7, 102362180210, 146609543648, 94651555249, 5271329761, 26876248645⟩
private def cert_58 : CoverCert := ⟨1306122, 1408505, 569, 769, 888, 1009, 50464, 135109, 104614, 2794806, 2964096, 2903106, (1071, 0, 416, 0), (28, 0, 32, 0), (-830, 669, 416, 0), (44, 100, 32, 0), (-492, -949, 416, 0), (55, 61, 32, 0), (525, -9, 410, 17), (-193, 485, -293, 9), (-255, -632, 148, -63), (-147, 133, 498, 391), (-182, 237, 496, -433), (114, -130, -95, 600), (122, -107, -86, -647), (253, -183, -566, 21), 0, 1, 2, 3, 7, 75228465822, 117058108280, 83891442068, 6399033444, 21463422866⟩
private def cert_59 : CoverCert := ⟨1306122, 1408505, 685, 849, 888, 1009, 50464, 116791, 104614, 2794806, 2927460, 2903106, (1071, 0, 416, 0), (28, 0, 32, 0), (-742, 767, 416, 0), (44, 82, 32, 0), (-492, -949, 416, 0), (55, 61, 32, 0), (584, 74, 363, -47), (-343, 504, 300, 14), (-152, -423, 543, -22), (34, -25, 311, 654), (25, 6, 136, -689), (87, 154, -394, 452), (99, 139, -525, -349), (-199, -502, -157, 30), 0, 1, 2, 3, 6, 9164832962, 39929863616, 113599077349, 119731483467, 217574445350⟩
private def cert_60 : CoverCert := ⟨1306122, 1409185, 569, 813, 888, 978, 41464, 182566, 92517, 2776806, 3059010, 2878912, (1057, 0, 480, 0), (14, 0, 32, 0), (-786, 691, 480, 0), (88, 122, 32, 0), (-492, -933, 480, 0), (55, 45, 32, 0), (584, -11, 347, 41), (-211, 459, -255, 7), (-200, -606, 226, -40), (-129, 158, 523, 376), (-150, 286, 474, -342), (58, -131, -114, 626), (73, -110, -40, -656), (208, -208, -615, -41), 0, 1, 2, 3, 7, 56514545108, 103598905886, 72103838231, 1390710606, 16610789006⟩
private def cert_61 : CoverCert := ⟨1347745, 1438201, 619, 849, 920, 1009, 25497, 174717, 87357, 2703249, 3001689, 2826969, (1085, 0, 464, 0), (14, 0, 16, 0), (-786, 734, 464, 0), (88, 115, 16, 0), (-492, -965, 464, 0), (55, 45, 16, 0), (600, -151, 336, 23), (-147, 581, 285, 33), (-215, -145, 654, 109), (44, -25, 179, 694), (-23, 38, 338, -682), (56, 51, -548, 437), (101, 130, -446, -501), (-210, -591, -69, -62), 0, 1, 2, 5, 6, 32879959717, 10346664012, 190272643188, 126991890185, 154356992224⟩
private def cert_62 : CoverCert := ⟨1377441, 1469945, 619, 769, 920, 1009, 25777, 107195, 88315, 2674113, 2836949, 2799189, (1085, 0, 496, 0), (14, 0, 16, 0), (-830, 694, 496, 0), (44, 75, 16, 0), (-492, -965, 496, 0), (55, 45, 16, 0), (488, 241, 383, 68), (-385, 541, 242, -51), (-53, -325, 575, -305), (-60, -189, 514, 445), (90, 42, 18, -674), (69, 135, -172, 635), (36, 58, -661, -84), (-124, -632, -125, 12), 0, 1, 2, 3, 6, 46853274810, 49742364589, 94858258483, 102781551854, 207799807509⟩
private def cert_63 : CoverCert := ⟨1377441, 1469945, 727, 849, 920, 1009, 25777, 93230, 88315, 2674113, 2809019, 2799189, (1085, 0, 496, 0), (14, 0, 16, 0), (-742, 788, 496, 0), (44, 61, 16, 0), (-492, -965, 496, 0), (55, 45, 16, 0), (513, 136, 421, -75), (-401, 512, 295, 81), (-129, -409, 582, -74), (24, -57, 311, 664), (-32, -20, 222, -674), (184, 152, -426, 460), (116, 268, -415, -462), (-170, -582, -255, -13), 0, 1, 3, 6, 7, 62689968603, 65094071295, 65743154532, 92680387698, 108152894034⟩
private def cert_64 : CoverCert := ⟨1306122, 1408505, 775, 968, 810, 954, 50464, 160785, 114039, 2794806, 3015448, 2921956, (1071, 0, 416, 0), (28, 0, 32, 0), (-610, 871, 416, 0), (89, 97, 32, 0), (-602, -882, 416, 0), (55, 72, 32, 0), (519, -26, 409, 63), (-213, 469, -283, 6), (-303, -552, 217, -100), (-56, 163, 422, 486), (-164, 244, 540, -313), (123, -212, -190, 566), (141, -68, -61, -680), (279, -280, -586, -89), 0, 1, 2, 3, 7, 83375692808, 126230021021, 87416689153, 12718963005, 38761751440⟩
private def cert_65 : CoverCert := ⟨1306122, 1409185, 775, 936, 810, 921, 41464, 147821, 100624, 2776806, 2989520, 2895126, (1057, 0, 480, 0), (14, 0, 32, 0), (-610, 855, 480, 0), (89, 81, 32, 0), (-602, -866, 480, 0), (55, 56, 32, 0), (536, -6, 406, 64), (-256, 456, -297, 19), (-287, -529, 297, -79), (-97, 191, 492, 466), (-206, 346, 425, -392), (126, -189, -163, 576), (201, -94, -94, -673), (147, -255, -562, -93), 0, 1, 2, 3, 7, 75088018290, 101843079990, 68856005826, 5519025594, 41644012440⟩
private def cert_66 : CoverCert := ⟨1347745, 1438201, 812, 968, 846, 954, 25497, 143214, 94407, 2703249, 2938683, 2841069, (1085, 0, 464, 0), (14, 0, 16, 0), (-610, 890, 464, 0), (89, 78, 16, 0), (-602, -900, 464, 0), (55, 54, 16, 0), (555, -66, 421, -143), (-263, 541, -238, 19), (-249, -615, 231, 142), (-138, 277, 560, 315), (-166, 174, 479, -489), (168, -71, -31, 651), (15, -166, -181, -647), (194, -163, -574, 93), 0, 1, 2, 4, 7, 78569945744, 117304495102, 84418413498, 16957439274, 57112794868⟩
private def cert_67 : CoverCert := ⟨1377441, 1469945, 812, 968, 846, 954, 25777, 144786, 95443, 2674113, 2912131, 2813445, (1085, 0, 496, 0), (14, 0, 16, 0), (-610, 890, 496, 0), (89, 78, 16, 0), (-602, -900, 496, 0), (55, 54, 16, 0), (644, 23, 318, 77), (-242, 555, -250, 69), (-211, -510, 394, -85), (-188, 344, 582, -11), (51, 49, 161, -703), (-12, -43, 279, 654), (162, -244, -411, -418), (36, -300, -513, 471), 0, 1, 2, 4, 7, 91290077412, 162146589906, 128713320582, 77944923786, 100888456490⟩
private def cert_68 : CoverCert := ⟨1306122, 1408505, 775, 968, 888, 1009, 50464, 160785, 104614, 2794806, 3015448, 2903106, (1071, 0, 416, 0), (28, 0, 32, 0), (-610, 871, 416, 0), (89, 97, 32, 0), (-492, -949, 416, 0), (55, 61, 32, 0), (639, 26, 245, 9), (-334, 413, -299, 9), (-201, -583, 345, -2), (-17, 84, 270, 626), (-170, 303, 524, -90), (149, -269, -313, 505), (41, 2, 164, -683), (129, -269, -574, -322), 0, 1, 2, 3, 7, 103015954165, 149432807665, 97987029364, 12605566648, 30953880495⟩
private def cert_69 : CoverCert := ⟨1306122, 1409185, 775, 936, 888, 978, 41464, 147821, 92517, 2776806, 2989520, 2878912, (1057, 0, 480, 0), (14, 0, 32, 0), (-610, 855, 480, 0), (89, 81, 32, 0), (-492, -933, 480, 0), (55, 45, 32, 0), (588, 30, 324, -50), (-275, 496, -293, 4), (-225, -507, 282, 9), (-74, 158, 418, 487), (-162, 230, 561, -325), (157, -198, -147, 594), (54, -131, -71, -708), (203, -337, -570, -51), 0, 1, 2, 3, 7, 87770678046, 129841784808, 106533557894, 10540247964, 43583059146⟩
private def cert_70 : CoverCert := ⟨1347745, 1469945, 812, 968, 920, 1009, 42348, 148634, 94491, 2736951, 2949523, 2841237, (1085, 0, 480, 0), (14, 0, 32, 0), (-610, 890, 480, 0), (89, 78, 32, 0), (-492, -965, 480, 0), (55, 45, 32, 0), (594, 53, 379, 83), (-341, 535, -246, 38), (-253, 310, 567, 18), (-8, -32, 271, 657), (27, 67, 263, -675), (99, -193, -427, 387), (218, -168, -421, -438), (-188, -610, 290, -90), 0, 1, 2, 4, 5, 2558945464, 1808173118, 81935471540, 101542512137, 172571716157⟩
private def cert_71 : CoverCert := ⟨1355257, 1470833, 666, 885, 881, 1039, 42361, 175196, 168769, 2729465, 2995135, 2982281, (1113, 0, 416, 0), (14, 0, 32, 0), (-786, 775, 416, 0), (88, 110, 32, 0), (-547, -960, 416, 0), (110, 79, 32, 0), (640, 128, 295, 20), (-257, 528, 374, 48), (-121, -373, 601, -39), (-25, -84, 268, 632), (-3, -44, 279, -652), (53, 188, -438, 451), (55, 248, -459, -446), (-141, -529, -249, -79), 0, 1, 2, 5, 6, 21006434315, 17186870737, 216923828144, 166737183726, 152429459741⟩
private def cert_72 : CoverCert := ⟨1408505, 1500529, 768, 885, 881, 1039, 26044, 92264, 167049, 2643583, 2776023, 2925593, (1113, 0, 464, 0), (14, 0, 16, 0), (-742, 826, 464, 0), (44, 59, 16, 0), (-547, -960, 464, 0), (110, 79, 16, 0), (626, 191, 310, -85), (-286, 636, 153, 24), (-106, -154, 668, 63), (27, -23, 294, 682), (-15, -18, 379, -659), (108, -21, -454, 567), (16, 73, -468, -501), (-176, -582, 62, -14), 0, 1, 2, 3, 6, 2419210825, 282704018, 90147051064, 162913488622, 232709412043⟩
private def cert_73 : CoverCert := ⟨1438201, 1532273, 768, 885, 881, 986, 26318, 93235, 96600, 2614435, 2748269, 2754999, (1113, 0, 496, 0), (14, 0, 16, 0), (-742, 826, 496, 0), (44, 59, 16, 0), (-602, -934, 496, 0), (55, 53, 16, 0), (603, -3, 360, 98), (-268, 607, -198, 44), (-222, -572, 357, -198), (-218, 245, 710, 74), (106, 143, 278, -734), (-33, -35, 285, 681), (86, -101, -480, -407), (1, -283, -380, 596), 0, 1, 2, 4, 7, 46142496770, 91506618082, 60284267904, 93976740566, 121421068358⟩
private def cert_74 : CoverCert := ⟨1438201, 1532273, 768, 885, 953, 1039, 26318, 93235, 88660, 2614435, 2748269, 2739119, (1113, 0, 496, 0), (14, 0, 16, 0), (-742, 826, 496, 0), (44, 59, 16, 0), (-492, -996, 496, 0), (55, 43, 16, 0), (651, 133, 375, 57), (-302, 613, 286, 4), (-129, -244, 740, -112), (0, -66, 413, 674), (16, 70, 241, -728), (4, 76, -423, 546), (147, -20, -479, -524), (-198, -615, -22, -3), 0, 1, 2, 5, 6, 28246156338, 64832188026, 238034609121, 247195362057, 210263647185⟩
private def cert_75 : CoverCert := ⟨1355257, 1470833, 848, 1000, 881, 1039, 42361, 147147, 168769, 2729465, 2939037, 2982281, (1113, 0, 416, 0), (14, 0, 32, 0), (-610, 924, 416, 0), (89, 76, 32, 0), (-547, -960, 416, 0), (110, 79, 32, 0), (611, -73, 359, 69), (-242, 619, -95, -57), (-267, -599, 167, -59), (-103, 195, 679, -153), (64, -22, 227, -677), (-16, 23, 379, 615), (200, -112, -525, -378), (84, -57, -427, 500), 0, 1, 2, 4, 7, 56929210853, 97304880320, 83174422365, 55561681266, 88281623532⟩
private def cert_76 : CoverCert := ⟨1417585, 1507081, 884, 1031, 916, 1018, 26100, 143444, 94153, 2634615, 2869303, 2770721, (1141, 0, 400, 0), (14, 0, 16, 0), (-610, 957, 400, 0), (89, 74, 16, 0), (-602, -967, 400, 0), (55, 51, 16, 0), (651, -210, 250, 100), (-261, 651, -201, 35), (-259, -573, 242, 19), (-83, 171, 675, 93), (29, 86, 393, -660), (11, 11, 214, 802), (128, -93, -332, -584), (58, -211, -539, 337), 0, 1, 2, 4, 7, 80183101882, 128060278414, 96738629642, 61347592718, 77599279816⟩
private def cert_77 : CoverCert := ⟨1443185, 1534729, 884, 1031, 916, 1018, 26339, 144754, 95012, 2609493, 2846323, 2746839, (1141, 0, 432, 0), (14, 0, 16, 0), (-610, 957, 432, 0), (89, 74, 16, 0), (-602, -967, 432, 0), (55, 51, 16, 0), (617, -142, 380, 100), (-322, 587, -48, 8), (-250, -603, 258, 26), (-120, 211, 704, 87), (6, 45, 356, -694), (94, 41, 147, 785), (155, -71, -347, -587), (88, -178, -508, 301), 0, 1, 2, 4, 7, 85964853896, 143761338994, 81645183852, 82012861246, 149659717020⟩
private def cert_78 : CoverCert := ⟨1417585, 1474937, 884, 1016, 985, 1054, 21210, 135961, 81524, 2624835, 2854337, 2745463, (1134, 0, 400, 0), (7, 0, 16, 0), (-610, 950, 400, 0), (89, 66, 16, 0), (-492, -1020, 400, 0), (55, 35, 16, 0), (673, -23, 261, -71), (-298, 555, -114, 65), (-190, -558, 360, -51), (-111, 232, 720, 115), (-84, 84, 282, -685), (62, -66, 287, 707), (67, -149, -466, -439), (33, -137, -466, 461), 0, 1, 2, 4, 7, 61122103230, 87033482504, 68089513879, 69110151565, 107365535784⟩
private def cert_79 : CoverCert := ⟨1449337, 1507081, 902, 1031, 1001, 1070, 21440, 136715, 82407, 2593543, 2824093, 2715477, (1148, 0, 400, 0), (7, 0, 16, 0), (-610, 966, 400, 0), (89, 65, 16, 0), (-492, -1036, 400, 0), (55, 35, 16, 0), (729, -81, 256, 34), (-348, 573, 68, -26), (-239, -669, 80, -21), (9, 10, 691, 284), (-2, 20, 640, -392), (-34, -33, 52, 754), (14, -17, -199, -723), (175, 3, -618, 237), 0, 1, 2, 4, 7, 30478013204, 59285361004, 48262287256, 30704786370, 57193887032⟩
private def cert_80 : CoverCert := ⟨1443185, 1534729, 884, 1031, 985, 1070, 26339, 144754, 88731, 2609493, 2846323, 2734277, (1141, 0, 432, 0), (14, 0, 16, 0), (-610, 957, 432, 0), (89, 74, 16, 0), (-492, -1028, 432, 0), (55, 43, 16, 0), (719, -49, 206, -12), (-329, 579, 87, 54), (-256, -640, 273, -36), (-58, 31, 740, 435), (30, 145, 703, -478), (48, -48, -52, 779), (16, 6, -153, -766), (15, -95, -636, 38), 0, 1, 2, 4, 7, 100564170656, 142580466066, 107614877470, 14570497844, 114375222070⟩
private def cert_81 : CoverCert := ⟨1408505, 1500529, 848, 1000, 881, 986, 26044, 144696, 95595, 2643583, 2880887, 2782685, (1113, 0, 464, 0), (14, 0, 16, 0), (-610, 924, 464, 0), (89, 76, 16, 0), (-602, -934, 464, 0), (55, 53, 16, 0), (600, 123, 364, 123), (-302, 569, 352, 8), (-169, -368, 619, 158), (9, -2, 29, 728), (17, -106, 356, -647), (95, 156, -624, 294), (215, 215, -315, -541), (-186, -575, -300, -92), 0, 1, 2, 4, 5, 16807107363, 47439751941, 149636375272, 167922410245, 280804285423⟩
private def cert_82 : CoverCert := ⟨1408505, 1500529, 848, 1000, 953, 1039, 26044, 144696, 87737, 2643583, 2880887, 2766969, (1113, 0, 464, 0), (14, 0, 16, 0), (-610, 924, 464, 0), (89, 76, 16, 0), (-492, -996, 464, 0), (55, 43, 16, 0), (710, 87, 260, 17), (-226, 565, 275, 66), (-141, -670, 168, -10), (-137, -196, 723, 231), (-6, 1, 487, -538), (78, 42, -12, 734), (20, 52, -270, -586), (21, -104, -593, 206), 0, 1, 2, 4, 7, 46859251812, 111782715375, 76594312416, 72635173545, 153734951436⟩
private def cert_83 : CoverCert := ⟨1438201, 1532273, 848, 1000, 881, 986, 26318, 146219, 96600, 2614435, 2854237, 2754999, (1113, 0, 496, 0), (14, 0, 16, 0), (-610, 924, 496, 0), (89, 76, 16, 0), (-602, -934, 496, 0), (55, 53, 16, 0), (684, 57, 314, -86), (-252, 603, 284, -20), (-91, -264, 719, -64), (-41, 7, 426, 638), (-30, 39, 330, -704), (126, 54, -326, 590), (5, 134, -481, -485), (-212, -648, -83, -26), 0, 1, 2, 5, 6, 2323454784, 32445717180, 231142406904, 210340493598, 223626898404⟩
private def cert_84 : CoverCert := ⟨1438201, 1500913, 848, 984, 953, 1024, 21396, 138612, 82884, 2604591, 2839023, 2727567, (1106, 0, 496, 0), (7, 0, 16, 0), (-610, 916, 496, 0), (89, 68, 16, 0), (-492, -989, 496, 0), (55, 36, 16, 0), (652, 1, 174, 49), (-380, 553, -28, -27), (-148, -588, 423, -42), (-134, 158, 654, 355), (12, 139, 650, -416), (33, -85, 0, 741), (96, -122, -110, -750), (-34, -271, -552, 68), 0, 1, 2, 4, 7, 74724346646, 98350434234, 60186797724, 8564060304, 74771519552⟩
private def cert_85 : CoverCert := ⟨1469169, 1532273, 866, 1000, 969, 1039, 21619, 139312, 83093, 2574069, 2809455, 2697017, (1120, 0, 496, 0), (7, 0, 16, 0), (-610, 933, 496, 0), (89, 67, 16, 0), (-492, -1004, 496, 0), (55, 35, 16, 0), (672, -152, 245, 76), (-304, 526, -88, 28), (-135, -639, 398, -63), (-125, 149, 670, 389), (-53, 231, 565, -426), (88, -111, -60, 705), (142, -44, -61, -746), (3, -259, -590, -36), 0, 1, 2, 4, 7, 86736640114, 155563360022, 80119049372, 7586183762, 74126231562⟩
private def cert_86 : CoverCert := ⟨1470833, 1572516, 884, 1031, 916, 1018, 43801, 150590, 102261, 2616769, 2830347, 2733689, (1141, 0, 480, 0), (14, 0, 32, 0), (-610, 957, 480, 0), (89, 74, 32, 0), (-602, -967, 480, 0), (55, 51, 32, 0), (683, -174, 426, 85), (-306, 633, -3, -85), (-264, -621, 262, 1), (-178, 196, 730, 250), (19, 72, 488, -573), (4, -4, 65, 803), (109, -142, -259, -678), (185, -100, -547, 209), 0, 1, 2, 4, 7, 66702976474, 141632513060, 108014998792, 39443763574, 138096995880⟩
private def cert_87 : CoverCert := ⟨1470833, 1572516, 884, 981, 985, 1070, 43801, 91817, 96306, 2616769, 2712801, 2721779, (1141, 0, 480, 0), (14, 0, 32, 0), (-654, 932, 480, 0), (44, 49, 32, 0), (-492, -1028, 480, 0), (55, 43, 32, 0), (654, -107, 405, 110), (-350, 608, 19, -57), (-252, -660, 256, 111), (-133, 210, 726, 305), (-20, 70, 524, -511), (5, -4, -78, 759), (84, -122, -50, -735), (146, -71, -537, -47), 0, 1, 2, 4, 7, 103706385608, 169733358440, 124138291308, 15753420500, 158771349904⟩
private def cert_88 : CoverCert := ⟨1470833, 1572516, 947, 1031, 985, 1070, 43801, 86998, 96306, 2616769, 2703163, 2721779, (1141, 0, 480, 0), (14, 0, 32, 0), (-566, 989, 480, 0), (45, 42, 32, 0), (-492, -1028, 480, 0), (55, 43, 32, 0), (717, -49, 259, 89), (-408, 617, -96, -8), (-127, -575, 445, 9), (19, -107, 25, 796), (-131, 215, 713, 279), (47, -188, -576, 38), (-11, 143, 515, -593), (69, -190, -144, -766), 0, 1, 2, 3, 7, 59741682637, 130421415908, 42910289503, 169863385414, 182599328750⟩
private def cert_89 : CoverCert := ⟨1306122, 1355257, 569, 849, 947, 1077, 81325, 206421, 165466, 2856528, 3106720, 3024810, (1071, 0, 320, 0), (28, 0, 64, 0), (-786, 709, 320, 0), (88, 140, 64, 0), (-328, -1012, 320, 0), (109, 65, 64, 0), (611, 256, 32, -111), (-174, 423, -264, -377), (461, -108, 374, 358), (-226, 376, 469, 180), (-40, -154, 363, -517), (-54, 96, -327, 570), (131, -246, -528, -305), (-283, -560, 122, 143), 0, 1, 2, 5, 7, 16090480317, 69858620304, 39657266784, 10801121478, 54327289641⟩
private def cert_90 : CoverCert := ⟨1306122, 1372529, 666, 885, 1008, 1106, 40921, 169240, 144942, 2775720, 3032358, 2983762, (1113, 0, 288, 0), (14, 0, 32, 0), (-786, 775, 288, 0), (88, 110, 32, 0), (-328, -1057, 288, 0), (109, 49, 32, 0), (622, 107, 157, -98), (-222, 527, 244, 105), (-143, -543, -107, -10), (-39, -189, 516, -387), (72, 108, -102, -663), (-34, -97, 560, 397), (-61, 122, -612, 1), (125, 34, -105, 635), 0, 1, 2, 3, 6, 52954128369, 78665597667, 92359478007, 5633950431, 33550421994⟩
private def cert_91 : CoverCert := ⟨1310201, 1417585, 666, 885, 1008, 1106, 41587, 171995, 147301, 2772973, 3033789, 2984401, (1113, 0, 352, 0), (14, 0, 32, 0), (-786, 775, 352, 0), (88, 110, 32, 0), (-328, -1057, 352, 0), (109, 49, 32, 0), (556, 121, 359, 135), (-349, 530, 293, 14), (-135, -469, -324, -93), (-1, -169, 397, -536), (119, 207, -132, -598), (-115, -386, 485, 258), (202, 257, -596, 57), (-4, 58, -104, 671), 0, 1, 2, 3, 6, 97305049211, 107940011873, 160482895211, 2239119266, 25925181956⟩
private def cert_92 : CoverCert := ⟨1306122, 1408505, 569, 769, 947, 1077, 50464, 135109, 155331, 2794806, 2964096, 3004540, (1071, 0, 416, 0), (28, 0, 32, 0), (-830, 669, 416, 0), (44, 100, 32, 0), (-328, -1012, 416, 0), (109, 65, 32, 0), (578, 217, 365, -24), (-390, 438, 302, -16), (-117, -476, -269, 60), (5, -123, 299, 563), (-96, -377, 542, -156), (147, 256, -263, 543), (22, -27, 85, -677), (83, 252, -552, -271), 0, 1, 2, 3, 7, 69261013990, 75181616788, 116890095548, 9545151810, 35137107002⟩
private def cert_93 : CoverCert := ⟨1306122, 1469945, 569, 769, 947, 1077, 51553, 138024, 158683, 2796984, 2969926, 3011244, (1071, 0, 480, 0), (28, 0, 32, 0), (-830, 669, 480, 0), (44, 100, 32, 0), (-328, -1012, 480, 0), (109, 65, 32, 0), (575, 164, 381, -74), (-308, 352, 436, 48), (-37, -275, 353, 530), (115, 253, -198, 575), (-98, -420, 375, -276), (70, 393, -464, -180), (4, 154, -45, -679), (-91, -480, -425, 23), 0, 1, 2, 4, 5, 6505835864, 6782044164, 120404670440, 106914585776, 189723088472⟩
private def cert_94 : CoverCert := ⟨1306122, 1408505, 685, 849, 947, 1077, 50464, 116791, 155331, 2794806, 2927460, 3004540, (1071, 0, 416, 0), (28, 0, 32, 0), (-742, 767, 416, 0), (44, 82, 32, 0), (-328, -1012, 416, 0), (109, 65, 32, 0), (560, 57, 333, -66), (-283, 464, 411, -18), (-177, -361, -400, 5), (-74, -167, 326, 534), (-165, -465, 435, -211), (126, 297, -224, 591), (33, 92, -7, -690), (181, 445, -474, -182), 0, 1, 2, 3, 7, 77561679737, 79440898447, 134157009878, 18900880102, 23158505435⟩
private def cert_95 : CoverCert := ⟨1306122, 1409185, 685, 813, 947, 1049, 41464, 99716, 147821, 2776806, 2893310, 2989520, (1057, 0, 480, 0), (14, 0, 32, 0), (-742, 749, 480, 0), (44, 64, 32, 0), (-328, -998, 480, 0), (109, 51, 32, 0), (622, -2, 346, -4), (-208, 503, 389, 149), (-160, -440, -290, -135), (-189, -315, 249, 472), (-143, -333, 503, -321), (147, 175, -279, 608), (7, 198, 42, -677), (76, 253, -495, -184), 0, 1, 2, 3, 7, 45032064460, 65922941740, 85308883476, 21089545880, 43912806780⟩
private def cert_96 : CoverCert := ⟨1347745, 1469945, 727, 849, 977, 1077, 42348, 99100, 150481, 2736951, 2850455, 2953217, (1085, 0, 480, 0), (14, 0, 32, 0), (-742, 788, 480, 0), (44, 61, 32, 0), (-328, -1027, 480, 0), (109, 50, 32, 0), (551, 171, 430, 23), (-396, 446, 399, 25), (-179, -472, -425, -4), (-108, -392, 374, 476), (-101, -305, 474, -409), (158, 191, -106, 651), (118, 176, -125, -671), (178, 383, -507, 4), 0, 1, 2, 4, 7, 91845019875, 81424944860, 134777111400, 9191473705, 37590528080⟩
private def cert_97 : CoverCert := ⟨1306122, 1347745, 775, 936, 947, 1049, 40550, 144562, 144562, 2774978, 2983002, 2983002, (1057, 0, 416, 0), (14, 0, 32, 0), (-610, 855, 416, 0), (89, 81, 32, 0), (-328, -998, 416, 0), (109, 51, 32, 0), (701, -98, 117, -63), (77, 239, -59, -642), (-161, -495, 96, 459), (-527, 380, 170, 65), (78, 199, 639, 101), (159, 272, -183, 579), (-176, -475, 310, -386), (-34, -93, -650, -137), 0, 1, 2, 3, 5, 17720289263, 115720664328, 98700059414, 25161207792, 49171397141⟩
private def cert_98 : CoverCert := ⟨1306122, 1377441, 775, 936, 947, 1049, 24953, 142481, 142481, 2743784, 2978840, 2978840, (1057, 0, 464, 0), (14, 0, 16, 0), (-610, 855, 464, 0), (89, 81, 16, 0), (-328, -998, 464, 0), (109, 51, 16, 0), (720, -122, 44, -73), (-429, 316, 388, 51), (-27, -329, 224, -599), (-173, -548, 253, 321), (365, 189, 577, 101), (78, 174, -217, 624), (-20, 491, -127, -411), (24, -235, -598, -161), 0, 1, 2, 5, 7, 24056699673, 47499120069, 36969834129, 42429676662, 31040395287⟩
private def cert_99 : CoverCert := ⟨1355257, 1470833, 768, 885, 1008, 1106, 42361, 97333, 150042, 2729465, 2839409, 2944827, (1113, 0, 416, 0), (14, 0, 32, 0), (-742, 826, 416, 0), (44, 59, 32, 0), (-328, -1057, 416, 0), (109, 49, 32, 0), (658, 234, 257, 40), (-349, 506, 385, 28), (-173, -562, -140, -36), (13, -74, 357, 669), (-75, -346, 667, -107), (27, 109, -423, 503), (51, 13, 201, -715), (54, 198, -496, -387), 0, 1, 2, 3, 7, 60215907554, 72413489452, 116048033870, 53507711154, 93165745606⟩

private theorem chk_0 : Bool.and (checkCert cert_0) (checkCert cert_1) = true := by decide +kernel
private def vc_0 : VerifiedCert := ⟨cert_0, ((Bool.and_eq_true _ _).mp chk_0).1⟩
private def vc_1 : VerifiedCert := ⟨cert_1, ((Bool.and_eq_true _ _).mp chk_0).2⟩
private theorem chk_1 : Bool.and (checkCert cert_2) (checkCert cert_3) = true := by decide +kernel
private def vc_2 : VerifiedCert := ⟨cert_2, ((Bool.and_eq_true _ _).mp chk_1).1⟩
private def vc_3 : VerifiedCert := ⟨cert_3, ((Bool.and_eq_true _ _).mp chk_1).2⟩
private theorem chk_2 : Bool.and (checkCert cert_4) (checkCert cert_5) = true := by decide +kernel
private def vc_4 : VerifiedCert := ⟨cert_4, ((Bool.and_eq_true _ _).mp chk_2).1⟩
private def vc_5 : VerifiedCert := ⟨cert_5, ((Bool.and_eq_true _ _).mp chk_2).2⟩
private theorem chk_3 : Bool.and (checkCert cert_6) (checkCert cert_7) = true := by decide +kernel
private def vc_6 : VerifiedCert := ⟨cert_6, ((Bool.and_eq_true _ _).mp chk_3).1⟩
private def vc_7 : VerifiedCert := ⟨cert_7, ((Bool.and_eq_true _ _).mp chk_3).2⟩
private theorem chk_4 : Bool.and (checkCert cert_8) (checkCert cert_9) = true := by decide +kernel
private def vc_8 : VerifiedCert := ⟨cert_8, ((Bool.and_eq_true _ _).mp chk_4).1⟩
private def vc_9 : VerifiedCert := ⟨cert_9, ((Bool.and_eq_true _ _).mp chk_4).2⟩
private theorem chk_5 : Bool.and (checkCert cert_10) (checkCert cert_11) = true := by decide +kernel
private def vc_10 : VerifiedCert := ⟨cert_10, ((Bool.and_eq_true _ _).mp chk_5).1⟩
private def vc_11 : VerifiedCert := ⟨cert_11, ((Bool.and_eq_true _ _).mp chk_5).2⟩
private theorem chk_6 : Bool.and (checkCert cert_12) (checkCert cert_13) = true := by decide +kernel
private def vc_12 : VerifiedCert := ⟨cert_12, ((Bool.and_eq_true _ _).mp chk_6).1⟩
private def vc_13 : VerifiedCert := ⟨cert_13, ((Bool.and_eq_true _ _).mp chk_6).2⟩
private theorem chk_7 : Bool.and (checkCert cert_14) (checkCert cert_15) = true := by decide +kernel
private def vc_14 : VerifiedCert := ⟨cert_14, ((Bool.and_eq_true _ _).mp chk_7).1⟩
private def vc_15 : VerifiedCert := ⟨cert_15, ((Bool.and_eq_true _ _).mp chk_7).2⟩
private theorem chk_8 : Bool.and (checkCert cert_16) (checkCert cert_17) = true := by decide +kernel
private def vc_16 : VerifiedCert := ⟨cert_16, ((Bool.and_eq_true _ _).mp chk_8).1⟩
private def vc_17 : VerifiedCert := ⟨cert_17, ((Bool.and_eq_true _ _).mp chk_8).2⟩
private theorem chk_9 : Bool.and (checkCert cert_18) (checkCert cert_19) = true := by decide +kernel
private def vc_18 : VerifiedCert := ⟨cert_18, ((Bool.and_eq_true _ _).mp chk_9).1⟩
private def vc_19 : VerifiedCert := ⟨cert_19, ((Bool.and_eq_true _ _).mp chk_9).2⟩
private theorem chk_10 : Bool.and (checkCert cert_20) (checkCert cert_21) = true := by decide +kernel
private def vc_20 : VerifiedCert := ⟨cert_20, ((Bool.and_eq_true _ _).mp chk_10).1⟩
private def vc_21 : VerifiedCert := ⟨cert_21, ((Bool.and_eq_true _ _).mp chk_10).2⟩
private theorem chk_11 : Bool.and (checkCert cert_22) (checkCert cert_23) = true := by decide +kernel
private def vc_22 : VerifiedCert := ⟨cert_22, ((Bool.and_eq_true _ _).mp chk_11).1⟩
private def vc_23 : VerifiedCert := ⟨cert_23, ((Bool.and_eq_true _ _).mp chk_11).2⟩
private theorem chk_12 : Bool.and (checkCert cert_24) (checkCert cert_25) = true := by decide +kernel
private def vc_24 : VerifiedCert := ⟨cert_24, ((Bool.and_eq_true _ _).mp chk_12).1⟩
private def vc_25 : VerifiedCert := ⟨cert_25, ((Bool.and_eq_true _ _).mp chk_12).2⟩
private theorem chk_13 : Bool.and (checkCert cert_26) (checkCert cert_27) = true := by decide +kernel
private def vc_26 : VerifiedCert := ⟨cert_26, ((Bool.and_eq_true _ _).mp chk_13).1⟩
private def vc_27 : VerifiedCert := ⟨cert_27, ((Bool.and_eq_true _ _).mp chk_13).2⟩
private theorem chk_14 : Bool.and (checkCert cert_28) (checkCert cert_29) = true := by decide +kernel
private def vc_28 : VerifiedCert := ⟨cert_28, ((Bool.and_eq_true _ _).mp chk_14).1⟩
private def vc_29 : VerifiedCert := ⟨cert_29, ((Bool.and_eq_true _ _).mp chk_14).2⟩
private theorem chk_15 : Bool.and (checkCert cert_30) (checkCert cert_31) = true := by decide +kernel
private def vc_30 : VerifiedCert := ⟨cert_30, ((Bool.and_eq_true _ _).mp chk_15).1⟩
private def vc_31 : VerifiedCert := ⟨cert_31, ((Bool.and_eq_true _ _).mp chk_15).2⟩
private theorem chk_16 : Bool.and (checkCert cert_32) (checkCert cert_33) = true := by decide +kernel
private def vc_32 : VerifiedCert := ⟨cert_32, ((Bool.and_eq_true _ _).mp chk_16).1⟩
private def vc_33 : VerifiedCert := ⟨cert_33, ((Bool.and_eq_true _ _).mp chk_16).2⟩
private theorem chk_17 : Bool.and (checkCert cert_34) (checkCert cert_35) = true := by decide +kernel
private def vc_34 : VerifiedCert := ⟨cert_34, ((Bool.and_eq_true _ _).mp chk_17).1⟩
private def vc_35 : VerifiedCert := ⟨cert_35, ((Bool.and_eq_true _ _).mp chk_17).2⟩
private theorem chk_18 : Bool.and (checkCert cert_36) (checkCert cert_37) = true := by decide +kernel
private def vc_36 : VerifiedCert := ⟨cert_36, ((Bool.and_eq_true _ _).mp chk_18).1⟩
private def vc_37 : VerifiedCert := ⟨cert_37, ((Bool.and_eq_true _ _).mp chk_18).2⟩
private theorem chk_19 : Bool.and (checkCert cert_38) (checkCert cert_39) = true := by decide +kernel
private def vc_38 : VerifiedCert := ⟨cert_38, ((Bool.and_eq_true _ _).mp chk_19).1⟩
private def vc_39 : VerifiedCert := ⟨cert_39, ((Bool.and_eq_true _ _).mp chk_19).2⟩
private theorem chk_20 : Bool.and (checkCert cert_40) (checkCert cert_41) = true := by decide +kernel
private def vc_40 : VerifiedCert := ⟨cert_40, ((Bool.and_eq_true _ _).mp chk_20).1⟩
private def vc_41 : VerifiedCert := ⟨cert_41, ((Bool.and_eq_true _ _).mp chk_20).2⟩
private theorem chk_21 : Bool.and (checkCert cert_42) (checkCert cert_43) = true := by decide +kernel
private def vc_42 : VerifiedCert := ⟨cert_42, ((Bool.and_eq_true _ _).mp chk_21).1⟩
private def vc_43 : VerifiedCert := ⟨cert_43, ((Bool.and_eq_true _ _).mp chk_21).2⟩
private theorem chk_22 : Bool.and (checkCert cert_44) (checkCert cert_45) = true := by decide +kernel
private def vc_44 : VerifiedCert := ⟨cert_44, ((Bool.and_eq_true _ _).mp chk_22).1⟩
private def vc_45 : VerifiedCert := ⟨cert_45, ((Bool.and_eq_true _ _).mp chk_22).2⟩
private theorem chk_23 : Bool.and (checkCert cert_46) (checkCert cert_47) = true := by decide +kernel
private def vc_46 : VerifiedCert := ⟨cert_46, ((Bool.and_eq_true _ _).mp chk_23).1⟩
private def vc_47 : VerifiedCert := ⟨cert_47, ((Bool.and_eq_true _ _).mp chk_23).2⟩
private theorem chk_24 : Bool.and (checkCert cert_48) (checkCert cert_49) = true := by decide +kernel
private def vc_48 : VerifiedCert := ⟨cert_48, ((Bool.and_eq_true _ _).mp chk_24).1⟩
private def vc_49 : VerifiedCert := ⟨cert_49, ((Bool.and_eq_true _ _).mp chk_24).2⟩
private theorem chk_25 : Bool.and (checkCert cert_50) (checkCert cert_51) = true := by decide +kernel
private def vc_50 : VerifiedCert := ⟨cert_50, ((Bool.and_eq_true _ _).mp chk_25).1⟩
private def vc_51 : VerifiedCert := ⟨cert_51, ((Bool.and_eq_true _ _).mp chk_25).2⟩
private theorem chk_26 : Bool.and (checkCert cert_52) (checkCert cert_53) = true := by decide +kernel
private def vc_52 : VerifiedCert := ⟨cert_52, ((Bool.and_eq_true _ _).mp chk_26).1⟩
private def vc_53 : VerifiedCert := ⟨cert_53, ((Bool.and_eq_true _ _).mp chk_26).2⟩
private theorem chk_27 : Bool.and (checkCert cert_54) (checkCert cert_55) = true := by decide +kernel
private def vc_54 : VerifiedCert := ⟨cert_54, ((Bool.and_eq_true _ _).mp chk_27).1⟩
private def vc_55 : VerifiedCert := ⟨cert_55, ((Bool.and_eq_true _ _).mp chk_27).2⟩
private theorem chk_28 : Bool.and (checkCert cert_56) (checkCert cert_57) = true := by decide +kernel
private def vc_56 : VerifiedCert := ⟨cert_56, ((Bool.and_eq_true _ _).mp chk_28).1⟩
private def vc_57 : VerifiedCert := ⟨cert_57, ((Bool.and_eq_true _ _).mp chk_28).2⟩
private theorem chk_29 : Bool.and (checkCert cert_58) (checkCert cert_59) = true := by decide +kernel
private def vc_58 : VerifiedCert := ⟨cert_58, ((Bool.and_eq_true _ _).mp chk_29).1⟩
private def vc_59 : VerifiedCert := ⟨cert_59, ((Bool.and_eq_true _ _).mp chk_29).2⟩
private theorem chk_30 : Bool.and (checkCert cert_60) (checkCert cert_61) = true := by decide +kernel
private def vc_60 : VerifiedCert := ⟨cert_60, ((Bool.and_eq_true _ _).mp chk_30).1⟩
private def vc_61 : VerifiedCert := ⟨cert_61, ((Bool.and_eq_true _ _).mp chk_30).2⟩
private theorem chk_31 : Bool.and (checkCert cert_62) (checkCert cert_63) = true := by decide +kernel
private def vc_62 : VerifiedCert := ⟨cert_62, ((Bool.and_eq_true _ _).mp chk_31).1⟩
private def vc_63 : VerifiedCert := ⟨cert_63, ((Bool.and_eq_true _ _).mp chk_31).2⟩
private theorem chk_32 : Bool.and (checkCert cert_64) (checkCert cert_65) = true := by decide +kernel
private def vc_64 : VerifiedCert := ⟨cert_64, ((Bool.and_eq_true _ _).mp chk_32).1⟩
private def vc_65 : VerifiedCert := ⟨cert_65, ((Bool.and_eq_true _ _).mp chk_32).2⟩
private theorem chk_33 : Bool.and (checkCert cert_66) (checkCert cert_67) = true := by decide +kernel
private def vc_66 : VerifiedCert := ⟨cert_66, ((Bool.and_eq_true _ _).mp chk_33).1⟩
private def vc_67 : VerifiedCert := ⟨cert_67, ((Bool.and_eq_true _ _).mp chk_33).2⟩
private theorem chk_34 : Bool.and (checkCert cert_68) (checkCert cert_69) = true := by decide +kernel
private def vc_68 : VerifiedCert := ⟨cert_68, ((Bool.and_eq_true _ _).mp chk_34).1⟩
private def vc_69 : VerifiedCert := ⟨cert_69, ((Bool.and_eq_true _ _).mp chk_34).2⟩
private theorem chk_35 : Bool.and (checkCert cert_70) (checkCert cert_71) = true := by decide +kernel
private def vc_70 : VerifiedCert := ⟨cert_70, ((Bool.and_eq_true _ _).mp chk_35).1⟩
private def vc_71 : VerifiedCert := ⟨cert_71, ((Bool.and_eq_true _ _).mp chk_35).2⟩
private theorem chk_36 : Bool.and (checkCert cert_72) (checkCert cert_73) = true := by decide +kernel
private def vc_72 : VerifiedCert := ⟨cert_72, ((Bool.and_eq_true _ _).mp chk_36).1⟩
private def vc_73 : VerifiedCert := ⟨cert_73, ((Bool.and_eq_true _ _).mp chk_36).2⟩
private theorem chk_37 : Bool.and (checkCert cert_74) (checkCert cert_75) = true := by decide +kernel
private def vc_74 : VerifiedCert := ⟨cert_74, ((Bool.and_eq_true _ _).mp chk_37).1⟩
private def vc_75 : VerifiedCert := ⟨cert_75, ((Bool.and_eq_true _ _).mp chk_37).2⟩
private theorem chk_38 : Bool.and (checkCert cert_76) (checkCert cert_77) = true := by decide +kernel
private def vc_76 : VerifiedCert := ⟨cert_76, ((Bool.and_eq_true _ _).mp chk_38).1⟩
private def vc_77 : VerifiedCert := ⟨cert_77, ((Bool.and_eq_true _ _).mp chk_38).2⟩
private theorem chk_39 : Bool.and (checkCert cert_78) (checkCert cert_79) = true := by decide +kernel
private def vc_78 : VerifiedCert := ⟨cert_78, ((Bool.and_eq_true _ _).mp chk_39).1⟩
private def vc_79 : VerifiedCert := ⟨cert_79, ((Bool.and_eq_true _ _).mp chk_39).2⟩
private theorem chk_40 : Bool.and (checkCert cert_80) (checkCert cert_81) = true := by decide +kernel
private def vc_80 : VerifiedCert := ⟨cert_80, ((Bool.and_eq_true _ _).mp chk_40).1⟩
private def vc_81 : VerifiedCert := ⟨cert_81, ((Bool.and_eq_true _ _).mp chk_40).2⟩
private theorem chk_41 : Bool.and (checkCert cert_82) (checkCert cert_83) = true := by decide +kernel
private def vc_82 : VerifiedCert := ⟨cert_82, ((Bool.and_eq_true _ _).mp chk_41).1⟩
private def vc_83 : VerifiedCert := ⟨cert_83, ((Bool.and_eq_true _ _).mp chk_41).2⟩
private theorem chk_42 : Bool.and (checkCert cert_84) (checkCert cert_85) = true := by decide +kernel
private def vc_84 : VerifiedCert := ⟨cert_84, ((Bool.and_eq_true _ _).mp chk_42).1⟩
private def vc_85 : VerifiedCert := ⟨cert_85, ((Bool.and_eq_true _ _).mp chk_42).2⟩
private theorem chk_43 : Bool.and (checkCert cert_86) (checkCert cert_87) = true := by decide +kernel
private def vc_86 : VerifiedCert := ⟨cert_86, ((Bool.and_eq_true _ _).mp chk_43).1⟩
private def vc_87 : VerifiedCert := ⟨cert_87, ((Bool.and_eq_true _ _).mp chk_43).2⟩
private theorem chk_44 : Bool.and (checkCert cert_88) (checkCert cert_89) = true := by decide +kernel
private def vc_88 : VerifiedCert := ⟨cert_88, ((Bool.and_eq_true _ _).mp chk_44).1⟩
private def vc_89 : VerifiedCert := ⟨cert_89, ((Bool.and_eq_true _ _).mp chk_44).2⟩
private theorem chk_45 : Bool.and (checkCert cert_90) (checkCert cert_91) = true := by decide +kernel
private def vc_90 : VerifiedCert := ⟨cert_90, ((Bool.and_eq_true _ _).mp chk_45).1⟩
private def vc_91 : VerifiedCert := ⟨cert_91, ((Bool.and_eq_true _ _).mp chk_45).2⟩
private theorem chk_46 : Bool.and (checkCert cert_92) (checkCert cert_93) = true := by decide +kernel
private def vc_92 : VerifiedCert := ⟨cert_92, ((Bool.and_eq_true _ _).mp chk_46).1⟩
private def vc_93 : VerifiedCert := ⟨cert_93, ((Bool.and_eq_true _ _).mp chk_46).2⟩
private theorem chk_47 : Bool.and (checkCert cert_94) (checkCert cert_95) = true := by decide +kernel
private def vc_94 : VerifiedCert := ⟨cert_94, ((Bool.and_eq_true _ _).mp chk_47).1⟩
private def vc_95 : VerifiedCert := ⟨cert_95, ((Bool.and_eq_true _ _).mp chk_47).2⟩
private theorem chk_48 : Bool.and (checkCert cert_96) (checkCert cert_97) = true := by decide +kernel
private def vc_96 : VerifiedCert := ⟨cert_96, ((Bool.and_eq_true _ _).mp chk_48).1⟩
private def vc_97 : VerifiedCert := ⟨cert_97, ((Bool.and_eq_true _ _).mp chk_48).2⟩
private theorem chk_49 : Bool.and (checkCert cert_98) (checkCert cert_99) = true := by decide +kernel
private def vc_98 : VerifiedCert := ⟨cert_98, ((Bool.and_eq_true _ _).mp chk_49).1⟩
private def vc_99 : VerifiedCert := ⟨cert_99, ((Bool.and_eq_true _ _).mp chk_49).2⟩

private def pt_6 : PTree := .inf 0
private def pt_7 : PTree := .leaf vc_0
private def pt_5 : PTree := .split 0 (1099) pt_6 pt_7
private def pt_8 : PTree := .leaf vc_1
private def pt_4 : PTree := .split 2 (-698) pt_5 pt_8
private def pt_11 : PTree := .inf 0
private def pt_13 : PTree := .leaf vc_2
private def pt_14 : PTree := .inf 4
private def pt_12 : PTree := .split 0 (1127) pt_13 pt_14
private def pt_10 : PTree := .split 0 (1099) pt_11 pt_12
private def pt_16 : PTree := .inf 5
private def pt_18 : PTree := .inf 0
private def pt_19 : PTree := .leaf vc_3
private def pt_17 : PTree := .split 0 (1099) pt_18 pt_19
private def pt_15 : PTree := .split 3 (-765) pt_16 pt_17
private def pt_9 : PTree := .split 2 (-698) pt_10 pt_15
private def pt_3 : PTree := .split 1 (128) pt_4 pt_9
private def pt_22 : PTree := .leaf vc_4
private def pt_23 : PTree := .leaf vc_5
private def pt_21 : PTree := .split 2 (-698) pt_22 pt_23
private def pt_26 : PTree := .inf 0
private def pt_27 : PTree := .leaf vc_6
private def pt_25 : PTree := .split 0 (1099) pt_26 pt_27
private def pt_29 : PTree := .inf 0
private def pt_30 : PTree := .leaf vc_7
private def pt_28 : PTree := .split 0 (1099) pt_29 pt_30
private def pt_24 : PTree := .split 2 (-698) pt_25 pt_28
private def pt_20 : PTree := .split 1 (128) pt_21 pt_24
private def pt_2 : PTree := .split 3 (-656) pt_3 pt_20
private def pt_34 : PTree := .leaf vc_8
private def pt_35 : PTree := .leaf vc_9
private def pt_33 : PTree := .split 2 (-698) pt_34 pt_35
private def pt_36 : PTree := .inf 6
private def pt_32 : PTree := .split 3 (-219) pt_33 pt_36
private def pt_40 : PTree := .inf 0
private def pt_41 : PTree := .leaf vc_10
private def pt_39 : PTree := .split 0 (1099) pt_40 pt_41
private def pt_43 : PTree := .inf 0
private def pt_44 : PTree := .inf 6
private def pt_42 : PTree := .split 0 (1099) pt_43 pt_44
private def pt_38 : PTree := .split 2 (-698) pt_39 pt_42
private def pt_45 : PTree := .inf 6
private def pt_37 : PTree := .split 3 (-219) pt_38 pt_45
private def pt_31 : PTree := .split 1 (128) pt_32 pt_37
private def pt_1 : PTree := .split 3 (-437) pt_2 pt_31
private def pt_51 : PTree := .leaf vc_11
private def pt_53 : PTree := .leaf vc_12
private def pt_54 : PTree := .inf 4
private def pt_52 : PTree := .split 0 (1127) pt_53 pt_54
private def pt_50 : PTree := .split 0 (1099) pt_51 pt_52
private def pt_56 : PTree := .inf 5
private def pt_58 : PTree := .leaf vc_13
private def pt_60 : PTree := .leaf vc_14
private def pt_62 : PTree := .leaf vc_15
private def pt_63 : PTree := .leaf vc_16
private def pt_61 : PTree := .split 1 (320) pt_62 pt_63
private def pt_59 : PTree := .split 0 (1127) pt_60 pt_61
private def pt_57 : PTree := .split 0 (1099) pt_58 pt_59
private def pt_55 : PTree := .split 3 (-765) pt_56 pt_57
private def pt_49 : PTree := .split 2 (-698) pt_50 pt_55
private def pt_69 : PTree := .leaf vc_17
private def pt_71 : PTree := .leaf vc_18
private def pt_72 : PTree := .leaf vc_19
private def pt_70 : PTree := .split 0 (1071) pt_71 pt_72
private def pt_68 : PTree := .split 1 (448) pt_69 pt_70
private def pt_74 : PTree := .leaf vc_20
private def pt_76 : PTree := .leaf vc_21
private def pt_77 : PTree := .leaf vc_22
private def pt_75 : PTree := .split 0 (1071) pt_76 pt_77
private def pt_73 : PTree := .split 1 (448) pt_74 pt_75
private def pt_67 : PTree := .split 2 (-786) pt_68 pt_73
private def pt_80 : PTree := .leaf vc_23
private def pt_82 : PTree := .leaf vc_24
private def pt_83 : PTree := .leaf vc_25
private def pt_81 : PTree := .split 0 (1071) pt_82 pt_83
private def pt_79 : PTree := .split 1 (448) pt_80 pt_81
private def pt_85 : PTree := .leaf vc_26
private def pt_87 : PTree := .leaf vc_27
private def pt_88 : PTree := .leaf vc_28
private def pt_86 : PTree := .split 0 (1071) pt_87 pt_88
private def pt_84 : PTree := .split 1 (448) pt_85 pt_86
private def pt_78 : PTree := .split 2 (-786) pt_79 pt_84
private def pt_66 : PTree := .split 3 (-765) pt_67 pt_78
private def pt_90 : PTree := .inf 5
private def pt_92 : PTree := .leaf vc_29
private def pt_94 : PTree := .leaf vc_30
private def pt_96 : PTree := .leaf vc_31
private def pt_97 : PTree := .leaf vc_32
private def pt_95 : PTree := .split 1 (480) pt_96 pt_97
private def pt_93 : PTree := .split 0 (1071) pt_94 pt_95
private def pt_91 : PTree := .split 1 (448) pt_92 pt_93
private def pt_89 : PTree := .split 3 (-765) pt_90 pt_91
private def pt_65 : PTree := .split 2 (-698) pt_66 pt_89
private def pt_102 : PTree := .leaf vc_33
private def pt_104 : PTree := .inf 4
private def pt_105 : PTree := .leaf vc_34
private def pt_103 : PTree := .split 2 (-786) pt_104 pt_105
private def pt_101 : PTree := .split 3 (-765) pt_102 pt_103
private def pt_106 : PTree := .inf 4
private def pt_100 : PTree := .split 0 (1127) pt_101 pt_106
private def pt_110 : PTree := .inf 4
private def pt_112 : PTree := .inf 4
private def pt_113 : PTree := .inf 5
private def pt_111 : PTree := .split 2 (-742) pt_112 pt_113
private def pt_109 : PTree := .split 2 (-786) pt_110 pt_111
private def pt_115 : PTree := .inf 4
private def pt_116 : PTree := .leaf vc_35
private def pt_114 : PTree := .split 2 (-786) pt_115 pt_116
private def pt_108 : PTree := .split 3 (-765) pt_109 pt_114
private def pt_117 : PTree := .inf 4
private def pt_107 : PTree := .split 0 (1127) pt_108 pt_117
private def pt_99 : PTree := .split 1 (448) pt_100 pt_107
private def pt_121 : PTree := .inf 5
private def pt_122 : PTree := .leaf vc_36
private def pt_120 : PTree := .split 3 (-765) pt_121 pt_122
private def pt_124 : PTree := .inf 5
private def pt_126 : PTree := .leaf vc_37
private def pt_127 : PTree := .leaf vc_38
private def pt_125 : PTree := .split 1 (416) pt_126 pt_127
private def pt_123 : PTree := .split 3 (-765) pt_124 pt_125
private def pt_119 : PTree := .split 0 (1127) pt_120 pt_123
private def pt_130 : PTree := .inf 5
private def pt_132 : PTree := .leaf vc_39
private def pt_134 : PTree := .leaf vc_40
private def pt_136 : PTree := .leaf vc_41
private def pt_137 : PTree := .inf 5
private def pt_135 : PTree := .split 2 (-610) pt_136 pt_137
private def pt_133 : PTree := .split 0 (1113) pt_134 pt_135
private def pt_131 : PTree := .split 1 (480) pt_132 pt_133
private def pt_129 : PTree := .split 3 (-765) pt_130 pt_131
private def pt_139 : PTree := .inf 5
private def pt_141 : PTree := .leaf vc_42
private def pt_142 : PTree := .inf 5
private def pt_140 : PTree := .split 2 (-610) pt_141 pt_142
private def pt_138 : PTree := .split 3 (-765) pt_139 pt_140
private def pt_128 : PTree := .split 0 (1127) pt_129 pt_138
private def pt_118 : PTree := .split 1 (448) pt_119 pt_128
private def pt_98 : PTree := .split 2 (-698) pt_99 pt_118
private def pt_64 : PTree := .split 0 (1099) pt_65 pt_98
private def pt_48 : PTree := .split 1 (384) pt_49 pt_64
private def pt_146 : PTree := .leaf vc_43
private def pt_149 : PTree := .leaf vc_44
private def pt_150 : PTree := .leaf vc_45
private def pt_148 : PTree := .split 1 (320) pt_149 pt_150
private def pt_151 : PTree := .inf 4
private def pt_147 : PTree := .split 0 (1127) pt_148 pt_151
private def pt_145 : PTree := .split 0 (1099) pt_146 pt_147
private def pt_153 : PTree := .leaf vc_46
private def pt_156 : PTree := .leaf vc_47
private def pt_157 : PTree := .leaf vc_48
private def pt_155 : PTree := .split 1 (320) pt_156 pt_157
private def pt_159 : PTree := .leaf vc_49
private def pt_162 : PTree := .leaf vc_50
private def pt_163 : PTree := .leaf vc_51
private def pt_161 : PTree := .split 0 (1141) pt_162 pt_163
private def pt_166 : PTree := .leaf vc_52
private def pt_167 : PTree := .leaf vc_53
private def pt_165 : PTree := .split 1 (352) pt_166 pt_167
private def pt_168 : PTree := .leaf vc_54
private def pt_164 : PTree := .split 0 (1141) pt_165 pt_168
private def pt_160 : PTree := .split 3 (-547) pt_161 pt_164
private def pt_158 : PTree := .split 1 (320) pt_159 pt_160
private def pt_154 : PTree := .split 0 (1127) pt_155 pt_158
private def pt_152 : PTree := .split 0 (1099) pt_153 pt_154
private def pt_144 : PTree := .split 2 (-698) pt_145 pt_152
private def pt_173 : PTree := .leaf vc_55
private def pt_175 : PTree := .leaf vc_56
private def pt_176 : PTree := .leaf vc_57
private def pt_174 : PTree := .split 0 (1071) pt_175 pt_176
private def pt_172 : PTree := .split 1 (448) pt_173 pt_174
private def pt_179 : PTree := .leaf vc_58
private def pt_180 : PTree := .leaf vc_59
private def pt_178 : PTree := .split 2 (-786) pt_179 pt_180
private def pt_182 : PTree := .leaf vc_60
private def pt_184 : PTree := .leaf vc_61
private def pt_186 : PTree := .leaf vc_62
private def pt_187 : PTree := .leaf vc_63
private def pt_185 : PTree := .split 2 (-786) pt_186 pt_187
private def pt_183 : PTree := .split 1 (480) pt_184 pt_185
private def pt_181 : PTree := .split 0 (1071) pt_182 pt_183
private def pt_177 : PTree := .split 1 (448) pt_178 pt_181
private def pt_171 : PTree := .split 3 (-547) pt_172 pt_177
private def pt_190 : PTree := .leaf vc_64
private def pt_192 : PTree := .leaf vc_65
private def pt_194 : PTree := .leaf vc_66
private def pt_195 : PTree := .leaf vc_67
private def pt_193 : PTree := .split 1 (480) pt_194 pt_195
private def pt_191 : PTree := .split 0 (1071) pt_192 pt_193
private def pt_189 : PTree := .split 1 (448) pt_190 pt_191
private def pt_197 : PTree := .leaf vc_68
private def pt_199 : PTree := .leaf vc_69
private def pt_200 : PTree := .leaf vc_70
private def pt_198 : PTree := .split 0 (1071) pt_199 pt_200
private def pt_196 : PTree := .split 1 (448) pt_197 pt_198
private def pt_188 : PTree := .split 3 (-547) pt_189 pt_196
private def pt_170 : PTree := .split 2 (-698) pt_171 pt_188
private def pt_204 : PTree := .leaf vc_71
private def pt_205 : PTree := .inf 4
private def pt_203 : PTree := .split 0 (1127) pt_204 pt_205
private def pt_208 : PTree := .inf 4
private def pt_210 : PTree := .leaf vc_72
private def pt_212 : PTree := .leaf vc_73
private def pt_213 : PTree := .leaf vc_74
private def pt_211 : PTree := .split 3 (-547) pt_212 pt_213
private def pt_209 : PTree := .split 1 (480) pt_210 pt_211
private def pt_207 : PTree := .split 2 (-786) pt_208 pt_209
private def pt_214 : PTree := .inf 4
private def pt_206 : PTree := .split 0 (1127) pt_207 pt_214
private def pt_202 : PTree := .split 1 (448) pt_203 pt_206
private def pt_217 : PTree := .leaf vc_75
private def pt_220 : PTree := .leaf vc_76
private def pt_221 : PTree := .leaf vc_77
private def pt_219 : PTree := .split 1 (416) pt_220 pt_221
private def pt_224 : PTree := .leaf vc_78
private def pt_225 : PTree := .leaf vc_79
private def pt_223 : PTree := .split 0 (1141) pt_224 pt_225
private def pt_226 : PTree := .leaf vc_80
private def pt_222 : PTree := .split 1 (416) pt_223 pt_226
private def pt_218 : PTree := .split 3 (-547) pt_219 pt_222
private def pt_216 : PTree := .split 0 (1127) pt_217 pt_218
private def pt_230 : PTree := .leaf vc_81
private def pt_231 : PTree := .leaf vc_82
private def pt_229 : PTree := .split 3 (-547) pt_230 pt_231
private def pt_233 : PTree := .leaf vc_83
private def pt_235 : PTree := .leaf vc_84
private def pt_236 : PTree := .leaf vc_85
private def pt_234 : PTree := .split 0 (1113) pt_235 pt_236
private def pt_232 : PTree := .split 3 (-547) pt_233 pt_234
private def pt_228 : PTree := .split 1 (480) pt_229 pt_232
private def pt_238 : PTree := .leaf vc_86
private def pt_240 : PTree := .leaf vc_87
private def pt_241 : PTree := .leaf vc_88
private def pt_239 : PTree := .split 2 (-610) pt_240 pt_241
private def pt_237 : PTree := .split 3 (-547) pt_238 pt_239
private def pt_227 : PTree := .split 0 (1127) pt_228 pt_237
private def pt_215 : PTree := .split 1 (448) pt_216 pt_227
private def pt_201 : PTree := .split 2 (-698) pt_202 pt_215
private def pt_169 : PTree := .split 0 (1099) pt_170 pt_201
private def pt_143 : PTree := .split 1 (384) pt_144 pt_169
private def pt_47 : PTree := .split 3 (-656) pt_48 pt_143
private def pt_246 : PTree := .leaf vc_89
private def pt_249 : PTree := .leaf vc_90
private def pt_250 : PTree := .leaf vc_91
private def pt_248 : PTree := .split 1 (320) pt_249 pt_250
private def pt_251 : PTree := .inf 4
private def pt_247 : PTree := .split 0 (1127) pt_248 pt_251
private def pt_245 : PTree := .split 0 (1099) pt_246 pt_247
private def pt_254 : PTree := .inf 0
private def pt_255 : PTree := .inf 6
private def pt_253 : PTree := .split 0 (1071) pt_254 pt_255
private def pt_256 : PTree := .inf 6
private def pt_252 : PTree := .split 0 (1099) pt_253 pt_256
private def pt_244 : PTree := .split 2 (-698) pt_245 pt_252
private def pt_257 : PTree := .inf 6
private def pt_243 : PTree := .split 3 (-219) pt_244 pt_257
private def pt_263 : PTree := .leaf vc_92
private def pt_264 : PTree := .leaf vc_93
private def pt_262 : PTree := .split 1 (448) pt_263 pt_264
private def pt_266 : PTree := .leaf vc_94
private def pt_268 : PTree := .leaf vc_95
private def pt_269 : PTree := .leaf vc_96
private def pt_267 : PTree := .split 0 (1071) pt_268 pt_269
private def pt_265 : PTree := .split 1 (448) pt_266 pt_267
private def pt_261 : PTree := .split 2 (-786) pt_262 pt_265
private def pt_272 : PTree := .leaf vc_97
private def pt_274 : PTree := .leaf vc_98
private def pt_275 : PTree := .inf 2
private def pt_273 : PTree := .split 1 (480) pt_274 pt_275
private def pt_271 : PTree := .split 1 (448) pt_272 pt_273
private def pt_276 : PTree := .inf 6
private def pt_270 : PTree := .split 0 (1071) pt_271 pt_276
private def pt_260 : PTree := .split 2 (-698) pt_261 pt_270
private def pt_277 : PTree := .inf 6
private def pt_259 : PTree := .split 3 (-219) pt_260 pt_277
private def pt_283 : PTree := .inf 4
private def pt_284 : PTree := .leaf vc_99
private def pt_282 : PTree := .split 2 (-786) pt_283 pt_284
private def pt_285 : PTree := .inf 6
private def pt_281 : PTree := .split 2 (-698) pt_282 pt_285
private def pt_287 : PTree := .inf 4
private def pt_288 : PTree := .inf 6
private def pt_286 : PTree := .split 2 (-698) pt_287 pt_288
private def pt_280 : PTree := .split 0 (1127) pt_281 pt_286
private def pt_292 : PTree := .inf 4
private def pt_294 : PTree := .inf 4
private def pt_295 : PTree := .inf 6
private def pt_293 : PTree := .split 2 (-742) pt_294 pt_295
private def pt_291 : PTree := .split 2 (-786) pt_292 pt_293
private def pt_296 : PTree := .inf 4
private def pt_290 : PTree := .split 0 (1127) pt_291 pt_296
private def pt_297 : PTree := .inf 6
private def pt_289 : PTree := .split 2 (-698) pt_290 pt_297
private def pt_279 : PTree := .split 1 (448) pt_280 pt_289
private def pt_298 : PTree := .inf 6
private def pt_278 : PTree := .split 3 (-219) pt_279 pt_298
private def pt_258 : PTree := .split 0 (1099) pt_259 pt_278
private def pt_242 : PTree := .split 1 (384) pt_243 pt_258
private def pt_46 : PTree := .split 3 (-437) pt_47 pt_242
private def pt_0 : PTree := .split 1 (256) pt_1 pt_46

private def rootBox : Box4 := ⟨1043, 1155, 0, 512, -874, -521, -874, 0⟩
private theorem rootTree_ok : checkEnclosureTree rootBox pt_0 = true := by decide +kernel


end BorsukEightH1

end

open Metric Bornology BorsukEightH1
open scoped Pointwise

theorem OMA.solution : OMA.R_Borsuk_borsuk_conjecture_four_eight_parts_R1.H1 := by
  intro K hK hnt hc_lo hc_hi
  have hD : 0 < diam K := diam_pos hnt hK.isBounded
  obtain ⟨c₀, hS_comp, hS_diam, hS_min⟩ := exists_compact_centered_normalization hK hD
  let S : Set E4 := (fun x => x - c₀) '' ((diam K)⁻¹ • K)
  change IsCompact S at hS_comp
  change diam S = 1 at hS_diam
  change ∀ d : E4, radiusAt S 0 ≤ radiusAt S d at hS_min
  let φ : E4 → E4 := fun x => (diam K)⁻¹ • x - c₀
  have hφ_mem : ∀ {x : E4}, x ∈ K → φ x ∈ S :=
    fun hx => ⟨_, Set.smul_mem_smul_set hx, rfl⟩
  have hφ_dist : ∀ x y : E4, dist (φ x) (φ y) = (diam K)⁻¹ * dist x y := by
    intro x y
    have hsub : φ x - φ y = (diam K)⁻¹ • (x - y) := by dsimp [φ]; rw [smul_sub]; abel
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hD), ← dist_eq_norm]
  have hSne : S.Nonempty := by
    obtain ⟨x, hx⟩ := hnt.nonempty
    exact ⟨φ x, hφ_mem hx⟩
  let R := radiusAt S 0
  have hR_nn : 0 ≤ R := radiusAt_nonneg hS_comp hSne 0
  have hR_lo : (4 / 7 : ℝ) < R := by
    obtain ⟨x, hxK, hdist_lo⟩ := hc_lo (diam K • c₀)
    have hleR : dist (φ x) 0 ≤ R := dist_le_radiusAt hS_comp hSne (hφ_mem hxK) 0
    have hφc : φ (diam K • c₀) = 0 := by
      dsimp [φ]; rw [smul_smul, inv_mul_cancel₀ hD.ne', one_smul, sub_self]
    have hd_eq : dist (φ x) 0 = (diam K)⁻¹ * dist x (diam K • c₀) := by
      rw [← hφc, hφ_dist]
    have hmul := mul_lt_mul_of_pos_left hdist_lo (inv_pos.mpr hD)
    have hlhs : (diam K)⁻¹ * ((4 / 7 : ℝ) * diam K) = 4 / 7 := by field_simp
    linarith
  have hR_hi : R ≤ 627 / 1000 := by
    obtain ⟨c₁, hc₁⟩ := hc_hi
    have hle_d : radiusAt S (φ c₁) ≤ 627 / 1000 := by
      obtain ⟨z, hzS, hrz, _⟩ := radiusAt_attained hS_comp hSne (φ c₁)
      rw [hrz]
      rcases hzS with ⟨w, hw, rfl⟩
      obtain ⟨x, hxK, rfl⟩ := Set.mem_smul_set.mp hw
      change dist (φ x) (φ c₁) ≤ 627 / 1000
      rw [hφ_dist]
      have hmul := mul_le_mul_of_nonneg_left (hc₁ x hxK) (inv_pos.mpr hD).le
      have hrhs : (diam K)⁻¹ * ((627 / 1000 : ℝ) * diam K) = 627 / 1000 := by field_simp
      linarith
    exact (hS_min (φ c₁)).trans hle_d
  let r := R ^ 2
  have hr_lo_sq : (16 / 49 : ℝ) < r := by
    have hsq := pow_lt_pow_left₀ hR_lo (by norm_num) (by decide : 2 ≠ 0)
    norm_num at hsq; dsimp [r]; linarith
  have hr_hi_sq : r ≤ 393129 / 1000000 := by
    have hsq := pow_le_pow_left₀ hR_nn hR_hi 2
    norm_num at hsq; dsimp [r]; linarith
  have hr_pos : 0 < r := by linarith
  obtain ⟨P_tri, μ, c_Δ, τ, hPS, hPaff, hPnorm, hPdiam, hμpos, hμsum, hμbary, hτdist, hτlo, hτhi⟩ :=
    exists_acute_contact_triangle hS_comp hSne hS_diam hS_min hr_lo_sq
  obtain ⟨b, σ, s, h, x2, y2, x3, y3,
      hs_pos, hh_nn, hsh_r, h5h, h3s, hside1, hx23, hx30, hside23,
      hy2_nn, hy2_sq, hy3_np, hy3_sq,
      hb00, hb01, hb02, hb03, hb10, hb11, hb12, hb13, hb20, hb21, hb22, hb23⟩ :=
    exists_rotated_contact_coords hPaff hPnorm hPdiam hμpos hμsum hμbary hτdist hτlo hτhi hr_pos
  let P_st : ParamState := {
    ss := 2000 * s
    hh := 2000 * h
    xx2 := 2000 * x2
    yy2 := 2000 * y2
    xx3 := 2000 * x3
    yy3 := 2000 * y3
    rr := 4000000 * r
    hss_pos := by linarith
    hhh_nn := by linarith
    hsh_rr := by linarith [show (2000 * s) ^ 2 + (2000 * h) ^ 2 = 4000000 * (s ^ 2 + h ^ 2) by ring]
    hrr_lo := by linarith
    hrr_hi := by linarith
    h5h := by linarith [show 5 * (2000 * h) ^ 2 = 4000000 * (5 * h ^ 2) by ring,
                        show (2000 * s) ^ 2 = 4000000 * s ^ 2 by ring]
    h3s := by linarith [show 3 * (2000 * s) ^ 2 = 4000000 * (3 * s ^ 2) by ring]
    hside1 := by linarith [show 2 * (2000 * s) ^ 2 - 4000000 = 4000000 * (2 * s ^ 2 - 1) by ring,
                           show 2 * (2000 * s) * (2000 * x2) = 4000000 * (2 * s * x2) by ring]
    hx23 := by linarith
    hx30 := by linarith
    hside23 := by linarith [show (2000 * s) * (2000 * s + 2000 * x2) = 4000000 * (s * (s + x2)) by ring,
                            show 2 * (2000 * x3) ^ 2 = 4000000 * (2 * x3 ^ 2) by ring]
    hyy2_nn := by linarith
    hyy2_sq := by linarith [show (2000 * y2) ^ 2 = 4000000 * y2 ^ 2 by ring,
                            show (2000 * s) ^ 2 - (2000 * x2) ^ 2 = 4000000 * (s ^ 2 - x2 ^ 2) by ring]
    hyy3_np := by linarith
    hyy3_sq := by linarith [show (2000 * y3) ^ 2 = 4000000 * y3 ^ 2 by ring,
                            show (2000 * s) ^ 2 - (2000 * x3) ^ 2 = 4000000 * (s ^ 2 - x3 ^ 2) by ring]
  }
  let q : Fin 3 → E4 := P_tri ∘ σ
  have hqS : ∀ i, q i ∈ S := fun i => hPS (σ i)
  have hSdiam : ∀ u ∈ S, ∀ v ∈ S, dist u v ≤ 1 :=
    fun u hu v hv => hS_diam ▸ dist_le_diam_of_mem hS_comp.isBounded hu hv
  have hSnorm : ∀ u ∈ S, ‖u‖ ^ 2 ≤ r := by
    intro u hu
    have hle : dist u 0 ≤ R := dist_le_radiusAt hS_comp hSne hu 0
    rw [dist_zero_right] at hle
    exact pow_le_pow_left₀ (norm_nonneg u) hle 2
  have hq0 : b.repr (q 0) 0 = P_st.ss / 2000 ∧ b.repr (q 0) 1 = 0 ∧
      b.repr (q 0) 2 = P_st.hh / 2000 ∧ b.repr (q 0) 3 = 0 := by
    dsimp [q, P_st]; rw [hb00, hb01, hb02, hb03]; exact ⟨by ring, rfl, by ring, rfl⟩
  have hq1 : b.repr (q 1) 0 = P_st.xx2 / 2000 ∧ b.repr (q 1) 1 = P_st.yy2 / 2000 ∧
      b.repr (q 1) 2 = P_st.hh / 2000 ∧ b.repr (q 1) 3 = 0 := by
    dsimp [q, P_st]; rw [hb10, hb11, hb12, hb13]; exact ⟨by ring, by ring, by ring, rfl⟩
  have hq2 : b.repr (q 2) 0 = P_st.xx3 / 2000 ∧ b.repr (q 2) 1 = P_st.yy3 / 2000 ∧
      b.repr (q 2) 2 = P_st.hh / 2000 ∧ b.repr (q 2) 3 = 0 := by
    dsimp [q, P_st]; rw [hb20, hb21, hb22, hb23]; exact ⟨by ring, by ring, by ring, rfl⟩
  obtain ⟨D, hD_closed, hD_cov, hD_diam⟩ :=
    checkEnclosureTree_sound hSdiam hSnorm hqS rfl hq0 hq1 hq2 pt_0 (inBox_root_bounds P_st) rootTree_ok
  have hφ_cont : Continuous φ := by dsimp [φ]; fun_prop
  refine ⟨fun i => φ ⁻¹' (D i), fun i => (hD_closed i).preimage hφ_cont, ?_, ?_⟩
  · intro x hxK
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hD_cov (hφ_mem hxK))
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  · intro i x ⟨_, hxC⟩ y ⟨_, hyC⟩
    have hd_le : dist (φ x) (φ y) ≤ 999 / 1000 := hD_diam i (φ x) hxC (φ y) hyC
    rw [hφ_dist] at hd_le
    have hmul := mul_le_mul_of_nonneg_left hd_le hD.le
    have hlhs : diam K * ((diam K)⁻¹ * dist x y) = dist x y := by field_simp
    intro heq
    linarith

