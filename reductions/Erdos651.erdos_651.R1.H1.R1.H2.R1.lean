import OMAReductions.R_Erdos651_erdos_651_R1_H1_R1
import Mathlib.Data.Nat.Choose.Vandermonde

/-!
The three coordinate projections of a polyhedral orthant give three contraction
preorders. An antichain in one preorder contains a large planar line-free
family, where planar cups and caps provide the required witnesses.
-/

open scoped Affine EuclideanGeometry BigOperators

namespace OMA.R_Erdos651_erdos_651_R1_H1_R1_H2_R1

private theorem median_between {u v w : ℝ} :
    min u v ≤ max (min u v) (max (min u w) (min v w)) ∧
      max (min u v) (max (min u w) (min v w)) ≤ max u v := by
  exact ⟨le_max_left _ _, max_le (min_le_left _ _ |>.trans (le_max_left _ _))
    (max_le ((min_le_left _ _).trans (le_max_left _ _))
      ((min_le_left _ _).trans (le_max_right _ _)))⟩

private theorem affine_between_nonpos {a b u v t : ℝ}
    (hu : a + u * b ≤ 0) (hv : a + v * b ≤ 0)
    (ht₁ : min u v ≤ t) (ht₂ : t ≤ max u v) : a + t * b ≤ 0 := by
  have hsign := le_total 0 b
  rcases le_total u v with huv | hvu
  · rw [min_eq_left huv] at ht₁
    rw [max_eq_right huv] at ht₂
    rcases hsign with hb | hb
    · linarith [mul_le_mul_of_nonneg_right ht₂ hb]
    · linarith [mul_le_mul_of_nonpos_right ht₁ hb]
  · rw [min_eq_right hvu] at ht₁
    rw [max_eq_left hvu] at ht₂
    rcases hsign with hb | hb
    · linarith [mul_le_mul_of_nonneg_right ht₂ hb]
    · linarith [mul_le_mul_of_nonpos_right ht₁ hb]

/-- If every two coordinates allow an affine-line parameter, all three do.
The median of the three witnesses satisfies every coordinate. -/
theorem all_coordinates_of_pairs (a b : Fin 3 → ℝ)
    (h : ∀ j : Fin 3, ∃ t : ℝ, ∀ k : Fin 3, k ≠ j → a k + t * b k ≤ 0) :
    ∃ t : ℝ, ∀ k : Fin 3, a k + t * b k ≤ 0 := by
  obtain ⟨t₀, h₀⟩ := h 0
  obtain ⟨t₁, h₁⟩ := h 1
  obtain ⟨t₂, h₂⟩ := h 2
  refine ⟨max (min t₀ t₁) (max (min t₀ t₂) (min t₁ t₂)), ?_⟩
  intro k
  fin_cases k
  · apply affine_between_nonpos (h₁ 0 (by decide)) (h₂ 0 (by decide))
    · exact (le_max_right (min t₀ t₂) (min t₁ t₂)).trans (le_max_right _ _)
    · exact max_le ((min_le_right _ _).trans (le_max_left _ _))
        (max_le ((min_le_right _ _).trans (le_max_right _ _))
          ((min_le_left _ _).trans (le_max_left _ _)))
  · apply affine_between_nonpos (h₀ 1 (by decide)) (h₂ 1 (by decide))
    · exact (le_max_left (min t₀ t₂) (min t₁ t₂)).trans (le_max_right _ _)
    · exact max_le ((min_le_left _ _).trans (le_max_left _ _))
        (max_le (min_le_left _ _ |>.trans (le_max_left _ _))
          ((min_le_right _ _).trans (le_max_right _ _)))
  · exact affine_between_nonpos (h₀ 2 (by decide)) (h₁ 2 (by decide))
      median_between.1 median_between.2

/-- An extrapolated point of a segment can belong to the negative orthant
only when one endpoint is dominated by a contraction of the other. -/
theorem contraction_of_extrapolated_nonpos {ι : Type*} (x y : ι → ℝ) {t : ℝ}
    (ht : t < 0) (h : ∀ i, (1 - t) * x i + t * y i ≤ 0) :
    ∃ s : ℝ, 0 ≤ s ∧ s < 1 ∧ ∀ i, x i ≤ s * y i := by
  have hden : 0 < 1 - t := by linarith
  refine ⟨-t / (1 - t), div_nonneg (by linarith) hden.le, ?_, fun i => ?_⟩
  · exact (div_lt_one hden).2 (by linarith)
  · rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hden).2
    linarith only [h i]

/-- Conversely coordinatewise domination by a strict contraction gives
an explicit point of the full line in the closed negative orthant. -/
theorem nonpos_line_of_contraction {ι : Type*} (x y : ι → ℝ) {s : ℝ}
    (hs : s < 1) (h : ∀ i, x i ≤ s * y i) :
    ∃ t : ℝ, ∀ i, (1 - t) * x i + t * y i ≤ 0 := by
  have hden : 0 < 1 - s := by linarith
  refine ⟨-s / (1 - s), fun i => ?_⟩
  have heq : (1 - -s / (1 - s)) * x i + (-s / (1 - s)) * y i =
      (x i - s * y i) / (1 - s) := by
    field_simp
    ring
  rw [heq]
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (h i)) hden.le

/-- A strict common positive coordinate rules out an intersection on the segment.
If both endpoint contractions also fail, the whole line avoids the quadrant. -/
theorem pair_line_avoids {ι : Type*} (x y : ι → ℝ) (j : ι)
    (hx : 0 < x j) (hy : 0 < y j)
    (hxy : ¬ ∃ s : ℝ, 0 ≤ s ∧ s < 1 ∧ ∀ i, x i ≤ s * y i)
    (hyx : ¬ ∃ s : ℝ, 0 ≤ s ∧ s < 1 ∧ ∀ i, y i ≤ s * x i) :
    ¬ ∃ t : ℝ, ∀ i, (1 - t) * x i + t * y i ≤ 0 := by
  rintro ⟨t, ht⟩
  rcases lt_or_ge t 0 with hn | hn
  · exact hxy (contraction_of_extrapolated_nonpos x y hn ht)
  rcases lt_or_ge 1 t with hp | hp
  · apply hyx (contraction_of_extrapolated_nonpos y x (t := 1 - t) (by linarith) ?_)
    intro i
    convert ht i using 1
    ring
  · have hsum : 0 < (1 - t) * x j + t * y j := by
      rcases eq_or_lt_of_le hn with hzero | hpos
      · simpa [← hzero] using hx
      · positivity
    exact (not_le_of_gt hsum) (ht j)

theorem binomial_slack {a n : ℕ} (ha : 2 ≤ a) (hn : 2 ≤ n) :
    2 * ((n + a - 4).choose (a - 2) + 1) ≤ (n + a).choose a := by
  have hrepr : n + a = (n + a - 4) + 4 := by omega
  have hrhs : (n + a).choose a =
      ((n + a - 4) + 4).choose a := by rw [← hrepr]
  rw [hrhs, Nat.add_choose_eq]
  have hm : (a - 2, 2) ∈ Finset.HasAntidiagonal.antidiagonal a :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by omega)
  have hle : (n + a - 4).choose (a - 2) * (4 : ℕ).choose 2 ≤
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal a, (n + a - 4).choose ij.1 * (4 : ℕ).choose ij.2 :=
    Finset.single_le_sum (f := fun ij => (n + a - 4).choose ij.1 * (4 : ℕ).choose ij.2)
      (fun _ _ => Nat.zero_le _) hm
  have hc : 0 < (n + a - 4).choose (a - 2) := Nat.choose_pos (by omega)
  have h42 : (4 : ℕ).choose 2 = 6 := by decide
  rw [h42] at hle
  omega

private theorem of_line_free (e : (ℝ^3) ≃ᵃ[ℝ] (ℝ^3)) (x y : ℝ^3)
    (h : Disjoint (line[ℝ, x, y] : Set (ℝ^3)) {z | ∀ k : Fin 3, e z k ≤ 0}) :
    ∃ j : Fin 3, ¬ ∃ t : ℝ, ∀ k : Fin 2,
      (1 - t) * e x (j.succAbove k) + t * e y (j.succAbove k) ≤ 0 := by
  by_contra! hall
  have hp (j : Fin 3) : ∃ t : ℝ, ∀ k : Fin 3, k ≠ j →
      e x k + t * (e y k - e x k) ≤ 0 := by
    obtain ⟨t, ht⟩ := hall j
    refine ⟨t, fun k hkj => ?_⟩
    obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hkj
    convert ht i using 1
    ring
  obtain ⟨t, ht⟩ := all_coordinates_of_pairs (fun k => e x k)
    (fun k => e y k - e x k) hp
  let w := AffineMap.lineMap x y t
  have hw : w ∈ line[ℝ, x, y] := mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨t, rfl⟩
  apply Set.disjoint_left.mp h hw
  intro k
  change e.toAffineMap (AffineMap.lineMap x y t) k ≤ 0
  rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_module]
  change (1 - t) * e x k + t * e y k ≤ 0
  convert ht k using 1
  ring

private theorem orientation_symmetric {ι : Type*} {u v : ι → ℝ}
    (h : ∃ t : ℝ, ∀ k, (1 - t) * u k + t * v k ≤ 0) :
    ∃ t : ℝ, ∀ k, (1 - t) * v k + t * u k ≤ 0 := by
  obtain ⟨t, ht⟩ := h
  refine ⟨1 - t, fun k => ?_⟩
  convert ht k using 1
  ring

private theorem large_positive_half {V : Type} [DecidableEq V]
    (S : Finset V) (f : V → Fin 2 → ℝ) {m : ℕ} (hS : 2 * m < S.card)
    (hpos : ∀ x ∈ S, ∃ i, 0 < f x i) :
    ∃ i : Fin 2, ∃ T ⊆ S, m < T.card ∧ ∀ x ∈ T, 0 < f x i := by
  classical
  let A := S.filter (fun x => 0 < f x 0)
  let B := S.filter (fun x => ¬0 < f x 0)
  have hsum : A.card + B.card = S.card := Finset.card_filter_add_card_filter_not (s := S) _
  by_cases hA : m < A.card
  · exact ⟨0, A, Finset.filter_subset _ _, hA, fun x hx => (Finset.mem_filter.mp hx).2⟩
  · refine ⟨1, B, Finset.filter_subset _ _, by omega, ?_⟩
    intro x hx
    obtain ⟨i, hi⟩ := hpos x (Finset.mem_filter.mp hx).1
    fin_cases i
    · exact ((Finset.mem_filter.mp hx).2 hi).elim
    · exact hi

/-- Finite simultaneous-chain pigeonhole consequence of Dilworth's theorem. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] (R : Fin 3 → V → V → Prop) (m : ℕ),
    (∀ j x, R j x x) →
    (∀ j x y z, R j x y → R j y z → R j x z) →
    (∀ x y, x ≠ y → ∃ j, ¬R j x y ∧ ¬R j y x) →
    m ^ 3 < Fintype.card V →
    ∃ S : Finset V, m < S.card ∧ ∃ j : Fin 3,
      ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬R j x y ∧ ¬R j y x

/-- The planar cups-versus-caps theorem for a set of points whose pair lines
miss the negative quadrant. Witnesses are indexed by the original set. -/
def H2 : Prop :=
  ∀ (V : Type) [DecidableEq V] (S : Finset V) (f : V → Fin 2 → ℝ) (a n : ℕ),
    (∀ Z ⊆ S, Z.card ≤ 3 → AffineIndependent ℝ (fun z : ↥(Z : Set V) => f z)) →
    (∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      ¬ ∃ t : ℝ, ∀ i, (1 - t) * f x i + t * f y i ≤ 0) →
    2 ≤ a → 2 ≤ n → (n + a - 4).choose (a - 2) + 1 < S.card →
    (∃ K ⊆ S, K.card = n ∧ ∀ x ∈ K,
      f x ∉ convexHull ℝ (f '' (K.erase x : Set V))) ∨
    (∃ K ⊆ S, K.card = a ∧ ∀ x ∈ K,
      f x ∉ convexHull ℝ ({q : Fin 2 → ℝ | ∀ i, q i ≤ 0} ∪
        f '' (K.erase x : Set V)))

theorem main : H1 → H2 → OMA.R_Erdos651_erdos_651_R1_H1_R1.H2 := by
  classical
  intro hDilworth hPlanar P Y a n hOrthant _hGeneral hLines ha hn hLarge
  obtain ⟨e, rfl, hProjections⟩ := hOrthant
  let m := (n + a).choose a
  let f (j : Fin 3) : (ℝ^3) →ᵃ[ℝ] (Fin 2 → ℝ) :=
    (({ toFun := fun x k => x (j.succAbove k)
        map_add' := by intros; rfl
        map_smul' := by intros; rfl } :
        (ℝ^3) →ₗ[ℝ] (Fin 2 → ℝ)).toAffineMap).comp e.toAffineMap
  have hf (j : Fin 3) (x : ℝ^3) (i : Fin 2) : f j x i = e x (j.succAbove i) := rfl
  let R (j : Fin 3) (x y : (ℝ^3)) : Prop :=
    x = y ∨ ∃ s : ℝ, 0 ≤ s ∧ s < 1 ∧ ∀ k, f j x k ≤ s * f j y k
  have hRtrans (j : Fin 3) (x y z : (ℝ^3)) : R j x y → R j y z → R j x z := by
    rintro (rfl | ⟨r, hr0, hr1, hr⟩) hs
    · exact hs
    rcases hs with rfl | ⟨s, hs0, hs1, hs⟩
    · exact Or.inr ⟨r, hr0, hr1, hr⟩
    refine Or.inr ⟨r * s, mul_nonneg hr0 hs0, ?_, fun k => ?_⟩
    · calc
        r * s ≤ r * 1 := mul_le_mul_of_nonneg_left hs1.le hr0
        _ = r := mul_one _
        _ < 1 := hr1
    · calc
        f j x k ≤ r * f j y k := hr k
        _ ≤ r * (s * f j z k) := mul_le_mul_of_nonneg_left (hs k) hr0
        _ = (r * s) * f j z k := (mul_assoc _ _ _).symm
  have hRinc (x y : ↥Y) (hxy : x ≠ y) : ∃ j, ¬ R j x y ∧ ¬ R j y x := by
    have hv : (x : ℝ^3) ≠ (y : ℝ^3) := fun h => hxy (Subtype.ext h)
    obtain ⟨j, hj⟩ := of_line_free e x y (hLines x x.property y y.property hv)
    simp only [← hf] at hj
    refine ⟨j, ?_, ?_⟩
    · rintro (h | ⟨s, _, hs, h⟩)
      · exact hv h
      · exact hj (nonpos_line_of_contraction (f j x) (f j y) hs h)
    · rintro (h | ⟨s, _, hs, h⟩)
      · exact hv h.symm
      · exact hj (orientation_symmetric (nonpos_line_of_contraction (f j y) (f j x) hs h))
  have hcard : m ^ 3 < Fintype.card ↥Y := by
    simpa [m] using hLarge
  obtain ⟨T, hT, j, hAnti⟩ := hDilworth ↥Y (fun j x y => R j x y) m
    (fun _ _ => Or.inl rfl) (fun j x y z => hRtrans j x y z) hRinc hcard
  let S := T.map (Function.Embedding.subtype fun x : ℝ^3 => x ∈ Y)
  have hSY : S ⊆ Y := by
    intro x hx
    obtain ⟨z, _, rfl⟩ := Finset.mem_map.mp hx
    exact z.property
  have hS : m < S.card := by simpa only [S, Finset.card_map] using hT
  have hAnt (x : ℝ^3) (hx : x ∈ S) (y : ℝ^3) (hy : y ∈ S) (hne : x ≠ y) :
      ¬R j x y ∧ ¬R j y x := by
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hy
    exact hAnti u hu v hv (fun h => hne (congrArg Subtype.val h))
  have hm := binomial_slack ha hn
  have hpos (x : ℝ^3) (hx : x ∈ S) : ∃ i, 0 < f j x i := by
    by_contra! hx0
    have hOne : 1 < S.card := by omega
    obtain ⟨y, hy, hne⟩ := Finset.exists_mem_ne hOne x
    apply (hAnt x hx y hy hne.symm).1
    exact Or.inr ⟨0, le_rfl, zero_lt_one, by simpa using hx0⟩
  obtain ⟨i, U, hUS, hU, hUpos⟩ :=
    large_positive_half S (f j) (by omega : 2 * ((n + a - 4).choose (a - 2) + 1) < S.card) hpos
  have hUY := hUS.trans hSY
  have hULine (x : ℝ^3) (hx : x ∈ U) (y : ℝ^3) (hy : y ∈ U) (hne : x ≠ y) :
      ¬ ∃ t : ℝ, ∀ k, (1 - t) * f j x k + t * f j y k ≤ 0 := by
    obtain ⟨hn₁, hn₂⟩ := hAnt x (hUS hx) y (hUS hy) hne
    exact pair_line_avoids (f j x) (f j y) i (hUpos x hx) (hUpos y hy)
      (fun ht => hn₁ (Or.inr ht)) (fun ht => hn₂ (Or.inr ht))
  have hUP (Z : Finset (ℝ^3)) (hZU : Z ⊆ U) (hZ : Z.card ≤ 3) :
      AffineIndependent ℝ (fun z : ↥(Z : Set (ℝ^3)) => f j z) := by
    change AffineIndependent ℝ
      (fun z : ↥(Z : Set (ℝ^3)) => fun k : Fin 2 => e z (j.succAbove k))
    exact hProjections j Z (hZU.trans hUY) hZ
  rcases hPlanar (ℝ^3) U (f j) a n hUP hULine ha hn hU with
      ⟨K, hKU, hKcard, hK⟩ | ⟨K, hKU, hKcard, hK⟩
  · apply Or.inl
    refine ⟨K, hKU.trans hUY, hKcard, ?_⟩
    rw [convexIndependent_set_iff_notMem_convexHull_sdiff]
    intro x hx hcx
    apply hK x hx
    rw [← (f j).image_convexHull]
    exact ⟨x, by simpa only [Finset.coe_erase] using hcx, rfl⟩
  · apply Or.inr
    refine ⟨K, hKU.trans hUY, hKcard, ?_⟩
    intro x hx hcx
    apply hK x hx
    have him : (f j) '' ({z : ℝ^3 | ∀ k : Fin 3, e z k ≤ 0} ∪ (K.erase x : Set (ℝ^3))) ⊆
        {q : Fin 2 → ℝ | ∀ k, q k ≤ 0} ∪ (f j) '' (K.erase x : Set (ℝ^3)) := by
      rintro q ⟨z, hz | hz, rfl⟩
      · exact Or.inl fun k => hz (j.succAbove k)
      · exact Or.inr ⟨z, hz, rfl⟩
    refine convexHull_mono him ?_
    rw [← (f j).image_convexHull]
    exact ⟨x, hcx, rfl⟩

end OMA.R_Erdos651_erdos_651_R1_H1_R1_H2_R1
