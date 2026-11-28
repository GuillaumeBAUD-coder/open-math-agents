import OMAReductions.R_Erdos101_erdos_101_R2

/-!
# Four-partite rainbow extraction and intrinsic affine Menelaus-ratio concentration

Instead of lifting points to homogeneous coordinates with center-dependent
ratios, this reduction works directly in the affine plane. The first step
extracts a four-partite rainbow family of four-point lines, where each part
meets every selected line in a single point; this holds unconditionally by a
random four-coloring argument. The second step asks for a dense subfamily on
which the intrinsic affine Menelaus ratio around every triangle of lines takes
boundedly many values. From these two hypotheses, each rainbow line canonically
yields an ordered triple of points whose unique affine division parameter
defines global edge weights satisfying the triangle-ratio bound.
-/

namespace OMA.R_Erdos101_erdos_101_R2_H1_R2

open EuclideanGeometry SimpleGraph.TripartiteFromTriangles
open scoped Classical

/-- Every dense family of four-point lines admits a four-part partition of the
point set such that a positive proportion of the four-point lines are rainbow,
meeting each of the four parts in exactly one point. -/
def H1 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ∃ N : ℕ,
    ∀ S : Finset ℝ², N ≤ S.card → NonCollinearFor 5 (S : Set ℝ²) →
    δ * (S.card : ℝ) ^ 2 ≤ (linesWithPointsFor 4 (S : Set ℝ²)).ncard →
    ∃ V0 V1 V2 V3 : Finset ℝ²,
      V0 ⊆ S ∧ V1 ⊆ S ∧ V2 ⊆ S ∧ V3 ⊆ S ∧
      Disjoint V0 V1 ∧ Disjoint V0 V2 ∧ Disjoint V0 V3 ∧
      Disjoint V1 V2 ∧ Disjoint V1 V3 ∧ Disjoint V2 V3 ∧
      ∃ A : Finset (AffineSubspace ℝ ℝ²), ρ * (S.card : ℝ) ^ 2 ≤ A.card ∧
        ∀ L ∈ A, L ∈ linesWithPointsFor 4 (S : Set ℝ²) ∧
          (V0.filter (fun p => p ∈ L)).card = 1 ∧
          (V1.filter (fun p => p ∈ L)).card = 1 ∧
          (V2.filter (fun p => p ∈ L)).card = 1 ∧
          (V3.filter (fun p => p ∈ L)).card = 1

/-- Every dense four-partite rainbow family of four-point lines contains a dense
subfamily on which the intrinsic affine Menelaus ratio across every triangle of
lines takes values in a set of uniformly bounded cardinality. -/
def H2 : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∃ k : ℕ, ∃ η : ℝ, 0 < η ∧ ∃ N : ℕ,
    ∀ S : Finset ℝ², N ≤ S.card → NonCollinearFor 5 (S : Set ℝ²) →
    ∀ V0 V1 V2 V3 : Finset ℝ²,
      V0 ⊆ S → V1 ⊆ S → V2 ⊆ S → V3 ⊆ S →
      Disjoint V0 V1 → Disjoint V0 V2 → Disjoint V0 V3 →
      Disjoint V1 V2 → Disjoint V1 V3 → Disjoint V2 V3 →
      ∀ A : Finset (AffineSubspace ℝ ℝ²), ρ * (S.card : ℝ) ^ 2 ≤ A.card →
        (∀ L ∈ A, L ∈ linesWithPointsFor 4 (S : Set ℝ²) ∧
          (V0.filter (fun p => p ∈ L)).card = 1 ∧
          (V1.filter (fun p => p ∈ L)).card = 1 ∧
          (V2.filter (fun p => p ∈ L)).card = 1 ∧
          (V3.filter (fun p => p ∈ L)).card = 1) →
        ∃ B ⊆ A, η * (S.card : ℝ) ^ 2 ≤ B.card ∧
          ∃ K : Finset ℝˣ, K.card ≤ k ∧
            ∀ L1 ∈ B, ∀ L2 ∈ B, ∀ L3 ∈ B,
              ∀ x ∈ V0, ∀ y ∈ V1, ∀ z ∈ V2, ∀ w1 ∈ V2, ∀ w2 ∈ V1, ∀ w3 ∈ V0,
                x ∈ L1 → y ∈ L1 → w1 ∈ L1 →
                x ∈ L2 → w2 ∈ L2 → z ∈ L2 →
                w3 ∈ L3 → y ∈ L3 → z ∈ L3 →
                ∀ t1 t2 t3 : ℝ,
                  w1 = (1 - t1) • x + t1 • y →
                  z = (1 - t2) • x + t2 • w2 →
                  z = (1 - t3) • w3 + t3 • y →
                  ∃ u ∈ K, (u : ℝ) = (1 - t2) * (t1 / (1 - t1)) / t3

lemma line_eq_of_mem_linesWithPointsFor {S : Set ℝ²} {L : AffineSubspace ℝ ℝ²}
    (hL : L ∈ linesWithPointsFor 4 S) {a b : ℝ²} (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b) :
    line[ℝ, a, b] = L := by
  obtain ⟨⟨p, _, q, _, hpq, rfl⟩, _⟩ := hL
  have hfinL : Module.finrank ℝ (line[ℝ, p, q]).direction = 1 := by
    rw [direction_affineSpan, vectorSpan_pair]
    exact finrank_span_singleton (vsub_ne_zero.mpr hpq)
  have hfinab : Module.finrank ℝ (line[ℝ, a, b]).direction = 1 := by
    rw [direction_affineSpan, vectorSpan_pair]
    exact finrank_span_singleton (vsub_ne_zero.mpr hab)
  apply (AffineSubspace.eq_iff_direction_eq_of_mem (left_mem_affineSpan_pair ℝ a b) ha).mpr
  apply Submodule.eq_of_le_of_finrank_eq
  · exact AffineSubspace.direction_le (affineSpan_pair_le_of_mem_of_mem ha hb)
  · exact hfinab.trans hfinL.symm

lemma exists_affine_param {x y z : ℝ²} (hxz : x ≠ z) (hyz : y ≠ z)
    (hz : z ∈ line[ℝ, x, y]) :
    ∃ t : ℝ, t ≠ 0 ∧ t ≠ 1 ∧ z = (1 - t) • x + t • y := by
  obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hz
  have hzeq : z = (1 - t) • x + t • y := by
    rw [← ht, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    module
  refine ⟨t, ?_, ?_, hzeq⟩
  · intro ht0
    apply hxz
    rw [hzeq, ht0]
    module
  · intro ht1
    apply hyz
    rw [hzeq, ht1]
    module

lemma affine_param_unique {x y z : ℝ²} (hxy : x ≠ y) {t₁ t₂ : ℝ}
    (h₁ : z = (1 - t₁) • x + t₁ • y) (h₂ : z = (1 - t₂) • x + t₂ • y) :
    t₁ = t₂ := by
  have hdiff : (t₁ - t₂) • (y - x) = 0 := by
    have hsub : ((1 - t₁) • x + t₁ • y) - ((1 - t₂) • x + t₂ • y) = 0 := by
      rw [← h₁, ← h₂, sub_self]
    calc
      (t₁ - t₂) • (y - x) = ((1 - t₁) • x + t₁ • y) - ((1 - t₂) • x + t₂ • y) := by module
      _ = 0 := hsub
  rcases smul_eq_zero.mp hdiff with ht | hvec
  · exact sub_eq_zero.mp ht
  · exact absurd (sub_eq_zero.mp hvec).symm hxy

lemma existsUnique_of_filter_card_eq_one {V : Finset ℝ²} {L : AffineSubspace ℝ ℝ²}
    (h : (V.filter (fun p => p ∈ L)).card = 1) :
    ∃! p : ℝ², p ∈ V ∧ p ∈ L := by
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h
  refine ⟨p, ?_, ?_⟩
  · have : p ∈ V.filter (fun q => q ∈ L) := by rw [hp]; simp
    exact Finset.mem_filter.mp this
  · intro q hq
    have : q ∈ V.filter (fun r => r ∈ L) := Finset.mem_filter.mpr hq
    rw [hp, Finset.mem_singleton] at this
    exact this

theorem main : H1 → H2 → OMA.R_Erdos101_erdos_101_R2.H1 := by
  intro rainbow concentrate δ hδ
  obtain ⟨ρ, hρ, N1, hN1⟩ := rainbow δ hδ
  obtain ⟨k, η, hη, N2, hN2⟩ := concentrate ρ hρ
  refine ⟨k, η, hη, max N1 N2, ?_⟩
  intro S hS cap dense
  obtain ⟨V0, V1, V2, V3, hV0, hV1, hV2, hV3, h01, h02, h03, h12, h13, h23, A, hA_card, hA⟩ :=
    hN1 S ((le_max_left ..).trans hS) cap dense
  obtain ⟨B, hBA, hB_card, K, hK_card, hK⟩ :=
    hN2 S ((le_max_right ..).trans hS) cap V0 V1 V2 V3
      hV0 hV1 hV2 hV3 h01 h02 h03 h12 h13 h23 A hA_card hA
  have hB : ∀ L ∈ B, L ∈ linesWithPointsFor 4 (S : Set ℝ²) ∧
      (V0.filter (fun p => p ∈ L)).card = 1 ∧
      (V1.filter (fun p => p ∈ L)).card = 1 ∧
      (V2.filter (fun p => p ∈ L)).card = 1 ∧
      (V3.filter (fun p => p ∈ L)).card = 1 :=
    fun L hL => hA L (hBA hL)
  let mkTriple : {L // L ∈ B} → S × S × S := fun L =>
    let h0 := (existsUnique_of_filter_card_eq_one (hB L.1 L.2).2.1).exists
    let h1 := (existsUnique_of_filter_card_eq_one (hB L.1 L.2).2.2.1).exists
    let h2 := (existsUnique_of_filter_card_eq_one (hB L.1 L.2).2.2.2.1).exists
    (⟨Classical.choose h0, hV0 (Classical.choose_spec h0).1⟩,
     ⟨Classical.choose h1, hV1 (Classical.choose_spec h1).1⟩,
     ⟨Classical.choose h2, hV2 (Classical.choose_spec h2).1⟩)
  have hmk_mem : ∀ L : {L // L ∈ B},
      ((mkTriple L).1 : ℝ²) ∈ V0 ∧ ((mkTriple L).1 : ℝ²) ∈ L.1 ∧
      ((mkTriple L).2.1 : ℝ²) ∈ V1 ∧ ((mkTriple L).2.1 : ℝ²) ∈ L.1 ∧
      ((mkTriple L).2.2 : ℝ²) ∈ V2 ∧ ((mkTriple L).2.2 : ℝ²) ∈ L.1 := by
    intro L
    let h0 := (existsUnique_of_filter_card_eq_one (hB L.1 L.2).2.1).exists
    let h1 := (existsUnique_of_filter_card_eq_one (hB L.1 L.2).2.2.1).exists
    let h2 := (existsUnique_of_filter_card_eq_one (hB L.1 L.2).2.2.2.1).exists
    exact ⟨(Classical.choose_spec h0).1, (Classical.choose_spec h0).2,
      (Classical.choose_spec h1).1, (Classical.choose_spec h1).2,
      (Classical.choose_spec h2).1, (Classical.choose_spec h2).2⟩
  have hmk_ne : ∀ L : {L // L ∈ B},
      ((mkTriple L).1 : ℝ²) ≠ ((mkTriple L).2.1 : ℝ²) ∧
      ((mkTriple L).1 : ℝ²) ≠ ((mkTriple L).2.2 : ℝ²) ∧
      ((mkTriple L).2.1 : ℝ²) ≠ ((mkTriple L).2.2 : ℝ²) := by
    intro L
    obtain ⟨hxV, _, hyV, _, hzV, _⟩ := hmk_mem L
    refine ⟨?_, ?_, ?_⟩
    · intro h; exact Finset.disjoint_left.mp h01 hxV (h ▸ hyV)
    · intro h; exact Finset.disjoint_left.mp h02 hxV (h ▸ hzV)
    · intro h; exact Finset.disjoint_left.mp h12 hyV (h ▸ hzV)
  have hmk_line01 : ∀ L : {L // L ∈ B},
      line[ℝ, ((mkTriple L).1 : ℝ²), ((mkTriple L).2.1 : ℝ²)] = L.1 := by
    intro L
    obtain ⟨_, hxL, _, hyL, _, _⟩ := hmk_mem L
    exact line_eq_of_mem_linesWithPointsFor (hB L.1 L.2).1 hxL hyL (hmk_ne L).1
  have hmk_line02 : ∀ L : {L // L ∈ B},
      line[ℝ, ((mkTriple L).1 : ℝ²), ((mkTriple L).2.2 : ℝ²)] = L.1 := by
    intro L
    obtain ⟨_, hxL, _, _, _, hzL⟩ := hmk_mem L
    exact line_eq_of_mem_linesWithPointsFor (hB L.1 L.2).1 hxL hzL (hmk_ne L).2.1
  have hmk_line12 : ∀ L : {L // L ∈ B},
      line[ℝ, ((mkTriple L).2.1 : ℝ²), ((mkTriple L).2.2 : ℝ²)] = L.1 := by
    intro L
    obtain ⟨_, _, _, hyL, _, hzL⟩ := hmk_mem L
    exact line_eq_of_mem_linesWithPointsFor (hB L.1 L.2).1 hyL hzL (hmk_ne L).2.2
  have hmk_inj : Function.Injective mkTriple := by
    intro L1 L2 hEq
    apply Subtype.ext
    rw [← hmk_line01 L1, ← hmk_line01 L2, hEq]
  let T : Finset (S × S × S) := B.attach.image mkTriple
  have hT_card : T.card = B.card := by
    rw [Finset.card_image_of_injective _ hmk_inj, Finset.card_attach]
  have hT_dense : η * (S.card : ℝ) ^ 2 ≤ T.card := by
    rw [hT_card]
    exact hB_card
  have hT_injOn : (T : Set (S × S × S)).InjOn (fun e => line[ℝ, (e.1 : ℝ²), (e.2.1 : ℝ²)]) := by
    intro e1 he1 e2 he2 hline
    obtain ⟨L1, _, rfl⟩ := Finset.mem_image.mp he1
    obtain ⟨L2, _, rfl⟩ := Finset.mem_image.mp he2
    have hL : L1 = L2 := by
      apply Subtype.ext
      rw [← hmk_line01 L1, ← hmk_line01 L2]
      exact hline
    rw [hL]
  have hT_marks : ∀ e ∈ T, e.1 ≠ e.2.1 ∧ e.1 ≠ e.2.2 ∧ e.2.1 ≠ e.2.2 ∧
      line[ℝ, (e.1 : ℝ²), (e.2.1 : ℝ²)] ∈ linesWithPointsFor 4 (S : Set ℝ²) := by
    intro e he
    obtain ⟨L, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨h01ne, h02ne, h12ne⟩ := hmk_ne L
    refine ⟨fun h => h01ne (congrArg Subtype.val h),
      fun h => h02ne (congrArg Subtype.val h),
      fun h => h12ne (congrArg Subtype.val h), ?_⟩
    rw [hmk_line01 L]
    exact (hB L.1 L.2).1
  have hT_disj : ExplicitDisjoint T := by
    refine ⟨?_, ?_, ?_⟩
    · intro x y z x' h1 h2
      obtain ⟨L1, _, hL1⟩ := Finset.mem_image.mp h1
      obtain ⟨L2, _, hL2⟩ := Finset.mem_image.mp h2
      have hL : L1 = L2 := by
        apply Subtype.ext
        have e1 := hmk_line12 L1
        have e2 := hmk_line12 L2
        rw [hL1] at e1
        rw [hL2] at e2
        exact e1.symm.trans e2
      subst hL
      have hEq : (x, y, z) = (x', y, z) := hL1.symm.trans hL2
      exact congrArg Prod.fst hEq
    · intro x y z y' h1 h2
      obtain ⟨L1, _, hL1⟩ := Finset.mem_image.mp h1
      obtain ⟨L2, _, hL2⟩ := Finset.mem_image.mp h2
      have hL : L1 = L2 := by
        apply Subtype.ext
        have e1 := hmk_line02 L1
        have e2 := hmk_line02 L2
        rw [hL1] at e1
        rw [hL2] at e2
        exact e1.symm.trans e2
      subst hL
      have hEq : (x, y, z) = (x, y', z) := hL1.symm.trans hL2
      exact congrArg (fun p => p.2.1) hEq
    · intro x y z z' h1 h2
      obtain ⟨L1, _, hL1⟩ := Finset.mem_image.mp h1
      obtain ⟨L2, _, hL2⟩ := Finset.mem_image.mp h2
      have hL : L1 = L2 := by
        apply Subtype.ext
        have e1 := hmk_line01 L1
        have e2 := hmk_line01 L2
        rw [hL1] at e1
        rw [hL2] at e2
        exact e1.symm.trans e2
      subst hL
      have hEq : (x, y, z) = (x, y, z') := hL1.symm.trans hL2
      exact congrArg (fun p => p.2.2) hEq
  have hT_param : ∀ e ∈ T,
      ∃ t : ℝ, t ≠ 0 ∧ t ≠ 1 ∧ (e.2.2 : ℝ²) = (1 - t) • (e.1 : ℝ²) + t • (e.2.1 : ℝ²) := by
    intro e he
    obtain ⟨L, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨_, _, _, _, _, hzL⟩ := hmk_mem L
    obtain ⟨_, h02ne, h12ne⟩ := hmk_ne L
    rw [← hmk_line01 L] at hzL
    exact exists_affine_param h02ne h12ne hzL
  let a : S → S → ℝˣ := fun x z =>
    if h : ∃ y : S, (x, y, z) ∈ T then
      let y := Classical.choose h
      let hy : (x, y, z) ∈ T := Classical.choose_spec h
      let ht := hT_param (x, y, z) hy
      Units.mk0 (1 - Classical.choose ht)
        (sub_ne_zero.mpr (Classical.choose_spec ht).2.1.symm)
    else 1
  let b : S → S → ℝˣ := fun y z =>
    if h : ∃ x : S, (x, y, z) ∈ T then
      let x := Classical.choose h
      let hx : (x, y, z) ∈ T := Classical.choose_spec h
      let ht := hT_param (x, y, z) hx
      Units.mk0 (Classical.choose ht) (Classical.choose_spec ht).1
    else 1
  let d : S → S → ℝˣ := fun x y =>
    if h : ∃ z : S, (x, y, z) ∈ T then
      let z := Classical.choose h
      let hz : (x, y, z) ∈ T := Classical.choose_spec h
      let ht := hT_param (x, y, z) hz
      Units.mk0 (Classical.choose ht / (1 - Classical.choose ht))
        (div_ne_zero (Classical.choose_spec ht).1
          (sub_ne_zero.mpr (Classical.choose_spec ht).2.1.symm))
    else 1
  have ha_val : ∀ {x y z : S} (hmem : (x, y, z) ∈ T) {t : ℝ},
      (z : ℝ²) = (1 - t) • (x : ℝ²) + t • (y : ℝ²) → (a x z : ℝ) = 1 - t := by
    intro x y z hmem t hzt
    have hex : ∃ y' : S, (x, y', z) ∈ T := ⟨y, hmem⟩
    let t' : ℝ :=
      Classical.choose (hT_param (x, Classical.choose hex, z) (Classical.choose_spec hex))
    have ha_def : (a x z : ℝ) = 1 - t' := by
      simp only [a, dif_pos hex, Units.val_mk0, t']
    rw [ha_def]
    have hy_eq : Classical.choose hex = y := hT_disj.inj₁ (Classical.choose_spec hex) hmem
    have hspec : (z : ℝ²) = (1 - t') • (x : ℝ²) + t' • (Classical.choose hex).1 :=
      (Classical.choose_spec
        (hT_param (x, Classical.choose hex, z) (Classical.choose_spec hex))).2.2
    rw [hy_eq] at hspec
    have hxy : (x : ℝ²) ≠ (y : ℝ²) := fun h => (hT_marks (x, y, z) hmem).1 (Subtype.ext h)
    rw [affine_param_unique hxy hspec hzt]
  have hb_val : ∀ {x y z : S} (hmem : (x, y, z) ∈ T) {t : ℝ},
      (z : ℝ²) = (1 - t) • (x : ℝ²) + t • (y : ℝ²) → (b y z : ℝ) = t := by
    intro x y z hmem t hzt
    have hex : ∃ x' : S, (x', y, z) ∈ T := ⟨x, hmem⟩
    let t' : ℝ :=
      Classical.choose (hT_param (Classical.choose hex, y, z) (Classical.choose_spec hex))
    have hb_def : (b y z : ℝ) = t' := by
      simp only [b, dif_pos hex, Units.val_mk0, t']
    rw [hb_def]
    have hx_eq : Classical.choose hex = x := hT_disj.inj₀ (Classical.choose_spec hex) hmem
    have hspec : (z : ℝ²) = (1 - t') • (Classical.choose hex).1 + t' • (y : ℝ²) :=
      (Classical.choose_spec
        (hT_param (Classical.choose hex, y, z) (Classical.choose_spec hex))).2.2
    rw [hx_eq] at hspec
    have hxy : (x : ℝ²) ≠ (y : ℝ²) := fun h => (hT_marks (x, y, z) hmem).1 (Subtype.ext h)
    rw [affine_param_unique hxy hspec hzt]
  have hd_val : ∀ {x y z : S} (hmem : (x, y, z) ∈ T) {t : ℝ},
      (z : ℝ²) = (1 - t) • (x : ℝ²) + t • (y : ℝ²) → (d x y : ℝ) = t / (1 - t) := by
    intro x y z hmem t hzt
    have hex : ∃ z' : S, (x, y, z') ∈ T := ⟨z, hmem⟩
    let t' : ℝ :=
      Classical.choose (hT_param (x, y, Classical.choose hex) (Classical.choose_spec hex))
    have hd_def : (d x y : ℝ) = t' / (1 - t') := by
      simp only [d, dif_pos hex, Units.val_mk0, t']
    rw [hd_def]
    have hz_eq : Classical.choose hex = z := hT_disj.inj₂ (Classical.choose_spec hex) hmem
    have hspec : (Classical.choose hex).1 = (1 - t') • (x : ℝ²) + t' • (y : ℝ²) :=
      (Classical.choose_spec
        (hT_param (x, y, Classical.choose hex) (Classical.choose_spec hex))).2.2
    rw [hz_eq] at hspec
    have hxy : (x : ℝ²) ≠ (y : ℝ²) := fun h => (hT_marks (x, y, z) hmem).1 (Subtype.ext h)
    rw [affine_param_unique hxy hspec hzt]
  refine ⟨T, hT_disj, hT_dense, hT_injOn, hT_marks, a, b, d, ?_, K, hK_card, ?_⟩
  · rintro ⟨x, y, z⟩ he
    obtain ⟨t, _, _, hzt⟩ := hT_param (x, y, z) he
    have ha' := ha_val he hzt
    have hb' := hb_val he hzt
    have hd' := hd_val he hzt
    refine ⟨?_, ?_, ?_⟩
    · dsimp only
      rw [ha', hb']
      ring
    · dsimp only
      rw [ha', hb']
      exact hzt.symm
    · apply Units.ext
      dsimp only
      rw [Units.val_div_eq_div_val, ha', hb', hd']
  · intro x y z ⟨w1, h1⟩ ⟨w2, h2⟩ ⟨w3, h3⟩
    obtain ⟨L1, _, hL1⟩ := Finset.mem_image.mp h1
    obtain ⟨L2, _, hL2⟩ := Finset.mem_image.mp h2
    obtain ⟨L3, _, hL3⟩ := Finset.mem_image.mp h3
    obtain ⟨t1, _, _, ht1⟩ := hT_param (x, y, w1) h1
    obtain ⟨t2, _, _, ht2⟩ := hT_param (x, w2, z) h2
    obtain ⟨t3, _, _, ht3⟩ := hT_param (w3, y, z) h3
    have hm1 := hmk_mem L1
    have hm2 := hmk_mem L2
    have hm3 := hmk_mem L3
    rw [hL1] at hm1
    rw [hL2] at hm2
    rw [hL3] at hm3
    obtain ⟨u, huK, hu_eq⟩ := hK L1.1 L1.2 L2.1 L2.2 L3.1 L3.2
      (x : ℝ²) hm1.1 (y : ℝ²) hm1.2.2.1 (z : ℝ²) hm2.2.2.2.2.1
      (w1 : ℝ²) hm1.2.2.2.2.1 (w2 : ℝ²) hm2.2.2.1 (w3 : ℝ²) hm3.1
      hm1.2.1 hm1.2.2.2.1 hm1.2.2.2.2.2
      hm2.2.1 hm2.2.2.2.1 hm2.2.2.2.2.2
      hm3.2.1 hm3.2.2.2.1 hm3.2.2.2.2.2
      t1 t2 t3 ht1 ht2 ht3
    have hratio : a x z * d x y / b y z = u := by
      apply Units.ext
      rw [Units.val_div_eq_div_val, Units.val_mul, ha_val h2 ht2, hd_val h1 ht1, hb_val h3 ht3,
        hu_eq]
    rw [hratio]
    exact huK

end OMA.R_Erdos101_erdos_101_R2_H1_R2
