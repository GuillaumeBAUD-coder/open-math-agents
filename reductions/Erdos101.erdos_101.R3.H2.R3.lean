import OMAReductions.R_Erdos101_erdos_101_R3
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal

-- Reduction Erdos101.erdos_101.R3.H2.R3 of step Erdos101.erdos_101.R3.H2
-- Credit: @Masselorc
-- Reuses anchor-incidence and shared-witness filtering lemmas from @barislabs.
-- uses note #189753
-- uses note #189769
-- uses note #189775
-- They are combined with Szemeredi Triangle Removal
-- (SimpleGraph.farFromTriangleFree_of_disjoint_triangles / triangleRemovalBound_pos).
--
-- H1 (corollary of Melchior's inequality, as noted by @RickyDash in #192065):
--   Every large no-five-collinear planar set with at most K * |T| ordinary lines
--   has fewer than |T|^2 / s four-point lines.
-- H2 (clean 16-anchor triangle front under superlinear ordinary lines):
--   For every c, C > 0, there exist K, N such that no anchor-generated configuration
--   (T, B) with |T| >= N, |B|^2 <= C * |T|, more than K * |T| ordinary lines, and
--   a valid 4-anchor witness map W on T \ B contains >= |T|^3 / c non-collinear
--   triangles whose 3 pairwise lines are clean 16-distinct-anchor four-point lines.

open EuclideanGeometry
open scoped Classical

namespace OMA.R_Erdos101_erdos_101_R3_H2_R3

-- Adapted from @barislabs note #189753.
private theorem at_most_four (T : Finset ℝ²) (cap : NonCollinearFor 5 (T : Set ℝ²)) (a b : ℝ²) :
    (T.filter (fun p => p ∈ line[ℝ, a, b])).card ≤ 4 := by
  classical
  by_contra h
  have large : 5 ≤ (T.filter (fun p => p ∈ line[ℝ, a, b])).card := by omega
  obtain ⟨U, sub, five⟩ := Finset.exists_subset_card_eq large
  apply cap (U : Set ℝ²) (Finset.coe_subset.mpr (sub.trans (Finset.filter_subset ..)))
    U.finite_toSet (by simpa using five)
  apply (collinear_iff_exists_forall_eq_smul_vadd _).mpr
  refine ⟨a, b -ᵥ a, ?_⟩
  intro p hp
  obtain ⟨u, hu⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp (Finset.mem_filter.mp (sub hp)).2
  exact ⟨u, hu.symm⟩

-- Adapted from @barislabs note #189769.
private theorem lines_meeting_anchors_card (T B : Finset ℝ²)
    (L4 : Finset (AffineSubspace ℝ ℝ²))
    (hL4 : ∀ L ∈ L4, L ∈ linesWithPointsFor 4 (T : Set ℝ²)) :
    (L4.filter (fun L => ∃ a ∈ B, a ∈ L)).card ≤ B.card * T.card := by
  classical
  let candidates := (B ×ˢ T).image (fun e => line[ℝ, e.1, e.2])
  have incl : L4.filter (fun L => ∃ a ∈ B, a ∈ L) ⊆ candidates := by
    intro L hL
    obtain ⟨hL_mem, a, ha, onL⟩ := Finset.mem_filter.mp hL
    have hL' := hL4 L hL_mem
    dsimp only [linesWithPointsFor] at hL'
    rcases hL'.1 with ⟨p, hp, q, hq, pq, rfl⟩
    obtain ⟨x, hx, ne, hline⟩ : ∃ x ∈ T, a ≠ x ∧ x ∈ line[ℝ, p, q] := by
      by_cases ap : a = p
      · exact ⟨q, hq, ap ▸ pq, right_mem_affineSpan_pair ..⟩
      · exact ⟨p, hp, ap, left_mem_affineSpan_pair ..⟩
    exact Finset.mem_image.mpr
      ⟨(a, x), Finset.mem_product.mpr ⟨ha, hx⟩,
        affineSpan_pair_eq_of_mem_of_mem_of_ne onL hline ne⟩
  calc (L4.filter (fun L => ∃ a ∈ B, a ∈ L)).card
      ≤ candidates.card := Finset.card_le_card incl
    _ ≤ (B ×ˢ T).card := Finset.card_image_le
    _ = B.card * T.card := Finset.card_product ..

-- Adapted from @barislabs note #189769.
private theorem shared_lines_card (T B : Finset ℝ²) (W : ℝ² → Finset ℝ²)
    (L4 : Finset (AffineSubspace ℝ ℝ²))
    (hL4 : ∀ L ∈ L4, L ∈ linesWithPointsFor 4 (T : Set ℝ²))
    (cap : NonCollinearFor 5 (T : Set ℝ²))
    (size : ∀ p ∈ T \ B, (W p).card ≤ 4)
    (cover : ∀ q ∈ T \ B, ∀ a ∈ W q, ∃ b ∈ B, q ∈ line[ℝ, a, b]) :
    (L4.filter (fun L =>
      ∃ p ∈ T \ B, ∃ q ∈ T \ B, p ≠ q ∧ p ∈ L ∧ q ∈ L ∧ ∃ a ∈ W p, a ∈ W q)).card ≤
    (T \ B).card * (16 * B.card) := by
  classical
  let joins (p a b : ℝ²) := (T.filter (fun q => q ∈ line[ℝ, a, b])).image (fun q => line[ℝ, p, q])
  let pencil (p a : ℝ²) := B.biUnion (joins p a)
  let throughPoint (p : ℝ²) := (W p).biUnion (pencil p)
  let candidates := (T \ B).biUnion throughPoint
  have incl :
      L4.filter (fun L =>
        ∃ p ∈ T \ B, ∃ q ∈ T \ B, p ≠ q ∧ p ∈ L ∧ q ∈ L ∧ ∃ a ∈ W p, a ∈ W q) ⊆
      candidates := by
    intro L hL
    obtain ⟨hL_mem, p, hp, q, hq, ne, pl, ql, a, ap, aq⟩ := Finset.mem_filter.mp hL
    have hL' := hL4 L hL_mem
    dsimp only [linesWithPointsFor] at hL'
    rcases hL'.1 with ⟨u, _, v, _, _, rfl⟩
    obtain ⟨b, hb, qab⟩ := cover q hq a aq
    apply Finset.mem_biUnion.mpr
    refine ⟨p, hp, Finset.mem_biUnion.mpr ⟨a, ap, Finset.mem_biUnion.mpr ⟨b, hb, ?_⟩⟩⟩
    exact Finset.mem_image.mpr
      ⟨q, Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hq).1, qab⟩,
        affineSpan_pair_eq_of_mem_of_mem_of_ne pl ql ne⟩
  have pencil_size (p a : ℝ²) : (pencil p a).card ≤ B.card * 4 :=
    calc (pencil p a).card
        ≤ ∑ b ∈ B, (joins p a b).card := Finset.card_biUnion_le
      _ ≤ ∑ _ ∈ B, 4 := Finset.sum_le_sum fun b _ =>
          Finset.card_image_le.trans (at_most_four T cap a b)
      _ = B.card * 4 := by simp
  have point_size (p : ℝ²) (hp : p ∈ T \ B) : (throughPoint p).card ≤ 16 * B.card :=
    calc (throughPoint p).card
        ≤ ∑ a ∈ W p, (pencil p a).card := Finset.card_biUnion_le
      _ ≤ ∑ _ ∈ W p, B.card * 4 := Finset.sum_le_sum fun a _ => pencil_size p a
      _ = (W p).card * (B.card * 4) := by simp
      _ ≤ 4 * (B.card * 4) := Nat.mul_le_mul_right _ (size p hp)
      _ = 16 * B.card := by ring
  calc (L4.filter (fun L =>
          ∃ p ∈ T \ B, ∃ q ∈ T \ B, p ≠ q ∧ p ∈ L ∧ q ∈ L ∧ ∃ a ∈ W p, a ∈ W q)).card
      ≤ candidates.card := Finset.card_le_card incl
    _ ≤ ∑ p ∈ T \ B, (throughPoint p).card := Finset.card_biUnion_le
    _ ≤ ∑ _ ∈ T \ B, 16 * B.card := Finset.sum_le_sum point_size
    _ = (T \ B).card * (16 * B.card) := by simp

-- Adapted from @barislabs note #189775.
private theorem distinct_endpoints {B W : Finset ℝ²} {p : ℝ²} (outside : p ∉ B)
    (chosen : ∃ a ∈ B, ∃ b ∈ B, ∃ c₁ ∈ B, ∃ d ∈ B,
      W = {a, b, c₁, d} ∧ a ≠ b ∧ c₁ ≠ d ∧
      line[ℝ, a, b] ≠ line[ℝ, c₁, d] ∧ p ∈ line[ℝ, a, b] ∧ p ∈ line[ℝ, c₁, d]) :
    W.card = 4 := by
  classical
  rcases chosen with ⟨a, ha, b, hb, c₁, hc, d, hd, rfl, ab, cd, different, pl, pr⟩
  have separate (x y : ℝ²) (hx : x ∈ B) (left : x ∈ line[ℝ, a, b]) (right : y ∈ line[ℝ, c₁, d]) :
      x ≠ y := by
    rintro rfl
    have xp : x ≠ p := by
      rintro rfl
      exact outside hx
    exact different
      ((affineSpan_pair_eq_of_mem_of_mem_of_ne left pl xp).symm.trans
        (affineSpan_pair_eq_of_mem_of_mem_of_ne right pr xp))
  have ac := separate a c₁ ha (left_mem_affineSpan_pair ..) (left_mem_affineSpan_pair ..)
  have ad := separate a d ha (left_mem_affineSpan_pair ..) (right_mem_affineSpan_pair ..)
  have bc := separate b c₁ hb (right_mem_affineSpan_pair ..) (left_mem_affineSpan_pair ..)
  have bd := separate b d hb (right_mem_affineSpan_pair ..) (right_mem_affineSpan_pair ..)
  simp [ab, cd, ac, ad, bc, bd]

-- Adapted from @barislabs note #189775.
private theorem exists_witnesses_with_bound (T B : Finset ℝ²)
    (L4 : Finset (AffineSubspace ℝ ℝ²))
    (hL4 : ∀ L ∈ L4, L ∈ linesWithPointsFor 4 (T : Set ℝ²))
    (cap : NonCollinearFor 5 (T : Set ℝ²))
    (gen : ∀ p ∈ T, p ∈ B ∨ ∃ a ∈ B, ∃ b ∈ B, ∃ c₁ ∈ B, ∃ d ∈ B,
      a ≠ b ∧ c₁ ≠ d ∧ line[ℝ, a, b] ≠ line[ℝ, c₁, d] ∧ p ∈ line[ℝ, a, b] ∧ p ∈ line[ℝ, c₁, d]) :
    ∃ W : ℝ² → Finset ℝ²,
      (∀ p ∈ T \ B, ∃ a ∈ B, ∃ b ∈ B, ∃ c₁ ∈ B, ∃ d ∈ B,
        W p = {a, b, c₁, d} ∧ a ≠ b ∧ c₁ ≠ d ∧
        line[ℝ, a, b] ≠ line[ℝ, c₁, d] ∧ p ∈ line[ℝ, a, b] ∧ p ∈ line[ℝ, c₁, d]) ∧
      (L4.filter (fun L =>
        ∃ p ∈ T \ B, ∃ q ∈ T \ B, p ≠ q ∧ p ∈ L ∧ q ∈ L ∧ ∃ a ∈ W p, a ∈ W q)).card ≤
      (T \ B).card * (16 * B.card) := by
  classical
  have available (p : ℝ²) :
      ∃ S : Finset ℝ², p ∈ T \ B →
        ∃ a ∈ B, ∃ b ∈ B, ∃ c₁ ∈ B, ∃ d ∈ B,
          S = {a, b, c₁, d} ∧ a ≠ b ∧ c₁ ≠ d ∧
          line[ℝ, a, b] ≠ line[ℝ, c₁, d] ∧ p ∈ line[ℝ, a, b] ∧ p ∈ line[ℝ, c₁, d] := by
    by_cases hp : p ∈ T \ B
    · rcases (gen p (Finset.mem_sdiff.mp hp).1).resolve_left (Finset.mem_sdiff.mp hp).2 with
        ⟨a, ha, b, hb, c₁, hc, d, hd, ab, cd, ne, pl, pr⟩
      exact ⟨{a, b, c₁, d}, fun _ => ⟨a, ha, b, hb, c₁, hc, d, hd, rfl, ab, cd, ne, pl, pr⟩⟩
    · exact ⟨∅, fun h => (hp h).elim⟩
  choose W valid using available
  refine ⟨W, valid, shared_lines_card T B W L4 hL4 cap
    (fun p hp => (distinct_endpoints (Finset.mem_sdiff.mp hp).2 (valid p hp)).le) ?_⟩
  intro p hp x hx
  rcases valid p hp with ⟨a, ha, b, hb, c₁, hc, d, hd, eq, _, _, _, pl, pr⟩
  rw [eq] at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨b, hb, pl⟩
  · exact ⟨a, ha, by simpa only [Set.pair_comm x a] using pl⟩
  · exact ⟨d, hd, pr⟩
  · exact ⟨c₁, hc, by simpa only [Set.pair_comm x c₁] using pr⟩

private lemma eq_of_mem_line_of_ne {a b x y : ℝ²}
    (hx : x ∈ affineSpan ℝ ({a, b} : Set ℝ²))
    (hy : y ∈ affineSpan ℝ ({a, b} : Set ℝ²))
    (hxy : x ≠ y) :
    affineSpan ℝ ({x, y} : Set ℝ²) = affineSpan ℝ ({a, b} : Set ℝ²) := by
  apply le_antisymm
  · refine affineSpan_le.mpr ?_
    intro p hp
    rcases hp with rfl | rfl
    · exact hx
    · exact hy
  · obtain ⟨u, hu⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hx
    obtain ⟨v, hv⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hy
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add] at hu hv
    have huv : v - u ≠ 0 := by
      intro h0
      have heq : u = v := by linarith
      apply hxy
      rw [← hu, ← hv, heq]
    have hyx : y - x = (v - u) • (b - a) := by
      rw [← hv, ← hu, sub_smul]
      abel
    have hba : (v - u)⁻¹ • (y - x) = b - a := by
      rw [hyx, smul_smul, inv_mul_cancel₀ huv, one_smul]
    refine affineSpan_le.mpr ?_
    intro p hp
    rcases hp with rfl | rfl
    · refine mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨-u * (v - u)⁻¹, ?_⟩
      rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, mul_smul, hba, ← hu, neg_smul]
      abel
    · refine mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨(1 - u) * (v - u)⁻¹, ?_⟩
      rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, mul_smul, hba, ← hu, sub_smul, one_smul]
      abel

private lemma collinear_mem_affineSpan_of_ne {x y z : ℝ²}
    (hcol : Collinear ℝ ({x, y, z} : Set ℝ²)) (hxy : x ≠ y) :
    z ∈ affineSpan ℝ ({x, y} : Set ℝ²) := by
  obtain ⟨p₀, v, hv⟩ := (collinear_iff_exists_forall_eq_smul_vadd _).mp hcol
  obtain ⟨rx, hrx⟩ := hv x (by simp)
  obtain ⟨ry, hry⟩ := hv y (by simp)
  obtain ⟨rz, hrz⟩ := hv z (by simp)
  rw [vadd_eq_add] at hrx hry hrz
  have hryx : ry - rx ≠ 0 := by
    intro h0
    have heq : rx = ry := by linarith
    apply hxy
    rw [hrx, hry, heq]
  have hyx : y - x = (ry - rx) • v := by
    rw [hrx, hry, sub_smul]
    abel
  have hv_eq : (ry - rx)⁻¹ • (y - x) = v := by
    rw [hyx, smul_smul, inv_mul_cancel₀ hryx, one_smul]
  refine mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨(rz - rx) * (ry - rx)⁻¹, ?_⟩
  rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, mul_smul, hv_eq, hrx, hrz, sub_smul]
  abel

private theorem noncollinear_triangles_of_four_point_lines
    (T : Finset ℝ²) (F : Finset (AffineSubspace ℝ ℝ²)) (ε : ℝ)
    (hF : ∀ L ∈ F, L ∈ linesWithPointsFor 4 (T : Set ℝ²))
    (hbig : ε * (T.card : ℝ) ^ 2 ≤ (F.card : ℝ)) :
    SimpleGraph.triangleRemovalBound ε * (T.card : ℝ) ^ 3 - 4 * (F.card : ℝ) ≤
      (((T.powersetCard 3).filter (fun s : Finset ℝ² =>
        ¬ Collinear ℝ (s : Set ℝ²) ∧
        ∀ x ∈ s, ∀ y ∈ s, x ≠ y → affineSpan ℝ ({x, y} : Set ℝ²) ∈ F)).card : ℝ) := by
  classical
  have hL_span : ∀ L ∈ F, ∃ a b : ℝ², affineSpan ℝ ({a, b} : Set ℝ²) = L := by
    intro L hL
    have hL' := hF L hL
    dsimp only [linesWithPointsFor] at hL'
    rcases hL'.1 with ⟨a, _, b, _, _, hEq⟩
    exact ⟨a, b, hEq⟩
  have hL_eq : ∀ L ∈ F, ∀ x y : ℝ², x ∈ L → y ∈ L → x ≠ y →
      affineSpan ℝ ({x, y} : Set ℝ²) = L := by
    intro L hL x y hx hy hxy
    obtain ⟨a, b, rfl⟩ := hL_span L hL
    exact eq_of_mem_line_of_ne hx hy hxy
  have hcard_sub : ∀ L ∈ F, (Finset.univ.filter (fun u : ↥T => (u : ℝ²) ∈ L)).card = 4 := by
    intro L hL
    have hL' := hF L hL
    dsimp only [linesWithPointsFor] at hL'
    have hncard : ((L : Set ℝ²) ∩ (T : Set ℝ²)).ncard = 4 := hL'.2
    have hfilt : ((T.filter (fun p => p ∈ L) : Finset ℝ²) : Set ℝ²) = (L : Set ℝ²) ∩ (T : Set ℝ²) := by
      ext p
      simp [and_comm]
    have hcardT : (T.filter (fun p => p ∈ L)).card = 4 := by
      rw [← Set.ncard_coe_finset, hfilt, hncard]
    have himg : (Finset.univ.filter (fun u : ↥T => (u : ℝ²) ∈ L)).image Subtype.val =
        T.filter (fun p => p ∈ L) := by
      ext p
      simp
      tauto
    rw [← Finset.card_image_of_injective _ Subtype.val_injective, himg, hcardT]
  let G : SimpleGraph ↥T :=
    { Adj := fun u v => u ≠ v ∧ ∃ L ∈ F, (u : ℝ²) ∈ L ∧ (v : ℝ²) ∈ L
      symm := ⟨fun _ _ ⟨hne, L, hL, hu, hv⟩ => ⟨hne.symm, L, hL, hv, hu⟩⟩
      loopless := ⟨fun _ h => h.1 rfl⟩ }
  have hex_tri : ∀ L : AffineSubspace ℝ ℝ², L ∈ F →
      ∃ t : Finset ↥T, t ⊆ Finset.univ.filter (fun u : ↥T => (u : ℝ²) ∈ L) ∧ t.card = 3 := by
    intro L hL
    exact Finset.exists_subset_card_eq (by rw [hcard_sub L hL]; decide)
  let tri : AffineSubspace ℝ ℝ² → Finset ↥T :=
    fun L => if hL : L ∈ F then (hex_tri L hL).choose else ∅
  have htri_sub : ∀ L ∈ F, tri L ⊆ Finset.univ.filter (fun u : ↥T => (u : ℝ²) ∈ L) := by
    intro L hL
    dsimp only [tri]
    rw [dif_pos hL]
    exact (hex_tri L hL).choose_spec.1
  have htri_card : ∀ L ∈ F, (tri L).card = 3 := by
    intro L hL
    dsimp only [tri]
    rw [dif_pos hL]
    exact (hex_tri L hL).choose_spec.2
  have htri_inj : Set.InjOn tri (F : Set (AffineSubspace ℝ ℝ²)) := by
    intro L₁ hL₁ L₂ hL₂ hEq
    have hcard1 : 1 < (tri L₁).card := by rw [htri_card L₁ hL₁]; decide
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hcard1
    have hu1 : (u : ℝ²) ∈ L₁ := (Finset.mem_filter.mp (htri_sub L₁ hL₁ hu)).2
    have hv1 : (v : ℝ²) ∈ L₁ := (Finset.mem_filter.mp (htri_sub L₁ hL₁ hv)).2
    have hu2 : (u : ℝ²) ∈ L₂ := (Finset.mem_filter.mp (htri_sub L₂ hL₂ (hEq ▸ hu))).2
    have hv2 : (v : ℝ²) ∈ L₂ := (Finset.mem_filter.mp (htri_sub L₂ hL₂ (hEq ▸ hv))).2
    have hne : (u : ℝ²) ≠ (v : ℝ²) := Subtype.coe_ne_coe.mpr huv
    exact (hL_eq L₁ hL₁ _ _ hu1 hv1 hne).symm.trans (hL_eq L₂ hL₂ _ _ hu2 hv2 hne)
  let tris : Finset (Finset ↥T) := F.image tri
  have htris_sub : tris ⊆ G.cliqueFinset 3 := by
    intro t ht
    obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp ht
    rw [SimpleGraph.mem_cliqueFinset_iff]
    refine ⟨?_, htri_card L hL⟩
    intro u hu v hv huv
    exact ⟨huv, L, hL,
      (Finset.mem_filter.mp (htri_sub L hL hu)).2,
      (Finset.mem_filter.mp (htri_sub L hL hv)).2⟩
  have htris_pd : (tris : Set (Finset ↥T)).Pairwise
      (fun x y => ((x : Set ↥T) ∩ (y : Set ↥T)).Subsingleton) := by
    intro x hx y hy hxy
    obtain ⟨L₁, hL₁, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
    obtain ⟨L₂, hL₂, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
    have hLne : L₁ ≠ L₂ := fun h => hxy (congrArg tri h)
    intro u hu v hv
    by_contra huv
    have hne : (u : ℝ²) ≠ (v : ℝ²) := Subtype.coe_ne_coe.mpr huv
    have hu1 : (u : ℝ²) ∈ L₁ := (Finset.mem_filter.mp (htri_sub L₁ hL₁ hu.1)).2
    have hv1 : (v : ℝ²) ∈ L₁ := (Finset.mem_filter.mp (htri_sub L₁ hL₁ hv.1)).2
    have hu2 : (u : ℝ²) ∈ L₂ := (Finset.mem_filter.mp (htri_sub L₂ hL₂ hu.2)).2
    have hv2 : (v : ℝ²) ∈ L₂ := (Finset.mem_filter.mp (htri_sub L₂ hL₂ hv.2)).2
    exact hLne ((hL_eq L₁ hL₁ _ _ hu1 hv1 hne).symm.trans (hL_eq L₂ hL₂ _ _ hu2 hv2 hne))
  have htris_card : tris.card = F.card := Finset.card_image_of_injOn htri_inj
  have htris_big : ε * ((Fintype.card ↥T ^ 2 : ℕ) : ℝ) ≤ (tris.card : ℝ) := by
    rw [htris_card, Fintype.card_coe, Nat.cast_pow]
    exact hbig
  have hfar : G.FarFromTriangleFree ε :=
    SimpleGraph.farFromTriangleFree_of_disjoint_triangles tris htris_sub htris_pd htris_big
  have hcliques : SimpleGraph.triangleRemovalBound ε * (Fintype.card ↥T : ℝ) ^ 3 ≤
      ((G.cliqueFinset 3).card : ℝ) := hfar.le_card_cliqueFinset
  rw [Fintype.card_coe] at hcliques
  let colCliques : Finset (Finset ↥T) :=
    (G.cliqueFinset 3).filter (fun t => Collinear ℝ (Subtype.val '' (t : Set ↥T)))
  let propCliques : Finset (Finset ↥T) :=
    (G.cliqueFinset 3).filter (fun t => ¬ Collinear ℝ (Subtype.val '' (t : Set ↥T)))
  have hsplit : (G.cliqueFinset 3).card = colCliques.card + propCliques.card := by
    have hunion : G.cliqueFinset 3 = colCliques ∪ propCliques := by
      ext t
      simp only [Finset.mem_union, Finset.mem_filter, colCliques, propCliques]
      tauto
    have hdisj : Disjoint colCliques propCliques :=
      Finset.disjoint_filter.mpr (fun _ _ h1 h2 => h2 h1)
    rw [hunion, Finset.card_union_of_disjoint hdisj]
  have hcol_sub : colCliques ⊆
      F.biUnion (fun L => (Finset.univ.filter (fun u : ↥T => (u : ℝ²) ∈ L)).powersetCard 3) := by
    intro t ht
    have ht_clq : G.IsNClique 3 t := SimpleGraph.mem_cliqueFinset_iff.mp (Finset.mem_filter.mp ht).1
    have ht_col : Collinear ℝ (Subtype.val '' (t : Set ↥T)) := (Finset.mem_filter.mp ht).2
    have hcard1 : 1 < t.card := by rw [ht_clq.2]; decide
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hcard1
    have hadj : G.Adj u v := ht_clq.1 hu hv huv
    obtain ⟨_, L, hL, huL, hvL⟩ := hadj
    have hne : (u : ℝ²) ≠ (v : ℝ²) := Subtype.coe_ne_coe.mpr huv
    have hL_uv : affineSpan ℝ ({(u : ℝ²), (v : ℝ²)} : Set ℝ²) = L := hL_eq L hL _ _ huL hvL hne
    refine Finset.mem_biUnion.mpr ⟨L, hL, Finset.mem_powersetCard.mpr ⟨?_, ht_clq.2⟩⟩
    intro w hw
    have hcol3 : Collinear ℝ ({(u : ℝ²), (v : ℝ²), (w : ℝ²)} : Set ℝ²) := by
      obtain ⟨p₀, dir, hdir⟩ := (collinear_iff_exists_forall_eq_smul_vadd _).mp ht_col
      refine (collinear_iff_exists_forall_eq_smul_vadd _).mpr ⟨p₀, dir, ?_⟩
      intro p hp
      rcases hp with rfl | rfl | rfl
      · exact hdir _ ⟨u, hu, rfl⟩
      · exact hdir _ ⟨v, hv, rfl⟩
      · exact hdir _ ⟨w, hw, rfl⟩
    have hwL : (w : ℝ²) ∈ L := by
      rw [← hL_uv]
      exact collinear_mem_affineSpan_of_ne hcol3 hne
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, hwL⟩
  have hcol_le : colCliques.card ≤ 4 * F.card := by
    calc colCliques.card
        ≤ (F.biUnion (fun L => (Finset.univ.filter (fun u : ↥T => (u : ℝ²) ∈ L)).powersetCard 3)).card :=
          Finset.card_le_card hcol_sub
      _ ≤ ∑ L ∈ F, ((Finset.univ.filter (fun u : ↥T => (u : ℝ²) ∈ L)).powersetCard 3).card :=
          Finset.card_biUnion_le
      _ = ∑ _L ∈ F, 4 := by
          refine Finset.sum_congr rfl fun L hL => ?_
          rw [Finset.card_powersetCard, hcard_sub L hL]
          norm_num
      _ = 4 * F.card := by simp [mul_comm]
  let out : Finset (Finset ℝ²) :=
    (T.powersetCard 3).filter (fun s : Finset ℝ² =>
      ¬ Collinear ℝ (s : Set ℝ²) ∧
      ∀ x ∈ s, ∀ y ∈ s, x ≠ y → affineSpan ℝ ({x, y} : Set ℝ²) ∈ F)
  let lift : Finset ↥T → Finset ℝ² := fun t => t.image Subtype.val
  have hlift_inj : Function.Injective lift := by
    intro t₁ t₂ hEq
    ext u
    have hmem : (u : ℝ²) ∈ lift t₁ ↔ (u : ℝ²) ∈ lift t₂ := by rw [hEq]
    simpa [lift] using hmem
  have hprop_sub : propCliques.image lift ⊆ out := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    have ht_clq : G.IsNClique 3 t := SimpleGraph.mem_cliqueFinset_iff.mp (Finset.mem_filter.mp ht).1
    have ht_ncol : ¬ Collinear ℝ (Subtype.val '' (t : Set ↥T)) := (Finset.mem_filter.mp ht).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_, ?_⟩
    · intro p hp
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hp
      exact u.2
    · rw [Finset.card_image_of_injective _ Subtype.val_injective, ht_clq.2]
    · simpa [lift, Finset.coe_image] using ht_ncol
    · intro x hx y hy hxy
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
      have huv : u ≠ v := fun h => hxy (congrArg Subtype.val h)
      obtain ⟨_, L, hL, huL, hvL⟩ := ht_clq.1 hu hv huv
      rw [hL_eq L hL _ _ huL hvL hxy]
      exact hL
  have hprop_le : propCliques.card ≤ out.card := by
    rw [← Finset.card_image_of_injective propCliques hlift_inj]
    exact Finset.card_le_card hprop_sub
  have hsplitR : ((G.cliqueFinset 3).card : ℝ) = (colCliques.card : ℝ) + (propCliques.card : ℝ) := by
    exact_mod_cast hsplit
  have hcolR : (colCliques.card : ℝ) ≤ 4 * (F.card : ℝ) := by exact_mod_cast hcol_le
  have hpropR : (propCliques.card : ℝ) ≤ (out.card : ℝ) := by exact_mod_cast hprop_le
  change SimpleGraph.triangleRemovalBound ε * (T.card : ℝ) ^ 3 - 4 * (F.card : ℝ) ≤ (out.card : ℝ)
  linarith


def H1 : Prop :=
  ∀ s K : ℕ, 0 < s →
    ∃ N : ℕ, ∀ T : Finset ℝ², N ≤ T.card →
      NonCollinearFor 5 (T : Set ℝ²) →
      (linesWithPointsFor 2 (T : Set ℝ²)).ncard ≤ K * T.card →
      s * (linesWithPointsFor 4 (T : Set ℝ²)).ncard < T.card ^ 2

def H2 : Prop :=
  ∀ c C : ℕ, 0 < c →
    ∃ K N : ℕ, ∀ T B : Finset ℝ², N ≤ T.card →
      NonCollinearFor 5 (T : Set ℝ²) →
      B ⊆ T → B.card ^ 2 ≤ C * T.card →
      K * T.card < (linesWithPointsFor 2 (T : Set ℝ²)).ncard →
      ∀ W : ℝ² → Finset ℝ²,
        (∀ p ∈ T \ B, ∃ a ∈ B, ∃ b ∈ B, ∃ c₁ ∈ B, ∃ d ∈ B,
          W p = {a, b, c₁, d} ∧ a ≠ b ∧ c₁ ≠ d ∧
          line[ℝ, a, b] ≠ line[ℝ, c₁, d] ∧ p ∈ line[ℝ, a, b] ∧ p ∈ line[ℝ, c₁, d]) →
        c * ((T.powersetCard 3).filter (fun s : Finset ℝ² =>
          ¬ Collinear ℝ (s : Set ℝ²) ∧
          ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
            line[ℝ, x, y] ∈ linesWithPointsFor 4 (T : Set ℝ²) ∧
            (∀ a ∈ B, a ∉ line[ℝ, x, y]) ∧
            (∀ p ∈ T \ B, ∀ q ∈ T \ B, p ≠ q →
              p ∈ line[ℝ, x, y] → q ∈ line[ℝ, x, y] → Disjoint (W p) (W q)))).card <
          T.card ^ 3

theorem main : H1 → H2 → OMA.R_Erdos101_erdos_101_R3.H2 := by
  intro hH1 hH2 s C hs
  classical
  let ε : ℝ := 1 / (2 * (s : ℝ))
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hε : 0 < ε := by
    dsimp only [ε]
    positivity
  have hδ : 0 < SimpleGraph.triangleRemovalBound ε :=
    SimpleGraph.triangleRemovalBound_pos hε
  obtain ⟨c0, hc0⟩ := exists_nat_gt (2 / SimpleGraph.triangleRemovalBound ε)
  let c : ℕ := c0 + 1
  have hc : 0 < c := Nat.succ_pos c0
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hc_mul_δ : (2 : ℝ) < (c : ℝ) * SimpleGraph.triangleRemovalBound ε := by
    have hlt : 2 / SimpleGraph.triangleRemovalBound ε < (c : ℝ) := by
      dsimp only [c]
      push_cast
      linarith
    have := (div_lt_iff₀ hδ).mp hlt
    linarith
  obtain ⟨K, N₂, hN₂⟩ := hH2 c C hc
  obtain ⟨N₁, hN₁⟩ := hH1 s K hs
  refine ⟨max (max N₁ N₂) (max (4 * c + 1) ((34 * s) ^ 2 * C + 1)), ?_⟩
  intro T B hN hcap hBsub hBsq hgen
  have hN₁' : N₁ ≤ T.card := le_trans (le_trans (le_max_left N₁ N₂) (le_max_left _ _)) hN
  have hN₂' : N₂ ≤ T.card := le_trans (le_trans (le_max_right N₁ N₂) (le_max_left _ _)) hN
  have hN4c : 4 * c + 1 ≤ T.card := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN34 : (34 * s) ^ 2 * C + 1 ≤ T.card :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hTpos : 0 < T.card := by omega
  by_cases hord : (linesWithPointsFor 2 (T : Set ℝ²)).ncard ≤ K * T.card
  · exact hN₁ T hN₁' hcap hord
  · have hord_gt : K * T.card < (linesWithPointsFor 2 (T : Set ℝ²)).ncard := by omega
    let allPairs := (T ×ˢ T).image (fun e => line[ℝ, e.1, e.2])
    let L4 := allPairs.filter (fun L => L ∈ linesWithPointsFor 4 (T : Set ℝ²))
    have hL4_mem : ∀ L, L ∈ L4 ↔ L ∈ linesWithPointsFor 4 (T : Set ℝ²) := by
      intro L
      constructor
      · intro h
        exact (Finset.mem_filter.mp h).2
      · intro h
        refine Finset.mem_filter.mpr ⟨?_, h⟩
        have h' := h
        dsimp only [linesWithPointsFor] at h'
        rcases h'.1 with ⟨p, hp, q, hq, _, rfl⟩
        exact Finset.mem_image.mpr ⟨(p, q), Finset.mem_product.mpr ⟨hp, hq⟩, rfl⟩
    have hL4_coe : (L4 : Set (AffineSubspace ℝ ℝ²)) = linesWithPointsFor 4 (T : Set ℝ²) := by
      ext L
      exact hL4_mem L
    have hL4_ncard : (linesWithPointsFor 4 (T : Set ℝ²)).ncard = L4.card := by
      rw [← hL4_coe, Set.ncard_coe_finset]
    have hL4_le_sq : L4.card ≤ T.card ^ 2 := by
      calc L4.card
          ≤ allPairs.card := Finset.card_filter_le ..
        _ ≤ (T ×ˢ T).card := Finset.card_image_le
        _ = T.card * T.card := Finset.card_product ..
        _ = T.card ^ 2 := by ring
    obtain ⟨W, hW_valid, hW_sh⟩ :=
      exists_witnesses_with_bound T B L4 (fun L hL => (hL4_mem L).mp hL) hcap hgen
    let F_clean := L4.filter (fun L =>
      (∀ a ∈ B, a ∉ L) ∧
      (∀ p ∈ T \ B, ∀ q ∈ T \ B, p ≠ q → p ∈ L → q ∈ L → Disjoint (W p) (W q)))
    let F_anc := L4.filter (fun L => ∃ a ∈ B, a ∈ L)
    let F_sh := L4.filter (fun L =>
      ∃ p ∈ T \ B, ∃ q ∈ T \ B, p ≠ q ∧ p ∈ L ∧ q ∈ L ∧ ∃ a ∈ W p, a ∈ W q)
    have hcover : L4 ⊆ F_clean ∪ (F_anc ∪ F_sh) := by
      intro L hL
      by_cases hA : ∃ a ∈ B, a ∈ L
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hL, hA⟩))
      · by_cases hS : ∃ p ∈ T \ B, ∃ q ∈ T \ B, p ≠ q ∧ p ∈ L ∧ q ∈ L ∧ ∃ a ∈ W p, a ∈ W q
        · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hL, hS⟩))
        · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hL, ?_, ?_⟩)
          · intro a ha haL
            exact hA ⟨a, ha, haL⟩
          · intro p hp q hq hpq hpL hqL
            refine Finset.disjoint_left.mpr ?_
            intro a hap haq
            exact hS ⟨p, hp, q, hq, hpq, hpL, hqL, a, hap, haq⟩
    have hL4_split : L4.card ≤ F_clean.card + F_anc.card + F_sh.card := by
      calc L4.card
          ≤ (F_clean ∪ (F_anc ∪ F_sh)).card := Finset.card_le_card hcover
        _ ≤ F_clean.card + (F_anc ∪ F_sh).card := Finset.card_union_le ..
        _ ≤ F_clean.card + (F_anc.card + F_sh.card) :=
            Nat.add_le_add_left (Finset.card_union_le ..) _
        _ = F_clean.card + F_anc.card + F_sh.card := by omega
    have hF_anc : F_anc.card ≤ B.card * T.card :=
      lines_meeting_anchors_card T B L4 (fun L hL => (hL4_mem L).mp hL)
    have hTdiff : (T \ B).card ≤ T.card := Finset.card_le_card Finset.sdiff_subset
    have hbad : F_anc.card + F_sh.card ≤ 17 * B.card * T.card := by
      have hsh' : F_sh.card ≤ T.card * (16 * B.card) :=
        le_trans hW_sh (Nat.mul_le_mul_right _ hTdiff)
      nlinarith
    have h34B : 34 * s * B.card < T.card := by
      have hsq_lt : (34 * s * B.card) ^ 2 < T.card ^ 2 := by
        calc (34 * s * B.card) ^ 2
            = (34 * s) ^ 2 * B.card ^ 2 := by ring
          _ ≤ (34 * s) ^ 2 * (C * T.card) := Nat.mul_le_mul_left _ hBsq
          _ = ((34 * s) ^ 2 * C) * T.card := by ring
          _ < T.card * T.card := Nat.mul_lt_mul_of_pos_right (by omega) hTpos
          _ = T.card ^ 2 := by ring
      by_contra hle
      have hge : T.card ≤ 34 * s * B.card := by omega
      have : T.card ^ 2 ≤ (34 * s * B.card) ^ 2 := Nat.pow_le_pow_left hge 2
      omega
    by_contra hnot
    rw [hL4_ncard] at hnot
    have hL4_big : T.card ^ 2 ≤ s * L4.card := by omega
    have h2bad : 2 * s * (F_anc.card + F_sh.card) < T.card ^ 2 := by
      calc 2 * s * (F_anc.card + F_sh.card)
          ≤ 2 * s * (17 * B.card * T.card) := Nat.mul_le_mul_left _ hbad
        _ = (34 * s * B.card) * T.card := by ring
        _ < T.card * T.card := Nat.mul_lt_mul_of_pos_right h34B hTpos
        _ = T.card ^ 2 := by ring
    have hclean_big_nat : T.card ^ 2 ≤ 2 * s * F_clean.card := by
      have h2L4 : 2 * T.card ^ 2 ≤ 2 * s * F_clean.card + 2 * s * (F_anc.card + F_sh.card) := by
        calc 2 * T.card ^ 2
            ≤ 2 * (s * L4.card) := Nat.mul_le_mul_left 2 hL4_big
          _ = 2 * s * L4.card := by ring
          _ ≤ 2 * s * (F_clean.card + (F_anc.card + F_sh.card)) :=
              Nat.mul_le_mul_left _ (by omega)
          _ = 2 * s * F_clean.card + 2 * s * (F_anc.card + F_sh.card) := by ring
      omega
    have hclean_big : ε * (T.card : ℝ) ^ 2 ≤ (F_clean.card : ℝ) := by
      have hcleanR : (T.card : ℝ) ^ 2 ≤ 2 * (s : ℝ) * (F_clean.card : ℝ) := by
        exact_mod_cast hclean_big_nat
      have h2s : (0 : ℝ) < 2 * (s : ℝ) := by positivity
      have h2s_ne : (2 * (s : ℝ)) ≠ 0 := ne_of_gt h2s
      have hε_eq : (2 * (s : ℝ)) * ε = 1 := by
        dsimp only [ε]
        exact mul_one_div_cancel h2s_ne
      have hmul : (2 * (s : ℝ)) * (ε * (T.card : ℝ) ^ 2) ≤ (2 * (s : ℝ)) * (F_clean.card : ℝ) := by
        calc (2 * (s : ℝ)) * (ε * (T.card : ℝ) ^ 2)
            = ((2 * (s : ℝ)) * ε) * (T.card : ℝ) ^ 2 := by ring
          _ = (T.card : ℝ) ^ 2 := by rw [hε_eq, one_mul]
          _ ≤ 2 * (s : ℝ) * (F_clean.card : ℝ) := hcleanR
      exact le_of_mul_le_mul_left hmul h2s
    have hF_clean_L4 : ∀ L ∈ F_clean, L ∈ linesWithPointsFor 4 (T : Set ℝ²) :=
      fun L hL => (hL4_mem L).mp (Finset.mem_filter.mp hL).1
    have htri := noncollinear_triangles_of_four_point_lines T F_clean ε hF_clean_L4 hclean_big
    have hF_clean_le_sq : F_clean.card ≤ T.card ^ 2 :=
      le_trans (Finset.card_filter_le ..) hL4_le_sq
    have htri_eq :
        (T.powersetCard 3).filter (fun s : Finset ℝ² =>
          ¬ Collinear ℝ (s : Set ℝ²) ∧
          ∀ x ∈ s, ∀ y ∈ s, x ≠ y → affineSpan ℝ ({x, y} : Set ℝ²) ∈ F_clean) =
        (T.powersetCard 3).filter (fun s : Finset ℝ² =>
          ¬ Collinear ℝ (s : Set ℝ²) ∧
          ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
            line[ℝ, x, y] ∈ linesWithPointsFor 4 (T : Set ℝ²) ∧
            (∀ a ∈ B, a ∉ line[ℝ, x, y]) ∧
            (∀ p ∈ T \ B, ∀ q ∈ T \ B, p ≠ q →
              p ∈ line[ℝ, x, y] → q ∈ line[ℝ, x, y] → Disjoint (W p) (W q))) := by
      refine Finset.filter_congr fun s _ => ?_
      simp only [F_clean, Finset.mem_filter, hL4_mem]
    rw [htri_eq] at htri
    have hH2_lt := hN₂ T B hN₂' hcap hBsub hBsq hord_gt W hW_valid
    have hH2_ltR :
        (c : ℝ) * (((T.powersetCard 3).filter (fun s : Finset ℝ² =>
          ¬ Collinear ℝ (s : Set ℝ²) ∧
          ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
            line[ℝ, x, y] ∈ linesWithPointsFor 4 (T : Set ℝ²) ∧
            (∀ a ∈ B, a ∉ line[ℝ, x, y]) ∧
            (∀ p ∈ T \ B, ∀ q ∈ T \ B, p ≠ q →
              p ∈ line[ℝ, x, y] → q ∈ line[ℝ, x, y] → Disjoint (W p) (W q)))).card : ℝ) <
        (T.card : ℝ) ^ 3 := by
      exact_mod_cast hH2_lt
    have hF_sqR : (F_clean.card : ℝ) ≤ (T.card : ℝ) ^ 2 := by exact_mod_cast hF_clean_le_sq
    have h4cR : 4 * (c : ℝ) < (T.card : ℝ) := by
      have : 4 * c < T.card := by omega
      exact_mod_cast this
    have hTposR : (0 : ℝ) < (T.card : ℝ) := by exact_mod_cast hTpos
    have hTsq_nn : (0 : ℝ) ≤ (T.card : ℝ) ^ 2 := by positivity
    have hTcube_pos : (0 : ℝ) < (T.card : ℝ) ^ 3 := by positivity
    have hmul_tri :
        (c : ℝ) * SimpleGraph.triangleRemovalBound ε * (T.card : ℝ) ^ 3 -
          4 * (c : ℝ) * (F_clean.card : ℝ) ≤
        (c : ℝ) * (((T.powersetCard 3).filter (fun s : Finset ℝ² =>
          ¬ Collinear ℝ (s : Set ℝ²) ∧
          ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
            line[ℝ, x, y] ∈ linesWithPointsFor 4 (T : Set ℝ²) ∧
            (∀ a ∈ B, a ∉ line[ℝ, x, y]) ∧
            (∀ p ∈ T \ B, ∀ q ∈ T \ B, p ≠ q →
              p ∈ line[ℝ, x, y] → q ∈ line[ℝ, x, y] → Disjoint (W p) (W q)))).card : ℝ) := by
      have := mul_le_mul_of_nonneg_left htri (le_of_lt hcR)
      linarith
    have h2Tcube : 2 * (T.card : ℝ) ^ 3 <
        (c : ℝ) * SimpleGraph.triangleRemovalBound ε * (T.card : ℝ) ^ 3 :=
      mul_lt_mul_of_pos_right hc_mul_δ hTcube_pos
    have h4cF : 4 * (c : ℝ) * (F_clean.card : ℝ) ≤ (T.card : ℝ) ^ 3 := by
      calc 4 * (c : ℝ) * (F_clean.card : ℝ)
          ≤ 4 * (c : ℝ) * (T.card : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hF_sqR (by positivity)
        _ ≤ (T.card : ℝ) * (T.card : ℝ) ^ 2 := mul_le_mul_of_nonneg_right (le_of_lt h4cR) hTsq_nn
        _ = (T.card : ℝ) ^ 3 := by ring
    linarith

end OMA.R_Erdos101_erdos_101_R3_H2_R3
