import OMAReductions.R_Erdos101_erdos_101_R3

/-!
# Anchor-disjoint high-degree cores and 4-partite rainbow sparsity for `Erdos101.erdos_101.R3.H2`

Given an anchor-generated four-point configuration `(T, B)` with `B ⊆ T` and `|B|^2 ≤ C |T|`,
we unconditionally prove inside `main`:

1. **Anchor-meeting line elimination**: each point of `B` lies on at most `(|T| - 1) / 3`
   four-point lines of `T`, so at most `|B| |T| / 3 = O(sqrt(C) |T|^{3/2})` four-point lines
   meet `B`; removing `B` leaves `U = T \ B` with `|T| ≤ 2 |U|` and `≥ (5 / (6 s)) |T|^2`
   four-point lines entirely inside `U`.
2. **Four-anchor distinctness and two-point anchor-line cap**: every point `p ∈ U` is the
   intersection of two distinct anchor lines through four pairwise distinct points of `B`,
   and no anchor line `line[ℝ, a, b]` (`a ≠ b ∈ B`) contains more than two points of `U`.
3. **Minimum-degree core pruning**: choosing a minimum-cardinality subset `V ⊆ U` above a
   linear-plus-quadratic line threshold yields a dense anchor-generated core `V ⊆ U`
   (`|U| ≤ s |V|`, `|B|^2 ≤ 2 C s |V|`) in which every point `p ∈ V` lies on at least
   `|V| / (4 s)` four-point lines of `V`.

We then reduce `OMA.R_Erdos101_erdos_101_R3.H2` to two independent statements:
- `H1`: 4-partite rainbow extraction with linearly dense pencils from any high-degree
  four-point line core (unconditionally provable by random 4-coloring and one-step pruning).
- `H2`: uniform sparsity for 4-partite rainbow families inside anchor-generated cores whose
  anchor lines each carry at most two points of `V`.
-/

namespace OMA.R_Erdos101_erdos_101_R3_H2_R1

open EuclideanGeometry
open scoped Classical

/-- From a high-degree four-point line core `V`, extract pairwise disjoint parts
`V0, V1, V2, V3 ⊆ V` and a positive-density family `A` of four-point lines of `V`
such that every line in `A` meets each part in one point and every point of `V0`
lies on linearly many lines of `A`. -/
def H1 : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ η : ℝ, 0 < η ∧ ∃ N : ℕ, ∀ V : Finset ℝ²,
    N ≤ V.card → NonCollinearFor 5 (V : Set ℝ²) →
    (∀ p ∈ V, ∃ A : Finset (AffineSubspace ℝ ℝ²), τ * (V.card : ℝ) ≤ A.card ∧
      ∀ L ∈ A, p ∈ L ∧ L ∈ linesWithPointsFor 4 (V : Set ℝ²)) →
    ∃ V0 V1 V2 V3 : Finset ℝ²,
      V0 ⊆ V ∧ V1 ⊆ V ∧ V2 ⊆ V ∧ V3 ⊆ V ∧
      Disjoint V0 V1 ∧ Disjoint V0 V2 ∧ Disjoint V0 V3 ∧
      Disjoint V1 V2 ∧ Disjoint V1 V3 ∧ Disjoint V2 V3 ∧
      ∃ A : Finset (AffineSubspace ℝ ℝ²), η * (V.card : ℝ) ^ 2 ≤ A.card ∧
        (∀ L ∈ A, L ∈ linesWithPointsFor 4 (V : Set ℝ²) ∧
          (V0.filter (fun p => p ∈ L)).card = 1 ∧
          (V1.filter (fun p => p ∈ L)).card = 1 ∧
          (V2.filter (fun p => p ∈ L)).card = 1 ∧
          (V3.filter (fun p => p ∈ L)).card = 1) ∧
        ∀ p ∈ V0, η * (V.card : ℝ) ≤ (A.filter (fun L => p ∈ L)).card

/-- Uniform sparsity for 4-partite rainbow families of four-point lines inside an
anchor-generated point set `V` disjoint from `B`, where every anchor line carries at most
two points of `V` and every point of `V` is the intersection of lines through four distinct anchors. -/
def H2 : Prop :=
  ∀ K : ℕ, ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ V B : Finset ℝ²,
    N ≤ V.card → Disjoint V B → NonCollinearFor 5 ((V ∪ B : Finset ℝ²) : Set ℝ²) →
    B.card ^ 2 ≤ K * V.card →
    (∀ a ∈ B, ∀ b ∈ B, a ≠ b → (V.filter (fun p => p ∈ line[ℝ, a, b])).card ≤ 2) →
    (∀ p ∈ V, ∃ a ∈ B, ∃ b ∈ B, ∃ c ∈ B, ∃ d ∈ B,
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      line[ℝ, a, b] ≠ line[ℝ, c, d] ∧ p ∈ line[ℝ, a, b] ∧ p ∈ line[ℝ, c, d]) →
    ∀ V0 V1 V2 V3 : Finset ℝ²,
      V0 ⊆ V ∧ V1 ⊆ V ∧ V2 ⊆ V ∧ V3 ⊆ V →
      Disjoint V0 V1 ∧ Disjoint V0 V2 ∧ Disjoint V0 V3 ∧
      Disjoint V1 V2 ∧ Disjoint V1 V3 ∧ Disjoint V2 V3 →
      ∀ A : Finset (AffineSubspace ℝ ℝ²),
        (∀ L ∈ A, L ∈ linesWithPointsFor 4 (V : Set ℝ²) ∧
          (V0.filter (fun p => p ∈ L)).card = 1 ∧
          (V1.filter (fun p => p ∈ L)).card = 1 ∧
          (V2.filter (fun p => p ∈ L)).card = 1 ∧
          (V3.filter (fun p => p ∈ L)).card = 1) →
        (∀ p ∈ V0, η * (V.card : ℝ) ≤ (A.filter (fun L => p ∈ L)).card) →
        (A.card : ℝ) < η * (V.card : ℝ) ^ 2

lemma four_lines_finite (S : Finset ℝ²) :
    (linesWithPointsFor 4 (S : Set ℝ²)).Finite := by
  apply (S.finite_toSet.image2 (fun p q => line[ℝ, p, q]) S.finite_toSet).subset
  rintro L ⟨⟨p, hp, q, hq, _, he⟩, _⟩
  exact ⟨p, hp, q, hq, he⟩

lemma four_points {S : Finset ℝ²} {L : AffineSubspace ℝ ℝ²}
    (hL : L ∈ linesWithPointsFor 4 (S : Set ℝ²)) :
    (S.filter (fun p => p ∈ L)).card = 4 := by
  have he : ((S.filter (fun p => p ∈ L) : Finset ℝ²) : Set ℝ²) = (L : Set ℝ²) ∩ S := by
    ext p
    simp [and_comm]
  rw [← Set.ncard_coe_finset, he]
  exact hL.2

lemma line_through {S : Finset ℝ²} {L : AffineSubspace ℝ ℝ²}
    (hL : L ∈ linesWithPointsFor 4 (S : Set ℝ²)) {p q : ℝ²}
    (hp : p ∈ L) (hq : q ∈ L) (hne : p ≠ q) : line[ℝ, p, q] = L := by
  obtain ⟨⟨a, _, b, _, _, rfl⟩, _⟩ := hL
  exact affineSpan_pair_eq_of_mem_of_mem_of_ne hp hq hne

lemma line_mem_four_of_subset {S U : Finset ℝ²} {L : AffineSubspace ℝ ℝ²}
    (hUS : U ⊆ S) (hL : L ∈ linesWithPointsFor 4 (S : Set ℝ²))
    (hsub : S.filter (fun p => p ∈ L) ⊆ U) :
    L ∈ linesWithPointsFor 4 (U : Set ℝ²) := by
  have hfilt_eq : U.filter (fun p => p ∈ L) = S.filter (fun p => p ∈ L) := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun ⟨hpU, hpL⟩ => ⟨hUS hpU, hpL⟩, fun h => ⟨hsub (Finset.mem_filter.mpr h), h.2⟩⟩
  have hcard4 : (U.filter (fun p => p ∈ L)).card = 4 := by
    rw [hfilt_eq]
    exact four_points hL
  have htwo : 1 < (U.filter (fun p => p ∈ L)).card := by omega
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp htwo
  have hpU := Finset.mem_filter.mp hp
  have hqU := Finset.mem_filter.mp hq
  refine ⟨⟨p, hpU.1, q, hqU.1, hpq, line_through hL hpU.2 hqU.2 hpq⟩, ?_⟩
  have he : (L : Set ℝ²) ∩ (U : Set ℝ²) = ((U.filter (fun x => x ∈ L) : Finset ℝ²) : Set ℝ²) := by
    ext x
    simp [and_comm]
  rw [he, Set.ncard_coe_finset]
  exact hcard4

lemma pencil_bound {S : Finset ℝ²} {A : Finset (AffineSubspace ℝ ℝ²)}
    (hA : ∀ L ∈ A, L ∈ linesWithPointsFor 4 (S : Set ℝ²))
    {p : ℝ²} (hp : p ∈ S) :
    3 * (A.filter (fun L => p ∈ L)).card ≤ S.card - 1 := by
  let pencil := A.filter (fun L => p ∈ L)
  let others := fun L : AffineSubspace ℝ ℝ² => (S.filter (fun q => q ∈ L)).erase p
  have hdisj : (pencil : Set (AffineSubspace ℝ ℝ²)).PairwiseDisjoint others := by
    intro L hL M hM hne
    obtain ⟨hLA, hpL⟩ := Finset.mem_filter.mp hL
    obtain ⟨hMA, hpM⟩ := Finset.mem_filter.mp hM
    apply Finset.disjoint_left.mpr
    intro q hqL hqM
    obtain ⟨hqp, hqL'⟩ := Finset.mem_erase.mp hqL
    have hqM' := (Finset.mem_erase.mp hqM).2
    exact hne ((line_through (hA L hLA) hpL (Finset.mem_filter.mp hqL').2 hqp.symm).symm.trans
      (line_through (hA M hMA) hpM (Finset.mem_filter.mp hqM').2 hqp.symm))
  have hcard : ∀ L ∈ pencil, (others L).card = 3 := by
    intro L hL
    obtain ⟨hLA, hpL⟩ := Finset.mem_filter.mp hL
    rw [Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hp, hpL⟩), four_points (hA L hLA)]
  have hsub : pencil.biUnion others ⊆ S.erase p := by
    intro q hq
    obtain ⟨L, _, hqL⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨hqp, hqS⟩ := Finset.mem_erase.mp hqL
    exact Finset.mem_erase.mpr ⟨hqp, (Finset.mem_filter.mp hqS).1⟩
  have hsum : 3 * pencil.card = (pencil.biUnion others).card := by
    rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl hcard, Finset.sum_const, smul_eq_mul,
      mul_comm]
  rw [hsum]
  exact (Finset.card_le_card hsub).trans_eq (Finset.card_erase_of_mem hp)

lemma total_four_lines_le {S : Finset ℝ²} {A : Finset (AffineSubspace ℝ ℝ²)}
    (hA : ∀ L ∈ A, L ∈ linesWithPointsFor 4 (S : Set ℝ²)) :
    12 * A.card ≤ S.card ^ 2 := by
  have hinc : 4 * A.card = ∑ p ∈ S, (A.filter (fun L => p ∈ L)).card := by
    have h1 : ∑ L ∈ A, (S.filter (fun p => p ∈ L)).card =
        ∑ p ∈ S, (A.filter (fun L => p ∈ L)).card :=
      Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun L p => p ∈ L)
    rw [← h1]
    calc 4 * A.card = ∑ _L ∈ A, 4 := by simp [mul_comm]
      _ = ∑ L ∈ A, (S.filter (fun p => p ∈ L)).card :=
          Finset.sum_congr rfl fun L hL => (four_points (hA L hL)).symm
  have h3 : 3 * ∑ p ∈ S, (A.filter (fun L => p ∈ L)).card ≤ S.card * S.card := by
    calc 3 * ∑ p ∈ S, (A.filter (fun L => p ∈ L)).card
        = ∑ p ∈ S, 3 * (A.filter (fun L => p ∈ L)).card := by rw [Finset.mul_sum]
      _ ≤ ∑ _p ∈ S, S.card := Finset.sum_le_sum fun p hp =>
          (pencil_bound hA hp).trans (Nat.sub_le _ _)
      _ = S.card * S.card := by simp
  nlinarith [sq S.card]

lemma anchor_meeting_lines_bound {T B : Finset ℝ²} (hBT : B ⊆ T) :
    let A := (four_lines_finite T).toFinset
    3 * (A.filter (fun L => ∃ b ∈ B, b ∈ L)).card ≤ B.card * T.card := by
  intro A
  have hA : ∀ L ∈ A, L ∈ linesWithPointsFor 4 (T : Set ℝ²) := fun L hL =>
    (Set.Finite.mem_toFinset _).mp hL
  have hcover : A.filter (fun L => ∃ b ∈ B, b ∈ L) ⊆ B.biUnion (fun b => A.filter (fun L => b ∈ L)) := by
    intro L hL
    obtain ⟨hLA, b, hbB, hbL⟩ := Finset.mem_filter.mp hL
    exact Finset.mem_biUnion.mpr ⟨b, hbB, Finset.mem_filter.mpr ⟨hLA, hbL⟩⟩
  have hle : (A.filter (fun L => ∃ b ∈ B, b ∈ L)).card ≤
      ∑ b ∈ B, (A.filter (fun L => b ∈ L)).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  calc 3 * (A.filter (fun L => ∃ b ∈ B, b ∈ L)).card
      ≤ 3 * ∑ b ∈ B, (A.filter (fun L => b ∈ L)).card := Nat.mul_le_mul_left 3 hle
    _ = ∑ b ∈ B, 3 * (A.filter (fun L => b ∈ L)).card := by rw [Finset.mul_sum]
    _ ≤ ∑ _b ∈ B, T.card := Finset.sum_le_sum fun b hb =>
        (pencil_bound hA (hBT hb)).trans (Nat.sub_le _ _)
    _ = B.card * T.card := by simp

lemma anchor_line_cap {V B : Finset ℝ²}
    (hdisj : Disjoint V B) (hnc : NonCollinearFor 5 ((V ∪ B : Finset ℝ²) : Set ℝ²))
    {a b : ℝ²} (ha : a ∈ B) (hb : b ∈ B) (hab : a ≠ b) :
    (V.filter (fun p => p ∈ line[ℝ, a, b])).card ≤ 2 := by
  by_contra hgt
  push Not at hgt
  let S5 : Finset ℝ² := insert a (insert b (V.filter (fun p => p ∈ line[ℝ, a, b])))
  have ha_not : a ∉ V.filter (fun p => p ∈ line[ℝ, a, b]) := fun h =>
    Finset.disjoint_left.mp hdisj (Finset.mem_filter.mp h).1 ha
  have hb_not : b ∉ V.filter (fun p => p ∈ line[ℝ, a, b]) := fun h =>
    Finset.disjoint_left.mp hdisj (Finset.mem_filter.mp h).1 hb
  have ha_not2 : a ∉ insert b (V.filter (fun p => p ∈ line[ℝ, a, b])) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hab, ha_not⟩
  have hcard : 5 ≤ S5.card := by
    rw [Finset.card_insert_of_notMem ha_not2, Finset.card_insert_of_notMem hb_not]
    omega
  obtain ⟨W, hWS5, hW5⟩ := Finset.exists_subset_card_eq hcard
  have hWsub : (W : Set ℝ²) ⊆ ((V ∪ B : Finset ℝ²) : Set ℝ²) := by
    intro x hx
    have hxS5 := hWS5 hx
    simp only [S5, Finset.mem_insert, Finset.mem_filter] at hxS5
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
    rcases hxS5 with rfl | rfl | ⟨hxV, _⟩
    · exact Or.inr ha
    · exact Or.inr hb
    · exact Or.inl hxV
  have hW_sub_L : (W : Set ℝ²) ⊆ (line[ℝ, a, b] : Set ℝ²) := by
    intro x hx
    have hxS5 := hWS5 hx
    simp only [S5, Finset.mem_insert, Finset.mem_filter] at hxS5
    rcases hxS5 with hxa | hxb | ⟨_, hxL⟩
    · rw [hxa]; exact left_mem_affineSpan_pair ℝ a b
    · rw [hxb]; exact right_mem_affineSpan_pair ℝ a b
    · exact hxL
  have hLcol : Collinear ℝ (line[ℝ, a, b] : Set ℝ²) := by
    rw [collinear_iff_of_mem (left_mem_affineSpan_pair ℝ a b)]
    refine ⟨b -ᵥ a, fun x hx => ?_⟩
    obtain ⟨r, hr⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hx
    refine ⟨r, ?_⟩
    rw [← hr, AffineMap.lineMap_apply]
  have hWcol : Collinear ℝ (W : Set ℝ²) := hLcol.subset hW_sub_L
  exact hnc (W : Set ℝ²) hWsub W.finite_toSet (by rw [Set.ncard_coe_finset]; exact hW5) hWcol

lemma four_anchors_distinct {V B : Finset ℝ²} (hdisj : Disjoint V B)
    {p a b c d : ℝ²} (hp : p ∈ V) (ha : a ∈ B) (hb : b ∈ B) (_hc : c ∈ B) (_hd : d ∈ B)
    (hab : a ≠ b) (hcd : c ≠ d) (hline : line[ℝ, a, b] ≠ line[ℝ, c, d])
    (hp1 : p ∈ line[ℝ, a, b]) (hp2 : p ∈ line[ℝ, c, d]) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  have hp_not_B : p ∉ B := Finset.disjoint_left.mp hdisj hp
  have hneq : ∀ x ∈ B, x ∈ line[ℝ, a, b] → x ∈ line[ℝ, c, d] → False := by
    intro x hxB hx1 hx2
    have hpx : p ≠ x := fun h => hp_not_B (h ▸ hxB)
    have hL1 : line[ℝ, p, x] = line[ℝ, a, b] :=
      affineSpan_pair_eq_of_mem_of_mem_of_ne hp1 hx1 hpx
    have hL2 : line[ℝ, p, x] = line[ℝ, c, d] :=
      affineSpan_pair_eq_of_mem_of_mem_of_ne hp2 hx2 hpx
    exact hline (hL1.symm.trans hL2)
  refine ⟨hab, ?_, ?_, ?_, ?_, hcd⟩
  · intro hac
    exact hneq a ha (left_mem_affineSpan_pair ℝ a b) (hac ▸ left_mem_affineSpan_pair ℝ c d)
  · intro had
    exact hneq a ha (left_mem_affineSpan_pair ℝ a b) (had ▸ right_mem_affineSpan_pair ℝ c d)
  · intro hbc
    exact hneq b hb (right_mem_affineSpan_pair ℝ a b) (hbc ▸ left_mem_affineSpan_pair ℝ c d)
  · intro hbd
    exact hneq b hb (right_mem_affineSpan_pair ℝ a b) (hbd ▸ right_mem_affineSpan_pair ℝ c d)

lemma min_degree_core_pruning {U : Finset ℝ²} {s : ℕ} (hs : 0 < s)
    (hdense : (U.card : ℝ) ^ 2 / (3 * (s : ℝ)) + (U.card : ℝ) * ((U.card : ℝ) / (4 * (s : ℝ))) ≤
      ((linesWithPointsFor 4 (U : Set ℝ²)).ncard : ℝ)) :
    ∃ V ⊆ U,
      U.card ≤ s * V.card ∧
      ∀ p ∈ V,
        let A := (four_lines_finite V).toFinset
        (V.card : ℝ) / (4 * (s : ℝ)) ≤ (A.filter (fun L => p ∈ L)).card := by
  let good : Finset ℝ² → Prop := fun W =>
    W ⊆ U ∧
    (U.card : ℝ) ^ 2 / (3 * (s : ℝ)) + (W.card : ℝ) * ((U.card : ℝ) / (4 * (s : ℝ))) ≤
      ((linesWithPointsFor 4 (W : Set ℝ²)).ncard : ℝ)
  have hex : ∃ n : ℕ, ∃ W : Finset ℝ², W.card = n ∧ good W := ⟨U.card, U, rfl, Finset.Subset.rfl, hdense⟩
  let n₀ := Nat.find hex
  obtain ⟨V, hVcard, hVU, hVbound⟩ := Nat.find_spec hex
  have hmin : ∀ W : Finset ℝ², good W → V.card ≤ W.card := by
    intro W hW
    rw [hVcard]
    exact Nat.find_min' hex ⟨W, rfl, hW⟩
  have hA_card : ((four_lines_finite V).toFinset.card : ℝ) =
      ((linesWithPointsFor 4 (V : Set ℝ²)).ncard : ℝ) := by
    rw [Set.ncard_eq_toFinset_card _ (four_lines_finite V)]
  have hV_large : U.card ≤ s * V.card := by
    have h12 := total_four_lines_le (S := V) (A := (four_lines_finite V).toFinset)
      (fun L hL => (Set.Finite.mem_toFinset _).mp hL)
    have h12R : (12 : ℝ) * ((four_lines_finite V).toFinset.card : ℝ) ≤ (V.card : ℝ) ^ 2 := by
      exact_mod_cast h12
    have hA_lo : (U.card : ℝ) ^ 2 / (3 * (s : ℝ)) ≤ ((four_lines_finite V).toFinset.card : ℝ) := by
      rw [hA_card]
      have hnn : 0 ≤ (V.card : ℝ) * ((U.card : ℝ) / (4 * (s : ℝ))) := by positivity
      linarith
    have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
    have hsq : (4 : ℝ) * (U.card : ℝ) ^ 2 / (s : ℝ) ≤ (V.card : ℝ) ^ 2 := by
      have h1 : (12 : ℝ) * ((U.card : ℝ) ^ 2 / (3 * (s : ℝ))) ≤ (V.card : ℝ) ^ 2 := by linarith
      have h2 : (12 : ℝ) * ((U.card : ℝ) ^ 2 / (3 * (s : ℝ))) = (4 : ℝ) * (U.card : ℝ) ^ 2 / (s : ℝ) := by
        field_simp [hs_pos.ne']
        ring
      linarith
    have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
    have hsq2 : (U.card : ℝ) ^ 2 ≤ ((s : ℝ) * (V.card : ℝ)) ^ 2 := by
      have h1 : (4 : ℝ) * (U.card : ℝ) ^ 2 ≤ (s : ℝ) * (V.card : ℝ) ^ 2 := by
        linarith [(div_le_iff₀ hs_pos).mp hsq]
      have h2 : (s : ℝ) * (V.card : ℝ) ^ 2 ≤ (s : ℝ) ^ 2 * (V.card : ℝ) ^ 2 := by
        nlinarith [sq_nonneg (V.card : ℝ)]
      have h3 : (U.card : ℝ) ^ 2 ≤ (4 : ℝ) * (U.card : ℝ) ^ 2 := by nlinarith
      nlinarith
    have hR : (U.card : ℝ) ≤ (s : ℝ) * (V.card : ℝ) := by
      nlinarith [show (0 : ℝ) ≤ (U.card : ℝ) by positivity,
                 show (0 : ℝ) ≤ (s : ℝ) * (V.card : ℝ) by positivity]
    exact_mod_cast hR
  refine ⟨V, hVU, hV_large, fun p hp => ?_⟩
  let A := (four_lines_finite V).toFinset
  have hdeg_U : (U.card : ℝ) / (4 * (s : ℝ)) ≤ (A.filter (fun L => p ∈ L)).card := by
    by_contra hlt
    push Not at hlt
    let V' := V.erase p
    have hV'_sub : V' ⊆ V := Finset.erase_subset p V
    have hkeep : A.filter (fun L => p ∉ L) ⊆ (four_lines_finite V').toFinset := by
      intro L hL
      obtain ⟨hLA, hpL⟩ := Finset.mem_filter.mp hL
      rw [Set.Finite.mem_toFinset]
      refine line_mem_four_of_subset hV'_sub ((Set.Finite.mem_toFinset _).mp hLA) ?_
      intro q hq
      have hqV := Finset.mem_filter.mp hq
      exact Finset.mem_erase.mpr ⟨fun hqp => hpL (hqp ▸ hqV.2), hqV.1⟩
    have hpart : (A.filter (fun L => p ∈ L)).card + (A.filter (fun L => p ∉ L)).card = A.card :=
      Finset.card_filter_add_card_filter_not (fun L => p ∈ L)
    have hV'_card_nat : V'.card + 1 = V.card := by
      rw [Finset.card_erase_of_mem hp]
      have hpos : 0 < V.card := Finset.card_pos.mpr ⟨p, hp⟩
      omega
    have hV'_cardR : (V'.card : ℝ) + 1 = (V.card : ℝ) := by exact_mod_cast hV'_card_nat
    have hA'_ge : ((A.filter (fun L => p ∉ L)).card : ℝ) ≤
        ((linesWithPointsFor 4 (V' : Set ℝ²)).ncard : ℝ) := by
      rw [Set.ncard_eq_toFinset_card _ (four_lines_finite V')]
      exact_mod_cast Finset.card_le_card hkeep
    have hpartR : ((A.filter (fun L => p ∈ L)).card : ℝ) + ((A.filter (fun L => p ∉ L)).card : ℝ) =
        ((linesWithPointsFor 4 (V : Set ℝ²)).ncard : ℝ) := by
      rw [← hA_card]
      exact_mod_cast hpart
    have hgoodV' : good V' := by
      refine ⟨hV'_sub.trans hVU, ?_⟩
      have hstep : (V.card : ℝ) * ((U.card : ℝ) / (4 * (s : ℝ))) =
          (V'.card : ℝ) * ((U.card : ℝ) / (4 * (s : ℝ))) + (U.card : ℝ) / (4 * (s : ℝ)) := by
        rw [← hV'_cardR]
        ring
      linarith
    have hcontra := hmin V' hgoodV'
    omega
  have hVU_le : (V.card : ℝ) ≤ (U.card : ℝ) := by exact_mod_cast Finset.card_le_card hVU
  have hdiv : (V.card : ℝ) / (4 * (s : ℝ)) ≤ (U.card : ℝ) / (4 * (s : ℝ)) :=
    div_le_div_of_nonneg_right hVU_le (by positivity)
  exact hdiv.trans hdeg_U

theorem main : H1 → H2 → OMA.R_Erdos101_erdos_101_R3.H2 := by
  intro rainbow sparse s C hs
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  obtain ⟨η, hη, N1, hrain⟩ := rainbow (1 / (4 * (s : ℝ))) (by positivity)
  obtain ⟨N2, hsparse⟩ := sparse (2 * C * s) η hη
  let N0 : ℕ := max (max (4 * C * s ^ 2 + 16) (4 * C + 16)) (2 * s * max N1 N2)
  refine ⟨N0, ?_⟩
  intro T B hTN hnc hBT hBsq hgen
  by_contra hdense_nat
  push Not at hdense_nat
  have hT_big1 : 4 * C * s ^ 2 + 16 ≤ T.card :=
    (le_trans (le_max_left _ _) (le_max_left _ _)).trans hTN
  have hT_big2 : 4 * C + 16 ≤ T.card :=
    (le_trans (le_max_right _ _) (le_max_left _ _)).trans hTN
  have hT_big3 : 2 * s * max N1 N2 ≤ T.card := (le_max_right _ _).trans hTN
  -- Step 1: Remove B to obtain U = T \ B with T.card ≤ 2 * U.card.
  let U : Finset ℝ² := T \ B
  have h2B_le_T : 2 * B.card ≤ T.card := by
    have h1 : (2 * B.card) ^ 2 ≤ T.card ^ 2 := by
      calc (2 * B.card) ^ 2 = 4 * B.card ^ 2 := by ring
        _ ≤ 4 * (C * T.card) := Nat.mul_le_mul_left 4 hBsq
        _ = (4 * C) * T.card := by ring
        _ ≤ T.card * T.card := Nat.mul_le_mul_right T.card (by omega)
        _ = T.card ^ 2 := (sq T.card).symm
    nlinarith
  have hT_le_2U : T.card ≤ 2 * U.card := by
    have hcard_sdiff : U.card = T.card - B.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hBT]
    omega
  -- Step 2: Anchor-meeting four-point lines are at most T.card^2 / (6 * s).
  let AT := (four_lines_finite T).toFinset
  have hAT_card : AT.card = (linesWithPointsFor 4 (T : Set ℝ²)).ncard :=
    (Set.ncard_eq_toFinset_card _ (four_lines_finite T)).symm
  have hmeet := anchor_meeting_lines_bound hBT
  have h2sBT : 2 * s * (B.card * T.card) ≤ T.card ^ 2 := by
    have hsq : (2 * s * (B.card * T.card)) ^ 2 ≤ (T.card ^ 2) ^ 2 := by
      calc (2 * s * (B.card * T.card)) ^ 2
          = 4 * s ^ 2 * B.card ^ 2 * T.card ^ 2 := by ring
        _ ≤ 4 * s ^ 2 * (C * T.card) * T.card ^ 2 := by
            have := Nat.mul_le_mul_left (4 * s ^ 2) hBsq
            exact Nat.mul_le_mul_right (T.card ^ 2) this
        _ = (4 * C * s ^ 2) * T.card ^ 3 := by ring
        _ ≤ T.card * T.card ^ 3 := Nat.mul_le_mul_right (T.card ^ 3) (by omega)
        _ = (T.card ^ 2) ^ 2 := by ring
    nlinarith
  have hdisj_sub : AT.filter (fun L => ¬ ∃ b ∈ B, b ∈ L) ⊆ (four_lines_finite U).toFinset := by
    intro L hL
    obtain ⟨hLAT, hnoB⟩ := Finset.mem_filter.mp hL
    rw [Set.Finite.mem_toFinset]
    refine line_mem_four_of_subset (Finset.sdiff_subset) ((Set.Finite.mem_toFinset _).mp hLAT) ?_
    intro q hq
    obtain ⟨hqT, hqL⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_sdiff.mpr ⟨hqT, fun hqB => hnoB ⟨q, hqB, hqL⟩⟩
  have hpartT :
      (AT.filter (fun L => ∃ b ∈ B, b ∈ L)).card +
      (AT.filter (fun L => ¬ ∃ b ∈ B, b ∈ L)).card = AT.card :=
    Finset.card_filter_add_card_filter_not (fun L => ∃ b ∈ B, b ∈ L)
  have hAU_ge_nat : 5 * T.card ^ 2 ≤ 6 * s * (linesWithPointsFor 4 (U : Set ℝ²)).ncard := by
    have hU_card : (AT.filter (fun L => ¬ ∃ b ∈ B, b ∈ L)).card ≤
        (linesWithPointsFor 4 (U : Set ℝ²)).ncard := by
      rw [Set.ncard_eq_toFinset_card _ (four_lines_finite U)]
      exact Finset.card_le_card hdisj_sub
    have hAT_ge : T.card ^ 2 ≤ s * AT.card := by rwa [hAT_card]
    have h6meet : 6 * s * (AT.filter (fun L => ∃ b ∈ B, b ∈ L)).card ≤ T.card ^ 2 := by
      have h1 : 6 * s * (AT.filter (fun L => ∃ b ∈ B, b ∈ L)).card =
          2 * s * (3 * (AT.filter (fun L => ∃ b ∈ B, b ∈ L)).card) := by ring
      rw [h1]
      exact (Nat.mul_le_mul_left (2 * s) hmeet).trans h2sBT
    nlinarith
  have hU_le_T : U.card ≤ T.card := Finset.card_le_card Finset.sdiff_subset
  have hU_dense :
      (U.card : ℝ) ^ 2 / (3 * (s : ℝ)) + (U.card : ℝ) * ((U.card : ℝ) / (4 * (s : ℝ))) ≤
      ((linesWithPointsFor 4 (U : Set ℝ²)).ncard : ℝ) := by
    have h1 : (5 : ℝ) * (U.card : ℝ) ^ 2 ≤
        (6 * (s : ℝ)) * ((linesWithPointsFor 4 (U : Set ℝ²)).ncard : ℝ) := by
      have hUT : (U.card : ℝ) ^ 2 ≤ (T.card : ℝ) ^ 2 := by
        have : (U.card : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast hU_le_T
        nlinarith
      have h56 : (5 : ℝ) * (T.card : ℝ) ^ 2 ≤
          (6 * (s : ℝ)) * ((linesWithPointsFor 4 (U : Set ℝ²)).ncard : ℝ) := by
        exact_mod_cast hAU_ge_nat
      linarith
    have hlhs : (U.card : ℝ) ^ 2 / (3 * (s : ℝ)) + (U.card : ℝ) * ((U.card : ℝ) / (4 * (s : ℝ))) =
        (7 : ℝ) / (12 * (s : ℝ)) * (U.card : ℝ) ^ 2 := by
      field_simp [hsR.ne']
      ring
    rw [hlhs]
    have h56 : (5 : ℝ) / (6 * (s : ℝ)) * (U.card : ℝ) ^ 2 ≤
        ((linesWithPointsFor 4 (U : Set ℝ²)).ncard : ℝ) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      linarith
    have h710 : (7 : ℝ) / (12 * (s : ℝ)) ≤ (5 : ℝ) / (6 * (s : ℝ)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    have hstep : (7 : ℝ) / (12 * (s : ℝ)) * (U.card : ℝ) ^ 2 ≤
        (5 : ℝ) / (6 * (s : ℝ)) * (U.card : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right h710 (sq_nonneg _)
    exact hstep.trans h56
  -- Step 3: Minimum-degree core pruning on U.
  obtain ⟨V, hVU, hUsV, hVdeg⟩ := min_degree_core_pruning hs hU_dense
  have hVT : V ⊆ T := hVU.trans Finset.sdiff_subset
  have hdisjVB : Disjoint V B :=
    Finset.disjoint_left.mpr fun x hxV hxB => (Finset.mem_sdiff.mp (hVU hxV)).2 hxB
  have hV_ge_max : max N1 N2 ≤ V.card := by
    have : 2 * s * max N1 N2 ≤ 2 * s * V.card := by nlinarith
    exact Nat.le_of_mul_le_mul_left this (by positivity : 0 < 2 * s)
  have hV_N1 : N1 ≤ V.card := (le_max_left N1 N2).trans hV_ge_max
  have hV_N2 : N2 ≤ V.card := (le_max_right N1 N2).trans hV_ge_max
  have hVB_sub : (V ∪ B : Finset ℝ²) ⊆ T := Finset.union_subset hVT hBT
  have hnc_VB : NonCollinearFor 5 ((V ∪ B : Finset ℝ²) : Set ℝ²) :=
    NonCollinearFor.subset (Finset.coe_subset.mpr hVB_sub) hnc
  have hnc_V : NonCollinearFor 5 (V : Set ℝ²) :=
    NonCollinearFor.subset (Finset.coe_subset.mpr hVT) hnc
  have hBsq_V : B.card ^ 2 ≤ (2 * C * s) * V.card := by
    calc B.card ^ 2 ≤ C * T.card := hBsq
      _ ≤ C * (2 * U.card) := Nat.mul_le_mul_left C hT_le_2U
      _ ≤ C * (2 * (s * V.card)) := Nat.mul_le_mul_left C (Nat.mul_le_mul_left 2 hUsV)
      _ = (2 * C * s) * V.card := by ring
  -- Step 4: Apply H1 (4-partite rainbow extraction) to V.
  have hV_pencils : ∀ p ∈ V, ∃ A : Finset (AffineSubspace ℝ ℝ²),
      (1 / (4 * (s : ℝ))) * (V.card : ℝ) ≤ A.card ∧
      ∀ L ∈ A, p ∈ L ∧ L ∈ linesWithPointsFor 4 (V : Set ℝ²) := by
    intro p hp
    refine ⟨(four_lines_finite V).toFinset.filter (fun L => p ∈ L), ?_, ?_⟩
    · have hd := hVdeg p hp
      have heq : (1 / (4 * (s : ℝ))) * (V.card : ℝ) = (V.card : ℝ) / (4 * (s : ℝ)) := by ring
      linarith
    · intro L hL
      obtain ⟨hL1, hpL⟩ := Finset.mem_filter.mp hL
      exact ⟨hpL, (Set.Finite.mem_toFinset _).mp hL1⟩
  obtain ⟨V0, V1, V2, V3, h0, h1, h2, h3, hd01, hd02, hd03, hd12, hd13, hd23,
    A, hA_dense, hA_rain, hA_deg⟩ := hrain V hV_N1 hnc_V hV_pencils
  -- Step 5: Verify four-anchor distinctness and two-point cap, then apply H2 for contradiction.
  have hcap_V : ∀ a ∈ B, ∀ b ∈ B, a ≠ b →
      (V.filter (fun p => p ∈ line[ℝ, a, b])).card ≤ 2 :=
    fun a ha b hb hab => anchor_line_cap hdisjVB hnc_VB ha hb hab
  have hgen_V : ∀ p ∈ V, ∃ a ∈ B, ∃ b ∈ B, ∃ c ∈ B, ∃ d ∈ B,
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      line[ℝ, a, b] ≠ line[ℝ, c, d] ∧ p ∈ line[ℝ, a, b] ∧ p ∈ line[ℝ, c, d] := by
    intro p hpV
    have hpT : p ∈ T := hVT hpV
    have hp_notB : p ∉ B := Finset.disjoint_left.mp hdisjVB hpV
    rcases hgen p hpT with hpB | ⟨a, ha, b, hb, c, hc, d, hd, hab, hcd, hline, hp1, hp2⟩
    · exact absurd hpB hp_notB
    · obtain ⟨h1', h2', h3', h4', h5', h6'⟩ :=
        four_anchors_distinct hdisjVB hpV ha hb hc hd hab hcd hline hp1 hp2
      exact ⟨a, ha, b, hb, c, hc, d, hd, h1', h2', h3', h4', h5', h6', hline, hp1, hp2⟩
  have hcontra := hsparse V B hV_N2 hdisjVB hnc_VB hBsq_V hcap_V hgen_V
    V0 V1 V2 V3 ⟨h0, h1, h2, h3⟩ ⟨hd01, hd02, hd03, hd12, hd13, hd23⟩ A hA_rain hA_deg
  exact not_lt_of_ge hA_dense hcontra

end OMA.R_Erdos101_erdos_101_R3_H2_R1
