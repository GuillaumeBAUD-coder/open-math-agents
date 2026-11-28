import OMAReductions.R_Erdos101_erdos_101_R3

/-!
# Bipartite anchor-line intersection grid embedding for `Erdos101.erdos_101.R3.H2`

Given an anchor-generated four-point configuration `(T, B)` with `B ⊆ T` and `|B|^2 ≤ C |T|`,
we pass to `U = T \ B` and the finite family `LB` of all lines spanned by distinct pairs of
anchors in `B`, and unconditionally establish inside this file:

1. **Anchor-line count and two-point cap**: `2 |LB| ≤ |B|^2 ≤ C |T|`, every anchor line
   `M ∈ LB` contains at most two points of `U` (else five points of `T` would be collinear),
   and therefore no four-point line of `U` belongs to `LB`.
2. **Anchor-free four-point line density**: at most `|B| |T| / 3` four-point lines of `T`
   meet `B`, so for `|T| ≥ 4 C s^2 + 16`, `U` retains at least `5 |T|^2 / (6 s)` four-point lines.
3. **Quadratic pair bound on grid subsets**: any subset `W ⊆ U` retaining at least `1/16` of
   the four-point lines of `U` satisfies `5 |T|^2 ≤ 96 s t_4(W) ≤ 8 s |W|^2`, forcing
   `|T| ≤ 2 s |W|`, `|B|^2 ≤ 2 C s |W|`, and `|LB| ≤ 2 C s |W|`.

We then reduce `OMA.R_Erdos101_erdos_101_R3.H2` to two independent hypotheses:
- `H1`: Bipartite 2-coloring extraction of disjoint subfamilies `M0, M1 ⊆ LB` whose
  grid-coordinatized intersection set `W` retains at least `1/16` of the four-point lines of `U`
  (unconditionally true by a uniform random 2-coloring of `LB`, since the eight lines of `LB`
  witnessing the four points of any four-point line of `U` are pairwise distinct).
- `H2`: Uniform sparsity of four-point lines for point sets `W` embedded in the bipartite
  intersection grid `M0 ∩ M1` of two disjoint anchor-spanned line families from `B` with
  `|B|^2 ≤ K |W|`, `|M0| + |M1| ≤ K |W|`, and at most two points of `W` per grid line.
-/

namespace OMA.R_Erdos101_erdos_101_R3_H2_R4

open EuclideanGeometry
open scoped Classical

/-- Given a finite planar point set `U` and a finite family `LB` of affine subspaces such that
every member of `LB` contains at most two points of `U` and every point of `U` lies on two
distinct members of `LB`, there exist disjoint subfamilies `M0, M1 ⊆ LB` whose grid-coordinatized
subset `W` retains at least `1/16` of the four-point lines of `U`. -/
def H1 : Prop :=
  ∀ U : Finset ℝ², ∀ LB : Finset (AffineSubspace ℝ ℝ²),
    (∀ M ∈ LB, (U.filter (fun p => p ∈ M)).card ≤ 2) →
    (∀ p ∈ U, ∃ L1 ∈ LB, ∃ L2 ∈ LB, L1 ≠ L2 ∧ p ∈ L1 ∧ p ∈ L2) →
    ∃ M0 M1 : Finset (AffineSubspace ℝ ℝ²),
      M0 ⊆ LB ∧ M1 ⊆ LB ∧ Disjoint M0 M1 ∧
      (linesWithPointsFor 4 (U : Set ℝ²)).ncard ≤
        16 * (linesWithPointsFor 4
          ((U.filter (fun p => (∃ L0 ∈ M0, p ∈ L0) ∧ (∃ L1 ∈ M1, p ∈ L1)) : Finset ℝ²) : Set ℝ²)).ncard

/-- Uniform sparsity of four-point lines for finite point sets `W` embedded in the bipartite
intersection grid `M0 ∩ M1` of two disjoint families of anchor-spanned lines from a small anchor
set `B` (`|B|^2 ≤ K |W|`), where every grid line carries at most two points of `W`. -/
def H2 : Prop :=
  ∀ K : ℕ, ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ W B : Finset ℝ²,
    N ≤ W.card → Disjoint W B → NonCollinearFor 5 ((W ∪ B : Finset ℝ²) : Set ℝ²) →
    B.card ^ 2 ≤ K * W.card →
    ∀ M0 M1 : Finset (AffineSubspace ℝ ℝ²),
      Disjoint M0 M1 → M0.card + M1.card ≤ K * W.card →
      (∀ M ∈ M0 ∪ M1,
        (∃ a ∈ B, ∃ b ∈ B, a ≠ b ∧ M = line[ℝ, a, b]) ∧
        (W.filter (fun p => p ∈ M)).card ≤ 2) →
      (∀ p ∈ W, (∃ L0 ∈ M0, p ∈ L0) ∧ (∃ L1 ∈ M1, p ∈ L1)) →
      ((linesWithPointsFor 4 (W : Set ℝ²)).ncard : ℝ) < δ * (W.card : ℝ) ^ 2

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

lemma anchor_lines_card_le (B : Finset ℝ²) :
    2 * (B.offDiag.image (fun ab => line[ℝ, ab.1, ab.2])).card ≤ B.card ^ 2 := by
  let LB := B.offDiag.image (fun ab => line[ℝ, ab.1, ab.2])
  let fib := fun M : AffineSubspace ℝ ℝ² => B.offDiag.filter (fun ab => line[ℝ, ab.1, ab.2] = M)
  have hdisj : (LB : Set (AffineSubspace ℝ ℝ²)).PairwiseDisjoint fib := by
    intro M1 _ M2 _ hne
    apply Finset.disjoint_left.mpr
    intro ab h1 h2
    exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  have hge2 : ∀ M ∈ LB, 2 ≤ (fib M).card := by
    intro M hM
    obtain ⟨⟨a, b⟩, hab_od, rfl⟩ := Finset.mem_image.mp hM
    obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp hab_od
    have h1 : (a, b) ∈ fib line[ℝ, a, b] := Finset.mem_filter.mpr ⟨hab_od, rfl⟩
    have h2 : (b, a) ∈ fib line[ℝ, a, b] := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨hb, ha, hab.symm⟩, ?_⟩
      rw [Set.pair_comm]
    have hne : (a, b) ≠ (b, a) := fun h => hab (Prod.mk.inj h).1
    have hpair : ({(a, b), (b, a)} : Finset (ℝ² × ℝ²)) ⊆ fib line[ℝ, a, b] := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact h1
      · exact h2
    calc 2 = ({(a, b), (b, a)} : Finset (ℝ² × ℝ²)).card := (Finset.card_pair hne).symm
      _ ≤ (fib line[ℝ, a, b]).card := Finset.card_le_card hpair
  have hsub : LB.biUnion fib ⊆ B.offDiag := by
    intro ab hab
    obtain ⟨M, _, hM⟩ := Finset.mem_biUnion.mp hab
    exact (Finset.mem_filter.mp hM).1
  calc 2 * LB.card = ∑ _M ∈ LB, 2 := by simp [mul_comm]
    _ ≤ ∑ M ∈ LB, (fib M).card := Finset.sum_le_sum hge2
    _ = (LB.biUnion fib).card := (Finset.card_biUnion hdisj).symm
    _ ≤ B.offDiag.card := Finset.card_le_card hsub
    _ = B.card * B.card - B.card := B.offDiag_card
    _ ≤ B.card ^ 2 := by rw [sq]; exact Nat.sub_le _ _

lemma anchor_line_cap_two {T B : Finset ℝ²} (hBT : B ⊆ T)
    (hnc : NonCollinearFor 5 (T : Set ℝ²)) {M : AffineSubspace ℝ ℝ²}
    (hM : M ∈ B.offDiag.image (fun ab => line[ℝ, ab.1, ab.2])) :
    ((T \ B).filter (fun p => p ∈ M)).card ≤ 2 := by
  obtain ⟨⟨a, b⟩, hab_od, hMeq⟩ := Finset.mem_image.mp hM
  dsimp only at hMeq
  subst hMeq
  obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp hab_od
  by_contra hgt
  push Not at hgt
  let S5 : Finset ℝ² := insert a (insert b ((T \ B).filter (fun p => p ∈ line[ℝ, a, b])))
  have ha_not : a ∉ (T \ B).filter (fun p => p ∈ line[ℝ, a, b]) := fun h =>
    (Finset.mem_sdiff.mp (Finset.mem_filter.mp h).1).2 ha
  have hb_not : b ∉ (T \ B).filter (fun p => p ∈ line[ℝ, a, b]) := fun h =>
    (Finset.mem_sdiff.mp (Finset.mem_filter.mp h).1).2 hb
  have ha_not2 : a ∉ insert b ((T \ B).filter (fun p => p ∈ line[ℝ, a, b])) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hab, ha_not⟩
  have hcard : 5 ≤ S5.card := by
    rw [Finset.card_insert_of_notMem ha_not2, Finset.card_insert_of_notMem hb_not]
    omega
  obtain ⟨W, hWS5, hW5⟩ := Finset.exists_subset_card_eq hcard
  have hWsub : (W : Set ℝ²) ⊆ (T : Set ℝ²) := by
    intro x hx
    have hxS5 := hWS5 hx
    simp only [S5, Finset.mem_insert, Finset.mem_filter, Finset.mem_sdiff] at hxS5
    rcases hxS5 with hxa | hxb | ⟨⟨hxT, _⟩, _⟩
    · rw [hxa]; exact hBT ha
    · rw [hxb]; exact hBT hb
    · exact hxT
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

lemma four_line_not_mem_anchor_lines {T B : Finset ℝ²} (hBT : B ⊆ T)
    (hnc : NonCollinearFor 5 (T : Set ℝ²)) {L : AffineSubspace ℝ ℝ²}
    (hL : L ∈ linesWithPointsFor 4 ((T \ B : Finset ℝ²) : Set ℝ²)) :
    L ∉ B.offDiag.image (fun ab => line[ℝ, ab.1, ab.2]) := by
  intro hmem
  have hle := anchor_line_cap_two hBT hnc hmem
  have heq := four_points hL
  omega

lemma anchor_free_four_lines_density {T B : Finset ℝ²} {s C : ℕ}
    (hBT : B ⊆ T) (hBsq : B.card ^ 2 ≤ C * T.card) (hT_big : 4 * C * s ^ 2 ≤ T.card)
    (hdense : T.card ^ 2 ≤ s * (linesWithPointsFor 4 (T : Set ℝ²)).ncard) :
    5 * T.card ^ 2 ≤ 6 * s * (linesWithPointsFor 4 ((T \ B : Finset ℝ²) : Set ℝ²)).ncard := by
  let U : Finset ℝ² := T \ B
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
        _ ≤ T.card * T.card ^ 3 := Nat.mul_le_mul_right (T.card ^ 3) hT_big
        _ = (T.card ^ 2) ^ 2 := by ring
    nlinarith
  have hdisj_sub : AT.filter (fun L => ¬ ∃ b ∈ B, b ∈ L) ⊆ (four_lines_finite U).toFinset := by
    intro L hL
    obtain ⟨hLAT, hnoB⟩ := Finset.mem_filter.mp hL
    rw [Set.Finite.mem_toFinset]
    refine line_mem_four_of_subset Finset.sdiff_subset ((Set.Finite.mem_toFinset _).mp hLAT) ?_
    intro q hq
    obtain ⟨hqT, hqL⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_sdiff.mpr ⟨hqT, fun hqB => hnoB ⟨q, hqB, hqL⟩⟩
  have hpartT :
      (AT.filter (fun L => ∃ b ∈ B, b ∈ L)).card +
      (AT.filter (fun L => ¬ ∃ b ∈ B, b ∈ L)).card = AT.card :=
    Finset.card_filter_add_card_filter_not (fun L => ∃ b ∈ B, b ∈ L)
  have hU_card : (AT.filter (fun L => ¬ ∃ b ∈ B, b ∈ L)).card ≤
      (linesWithPointsFor 4 ((T \ B : Finset ℝ²) : Set ℝ²)).ncard := by
    rw [Set.ncard_eq_toFinset_card _ (four_lines_finite (T \ B))]
    exact Finset.card_le_card hdisj_sub
  have hAT_ge : T.card ^ 2 ≤ s * AT.card := by rwa [hAT_card]
  have h6meet : 6 * s * (AT.filter (fun L => ∃ b ∈ B, b ∈ L)).card ≤ T.card ^ 2 := by
    have h1 : 6 * s * (AT.filter (fun L => ∃ b ∈ B, b ∈ L)).card =
        2 * s * (3 * (AT.filter (fun L => ∃ b ∈ B, b ∈ L)).card) := by ring
    rw [h1]
    exact (Nat.mul_le_mul_left (2 * s) hmeet).trans h2sBT
  have h6U : 6 * s * (AT.filter (fun L => ¬ ∃ b ∈ B, b ∈ L)).card ≤
      6 * s * (linesWithPointsFor 4 ((T \ B : Finset ℝ²) : Set ℝ²)).ncard :=
    Nat.mul_le_mul_left (6 * s) hU_card
  nlinarith

lemma grid_subset_size_bound {T W : Finset ℝ²} {s : ℕ} (hs : 0 < s)
    (hW_dense : 5 * T.card ^ 2 ≤ 96 * s * (linesWithPointsFor 4 (W : Set ℝ²)).ncard) :
    T.card ≤ 2 * s * W.card := by
  have h12 : 12 * (linesWithPointsFor 4 (W : Set ℝ²)).ncard ≤ W.card ^ 2 := by
    rw [Set.ncard_eq_toFinset_card _ (four_lines_finite W)]
    exact total_four_lines_le (S := W) (A := (four_lines_finite W).toFinset)
      (fun L hL => (Set.Finite.mem_toFinset _).mp hL)
  have hsq : 5 * T.card ^ 2 ≤ 8 * s * W.card ^ 2 := by
    calc 5 * T.card ^ 2
        ≤ 96 * s * (linesWithPointsFor 4 (W : Set ℝ²)).ncard := hW_dense
      _ = 8 * s * (12 * (linesWithPointsFor 4 (W : Set ℝ²)).ncard) := by ring
      _ ≤ 8 * s * W.card ^ 2 := Nat.mul_le_mul_left (8 * s) h12
  have hs1 : 1 ≤ s := hs
  have hsq2 : T.card ^ 2 ≤ (2 * s * W.card) ^ 2 := by
    have h8_le : 8 * s ≤ 20 * s ^ 2 := by nlinarith
    have hmul : 8 * s * W.card ^ 2 ≤ 20 * s ^ 2 * W.card ^ 2 :=
      Nat.mul_le_mul_right (W.card ^ 2) h8_le
    nlinarith
  by_contra hlt
  push Not at hlt
  exact not_lt_of_ge hsq2 (Nat.pow_lt_pow_left hlt two_ne_zero)

theorem main : H1 → H2 → OMA.R_Erdos101_erdos_101_R3.H2 := by
  intro split sparse s C hs
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  obtain ⟨N2, hsparse⟩ := sparse (2 * C * s) (5 / (96 * (s : ℝ))) (by positivity)
  let N0 : ℕ := max (4 * C * s ^ 2 + 16) (2 * s * N2)
  refine ⟨N0, ?_⟩
  intro T B hTN hnc hBT hBsq hgen
  by_contra hdense_nat
  push Not at hdense_nat
  have hT_big1 : 4 * C * s ^ 2 ≤ T.card := by
    have := (le_max_left (4 * C * s ^ 2 + 16) (2 * s * N2)).trans hTN
    omega
  have hT_big2 : 2 * s * N2 ≤ T.card :=
    (le_max_right (4 * C * s ^ 2 + 16) (2 * s * N2)).trans hTN
  -- Step 1: Pass to U = T \ B and the anchor-line family LB.
  let U : Finset ℝ² := T \ B
  let LB : Finset (AffineSubspace ℝ ℝ²) := B.offDiag.image (fun ab => line[ℝ, ab.1, ab.2])
  have hU_dense : 5 * T.card ^ 2 ≤ 6 * s * (linesWithPointsFor 4 (U : Set ℝ²)).ncard :=
    anchor_free_four_lines_density hBT hBsq hT_big1 hdense_nat
  have hcap_U : ∀ M ∈ LB, (U.filter (fun p => p ∈ M)).card ≤ 2 :=
    fun M hM => anchor_line_cap_two hBT hnc hM
  have hcov_U : ∀ p ∈ U, ∃ L1 ∈ LB, ∃ L2 ∈ LB, L1 ≠ L2 ∧ p ∈ L1 ∧ p ∈ L2 := by
    intro p hpU
    obtain ⟨hpT, hp_notB⟩ := Finset.mem_sdiff.mp hpU
    rcases hgen p hpT with hpB | ⟨a, ha, b, hb, c, hc, d, hd, hab, hcd, hline, hp1, hp2⟩
    · exact absurd hpB hp_notB
    · refine ⟨line[ℝ, a, b], ?_, line[ℝ, c, d], ?_, hline, hp1, hp2⟩
      · exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩, rfl⟩
      · exact Finset.mem_image.mpr ⟨(c, d), Finset.mem_offDiag.mpr ⟨hc, hd, hcd⟩, rfl⟩
  -- Step 2: Apply H1 to extract disjoint subfamilies M0, M1 ⊆ LB with dense grid subset W.
  obtain ⟨M0, M1, hM0_sub, hM1_sub, hM_disj, hW_retain⟩ := split U LB hcap_U hcov_U
  let W : Finset ℝ² := U.filter (fun p => (∃ L0 ∈ M0, p ∈ L0) ∧ (∃ L1 ∈ M1, p ∈ L1))
  have hWU : W ⊆ U := Finset.filter_subset _ U
  have hWT : W ⊆ T := hWU.trans Finset.sdiff_subset
  have hW_dense_nat : 5 * T.card ^ 2 ≤ 96 * s * (linesWithPointsFor 4 (W : Set ℝ²)).ncard := by
    calc 5 * T.card ^ 2
        ≤ 6 * s * (linesWithPointsFor 4 (U : Set ℝ²)).ncard := hU_dense
      _ ≤ 6 * s * (16 * (linesWithPointsFor 4 (W : Set ℝ²)).ncard) :=
          Nat.mul_le_mul_left (6 * s) hW_retain
      _ = 96 * s * (linesWithPointsFor 4 (W : Set ℝ²)).ncard := by ring
  -- Step 3: Deduce linear size and anchor/line bounds for W, then apply H2 for contradiction.
  have hT_le_2sW : T.card ≤ 2 * s * W.card := grid_subset_size_bound hs hW_dense_nat
  have hW_N2 : N2 ≤ W.card := by
    have : 2 * s * N2 ≤ 2 * s * W.card := hT_big2.trans hT_le_2sW
    exact Nat.le_of_mul_le_mul_left this (by positivity : 0 < 2 * s)
  have hdisjWB : Disjoint W B :=
    Finset.disjoint_left.mpr fun x hxW hxB => (Finset.mem_sdiff.mp (hWU hxW)).2 hxB
  have hnc_WB : NonCollinearFor 5 ((W ∪ B : Finset ℝ²) : Set ℝ²) :=
    NonCollinearFor.subset (Finset.coe_subset.mpr (Finset.union_subset hWT hBT)) hnc
  have hBsq_W : B.card ^ 2 ≤ (2 * C * s) * W.card := by
    calc B.card ^ 2 ≤ C * T.card := hBsq
      _ ≤ C * (2 * s * W.card) := Nat.mul_le_mul_left C hT_le_2sW
      _ = (2 * C * s) * W.card := by ring
  have hM_card : M0.card + M1.card ≤ (2 * C * s) * W.card := by
    have hLB_le : LB.card ≤ B.card ^ 2 := by
      have h2 : 2 * LB.card ≤ B.card ^ 2 := anchor_lines_card_le B
      omega
    have hunion_sub : M0 ∪ M1 ⊆ LB := Finset.union_subset hM0_sub hM1_sub
    calc M0.card + M1.card = (M0 ∪ M1).card := (Finset.card_union_of_disjoint hM_disj).symm
      _ ≤ LB.card := Finset.card_le_card hunion_sub
      _ ≤ B.card ^ 2 := hLB_le
      _ ≤ (2 * C * s) * W.card := hBsq_W
  have hM_props : ∀ M ∈ M0 ∪ M1,
      (∃ a ∈ B, ∃ b ∈ B, a ≠ b ∧ M = line[ℝ, a, b]) ∧
      (W.filter (fun p => p ∈ M)).card ≤ 2 := by
    intro M hM
    have hM_LB : M ∈ LB := Finset.union_subset hM0_sub hM1_sub hM
    refine ⟨?_, ?_⟩
    · obtain ⟨⟨a, b⟩, hab_od, hMeq⟩ := Finset.mem_image.mp hM_LB
      obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp hab_od
      exact ⟨a, ha, b, hb, hab, hMeq.symm⟩
    · exact (Finset.card_le_card (Finset.filter_subset_filter _ hWU)).trans (hcap_U M hM_LB)
  have hW_grid : ∀ p ∈ W, (∃ L0 ∈ M0, p ∈ L0) ∧ (∃ L1 ∈ M1, p ∈ L1) :=
    fun p hp => (Finset.mem_filter.mp hp).2
  have hcontra := hsparse W B hW_N2 hdisjWB hnc_WB hBsq_W M0 M1 hM_disj hM_card hM_props hW_grid
  have hW_dense_real : (5 / (96 * (s : ℝ))) * (W.card : ℝ) ^ 2 ≤
      ((linesWithPointsFor 4 (W : Set ℝ²)).ncard : ℝ) := by
    have hW_le_T : W.card ≤ T.card := Finset.card_le_card hWT
    have hW_sq : 5 * W.card ^ 2 ≤ 96 * s * (linesWithPointsFor 4 (W : Set ℝ²)).ncard := by
      calc 5 * W.card ^ 2 ≤ 5 * T.card ^ 2 :=
            Nat.mul_le_mul_left 5 (Nat.pow_le_pow_left hW_le_T 2)
        _ ≤ 96 * s * (linesWithPointsFor 4 (W : Set ℝ²)).ncard := hW_dense_nat
    have hW_sqR : (5 : ℝ) * (W.card : ℝ) ^ 2 ≤
        (96 * (s : ℝ)) * ((linesWithPointsFor 4 (W : Set ℝ²)).ncard : ℝ) := by
      exact_mod_cast hW_sq
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    linarith
  exact not_lt_of_ge hW_dense_real hcontra

end OMA.R_Erdos101_erdos_101_R3_H2_R4
