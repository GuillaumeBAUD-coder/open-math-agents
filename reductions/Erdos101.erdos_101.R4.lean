import FormalConjectures.ErdosProblems.«101»

/-!
# Minimum-degree core and 4-partite rainbow regularization for four-point lines

This reduction of Erdős Problem 101 works purely through combinatorial incidence geometry,
without algebraic curves, distance ratios, or anchor sets.

First, a minimum-cardinality core extraction trims any dense point configuration with
`δ n²` four-point lines down to a linear-sized subconfiguration `V` in which every point
is incident to linearly many four-point lines of `V`.

The first hypothesis `H1` asks whether every such linear minimum-degree core admits a
4-partite rainbow regularization: four pairwise disjoint subsets `V0, V1, V2, V3 ⊆ V`
and a family `A` of quadratically many four-point lines of `V` such that each line in `A`
meets each `Vi` in exactly one point and every point in `V0 ∪ V1 ∪ V2 ∪ V3` has linear
degree in `A`.

From the rainbow condition and pencil packing, each part `Vi` automatically has linear
size. The second hypothesis `H2` asserts that no such regularized 4-partite rainbow
configuration with linear part sizes and linear minimum degree can support quadratically
many rainbow four-point lines.
-/

namespace OMA.R_Erdos101_erdos_101_R4

open EuclideanGeometry Filter Asymptotics
open scoped Classical Finset

/-- Every point set without five collinear points in which every point lies on linearly
many four-point lines admits a 4-partite rainbow subconfiguration with quadratically many
rainbow four-point lines and linear minimum rainbow degree across all four parts. -/
def H1 : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ η : ℝ, 0 < η ∧ ∃ N : ℕ,
    ∀ V : Finset ℝ², N ≤ V.card → NonCollinearFor 5 (V : Set ℝ²) →
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
          ∀ p ∈ V0 ∪ V1 ∪ V2 ∪ V3, η * (V.card : ℝ) ≤ (A.filter (fun L => p ∈ L)).card

/-- No sufficiently large point set without five collinear points contains four pairwise
disjoint linear-sized parts supporting a regularized 4-partite rainbow family of
quadratically many four-point lines with linear minimum degree. -/
def H2 : Prop :=
  ∀ η : ℝ, 0 < η → ∃ N : ℕ,
    ∀ V V0 V1 V2 V3 : Finset ℝ², N ≤ V.card → NonCollinearFor 5 (V : Set ℝ²) →
      V0 ⊆ V → V1 ⊆ V → V2 ⊆ V → V3 ⊆ V →
      Disjoint V0 V1 → Disjoint V0 V2 → Disjoint V0 V3 →
      Disjoint V1 V2 → Disjoint V1 V3 → Disjoint V2 V3 →
      η * (V.card : ℝ) ≤ V0.card → η * (V.card : ℝ) ≤ V1.card →
      η * (V.card : ℝ) ≤ V2.card → η * (V.card : ℝ) ≤ V3.card →
      ∀ A : Finset (AffineSubspace ℝ ℝ²),
        (∀ L ∈ A, L ∈ linesWithPointsFor 4 (V : Set ℝ²) ∧
          (V0.filter (fun p => p ∈ L)).card = 1 ∧
          (V1.filter (fun p => p ∈ L)).card = 1 ∧
          (V2.filter (fun p => p ∈ L)).card = 1 ∧
          (V3.filter (fun p => p ∈ L)).card = 1) →
        (∀ p ∈ V0 ∪ V1 ∪ V2 ∪ V3, η * (V.card : ℝ) ≤ (A.filter (fun L => p ∈ L)).card) →
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

lemma line_mem_four_of_subset {V S : Finset ℝ²} (hVS : V ⊆ S)
    {L : AffineSubspace ℝ ℝ²} (hL : L ∈ linesWithPointsFor 4 (S : Set ℝ²))
    (hsub : S.filter (fun p => p ∈ L) ⊆ V) :
    L ∈ linesWithPointsFor 4 (V : Set ℝ²) := by
  have hcardS : (S.filter (fun p => p ∈ L)).card = 4 := four_points hL
  have hflt : V.filter (fun p => p ∈ L) = S.filter (fun p => p ∈ L) := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hpV, hpL⟩
      exact ⟨hVS hpV, hpL⟩
    · rintro ⟨hpS, hpL⟩
      exact ⟨hsub (Finset.mem_filter.mpr ⟨hpS, hpL⟩), hpL⟩
  have hgt : 1 < (S.filter (fun p => p ∈ L)).card := by omega
  obtain ⟨p, hp, q, hq, hne⟩ := Finset.one_lt_card.mp hgt
  have hpV : p ∈ V := hsub hp
  have hqV : q ∈ V := hsub hq
  have hpL : p ∈ L := (Finset.mem_filter.mp hp).2
  have hqL : q ∈ L := (Finset.mem_filter.mp hq).2
  refine ⟨⟨p, hpV, q, hqV, hne, line_through hL hpL hqL hne⟩, ?_⟩
  have he : ((V.filter (fun r => r ∈ L) : Finset ℝ²) : Set ℝ²) = (L : Set ℝ²) ∩ V := by
    ext r
    simp [and_comm]
  rw [← he, Set.ncard_coe_finset, hflt, hcardS]

/-- Distinct four-point lines through a point `p ∈ S` partition triples among `S \ {p}`. -/
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
  have hcard (L) (hL : L ∈ pencil) : (others L).card = 3 := by
    obtain ⟨hLA, hpL⟩ := Finset.mem_filter.mp hL
    rw [Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hp, hpL⟩), four_points (hA L hLA)]
  have hsub : pencil.biUnion others ⊆ S.erase p := by
    intro q hq
    obtain ⟨L, _, hq⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hq
    exact Finset.mem_erase.mpr ⟨hne, (Finset.mem_filter.mp hmem).1⟩
  calc
    3 * pencil.card = ∑ L ∈ pencil, (others L).card := by
      simp [Finset.sum_congr rfl hcard, mul_comm]
    _ = (pencil.biUnion others).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (S.erase p).card := Finset.card_le_card hsub
    _ = S.card - 1 := Finset.card_erase_of_mem hp

/-- Counting ordered pairs on four-point lines yields `12 |A| ≤ |S| (|S| - 1)`. -/
lemma pair_bound {S : Finset ℝ²} {A : Finset (AffineSubspace ℝ ℝ²)}
    (hA : ∀ L ∈ A, L ∈ linesWithPointsFor 4 (S : Set ℝ²)) :
    12 * A.card ≤ S.card * (S.card - 1) := by
  have hcount : (∑ L ∈ A, (S.filter (fun p => p ∈ L)).card) =
      ∑ p ∈ S, (A.filter (fun L => p ∈ L)).card :=
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun L p => p ∈ L)
  have hs : (∑ L ∈ A, (S.filter (fun p => p ∈ L)).card) = A.card * 4 := by
    simp [Finset.sum_congr rfl (fun L hL => four_points (hA L hL))]
  calc
    12 * A.card = 3 * (A.card * 4) := by omega
    _ = 3 * ∑ p ∈ S, (A.filter (fun L => p ∈ L)).card := by rw [← hcount, hs]
    _ = ∑ p ∈ S, 3 * (A.filter (fun L => p ∈ L)).card := Finset.mul_sum ..
    _ ≤ ∑ _p ∈ S, (S.card - 1) := Finset.sum_le_sum fun p hp => pencil_bound hA hp
    _ = S.card * (S.card - 1) := by simp

/-- Minimum-cardinality core extraction: any point set `S` with at least `δ |S|²`
four-point lines contains a linear-sized core `V ⊆ S` (`6 δ |S|² ≤ |V|²`) in which
every point is incident to at least `(δ / 2) |V|` four-point lines of `V`. -/
lemma min_degree_core {S : Finset ℝ²} {δ : ℝ} (hδ : 0 < δ)
    (hdense : δ * (S.card : ℝ) ^ 2 ≤ ((linesWithPointsFor 4 (S : Set ℝ²)).ncard : ℝ)) :
    ∃ V ⊆ S, 6 * δ * (S.card : ℝ) ^ 2 ≤ (V.card : ℝ) ^ 2 ∧
      ∀ p ∈ V, ∃ A : Finset (AffineSubspace ℝ ℝ²), (δ / 2) * (V.card : ℝ) ≤ A.card ∧
        ∀ L ∈ A, p ∈ L ∧ L ∈ linesWithPointsFor 4 (V : Set ℝ²) := by
  let valid := (Finset.powerset S).filter (fun V : Finset ℝ² =>
    (δ / 2) * (S.card : ℝ) ^ 2 + (V.card : ℝ) * ((δ / 2) * (S.card : ℝ)) ≤
      ((linesWithPointsFor 4 (V : Set ℝ²)).ncard : ℝ))
  have hSmem : S ∈ valid := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.Subset.rfl, ?_⟩
    have hEq : (δ / 2) * (S.card : ℝ) ^ 2 + (S.card : ℝ) * ((δ / 2) * (S.card : ℝ)) =
        δ * (S.card : ℝ) ^ 2 := by ring
    linarith
  obtain ⟨V, hVmem, hVmin⟩ := Finset.exists_min_image valid Finset.card ⟨S, hSmem⟩
  obtain ⟨hVS_pow, hVfeas⟩ := Finset.mem_filter.mp hVmem
  have hVS : V ⊆ S := Finset.mem_powerset.mp hVS_pow
  let LV := (four_lines_finite V).toFinset
  have hLV_mem : ∀ L ∈ LV, L ∈ linesWithPointsFor 4 (V : Set ℝ²) :=
    fun _ hL => (four_lines_finite V).mem_toFinset.mp hL
  have hLV_card : ((linesWithPointsFor 4 (V : Set ℝ²)).ncard : ℝ) = (LV.card : ℝ) := by
    exact_mod_cast Set.ncard_eq_toFinset_card _ (four_lines_finite V)
  refine ⟨V, hVS, ?_, ?_⟩
  · have hpair : 12 * LV.card ≤ V.card * (V.card - 1) := pair_bound hLV_mem
    have hpair_sq : 12 * LV.card ≤ V.card * V.card :=
      hpair.trans (Nat.mul_le_mul_left V.card (Nat.sub_le V.card 1))
    have hpair_real : 12 * (LV.card : ℝ) ≤ (V.card : ℝ) ^ 2 := by
      have hcast : (12 * LV.card : ℝ) ≤ (V.card * V.card : ℝ) := by exact_mod_cast hpair_sq
      nlinarith
    have hterm_nonneg : 0 ≤ (V.card : ℝ) * ((δ / 2) * (S.card : ℝ)) := by positivity
    rw [hLV_card] at hVfeas
    nlinarith
  · intro p hp
    let W := V.erase p
    have hWV : W ⊆ V := Finset.erase_subset p V
    have hWS : W ⊆ S := hWV.trans hVS
    have hWcard : W.card + 1 = V.card := Finset.card_erase_add_one hp
    have hWnot : W ∉ valid := by
      intro hWmem
      have hle := hVmin W hWmem
      omega
    have hWlt : ((linesWithPointsFor 4 (W : Set ℝ²)).ncard : ℝ) <
        (δ / 2) * (S.card : ℝ) ^ 2 + (W.card : ℝ) * ((δ / 2) * (S.card : ℝ)) :=
      lt_of_not_ge fun hge => hWnot (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hWS, hge⟩)
    let LW := (four_lines_finite W).toFinset
    have hLW_card : ((linesWithPointsFor 4 (W : Set ℝ²)).ncard : ℝ) = (LW.card : ℝ) := by
      exact_mod_cast Set.ncard_eq_toFinset_card _ (four_lines_finite W)
    let Ap := LV.filter (fun L => p ∈ L)
    let Anp := LV.filter (fun L => p ∉ L)
    have hsub : Anp ⊆ LW := by
      intro L hL
      obtain ⟨hLV, hpL⟩ := Finset.mem_filter.mp hL
      apply (four_lines_finite W).mem_toFinset.mpr
      apply line_mem_four_of_subset hWV (hLV_mem L hLV)
      intro q hq
      obtain ⟨hqV, hqL⟩ := Finset.mem_filter.mp hq
      refine Finset.mem_erase.mpr ⟨?_, hqV⟩
      rintro rfl
      exact hpL hqL
    have hsplit : LV.card = Ap.card + Anp.card := by
      have hdisj : Disjoint Ap Anp := by
        rw [Finset.disjoint_left]
        intro L hL1 hL2
        exact (Finset.mem_filter.mp hL2).2 (Finset.mem_filter.mp hL1).2
      have hunion : Ap ∪ Anp = LV := by
        ext L
        simp only [Ap, Anp, Finset.mem_union, Finset.mem_filter]
        tauto
      rw [← hunion, Finset.card_union_of_disjoint hdisj]
    have hAnp_le : Anp.card ≤ LW.card := Finset.card_le_card hsub
    have hLV_le : (LV.card : ℝ) ≤ (Ap.card : ℝ) + (LW.card : ℝ) := by
      exact_mod_cast (show LV.card ≤ Ap.card + LW.card by omega)
    have hWcard_real : (W.card : ℝ) + 1 = (V.card : ℝ) := by exact_mod_cast hWcard
    have hV_le_S : (V.card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast Finset.card_le_card hVS
    rw [hLV_card] at hVfeas
    rw [hLW_card] at hWlt
    refine ⟨Ap, ?_, ?_⟩
    · nlinarith
    · intro L hL
      obtain ⟨hLV, hpL⟩ := Finset.mem_filter.mp hL
      exact ⟨hpL, hLV_mem L hLV⟩

/-- In any 4-partite rainbow family `A` of size at least `η |V|²`, pencil packing forces
every part meeting each line once to have linear size `η |V| ≤ |U|`. -/
lemma part_size_lower_bound {V U : Finset ℝ²} {A : Finset (AffineSubspace ℝ ℝ²)} {η : ℝ}
    (hUV : U ⊆ V)
    (hA : ∀ L ∈ A, L ∈ linesWithPointsFor 4 (V : Set ℝ²))
    (hpart : ∀ L ∈ A, (U.filter (fun p => p ∈ L)).card = 1)
    (hdense : η * (V.card : ℝ) ^ 2 ≤ (A.card : ℝ)) :
    η * (V.card : ℝ) ≤ (U.card : ℝ) := by
  by_cases hV0 : V.card = 0
  · simp [hV0]
  · have hVpos : (0 : ℝ) < (V.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hV0
    have hcount : (∑ L ∈ A, (U.filter (fun p => p ∈ L)).card) =
        ∑ p ∈ U, (A.filter (fun L => p ∈ L)).card :=
      Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun L p => p ∈ L)
    have hLHS : (∑ L ∈ A, (U.filter (fun p => p ∈ L)).card) = A.card := by
      simp [Finset.sum_congr rfl hpart]
    have hnat : 3 * A.card ≤ U.card * V.card := by
      calc
        3 * A.card = 3 * ∑ p ∈ U, (A.filter (fun L => p ∈ L)).card := by rw [← hcount, hLHS]
        _ = ∑ p ∈ U, 3 * (A.filter (fun L => p ∈ L)).card := Finset.mul_sum ..
        _ ≤ ∑ _p ∈ U, (V.card - 1) := Finset.sum_le_sum fun p hp => pencil_bound hA (hUV hp)
        _ = U.card * (V.card - 1) := by simp
        _ ≤ U.card * V.card := Nat.mul_le_mul_left U.card (Nat.sub_le V.card 1)
    have hreal : 3 * (A.card : ℝ) ≤ (U.card : ℝ) * (V.card : ℝ) := by exact_mod_cast hnat
    nlinarith

lemma configuration_bound (h1 : H1) (h2 : H2) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ S : Finset ℝ², N ≤ S.card → NonCollinearFor 5 (S : Set ℝ²) →
      ((linesWithPointsFor 4 (S : Set ℝ²)).ncard : ℝ) ≤ ε * (S.card : ℝ) ^ 2 := by
  obtain ⟨η, hη, N1, hreg⟩ := h1 (ε / 2) (half_pos hε)
  obtain ⟨N2, hsparse⟩ := h2 η hη
  let M : ℕ := max N1 N2
  obtain ⟨K, hK⟩ := exists_nat_gt ((M : ℝ) ^ 2 / (6 * ε))
  refine ⟨max K 1, ?_⟩
  intro S hS_card hS_nc
  by_contra! hlarge
  obtain ⟨V, hVS, hVsize, hVdeg⟩ := min_degree_core hε hlarge.le
  have hK_le : K ≤ S.card := (le_max_left K 1).trans hS_card
  have h1_le : 1 ≤ S.card := (le_max_right K 1).trans hS_card
  have hM_le_V : M ≤ V.card := by
    have h6ε : 0 < 6 * ε := by positivity
    have hMK : (M : ℝ) ^ 2 < (K : ℝ) * (6 * ε) := (div_lt_iff₀ h6ε).mp hK
    have hKS : (K : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hK_le
    have h1S : (1 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast h1_le
    have hS_sq : (S.card : ℝ) ≤ (S.card : ℝ) ^ 2 := by nlinarith
    have hMV_sq : (M : ℝ) ^ 2 ≤ (V.card : ℝ) ^ 2 := by nlinarith
    have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    have hV0 : (0 : ℝ) ≤ (V.card : ℝ) := Nat.cast_nonneg V.card
    have hMV_real : (M : ℝ) ≤ (V.card : ℝ) := by nlinarith
    exact_mod_cast hMV_real
  have hN1_le : N1 ≤ V.card := (le_max_left N1 N2).trans hM_le_V
  have hN2_le : N2 ≤ V.card := (le_max_right N1 N2).trans hM_le_V
  have hV_nc : NonCollinearFor 5 (V : Set ℝ²) := hS_nc.subset (Finset.coe_subset.mpr hVS)
  obtain ⟨V0, V1, V2, V3, hV0, hV1, hV2, hV3,
      hd01, hd02, hd03, hd12, hd13, hd23, A, hAdense, hAprop, hAdeg⟩ :=
    hreg V hN1_le hV_nc hVdeg
  have hAlines : ∀ L ∈ A, L ∈ linesWithPointsFor 4 (V : Set ℝ²) :=
    fun L hL => (hAprop L hL).1
  have hV0_sz : η * (V.card : ℝ) ≤ (V0.card : ℝ) :=
    part_size_lower_bound hV0 hAlines (fun L hL => (hAprop L hL).2.1) hAdense
  have hV1_sz : η * (V.card : ℝ) ≤ (V1.card : ℝ) :=
    part_size_lower_bound hV1 hAlines (fun L hL => (hAprop L hL).2.2.1) hAdense
  have hV2_sz : η * (V.card : ℝ) ≤ (V2.card : ℝ) :=
    part_size_lower_bound hV2 hAlines (fun L hL => (hAprop L hL).2.2.2.1) hAdense
  have hV3_sz : η * (V.card : ℝ) ≤ (V3.card : ℝ) :=
    part_size_lower_bound hV3 hAlines (fun L hL => (hAprop L hL).2.2.2.2) hAdense
  have hlt := hsparse V V0 V1 V2 V3 hN2_le hV_nc
    hV0 hV1 hV2 hV3 hd01 hd02 hd03 hd12 hd13 hd23
    hV0_sz hV1_sz hV2_sz hV3_sz A hAprop hAdeg
  linarith

theorem main : H1 → H2 → type_of% @Erdos101.erdos_101 := by
  intro h1 h2
  apply IsLittleO.of_bound
  intro ε hε
  obtain ⟨N, hbound⟩ := configuration_bound h1 h2 ε hε
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (sq_nonneg _)]
  have hmax : Erdos101.numLinesWithFourPointMax n ≤ ⌊ε * (n : ℝ) ^ 2⌋₊ := by
    apply csSup_le'
    rintro b ⟨S, hcard, hfin, hS, rfl⟩
    let T := hfin.toFinset
    have he : (T : Set ℝ²) = S := hfin.coe_toFinset
    have hTcard : T.card = n := (Set.ncard_eq_toFinset_card S hfin).symm.trans hcard
    apply Nat.le_floor
    have h := hbound T (hTcard ▸ hn) (he ▸ hS)
    simpa only [he, hTcard] using h
  exact (Nat.cast_le.mpr hmax).trans (Nat.floor_le (mul_nonneg hε.le (sq_nonneg _)))

end OMA.R_Erdos101_erdos_101_R4
