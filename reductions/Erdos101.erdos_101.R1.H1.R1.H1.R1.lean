import OMAReductions.R_Erdos101_erdos_101_R1_H1_R1

/-!
# Core pruning and 3-partite collinear triple reduction

We reduce the unmarked four-point-line capture problem to a 3-partite
collinear-triple inverse problem without reference to the ambient point set.
First we prove unconditionally that any subset containing at least three points
on each line of a positive-density family of four-point lines contains a
minimum-cardinality high-degree core whose size is comparable to the ambient
set and in which every point lies on linearly many surviving lines.
The first hypothesis extracts a positive-density 3-partite family of
line-distinct collinear triples from this core, and the second hypothesis
captures a positive proportion of those points on a bounded-degree curve.
-/

namespace OMA.R_Erdos101_erdos_101_R1_H1_R1_H1_R1

open EuclideanGeometry MvPolynomial
open scoped Classical

/-- From a high-degree point-line core in which every line is spanned by two
points of the core and contains at least three core points, one can extract
a positive-density family of line-distinct collinear triples across three
pairwise disjoint subsets of the core. -/
def H1 : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ η : ℝ, 0 < η ∧ ∃ N : ℕ,
    ∀ W : Finset ℝ², N ≤ W.card → NonCollinearFor 5 (W : Set ℝ²) →
    ∀ A : Finset (AffineSubspace ℝ ℝ²), τ * (W.card : ℝ)^2 ≤ A.card →
      (∀ L ∈ A, (∃ p ∈ W, ∃ q ∈ W, p ≠ q ∧ L = line[ℝ, p, q]) ∧
        3 ≤ (W.filter (fun p => p ∈ L)).card) →
      (∀ p ∈ W, τ * (W.card : ℝ) ≤ (A.filter (fun L => p ∈ L)).card) →
      ∃ W1 W2 W3 : Finset ℝ²,
        W1 ⊆ W ∧ W2 ⊆ W ∧ W3 ⊆ W ∧
        Disjoint W1 W2 ∧ Disjoint W1 W3 ∧ Disjoint W2 W3 ∧
        ∃ T : Finset (ℝ² × ℝ² × ℝ²), η * (W.card : ℝ)^2 ≤ T.card ∧
          (∀ e ∈ T, e.1 ∈ W1 ∧ e.2.1 ∈ W2 ∧ e.2.2 ∈ W3 ∧ e.2.2 ∈ line[ℝ, e.1, e.2.1]) ∧
          (T : Set (ℝ² × ℝ² × ℝ²)).InjOn (fun e => line[ℝ, e.1, e.2.1])

/-- Three pairwise disjoint planar point sets with no five collinear points
and quadratically many line-distinct collinear triples place a positive
proportion of their union on a curve of bounded degree. -/
def H2 : Prop :=
  ∀ η : ℝ, 0 < η → ∃ d : ℕ, ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ,
    ∀ W1 W2 W3 : Finset ℝ²,
      Disjoint W1 W2 → Disjoint W1 W3 → Disjoint W2 W3 →
      N ≤ (W1 ∪ W2 ∪ W3).card →
      NonCollinearFor 5 ((W1 ∪ W2 ∪ W3 : Finset ℝ²) : Set ℝ²) →
      ∀ T : Finset (ℝ² × ℝ² × ℝ²),
        η * ((W1 ∪ W2 ∪ W3).card : ℝ)^2 ≤ T.card →
        (∀ e ∈ T, e.1 ∈ W1 ∧ e.2.1 ∈ W2 ∧ e.2.2 ∈ W3 ∧ e.2.2 ∈ line[ℝ, e.1, e.2.1]) →
        (T : Set (ℝ² × ℝ² × ℝ²)).InjOn (fun e => line[ℝ, e.1, e.2.1]) →
        ∃ F : MvPolynomial (Fin 2) ℝ, F ≠ 0 ∧ F.totalDegree ≤ d ∧
          c * ((W1 ∪ W2 ∪ W3).card : ℝ) ≤
            ((W1 ∪ W2 ∪ W3).filter (fun p => eval (fun i => p i) F = 0)).card

/-- Two distinct points on a spanned line uniquely determine that line. -/
lemma line_eq_of_span {L : AffineSubspace ℝ ℝ²}
    (hL : ∃ a b : ℝ², L = line[ℝ, a, b]) {p q : ℝ²}
    (hp : p ∈ L) (hq : q ∈ L) (hne : p ≠ q) : line[ℝ, p, q] = L := by
  obtain ⟨a, b, rfl⟩ := hL
  exact affineSpan_pair_eq_of_mem_of_mem_of_ne hp hq hne

/-- Distinct lines through a core point contribute disjoint sets of at least
two additional points of the core. -/
lemma sub_pencil_bound {W : Finset ℝ²} {B : Finset (AffineSubspace ℝ ℝ²)}
    (hB : ∀ L ∈ B, (∃ a b : ℝ², L = line[ℝ, a, b]) ∧ 3 ≤ (W.filter (fun q => q ∈ L)).card)
    {p : ℝ²} (hp : p ∈ W) :
    2 * (B.filter (fun L => p ∈ L)).card ≤ W.card - 1 := by
  let pencil := B.filter (fun L => p ∈ L)
  let others := fun L : AffineSubspace ℝ ℝ² => (W.filter (fun q => q ∈ L)).erase p
  have hdisj : (pencil : Set (AffineSubspace ℝ ℝ²)).PairwiseDisjoint others := by
    intro L hL M hM hne
    obtain ⟨hLB, hpL⟩ := Finset.mem_filter.mp hL
    obtain ⟨hMB, hpM⟩ := Finset.mem_filter.mp hM
    apply Finset.disjoint_left.mpr
    intro q hqL hqM
    obtain ⟨hqp, hqL'⟩ := Finset.mem_erase.mp hqL
    have hqM' := (Finset.mem_erase.mp hqM).2
    exact hne ((line_eq_of_span (hB L hLB).1 hpL (Finset.mem_filter.mp hqL').2 hqp.symm).symm.trans
      (line_eq_of_span (hB M hMB).1 hpM (Finset.mem_filter.mp hqM').2 hqp.symm))
  have hcard (L) (hL : L ∈ pencil) : 2 ≤ (others L).card := by
    obtain ⟨hLB, hpL⟩ := Finset.mem_filter.mp hL
    have h3 := (hB L hLB).2
    rw [show (others L).card = (W.filter (fun q => q ∈ L)).card - 1 from
      Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hp, hpL⟩)]
    omega
  have hsub : pencil.biUnion others ⊆ W.erase p := by
    intro q hq
    obtain ⟨L, _, hq'⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hq'
    exact Finset.mem_erase.mpr ⟨hne, (Finset.mem_filter.mp hmem).1⟩
  calc
    2 * pencil.card = ∑ _L ∈ pencil, 2 := by simp [mul_comm]
    _ ≤ ∑ L ∈ pencil, (others L).card := Finset.sum_le_sum hcard
    _ = (pencil.biUnion others).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (W.erase p).card := Finset.card_le_card hsub
    _ = W.card - 1 := Finset.card_erase_of_mem hp

/-- Counting incidences of a family of lines with at least three points in W
gives the quadratic size bound 6 |B| ≤ |W| (|W| - 1). -/
lemma sub_pair_bound {W : Finset ℝ²} {B : Finset (AffineSubspace ℝ ℝ²)}
    (hB : ∀ L ∈ B, (∃ a b : ℝ², L = line[ℝ, a, b]) ∧ 3 ≤ (W.filter (fun q => q ∈ L)).card) :
    6 * B.card ≤ W.card * (W.card - 1) := by
  have hcount : (∑ L ∈ B, (W.filter (fun p => p ∈ L)).card) =
      ∑ p ∈ W, (B.filter (fun L => p ∈ L)).card :=
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun L p => p ∈ L)
  have hlow : 3 * B.card ≤ ∑ L ∈ B, (W.filter (fun p => p ∈ L)).card := by
    calc
      3 * B.card = ∑ _L ∈ B, 3 := by simp [mul_comm]
      _ ≤ ∑ L ∈ B, (W.filter (fun p => p ∈ L)).card := Finset.sum_le_sum (fun L hL => (hB L hL).2)
  calc
    6 * B.card = 2 * (3 * B.card) := by omega
    _ ≤ 2 * ∑ p ∈ W, (B.filter (fun L => p ∈ L)).card := by
      rw [← hcount]
      exact Nat.mul_le_mul_left 2 hlow
    _ = ∑ p ∈ W, 2 * (B.filter (fun L => p ∈ L)).card := Finset.mul_sum ..
    _ ≤ ∑ _p ∈ W, (W.card - 1) := Finset.sum_le_sum (fun p hp => sub_pencil_bound hB hp)
    _ = W.card * (W.card - 1) := by simp

/-- Minimum-cardinality core pruning: pass from (U, A) to a subset W ⊆ U and
its surviving lines B ⊆ A so that every point of W lies on at least (δ / 2)|S|
lines of B, |B| ≥ (δ / 2)|S|^2, and |W|^2 ≥ 3 δ |S|^2. -/
lemma high_degree_core {δ : ℝ} (hδ : 0 < δ) {S U : Finset ℝ²} (hUS : U ⊆ S)
    {A : Finset (AffineSubspace ℝ ℝ²)} (hdense : δ * (S.card : ℝ)^2 ≤ A.card)
    (hlines : ∀ L ∈ A, L ∈ linesWithPointsFor 4 (S : Set ℝ²) ∧ 3 ≤ (U.filter (fun p => p ∈ L)).card) :
    ∃ W ⊆ U, ∃ B ⊆ A,
      (δ / 2) * (S.card : ℝ)^2 ≤ (B.card : ℝ) ∧
      3 * δ * (S.card : ℝ)^2 ≤ (W.card : ℝ)^2 ∧
      (∀ L ∈ B, (∃ p ∈ W, ∃ q ∈ W, p ≠ q ∧ L = line[ℝ, p, q]) ∧
        3 ≤ (W.filter (fun p => p ∈ L)).card) ∧
      (∀ p ∈ W, (δ / 2) * (S.card : ℝ) ≤ ((B.filter (fun L => p ∈ L)).card : ℝ)) := by
  let surv (W : Finset ℝ²) := A.filter (fun L => 3 ≤ (W.filter (fun p => p ∈ L)).card)
  let good (W : Finset ℝ²) : Prop :=
    (δ / 2) * (S.card : ℝ)^2 + (W.card : ℝ) * ((δ / 2) * (S.card : ℝ)) ≤ ((surv W).card : ℝ)
  let C := U.powerset.filter good
  have hUgood : good U := by
    have hsurvU : surv U = A := by
      ext L
      simp only [surv, Finset.mem_filter, and_iff_left_iff_imp]
      exact fun hL => (hlines L hL).2
    have hUleS : (U.card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast Finset.card_le_card hUS
    have hnn : 0 ≤ (δ / 2) * (S.card : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_right hUleS hnn
    dsimp [good]
    rw [hsurvU]
    nlinarith only [hdense, hmul]
  have hCne : C.Nonempty := ⟨U, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.Subset.rfl, hUgood⟩⟩
  obtain ⟨W, hWC, hWmin⟩ := Finset.exists_min_image C Finset.card hCne
  obtain ⟨hWU', hWgood⟩ := Finset.mem_filter.mp hWC
  have hWU : W ⊆ U := Finset.mem_powerset.mp hWU'
  let B := surv W
  have hBA : B ⊆ A := Finset.filter_subset ..
  have hBdense : (δ / 2) * (S.card : ℝ)^2 ≤ (B.card : ℝ) := by
    have hnn : 0 ≤ (W.card : ℝ) * ((δ / 2) * (S.card : ℝ)) := by positivity
    dsimp [good] at hWgood
    linarith
  have hBlines : ∀ L ∈ B, (∃ p ∈ W, ∃ q ∈ W, p ≠ q ∧ L = line[ℝ, p, q]) ∧
      3 ≤ (W.filter (fun p => p ∈ L)).card := by
    intro L hL
    obtain ⟨hLA, h3⟩ := Finset.mem_filter.mp hL
    refine ⟨?_, h3⟩
    have h1 : 1 < (W.filter (fun p => p ∈ L)).card := by omega
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp h1
    obtain ⟨hpW, hpL⟩ := Finset.mem_filter.mp hp
    obtain ⟨hqW, hqL⟩ := Finset.mem_filter.mp hq
    exact ⟨p, hpW, q, hqW, hpq,
      (OMA.R_Erdos101_erdos_101_R1.line_through (hlines L hLA).1 hpL hqL hpq).symm⟩
  have hWsq : 3 * δ * (S.card : ℝ)^2 ≤ (W.card : ℝ)^2 := by
    have hpair : 6 * B.card ≤ W.card * (W.card - 1) := sub_pair_bound (fun L hL => by
      obtain ⟨⟨p, _, q, _, _, hEq⟩, h3⟩ := hBlines L hL
      exact ⟨⟨p, q, hEq⟩, h3⟩)
    have hle : 6 * B.card ≤ W.card * W.card :=
      hpair.trans (Nat.mul_le_mul_left W.card (Nat.sub_le W.card 1))
    have hR : 6 * (B.card : ℝ) ≤ (W.card : ℝ)^2 := by
      have : (6 * B.card : ℝ) ≤ (W.card * W.card : ℝ) := by exact_mod_cast hle
      nlinarith
    nlinarith only [hBdense, hR]
  have hdeg : ∀ p ∈ W, (δ / 2) * (S.card : ℝ) ≤ ((B.filter (fun L => p ∈ L)).card : ℝ) := by
    intro p hp
    let W' := W.erase p
    have hW'U : W' ⊆ U := (Finset.erase_subset p W).trans hWU
    have hW'lt : W'.card < W.card := Finset.card_erase_lt_of_mem hp
    have hnotgood : ¬ good W' := by
      intro hg
      have hle := hWmin W' (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hW'U, hg⟩)
      omega
    have hW'bad : ((surv W').card : ℝ) <
        (δ / 2) * (S.card : ℝ)^2 + (W'.card : ℝ) * ((δ / 2) * (S.card : ℝ)) :=
      lt_of_not_ge hnotgood
    have hcov : B ⊆ surv W' ∪ B.filter (fun L => p ∈ L) := by
      intro L hL
      by_cases hpL : p ∈ L
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hL, hpL⟩)
      · apply Finset.mem_union_left
        obtain ⟨hLA, h3⟩ := Finset.mem_filter.mp hL
        refine Finset.mem_filter.mpr ⟨hLA, ?_⟩
        have heq : W'.filter (fun q => q ∈ L) = W.filter (fun q => q ∈ L) := by
          ext q
          simp only [W', Finset.mem_filter, Finset.mem_erase]
          exact ⟨fun ⟨⟨_, hqW⟩, hqL⟩ => ⟨hqW, hqL⟩,
            fun ⟨hqW, hqL⟩ => ⟨⟨fun hqp => hpL (hqp ▸ hqL), hqW⟩, hqL⟩⟩
        rw [heq]
        exact h3
    have hcard : B.card ≤ (surv W').card + (B.filter (fun L => p ∈ L)).card :=
      (Finset.card_le_card hcov).trans (Finset.card_union_le ..)
    have hcardR : (B.card : ℝ) ≤ ((surv W').card : ℝ) + ((B.filter (fun L => p ∈ L)).card : ℝ) := by
      exact_mod_cast hcard
    have hWcard : (W'.card : ℝ) + 1 = (W.card : ℝ) := by
      exact_mod_cast Finset.card_erase_add_one hp
    dsimp [good] at hWgood
    nlinarith only [hWgood, hW'bad, hcardR, hWcard]
  exact ⟨W, hWU, B, hBA, hBdense, hWsq, hBlines, hdeg⟩

/-- A line-injective family of collinear triples in W1 × W2 × W3 injects into
W1 × W2 and therefore has size at most |W1 ∪ W2 ∪ W3|^2. -/
lemma tripartite_card_bound {W1 W2 W3 : Finset ℝ²} {T : Finset (ℝ² × ℝ² × ℝ²)}
    (hmem : ∀ e ∈ T, e.1 ∈ W1 ∧ e.2.1 ∈ W2 ∧ e.2.2 ∈ W3 ∧ e.2.2 ∈ line[ℝ, e.1, e.2.1])
    (hinj : (T : Set (ℝ² × ℝ² × ℝ²)).InjOn (fun e => line[ℝ, e.1, e.2.1])) :
    T.card ≤ (W1 ∪ W2 ∪ W3).card ^ 2 := by
  let proj : ℝ² × ℝ² × ℝ² → ℝ² × ℝ² := fun e => (e.1, e.2.1)
  have hpinj : (T : Set (ℝ² × ℝ² × ℝ²)).InjOn proj := by
    intro e he e' he' hEq
    obtain ⟨h1, h2⟩ := Prod.mk.inj hEq
    exact hinj he he' (by dsimp only; rw [h1, h2])
  have hsub : T.image proj ⊆ W1 ×ˢ W2 := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_product.mpr ⟨(hmem e he).1, (hmem e he).2.1⟩
  have h1 : T.card ≤ W1.card * W2.card := by
    calc
      T.card = (T.image proj).card := (Finset.card_image_of_injOn hpinj).symm
      _ ≤ (W1 ×ˢ W2).card := Finset.card_le_card hsub
      _ = W1.card * W2.card := Finset.card_product W1 W2
  have hW1 : W1.card ≤ (W1 ∪ W2 ∪ W3).card :=
    Finset.card_le_card (Finset.subset_union_left.trans Finset.subset_union_left)
  have hW2 : W2.card ≤ (W1 ∪ W2 ∪ W3).card :=
    Finset.card_le_card (Finset.subset_union_right.trans Finset.subset_union_left)
  calc
    T.card ≤ W1.card * W2.card := h1
    _ ≤ (W1 ∪ W2 ∪ W3).card * (W1 ∪ W2 ∪ W3).card := Nat.mul_le_mul hW1 hW2
    _ = (W1 ∪ W2 ∪ W3).card ^ 2 := by ring

theorem main : H1 → H2 → OMA.R_Erdos101_erdos_101_R1_H1_R1.H1 := by
  intro hpart hcurve δ hδ
  let τ : ℝ := δ / 2
  have hτ : 0 < τ := half_pos hδ
  obtain ⟨η, hη, N1, hN1⟩ := hpart τ hτ
  obtain ⟨d, c, hc, N2, hN2⟩ := hcurve η hη
  let α : ℝ := Real.sqrt (3 * δ)
  let β : ℝ := Real.sqrt η
  have hα : 0 < α := Real.sqrt_pos.mpr (by positivity)
  have hβ : 0 < β := Real.sqrt_pos.mpr hη
  obtain ⟨K1, hK1⟩ := exists_nat_gt ((N1 : ℝ) / α)
  obtain ⟨K2, hK2⟩ := exists_nat_gt ((N2 : ℝ) / (β * α))
  refine ⟨d, c * β * α, by positivity, max 1 (max K1 K2), ?_⟩
  intro S U hSN hUS hcap A hdense hlines
  obtain ⟨W, hWU, B, hBA, hBdense, hWsq, hBlines, hWdeg⟩ :=
    high_degree_core hδ hUS hdense hlines
  have hWS : W ⊆ S := hWU.trans hUS
  have hWleS : (W.card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast Finset.card_le_card hWS
  have hαS : α * (S.card : ℝ) ≤ (W.card : ℝ) := by
    have hsq : (α * (S.card : ℝ))^2 ≤ (W.card : ℝ)^2 := by
      have hα2 : α ^ 2 = 3 * δ := Real.sq_sqrt (by positivity)
      calc
        (α * (S.card : ℝ))^2 = α ^ 2 * (S.card : ℝ)^2 := by ring
        _ = 3 * δ * (S.card : ℝ)^2 := by rw [hα2]
        _ ≤ (W.card : ℝ)^2 := hWsq
    nlinarith [sq_nonneg ((W.card : ℝ) - α * (S.card : ℝ)),
      mul_nonneg hα.le (Nat.cast_nonneg S.card), Nat.cast_nonneg (α := ℝ) W.card]
  have hWN1 : N1 ≤ W.card := by
    have hSK1 : (K1 : ℝ) ≤ (S.card : ℝ) := by
      exact_mod_cast ((le_max_left K1 K2).trans ((le_max_right 1 (max K1 K2)).trans hSN))
    have hN1lt : (N1 : ℝ) < α * (K1 : ℝ) := by
      have := (div_lt_iff₀ hα).mp hK1
      linarith
    have hN1leW : (N1 : ℝ) ≤ (W.card : ℝ) := by
      nlinarith only [hN1lt, hSK1, hαS, hα]
    exact_mod_cast hN1leW
  have hBdenseW : τ * (W.card : ℝ)^2 ≤ (B.card : ℝ) := by
    have hsq : (W.card : ℝ)^2 ≤ (S.card : ℝ)^2 := by
      nlinarith only [hWleS, Nat.cast_nonneg (α := ℝ) W.card, Nat.cast_nonneg (α := ℝ) S.card]
    have hmul := mul_le_mul_of_nonneg_left hsq hτ.le
    exact hmul.trans hBdense
  have hWdegW : ∀ p ∈ W, τ * (W.card : ℝ) ≤ ((B.filter (fun L => p ∈ L)).card : ℝ) := by
    intro p hp
    exact (mul_le_mul_of_nonneg_left hWleS hτ.le).trans (hWdeg p hp)
  obtain ⟨W1, W2, W3, h1W, h2W, h3W, hd12, hd13, hd23, T, hTdense, hTmem, hTinj⟩ :=
    hN1 W hWN1 (hcap.subset (Finset.coe_subset.mpr hWS)) B hBdenseW hBlines hWdegW
  let V := W1 ∪ W2 ∪ W3
  have hVW : V ⊆ W := Finset.union_subset (Finset.union_subset h1W h2W) h3W
  have hVU : V ⊆ U := hVW.trans hWU
  have hVS : V ⊆ S := hVU.trans hUS
  have hVleW : (V.card : ℝ) ≤ (W.card : ℝ) := by exact_mod_cast Finset.card_le_card hVW
  have hTleVsq : (T.card : ℝ) ≤ (V.card : ℝ)^2 := by
    exact_mod_cast tripartite_card_bound hTmem hTinj
  have hβW : β * (W.card : ℝ) ≤ (V.card : ℝ) := by
    have hβ2 : β ^ 2 = η := Real.sq_sqrt hη.le
    have hsq : (β * (W.card : ℝ))^2 ≤ (V.card : ℝ)^2 := by
      calc
        (β * (W.card : ℝ))^2 = β ^ 2 * (W.card : ℝ)^2 := by ring
        _ = η * (W.card : ℝ)^2 := by rw [hβ2]
        _ ≤ (T.card : ℝ) := hTdense
        _ ≤ (V.card : ℝ)^2 := hTleVsq
    nlinarith [mul_nonneg hβ.le (Nat.cast_nonneg W.card), Nat.cast_nonneg (α := ℝ) V.card]
  have hβαS : (β * α) * (S.card : ℝ) ≤ (V.card : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hαS hβ.le
    nlinarith only [hmul, hβW]
  have hVN2 : N2 ≤ V.card := by
    have hSK2 : (K2 : ℝ) ≤ (S.card : ℝ) := by
      exact_mod_cast ((le_max_right K1 K2).trans ((le_max_right 1 (max K1 K2)).trans hSN))
    have hN2lt : (N2 : ℝ) < (β * α) * (K2 : ℝ) := by
      have := (div_lt_iff₀ (mul_pos hβ hα)).mp hK2
      linarith
    have hN2leV : (N2 : ℝ) ≤ (V.card : ℝ) := by
      have hβα : 0 < β * α := mul_pos hβ hα
      nlinarith only [hN2lt, hSK2, hβαS, hβα]
    exact_mod_cast hN2leV
  have hTdenseV : η * (V.card : ℝ)^2 ≤ (T.card : ℝ) := by
    have hsq : (V.card : ℝ)^2 ≤ (W.card : ℝ)^2 := by
      nlinarith only [hVleW, Nat.cast_nonneg (α := ℝ) V.card, Nat.cast_nonneg (α := ℝ) W.card]
    exact (mul_le_mul_of_nonneg_left hsq hη.le).trans hTdense
  obtain ⟨F, hF, hdeg, hcapV⟩ :=
    hN2 W1 W2 W3 hd12 hd13 hd23 hVN2 (hcap.subset (Finset.coe_subset.mpr hVS)) T hTdenseV hTmem hTinj
  refine ⟨F, hF, hdeg, ?_⟩
  have hfilt : (V.filter (fun p => eval (fun i => p i) F = 0)).card ≤
      (U.filter (fun p => eval (fun i => p i) F = 0)).card :=
    Finset.card_le_card (Finset.filter_subset_filter _ hVU)
  have hfiltR : ((V.filter (fun p => eval (fun i => p i) F = 0)).card : ℝ) ≤
      ((U.filter (fun p => eval (fun i => p i) F = 0)).card : ℝ) := by exact_mod_cast hfilt
  have hcmul := mul_le_mul_of_nonneg_left hβαS hc.le
  nlinarith only [hcmul, hcapV, hfiltR]

end OMA.R_Erdos101_erdos_101_R1_H1_R1_H1_R1
