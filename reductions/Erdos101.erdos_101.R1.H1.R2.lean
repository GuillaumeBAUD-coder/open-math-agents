import OMAReductions.R_Erdos101_erdos_101_R1

/-!
# Rainbow four-partite core regularization for four-point lines

Rather than peeling off curves iteratively, we first ask for a combinatorial
rainbow four-partite extraction: from any dense family of four-point lines
meeting a distinguished subset, extract pairwise disjoint parts with the first
part inside the distinguished subset so that a positive-density subfamily of
lines meets each part in exactly one point.

Given such a rainbow family, iterative minimum-degree pruning across all four
parts removes fewer than half the lines while preserving the rainbow incidence
structure and forcing every surviving point in all four parts to lie on linearly
many surviving lines. Pairwise disjoint pencils then force each of the four
parts to have linear size. This reduces marked bounded-degree curve capture to
the regularized four-partite rainbow setting.
-/

namespace OMA.R_Erdos101_erdos_101_R1_H1_R2

open EuclideanGeometry MvPolynomial
open scoped Classical

/-- Rainbow four-partite extraction: any quadratic-size family of four-point
lines meeting a subset T contains a quadratic-size subfamily that is rainbow
across four pairwise disjoint subsets of S, with the first subset inside T. -/
def H1 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧ ∃ N : ℕ,
    ∀ S T : Finset ℝ², N ≤ S.card → T ⊆ S → NonCollinearFor 5 (S : Set ℝ²) →
    ∀ A : Finset (AffineSubspace ℝ ℝ²), δ * (S.card : ℝ) ^ 2 ≤ A.card →
      (∀ L ∈ A, L ∈ linesWithPointsFor 4 (S : Set ℝ²) ∧ ∃ p ∈ T, p ∈ L) →
      ∃ V0 V1 V2 V3 : Finset ℝ², V0 ⊆ T ∧ V1 ⊆ S ∧ V2 ⊆ S ∧ V3 ⊆ S ∧
        Disjoint V0 V1 ∧ Disjoint V0 V2 ∧ Disjoint V0 V3 ∧
        Disjoint V1 V2 ∧ Disjoint V1 V3 ∧ Disjoint V2 V3 ∧
        ∃ B ⊆ A, η * (S.card : ℝ) ^ 2 ≤ B.card ∧
          ∀ L ∈ B, (V0.filter (fun p => p ∈ L)).card = 1 ∧
            (V1.filter (fun p => p ∈ L)).card = 1 ∧
            (V2.filter (fun p => p ∈ L)).card = 1 ∧
            (V3.filter (fun p => p ∈ L)).card = 1

/-- Rainbow four-partite regularized curve capture: in a four-partite rainbow
configuration of four-point lines where all four parts have linear size and
every point in all four parts has linear degree, a bounded-degree nonzero curve
captures a linear number of points in the first part. -/
def H2 : Prop :=
  ∀ η : ℝ, 0 < η → ∃ d : ℕ, ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ,
    ∀ S W0 W1 W2 W3 : Finset ℝ², N ≤ S.card →
      W0 ⊆ S → W1 ⊆ S → W2 ⊆ S → W3 ⊆ S →
      Disjoint W0 W1 → Disjoint W0 W2 → Disjoint W0 W3 →
      Disjoint W1 W2 → Disjoint W1 W3 → Disjoint W2 W3 →
      NonCollinearFor 5 (S : Set ℝ²) →
      η * S.card ≤ W0.card → η * S.card ≤ W1.card →
      η * S.card ≤ W2.card → η * S.card ≤ W3.card →
      ∀ B : Finset (AffineSubspace ℝ ℝ²), η * (S.card : ℝ) ^ 2 ≤ B.card →
        (∀ L ∈ B, L ∈ linesWithPointsFor 4 (S : Set ℝ²) ∧
          (W0.filter (fun p => p ∈ L)).card = 1 ∧
          (W1.filter (fun p => p ∈ L)).card = 1 ∧
          (W2.filter (fun p => p ∈ L)).card = 1 ∧
          (W3.filter (fun p => p ∈ L)).card = 1) →
        (∀ p ∈ W0 ∪ W1 ∪ W2 ∪ W3, η * S.card ≤ (B.filter (fun L => p ∈ L)).card) →
        ∃ F : MvPolynomial (Fin 2) ℝ, F ≠ 0 ∧ F.totalDegree ≤ d ∧
          c * S.card ≤ (W0.filter (fun p => eval (fun i => p i) F = 0)).card

/-- Double counting from linear-degree pencils in T yields quadratically many
four-point lines meeting T. -/
lemma dense_lines_meeting {S T : Finset ℝ²} {τ : ℝ} (hτ : 0 < τ)
    (hTS : T ⊆ S) (hT : τ * S.card ≤ T.card)
    (hstars : ∀ p ∈ T, ∃ Ap : Finset (AffineSubspace ℝ ℝ²), τ * S.card ≤ Ap.card ∧
      ∀ L ∈ Ap, p ∈ L ∧ L ∈ linesWithPointsFor 4 (S : Set ℝ²)) :
    ∃ A : Finset (AffineSubspace ℝ ℝ²), (τ ^ 2 / 4) * (S.card : ℝ) ^ 2 ≤ A.card ∧
      ∀ L ∈ A, L ∈ linesWithPointsFor 4 (S : Set ℝ²) ∧ ∃ p ∈ T, p ∈ L := by
  let Aall := (OMA.R_Erdos101_erdos_101_R1.four_lines_finite S).toFinset
  let A := Aall.filter (fun L => ∃ p ∈ T, p ∈ L)
  have hA : ∀ L ∈ A, L ∈ linesWithPointsFor 4 (S : Set ℝ²) ∧ ∃ p ∈ T, p ∈ L := by
    intro L hL
    obtain ⟨hLall, hmeet⟩ := Finset.mem_filter.mp hL
    exact ⟨((OMA.R_Erdos101_erdos_101_R1.four_lines_finite S).mem_toFinset).mp hLall, hmeet⟩
  have hdeg : ∀ p ∈ T, τ * (S.card : ℝ) ≤ ((A.filter (fun L => p ∈ L)).card : ℝ) := by
    intro p hp
    obtain ⟨Ap, hApcard, hAp⟩ := hstars p hp
    have hsub : Ap ⊆ A.filter (fun L => p ∈ L) := by
      intro L hL
      obtain ⟨hpL, hfour⟩ := hAp L hL
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, ⟨p, hp, hpL⟩⟩, hpL⟩
      exact ((OMA.R_Erdos101_erdos_101_R1.four_lines_finite S).mem_toFinset).mpr hfour
    exact hApcard.trans (by exact_mod_cast Finset.card_le_card hsub)
  have hcount : (∑ p ∈ T, (A.filter (fun L => p ∈ L)).card) =
      ∑ L ∈ A, (T.filter (fun p => p ∈ L)).card :=
    (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun L p => p ∈ L)).symm
  have hupper : (∑ p ∈ T, (A.filter (fun L => p ∈ L)).card) ≤ 4 * A.card := by
    rw [hcount]
    calc
      ∑ L ∈ A, (T.filter (fun p => p ∈ L)).card
        ≤ ∑ _L ∈ A, 4 := Finset.sum_le_sum fun L hL =>
          (Finset.card_le_card (Finset.filter_subset_filter _ hTS)).trans_eq
            (OMA.R_Erdos101_erdos_101_R1.four_points (hA L hL).1)
      _ = 4 * A.card := by simp [mul_comm]
  have hlower : (τ * (S.card : ℝ)) * (τ * (S.card : ℝ)) ≤
      ∑ p ∈ T, ((A.filter (fun L => p ∈ L)).card : ℝ) := by
    calc
      (τ * (S.card : ℝ)) * (τ * (S.card : ℝ))
        ≤ (T.card : ℝ) * (τ * (S.card : ℝ)) :=
          mul_le_mul_of_nonneg_right hT (by positivity)
      _ = ∑ _p ∈ T, (τ * (S.card : ℝ)) := by simp
      _ ≤ ∑ p ∈ T, ((A.filter (fun L => p ∈ L)).card : ℝ) :=
          Finset.sum_le_sum hdeg
  have hupperR : (∑ p ∈ T, ((A.filter (fun L => p ∈ L)).card : ℝ)) ≤ 4 * (A.card : ℝ) := by
    exact_mod_cast hupper
  refine ⟨A, ?_, hA⟩
  nlinarith only [hlower, hupperR]

/-- Removing a point off a line leaves the line's intersection with every part
unchanged. -/
lemma filter_erase_inter_of_not_mem {W V : Finset ℝ²} {p : ℝ²}
    {L : AffineSubspace ℝ ℝ²} (hpL : p ∉ L) :
    ((W.erase p ∩ V).filter (fun q => q ∈ L)) = (W ∩ V).filter (fun q => q ∈ L) := by
  ext q
  simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_erase]
  constructor
  · rintro ⟨⟨⟨_, hqW⟩, hqV⟩, hqL⟩
    exact ⟨⟨hqW, hqV⟩, hqL⟩
  · rintro ⟨⟨hqW, hqV⟩, hqL⟩
    refine ⟨⟨⟨?_, hqW⟩, hqV⟩, hqL⟩
    rintro rfl
    exact hpL hqL

/-- Iterative minimum-degree core peeling across all four parts preserves the
rainbow property and retains at least half of the lines while guaranteeing
linear degree for every surviving point in all four parts. -/
lemma rainbow_core {S V0 V1 V2 V3 : Finset ℝ²}
    (hV0S : V0 ⊆ S) (hV1S : V1 ⊆ S) (hV2S : V2 ⊆ S) (hV3S : V3 ⊆ S)
    {B : Finset (AffineSubspace ℝ ℝ²)} {η : ℝ} (hη : 0 < η)
    (hBdense : η * (S.card : ℝ) ^ 2 ≤ B.card)
    (hBrainbow : ∀ L ∈ B,
      (V0.filter (fun p => p ∈ L)).card = 1 ∧
      (V1.filter (fun p => p ∈ L)).card = 1 ∧
      (V2.filter (fun p => p ∈ L)).card = 1 ∧
      (V3.filter (fun p => p ∈ L)).card = 1) :
    ∃ W0 W1 W2 W3 : Finset ℝ², W0 ⊆ V0 ∧ W1 ⊆ V1 ∧ W2 ⊆ V2 ∧ W3 ⊆ V3 ∧
      ∃ B' ⊆ B, (η / 2) * (S.card : ℝ) ^ 2 ≤ B'.card ∧
        (∀ L ∈ B',
          (W0.filter (fun p => p ∈ L)).card = 1 ∧
          (W1.filter (fun p => p ∈ L)).card = 1 ∧
          (W2.filter (fun p => p ∈ L)).card = 1 ∧
          (W3.filter (fun p => p ∈ L)).card = 1) ∧
        (∀ p ∈ W0 ∪ W1 ∪ W2 ∪ W3, (η / 2) * S.card ≤ (B'.filter (fun L => p ∈ L)).card) := by
  let U := V0 ∪ V1 ∪ V2 ∪ V3
  have hUS : U ⊆ S := by
    intro p hp
    simp only [U, Finset.mem_union] at hp
    rcases hp with ((hp0 | hp1) | hp2) | hp3
    · exact hV0S hp0
    · exact hV1S hp1
    · exact hV2S hp2
    · exact hV3S hp3
  have peel : ∀ k : ℕ, ∀ W : Finset ℝ², W.card = k → W ⊆ U →
      ∀ C : Finset (AffineSubspace ℝ ℝ²), C ⊆ B →
        (B.card : ℝ) ≤ (C.card : ℝ) + ((η / 2) * S.card) * ((U.card - W.card : ℕ) : ℝ) →
        (∀ L ∈ C,
          ((W ∩ V0).filter (fun p => p ∈ L)).card = 1 ∧
          ((W ∩ V1).filter (fun p => p ∈ L)).card = 1 ∧
          ((W ∩ V2).filter (fun p => p ∈ L)).card = 1 ∧
          ((W ∩ V3).filter (fun p => p ∈ L)).card = 1) →
        ∃ W' ⊆ W, ∃ C' ⊆ C,
          (B.card : ℝ) ≤ (C'.card : ℝ) + ((η / 2) * S.card) * ((U.card - W'.card : ℕ) : ℝ) ∧
          (∀ L ∈ C',
            ((W' ∩ V0).filter (fun p => p ∈ L)).card = 1 ∧
            ((W' ∩ V1).filter (fun p => p ∈ L)).card = 1 ∧
            ((W' ∩ V2).filter (fun p => p ∈ L)).card = 1 ∧
            ((W' ∩ V3).filter (fun p => p ∈ L)).card = 1) ∧
          (∀ p ∈ W', (η / 2) * S.card ≤ (C'.filter (fun L => p ∈ L)).card) := by
    intro k
    induction k with
    | zero =>
      intro W hWcard _ C _ hinv hrb
      refine ⟨W, Finset.Subset.rfl, C, Finset.Subset.rfl, hinv, hrb, ?_⟩
      intro p hp
      exact absurd hp (by rw [Finset.card_eq_zero.mp hWcard]; simp)
    | succ k ih =>
      intro W hWcard hWU C hCB hinv hrb
      by_cases hdeg : ∀ p ∈ W, (η / 2) * S.card ≤ (C.filter (fun L => p ∈ L)).card
      · exact ⟨W, Finset.Subset.rfl, C, Finset.Subset.rfl, hinv, hrb, hdeg⟩
      · push Not at hdeg
        obtain ⟨p, hpW, hpdeg⟩ := hdeg
        let W1 := W.erase p
        let C1 := C.filter (fun L => p ∉ L)
        have hW1card : W1.card = k := by
          dsimp [W1]
          rw [Finset.card_erase_of_mem hpW, hWcard]
          omega
        have hW1U : W1 ⊆ U := (Finset.erase_subset p W).trans hWU
        have hC1B : C1 ⊆ B := (Finset.filter_subset _ C).trans hCB
        have hWUcard : W.card ≤ U.card := Finset.card_le_card hWU
        have hdiffNat : U.card - W1.card = (U.card - W.card) + 1 := by omega
        have hdiffR : ((U.card - W1.card : ℕ) : ℝ) = ((U.card - W.card : ℕ) : ℝ) + 1 := by
          exact_mod_cast hdiffNat
        have hCsplit : (C.filter (fun L => p ∈ L)).card + C1.card = C.card := by
          dsimp [C1]
          exact Finset.card_filter_add_card_filter_not (s := C) (fun L => p ∈ L)
        have hCsplitR : ((C.filter (fun L => p ∈ L)).card : ℝ) + (C1.card : ℝ) = (C.card : ℝ) := by
          exact_mod_cast hCsplit
        have hinv1 : (B.card : ℝ) ≤ (C1.card : ℝ) + ((η / 2) * S.card) * ((U.card - W1.card : ℕ) : ℝ) := by
          rw [hdiffR]
          nlinarith only [hinv, hCsplitR, hpdeg]
        have hrb1 : ∀ L ∈ C1,
            ((W1 ∩ V0).filter (fun q => q ∈ L)).card = 1 ∧
            ((W1 ∩ V1).filter (fun q => q ∈ L)).card = 1 ∧
            ((W1 ∩ V2).filter (fun q => q ∈ L)).card = 1 ∧
            ((W1 ∩ V3).filter (fun q => q ∈ L)).card = 1 := by
          intro L hL
          obtain ⟨hLC, hpL⟩ := Finset.mem_filter.mp hL
          obtain ⟨h0, h1, h2, h3⟩ := hrb L hLC
          dsimp [W1]
          rw [filter_erase_inter_of_not_mem hpL, filter_erase_inter_of_not_mem hpL,
              filter_erase_inter_of_not_mem hpL, filter_erase_inter_of_not_mem hpL]
          exact ⟨h0, h1, h2, h3⟩
        obtain ⟨W', hW'W1, C', hC'C1, hinv', hrb', hdeg'⟩ :=
          ih W1 hW1card hW1U C1 hC1B hinv1 hrb1
        exact ⟨W', hW'W1.trans (Finset.erase_subset p W),
          C', hC'C1.trans (Finset.filter_subset _ C), hinv', hrb', hdeg'⟩
  have hUV0 : U ∩ V0 = V0 := Finset.inter_eq_right.mpr (by
    intro p hp; simp only [U, Finset.mem_union]; left; left; left; exact hp)
  have hUV1 : U ∩ V1 = V1 := Finset.inter_eq_right.mpr (by
    intro p hp; simp only [U, Finset.mem_union]; left; left; right; exact hp)
  have hUV2 : U ∩ V2 = V2 := Finset.inter_eq_right.mpr (by
    intro p hp; simp only [U, Finset.mem_union]; left; right; exact hp)
  have hUV3 : U ∩ V3 = V3 := Finset.inter_eq_right.mpr (by
    intro p hp; simp only [U, Finset.mem_union]; right; exact hp)
  have hrb0 : ∀ L ∈ B,
      ((U ∩ V0).filter (fun p => p ∈ L)).card = 1 ∧
      ((U ∩ V1).filter (fun p => p ∈ L)).card = 1 ∧
      ((U ∩ V2).filter (fun p => p ∈ L)).card = 1 ∧
      ((U ∩ V3).filter (fun p => p ∈ L)).card = 1 := by
    rw [hUV0, hUV1, hUV2, hUV3]
    exact hBrainbow
  obtain ⟨W', hW'U, B', hB'B, hinv', hrb', hdeg'⟩ :=
    peel U.card U rfl Finset.Subset.rfl B Finset.Subset.rfl (by simp) hrb0
  refine ⟨W' ∩ V0, W' ∩ V1, W' ∩ V2, W' ∩ V3,
    Finset.inter_subset_right, Finset.inter_subset_right,
    Finset.inter_subset_right, Finset.inter_subset_right,
    B', hB'B, ?_, hrb', ?_⟩
  · have hdiffle : U.card - W'.card ≤ S.card :=
      (Nat.sub_le U.card W'.card).trans (Finset.card_le_card hUS)
    have hdiffleR : ((U.card - W'.card : ℕ) : ℝ) ≤ (S.card : ℝ) := by
      exact_mod_cast hdiffle
    have hmul : ((η / 2) * (S.card : ℝ)) * ((U.card - W'.card : ℕ) : ℝ) ≤
        ((η / 2) * (S.card : ℝ)) * (S.card : ℝ) :=
      mul_le_mul_of_nonneg_left hdiffleR (by positivity)
    nlinarith only [hBdense, hinv', hmul]
  · intro p hp
    apply hdeg' p
    simp only [Finset.mem_union, Finset.mem_inter] at hp
    rcases hp with ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) | ⟨h, _⟩ <;> exact h

/-- Each part of a dense rainbow four-point line family has linear size by the
pencil bound. -/
lemma part_size_of_rainbow {S W : Finset ℝ²} (hWS : W ⊆ S) (hn : 0 < S.card)
    {B : Finset (AffineSubspace ℝ ℝ²)} {η : ℝ}
    (hBfour : ∀ L ∈ B, L ∈ linesWithPointsFor 4 (S : Set ℝ²))
    (hBmeet : ∀ L ∈ B, (W.filter (fun p => p ∈ L)).card = 1)
    (hBdense : η * (S.card : ℝ) ^ 2 ≤ B.card) :
    η * S.card ≤ W.card := by
  have hsub : B ⊆ W.biUnion (fun p => B.filter (fun L => p ∈ L)) := by
    intro L hL
    have hpos : 0 < (W.filter (fun p => p ∈ L)).card := by rw [hBmeet L hL]; omega
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
    obtain ⟨hpW, hpL⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_biUnion.mpr ⟨p, hpW, Finset.mem_filter.mpr ⟨hL, hpL⟩⟩
  have hcard : B.card ≤ W.card * S.card := by
    calc
      B.card ≤ (W.biUnion (fun p => B.filter (fun L => p ∈ L))).card :=
        Finset.card_le_card hsub
      _ ≤ ∑ p ∈ W, (B.filter (fun L => p ∈ L)).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ W, S.card := Finset.sum_le_sum fun p hp => by
        have h := OMA.R_Erdos101_erdos_101_R1.pencil_bound hBfour (hWS hp)
        omega
      _ = W.card * S.card := by simp
  have hcardR : (B.card : ℝ) ≤ (W.card : ℝ) * (S.card : ℝ) := by exact_mod_cast hcard
  have hnR : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hn
  nlinarith only [hBdense, hcardR, hnR]

theorem main : H1 → H2 → OMA.R_Erdos101_erdos_101_R1.H1 := by
  intro h1 h2 τ hτ
  let δ := τ ^ 2 / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨η, hη, N1, hH1⟩ := h1 δ hδ
  obtain ⟨d, c, hc, N2, hH2⟩ := h2 (η / 2) (half_pos hη)
  refine ⟨d, c, hc, max 1 (max N1 N2), ?_⟩
  intro S T hn hTS hcap hT hstars
  have hn0 : 0 < S.card := by omega
  have hn1 : N1 ≤ S.card := by omega
  have hn2 : N2 ≤ S.card := by omega
  obtain ⟨A, hAdense, hA⟩ := dense_lines_meeting hτ hTS hT hstars
  obtain ⟨V0, V1, V2, V3, hV0T, hV1S, hV2S, hV3S,
    hd01, hd02, hd03, hd12, hd13, hd23, B, hBA, hBdense, hBrainbow⟩ :=
    hH1 S T hn1 hTS hcap A hAdense hA
  obtain ⟨W0, W1, W2, W3, hW0V0, hW1V1, hW2V2, hW3V3,
    B', hB'B, hB'dense, hB'rainbow, hB'deg⟩ :=
    rainbow_core (hV0T.trans hTS) hV1S hV2S hV3S hη hBdense hBrainbow
  have hB'four : ∀ L ∈ B', L ∈ linesWithPointsFor 4 (S : Set ℝ²) :=
    fun L hL => (hA L (hBA (hB'B hL))).1
  have hW0S : W0 ⊆ S := hW0V0.trans (hV0T.trans hTS)
  have hW1S : W1 ⊆ S := hW1V1.trans hV1S
  have hW2S : W2 ⊆ S := hW2V2.trans hV2S
  have hW3S : W3 ⊆ S := hW3V3.trans hV3S
  have hW0card : (η / 2) * S.card ≤ W0.card :=
    part_size_of_rainbow hW0S hn0 hB'four (fun L hL => (hB'rainbow L hL).1) hB'dense
  have hW1card : (η / 2) * S.card ≤ W1.card :=
    part_size_of_rainbow hW1S hn0 hB'four (fun L hL => (hB'rainbow L hL).2.1) hB'dense
  have hW2card : (η / 2) * S.card ≤ W2.card :=
    part_size_of_rainbow hW2S hn0 hB'four (fun L hL => (hB'rainbow L hL).2.2.1) hB'dense
  have hW3card : (η / 2) * S.card ≤ W3.card :=
    part_size_of_rainbow hW3S hn0 hB'four (fun L hL => (hB'rainbow L hL).2.2.2) hB'dense
  obtain ⟨F, hF, hdeg, hcapW0⟩ := hH2 S W0 W1 W2 W3 hn2 hW0S hW1S hW2S hW3S
    (hd01.mono hW0V0 hW1V1) (hd02.mono hW0V0 hW2V2) (hd03.mono hW0V0 hW3V3)
    (hd12.mono hW1V1 hW2V2) (hd13.mono hW1V1 hW3V3) (hd23.mono hW2V2 hW3V3)
    hcap hW0card hW1card hW2card hW3card B' hB'dense
    (fun L hL => ⟨hB'four L hL, hB'rainbow L hL⟩) hB'deg
  refine ⟨F, hF, hdeg, hcapW0.trans ?_⟩
  exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (hW0V0.trans hV0T))

/-- The regularized rainbow four-partite capture hypothesis is no stronger than
the parent marked capture hypothesis. -/
theorem rainbow_capture_of_parent (hparent : OMA.R_Erdos101_erdos_101_R1.H1) : H2 := by
  intro η hη
  obtain ⟨d, c, hc, N, hN⟩ := hparent η hη
  refine ⟨d, c, hc, N, ?_⟩
  intro S W0 W1 W2 W3 hn hW0S _ _ _ _ _ _ _ _ _ hcap hW0card _ _ _ B _ hB hdeg
  apply hN S W0 hn hW0S hcap hW0card
  intro p hp
  refine ⟨B.filter (fun L => p ∈ L), hdeg p ?_, ?_⟩
  · simp only [Finset.mem_union]
    left; left; left; exact hp
  · intro L hL
    obtain ⟨hLB, hpL⟩ := Finset.mem_filter.mp hL
    exact ⟨hpL, (hB L hLB).1⟩

end OMA.R_Erdos101_erdos_101_R1_H1_R2
