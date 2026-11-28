import OMAReductions.R_Erdos101_erdos_101_R3

/-!
# Proof of Erdos101.erdos_101.R3.H1

Unconditional extraction of a large anchor-generated subset retaining positive density
of four-point lines, via iterative degree pruning and a finite Bernoulli product measure
on Finset.powerset.
-/

-- Step Erdos101.erdos_101.R3.H1: hypothesis H1 of reduction Erdos101.erdos_101.R3
-- Credit: @SlipstreamAI

namespace Erdos101R3H1Proof

open EuclideanGeometry
open scoped Classical BigOperators

/- ### Part 1: Elementary affine geometry in ℝ² -/

lemma affineSpan_pair_eq_of_mem {a b p q : ℝ²} (hpq : p ≠ q) (hab : a ≠ b)
    (ha : a ∈ affineSpan ℝ ({p, q} : Set ℝ²)) (hb : b ∈ affineSpan ℝ ({p, q} : Set ℝ²)) :
    affineSpan ℝ ({a, b} : Set ℝ²) = affineSpan ℝ ({p, q} : Set ℝ²) := by
  have hle : affineSpan ℝ ({a, b} : Set ℝ²) ≤ affineSpan ℝ ({p, q} : Set ℝ²) := by
    rw [affineSpan_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  have hdir_le : (affineSpan ℝ ({a, b} : Set ℝ²)).direction ≤
      (affineSpan ℝ ({p, q} : Set ℝ²)).direction :=
    AffineSubspace.direction_le hle
  have hfin1 : Module.finrank ℝ (affineSpan ℝ ({a, b} : Set ℝ²)).direction = 1 := by
    rw [direction_affineSpan, vectorSpan_pair]
    exact finrank_span_singleton (vsub_ne_zero.mpr hab)
  have hfin2 : Module.finrank ℝ (affineSpan ℝ ({p, q} : Set ℝ²)).direction = 1 := by
    rw [direction_affineSpan, vectorSpan_pair]
    exact finrank_span_singleton (vsub_ne_zero.mpr hpq)
  have hdir_eq : (affineSpan ℝ ({a, b} : Set ℝ²)).direction =
      (affineSpan ℝ ({p, q} : Set ℝ²)).direction :=
    Submodule.eq_of_le_of_finrank_eq hdir_le (hfin1.trans hfin2.symm)
  refine le_antisymm hle fun x hx => ?_
  have hmem : x -ᵥ a ∈ (affineSpan ℝ ({a, b} : Set ℝ²)).direction := by
    rw [hdir_eq]
    exact AffineSubspace.vsub_mem_direction hx ha
  simpa [vsub_vadd] using
    AffineSubspace.vadd_mem_of_mem_direction hmem
      (subset_affineSpan ℝ ({a, b} : Set ℝ²) (Set.mem_insert a {b}))

lemma determined_line_eq_of_two_mem {S : Set ℝ²} {L : AffineSubspace ℝ ℝ²}
    (hL : L ∈ { affineSpan ℝ ({p, q} : Set ℝ²) | (p ∈ S) (q ∈ S) (_ : p ≠ q) })
    {a b : ℝ²} (hab : a ≠ b) (ha : a ∈ L) (hb : b ∈ L) :
    line[ℝ, a, b] = L := by
  rcases hL with ⟨p, _, q, _, hpq, rfl⟩
  exact affineSpan_pair_eq_of_mem hpq hab ha hb

lemma determined_lines_eq_of_two_mem {S : Set ℝ²} {L₁ L₂ : AffineSubspace ℝ ℝ²}
    (hL₁ : L₁ ∈ { affineSpan ℝ ({p, q} : Set ℝ²) | (p ∈ S) (q ∈ S) (_ : p ≠ q) })
    (hL₂ : L₂ ∈ { affineSpan ℝ ({p, q} : Set ℝ²) | (p ∈ S) (q ∈ S) (_ : p ≠ q) })
    {a b : ℝ²} (hab : a ≠ b) (ha₁ : a ∈ L₁) (hb₁ : b ∈ L₁) (ha₂ : a ∈ L₂) (hb₂ : b ∈ L₂) :
    L₁ = L₂ := by
  rw [← determined_line_eq_of_two_mem hL₁ hab ha₁ hb₁,
      ← determined_line_eq_of_two_mem hL₂ hab ha₂ hb₂]

lemma linesWithPointsFor_subset_image (k : ℕ) (S : Finset ℝ²) :
    linesWithPointsFor k (S : Set ℝ²) ⊆
      (((S ×ˢ S).image (fun pq : ℝ² × ℝ² => affineSpan ℝ ({pq.1, pq.2} : Set ℝ²))) :
        Set (AffineSubspace ℝ ℝ²)) := by
  intro L hL
  rcases hL.1 with ⟨p, hp, q, hq, _, rfl⟩
  rw [Finset.mem_coe, Finset.mem_image]
  exact ⟨(p, q), Finset.mem_product.mpr ⟨hp, hq⟩, rfl⟩

lemma linesWithPointsFor_finite (k : ℕ) (S : Finset ℝ²) :
    (linesWithPointsFor k (S : Set ℝ²)).Finite :=
  (Finset.finite_toSet _).subset (linesWithPointsFor_subset_image k S)

lemma filter_line_card_eq_four {S : Finset ℝ²} {L : AffineSubspace ℝ ℝ²}
    (hL : L ∈ linesWithPointsFor 4 (S : Set ℝ²)) :
    (S.filter (· ∈ L)).card = 4 := by
  have hset : ((S.filter (· ∈ L) : Finset ℝ²) : Set ℝ²) = (L : Set ℝ²) ∩ (S : Set ℝ²) := by
    ext x
    simp [and_comm]
  have hnc := hL.2
  rw [← hset, Set.ncard_coe_finset] at hnc
  exact hnc

lemma mem_linesWithPointsFor_of_subset {S T : Finset ℝ²} {L : AffineSubspace ℝ ℝ²}
    (hL : L ∈ linesWithPointsFor 4 (S : Set ℝ²)) (hTS : T ⊆ S)
    (hLT : S.filter (· ∈ L) ⊆ T) :
    L ∈ linesWithPointsFor 4 (T : Set ℝ²) := by
  have hcap : (L : Set ℝ²) ∩ (T : Set ℝ²) = (L : Set ℝ²) ∩ (S : Set ℝ²) := by
    ext x
    constructor
    · rintro ⟨hxL, hxT⟩
      exact ⟨hxL, hTS hxT⟩
    · rintro ⟨hxL, hxS⟩
      exact ⟨hxL, hLT (Finset.mem_filter.mpr ⟨hxS, hxL⟩)⟩
  have hcard : (S.filter (· ∈ L)).card = 4 := filter_line_card_eq_four hL
  have htwo : 1 < (S.filter (· ∈ L)).card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp htwo
  have haT : a ∈ T := hLT ha
  have hbT : b ∈ T := hLT hb
  have haL : a ∈ L := (Finset.mem_filter.mp ha).2
  have hbL : b ∈ L := (Finset.mem_filter.mp hb).2
  have hLeq : affineSpan ℝ ({a, b} : Set ℝ²) = L :=
    determined_line_eq_of_two_mem hL.1 hab haL hbL
  refine ⟨⟨a, haT, b, hbT, hab, hLeq⟩, ?_⟩
  rw [hcap]
  exact hL.2

lemma card_lines_le_sq {T : Finset ℝ²} {F : Finset (AffineSubspace ℝ ℝ²)}
    (hF : ∀ L ∈ F, L ∈ linesWithPointsFor 4 (T : Set ℝ²)) :
    F.card ≤ T.card ^ 2 := by
  have hsub : F ⊆ (T ×ˢ T).image (fun pq : ℝ² × ℝ² => affineSpan ℝ ({pq.1, pq.2} : Set ℝ²)) := by
    intro L hLF
    have hL := linesWithPointsFor_subset_image 4 T (hF L hLF)
    simpa using hL
  calc
    F.card ≤ ((T ×ˢ T).image (fun pq : ℝ² × ℝ² => affineSpan ℝ ({pq.1, pq.2} : Set ℝ²))).card :=
      Finset.card_le_card hsub
    _ ≤ (T ×ˢ T).card := Finset.card_image_le
    _ = T.card ^ 2 := by rw [Finset.card_product, sq]

/- ### Part 2: Iterative pruning to high minimum degree -/

noncomputable def activeLines (S : Finset ℝ²) (L0 : Finset (AffineSubspace ℝ ℝ²)) (U : Finset ℝ²) :
    Finset (AffineSubspace ℝ ℝ²) :=
  L0.filter (fun L => S.filter (· ∈ L) ⊆ U)

lemma activeLines_self (S : Finset ℝ²) (L0 : Finset (AffineSubspace ℝ ℝ²)) :
    activeLines S L0 S = L0 := by
  ext L
  simp [activeLines, Finset.filter_subset]

lemma activeLines_erase_diff (S : Finset ℝ²) (L0 : Finset (AffineSubspace ℝ ℝ²))
    (U : Finset ℝ²) (p : ℝ²) :
    activeLines S L0 U \ activeLines S L0 (U.erase p) ⊆
      (activeLines S L0 U).filter (fun L => p ∈ L) := by
  intro L hL
  rw [Finset.mem_sdiff] at hL
  rw [Finset.mem_filter]
  refine ⟨hL.1, ?_⟩
  by_contra hpL
  apply hL.2
  rw [activeLines, Finset.mem_filter] at hL ⊢
  refine ⟨hL.1.1, ?_⟩
  intro x hx
  have hxU : x ∈ U := hL.1.2 hx
  have hxp : x ≠ p := by
    intro h
    subst h
    exact hpL (Finset.mem_filter.mp hx).2
  exact Finset.mem_erase.mpr ⟨hxp, hxU⟩

lemma activeLines_erase_subset (S : Finset ℝ²) (L0 : Finset (AffineSubspace ℝ ℝ²))
    (U : Finset ℝ²) (p : ℝ²) :
    activeLines S L0 (U.erase p) ⊆ activeLines S L0 U := by
  intro L hL
  rw [activeLines, Finset.mem_filter] at hL ⊢
  exact ⟨hL.1, hL.2.trans (Finset.erase_subset p U)⟩

lemma exists_pruned_subset (S : Finset ℝ²) (L0 : Finset (AffineSubspace ℝ ℝ²))
    (s : ℕ) :
    ∀ U : Finset ℝ², U ⊆ S →
      2 * s * L0.card ≤ 2 * s * (activeLines S L0 U).card + (S.card - U.card) * S.card →
      ∃ U1 : Finset ℝ², U1 ⊆ S ∧
        2 * s * L0.card ≤ 2 * s * (activeLines S L0 U1).card + (S.card - U1.card) * S.card ∧
        ∀ p ∈ U1, S.card ≤ 2 * s * ((activeLines S L0 U1).filter (fun L => p ∈ L)).card := by
  intro U
  induction hcard : U.card using Nat.strong_induction_on generalizing U with
  | _ m ih =>
    intro hUS hinv
    rw [← hcard] at hinv
    by_cases hgood : ∀ p ∈ U,
        S.card ≤ 2 * s * ((activeLines S L0 U).filter (fun L => p ∈ L)).card
    · exact ⟨U, hUS, hinv, hgood⟩
    · push Not at hgood
      obtain ⟨p, hpU, hdeg⟩ := hgood
      let U' := U.erase p
      have hU'S : U' ⊆ S := (Finset.erase_subset p U).trans hUS
      have hU'card : U'.card < m := by
        rw [← hcard]
        exact Finset.card_erase_lt_of_mem hpU
      have hU'eq : U'.card + 1 = U.card := Finset.card_erase_add_one hpU
      have hUleS : U.card ≤ S.card := Finset.card_le_card hUS
      have hsubL : activeLines S L0 U' ⊆ activeLines S L0 U :=
        activeLines_erase_subset S L0 U p
      have hdiff : (activeLines S L0 U).card - (activeLines S L0 U').card ≤
          ((activeLines S L0 U).filter (fun L => p ∈ L)).card := by
        have hsd : (activeLines S L0 U \ activeLines S L0 U').card =
            (activeLines S L0 U).card - (activeLines S L0 U').card := by
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsubL]
        rw [← hsd]
        exact Finset.card_le_card (activeLines_erase_diff S L0 U p)
      have hleL : (activeLines S L0 U').card ≤ (activeLines S L0 U).card :=
        Finset.card_le_card hsubL
      have hinv' : 2 * s * L0.card ≤
          2 * s * (activeLines S L0 U').card + (S.card - U'.card) * S.card := by
        have hstep : 2 * s * (activeLines S L0 U).card ≤
            2 * s * (activeLines S L0 U').card + S.card := by
          have h1 : 2 * s * ((activeLines S L0 U).card - (activeLines S L0 U').card) ≤
              2 * s * ((activeLines S L0 U).filter (fun L => p ∈ L)).card :=
            Nat.mul_le_mul_left _ hdiff
          have h2 : 2 * s * (activeLines S L0 U).card - 2 * s * (activeLines S L0 U').card ≤
              S.card := by
            rw [← Nat.mul_sub]
            omega
          have h3 : 2 * s * (activeLines S L0 U').card ≤ 2 * s * (activeLines S L0 U).card :=
            Nat.mul_le_mul_left _ hleL
          omega
        have hsub_eq : S.card - U'.card = (S.card - U.card) + 1 := by omega
        rw [hsub_eq, Nat.add_mul, one_mul]
        omega
      exact ih U'.card hU'card U' rfl hU'S hinv'

/- ### Part 3: Finite Bernoulli product measure on Finset.powerset -/

def bWeight {α : Type*} (q : ℝ) (U B : Finset α) : ℝ :=
  q ^ B.card * (1 - q) ^ (U.card - B.card)

lemma bWeight_nonneg {α : Type*} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (U B : Finset α) :
    0 ≤ bWeight q U B := by
  unfold bWeight
  have h1 : 0 ≤ 1 - q := by linarith
  positivity

lemma sum_bWeight {α : Type*} [DecidableEq α] (q : ℝ) (U : Finset α) :
    ∑ B ∈ U.powerset, bWeight q U B = 1 := by
  induction U using Finset.induction_on with
  | empty =>
    simp [bWeight]
  | @insert a U ha ih =>
    rw [Finset.powerset_insert, Finset.sum_union]
    · have h1 : ∑ B ∈ U.powerset, bWeight q (insert a U) B =
          (1 - q) * ∑ B ∈ U.powerset, bWeight q U B := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro B hB
        have hBU : B.card ≤ U.card := Finset.card_le_card (Finset.mem_powerset.mp hB)
        unfold bWeight
        rw [Finset.card_insert_of_notMem ha, Nat.succ_sub hBU, pow_succ]
        ring
      have h2 : ∑ B ∈ U.powerset.image (insert a), bWeight q (insert a U) B =
          q * ∑ B ∈ U.powerset, bWeight q U B := by
        rw [Finset.sum_image]
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro B hB
          have haB : a ∉ B := fun h => ha (Finset.mem_powerset.mp hB h)
          unfold bWeight
          rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem haB,
              Nat.succ_sub_succ, pow_succ]
          ring
        · intro B₁ hB₁ B₂ hB₂ hEq
          have ha1 : a ∉ B₁ := fun h => ha (Finset.mem_powerset.mp hB₁ h)
          have ha2 : a ∉ B₂ := fun h => ha (Finset.mem_powerset.mp hB₂ h)
          have := congrArg (fun X => X.erase a) hEq
          simpa [Finset.erase_insert ha1, Finset.erase_insert ha2] using this
      rw [h1, h2, ih]
      ring
    · rw [Finset.disjoint_left]
      intro B hB1 hB2
      obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp hB2
      exact ha (Finset.mem_powerset.mp hB1 (Finset.mem_insert_self a C))

lemma sum_bWeight_card {α : Type*} [DecidableEq α] (q : ℝ) (U : Finset α) :
    ∑ B ∈ U.powerset, bWeight q U B * (B.card : ℝ) = q * (U.card : ℝ) := by
  induction U using Finset.induction_on with
  | empty =>
    simp [bWeight]
  | @insert a U ha ih =>
    rw [Finset.powerset_insert, Finset.sum_union]
    · have h1 : ∑ B ∈ U.powerset, bWeight q (insert a U) B * (B.card : ℝ) =
          (1 - q) * ∑ B ∈ U.powerset, bWeight q U B * (B.card : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro B hB
        have hBU : B.card ≤ U.card := Finset.card_le_card (Finset.mem_powerset.mp hB)
        unfold bWeight
        rw [Finset.card_insert_of_notMem ha, Nat.succ_sub hBU, pow_succ]
        ring
      have h2 : ∑ B ∈ U.powerset.image (insert a), bWeight q (insert a U) B * (B.card : ℝ) =
          q * (∑ B ∈ U.powerset, bWeight q U B * (B.card : ℝ) +
               ∑ B ∈ U.powerset, bWeight q U B) := by
        rw [Finset.sum_image]
        · rw [← Finset.sum_add_distrib, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro B hB
          have haB : a ∉ B := fun h => ha (Finset.mem_powerset.mp hB h)
          unfold bWeight
          rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem haB,
              Nat.succ_sub_succ, pow_succ, Nat.cast_add, Nat.cast_one]
          ring
        · intro B₁ hB₁ B₂ hB₂ hEq
          have ha1 : a ∉ B₁ := fun h => ha (Finset.mem_powerset.mp hB₁ h)
          have ha2 : a ∉ B₂ := fun h => ha (Finset.mem_powerset.mp hB₂ h)
          have := congrArg (fun X => X.erase a) hEq
          simpa [Finset.erase_insert ha1, Finset.erase_insert ha2] using this
      rw [h1, h2, ih, sum_bWeight, Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one]
      ring
    · rw [Finset.disjoint_left]
      intro B hB1 hB2
      obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp hB2
      exact ha (Finset.mem_powerset.mp hB1 (Finset.mem_insert_self a C))

lemma sum_bWeight_mul_disjoint {α : Type*} [DecidableEq α] (q : ℝ) {A C : Finset α} (hAC : Disjoint A C)
    (f g : Finset α → ℝ) :
    ∑ B ∈ (A ∪ C).powerset, bWeight q (A ∪ C) B * (f (B ∩ A) * g (B ∩ C)) =
      (∑ B₁ ∈ A.powerset, bWeight q A B₁ * f B₁) *
      (∑ B₂ ∈ C.powerset, bWeight q C B₂ * g B₂) := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  symm
  refine Finset.sum_nbij (fun p : Finset α × Finset α => p.1 ∪ p.2) ?_ ?_ ?_ ?_
  · rintro ⟨B₁, B₂⟩ hp
    rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hp
    rw [Finset.mem_powerset]
    exact Finset.union_subset_union hp.1 hp.2
  · rintro ⟨B₁, B₂⟩ hp ⟨D₁, D₂⟩ hq hEq
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hp hq
    dsimp only at hEq
    have h1 : B₁ = D₁ := by
      have := congrArg (fun X => X ∩ A) hEq
      have hB2A : B₂ ∩ A = ∅ := Finset.disjoint_iff_inter_eq_empty.mp (hAC.symm.mono_left hp.2)
      have hD2A : D₂ ∩ A = ∅ := Finset.disjoint_iff_inter_eq_empty.mp (hAC.symm.mono_left hq.2)
      simpa [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hp.1,
             Finset.inter_eq_left.mpr hq.1, hB2A, hD2A] using this
    have h2 : B₂ = D₂ := by
      have := congrArg (fun X => X ∩ C) hEq
      have hB1C : B₁ ∩ C = ∅ := Finset.disjoint_iff_inter_eq_empty.mp (hAC.mono_left hp.1)
      have hD1C : D₁ ∩ C = ∅ := Finset.disjoint_iff_inter_eq_empty.mp (hAC.mono_left hq.1)
      simpa [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hp.2,
             Finset.inter_eq_left.mpr hq.2, hB1C, hD1C] using this
    exact Prod.ext h1 h2
  · intro B hB
    rw [Finset.mem_coe, Finset.mem_powerset] at hB
    refine ⟨(B ∩ A, B ∩ C), ?_, ?_⟩
    · rw [Finset.mem_coe, Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset]
      exact ⟨Finset.inter_subset_right, Finset.inter_subset_right⟩
    · dsimp only
      rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hB]
  · rintro ⟨B₁, B₂⟩ hp
    rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hp
    dsimp only
    have hdisj : Disjoint B₁ B₂ := hAC.mono hp.1 hp.2
    have hB1A : (B₁ ∪ B₂) ∩ A = B₁ := by
      rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hp.1,
          Finset.disjoint_iff_inter_eq_empty.mp (hAC.symm.mono_left hp.2), Finset.union_empty]
    have hB2C : (B₁ ∪ B₂) ∩ C = B₂ := by
      rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hp.2,
          Finset.disjoint_iff_inter_eq_empty.mp (hAC.mono_left hp.1), Finset.empty_union]
    have hc1 : B₁.card ≤ A.card := Finset.card_le_card hp.1
    have hc2 : B₂.card ≤ C.card := Finset.card_le_card hp.2
    have hsub_card : (A ∪ C).card - (B₁ ∪ B₂).card =
        (A.card - B₁.card) + (C.card - B₂.card) := by
      rw [Finset.card_union_of_disjoint hAC, Finset.card_union_of_disjoint hdisj]
      omega
    rw [hB1A, hB2C]
    unfold bWeight
    rw [hsub_card, Finset.card_union_of_disjoint hdisj, pow_add, pow_add]
    ring

lemma sum_bWeight_prod_disjoint {α ι : Type*} [DecidableEq α] [DecidableEq ι] (q : ℝ) (U : Finset α)
    (F : Finset ι) (A : ι → Finset α) (h : ι → Finset α → ℝ)
    (hsub : ∀ i ∈ F, A i ⊆ U)
    (hpw : (F : Set ι).PairwiseDisjoint A) :
    ∑ B ∈ U.powerset, bWeight q U B * ∏ i ∈ F, h i (B ∩ A i) =
      ∏ i ∈ F, (∑ C ∈ (A i).powerset, bWeight q (A i) C * h i C) := by
  induction F using Finset.induction_on generalizing U with
  | empty =>
    simp [sum_bWeight]
  | @insert i F hi ih =>
    have hAiU : A i ⊆ U := hsub i (Finset.mem_insert_self i F)
    have hsplit : A i ∪ (U \ A i) = U := Finset.union_sdiff_of_subset hAiU
    have hdisj : Disjoint (A i) (U \ A i) := Finset.disjoint_sdiff
    have hsub' : ∀ j ∈ F, A j ⊆ U \ A i := by
      intro j hj
      rw [Finset.subset_sdiff]
      refine ⟨hsub j (Finset.mem_insert_of_mem hj), ?_⟩
      have hne : j ≠ i := fun h => hi (h ▸ hj)
      exact hpw (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hj))
        (Finset.mem_coe.mpr (Finset.mem_insert_self i F)) hne
    have hpw' : (F : Set ι).PairwiseDisjoint A :=
      hpw.subset (Finset.coe_subset.mpr (Finset.subset_insert i F))
    have hrewrite :
        ∑ B ∈ U.powerset, bWeight q U B * ∏ j ∈ insert i F, h j (B ∩ A j) =
        ∑ B ∈ (A i ∪ (U \ A i)).powerset,
          bWeight q (A i ∪ (U \ A i)) B *
            (h i (B ∩ A i) * ∏ j ∈ F, h j ((B ∩ (U \ A i)) ∩ A j)) := by
      rw [hsplit]
      apply Finset.sum_congr rfl
      intro B _
      rw [Finset.prod_insert hi]
      congr 2
      apply Finset.prod_congr rfl
      intro j hj
      have hinter : (B ∩ (U \ A i)) ∩ A j = B ∩ A j := by
        rw [Finset.inter_assoc, Finset.inter_eq_right.mpr (hsub' j hj)]
      rw [hinter]
    rw [hrewrite, sum_bWeight_mul_disjoint q hdisj (h i)
          (fun C => ∏ j ∈ F, h j (C ∩ A j)),
        ih (U \ A i) hsub' hpw', Finset.prod_insert hi]

lemma sum_bWeight_triple_bound {α : Type*} [DecidableEq α] {q : ℝ} (_hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    {A : Finset α} (hA : A.card = 3) :
    ∑ C ∈ A.powerset, bWeight q A C * (if 2 ≤ C.card then (1 / 2 : ℝ) else 1) ≤ 1 - q ^ 2 := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hA
  have h1 : ({x, y, z} : Finset α).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [hyz]
    · simp [hxy, hxz]
  have hpow : ({x, y, z} : Finset α).powerset =
      {∅, {x}, {y}, {z}, {x, y}, {x, z}, {y, z}, {x, y, z}} := by
    ext C
    simp only [Finset.mem_powerset, Finset.mem_insert, Finset.mem_singleton, Finset.subset_iff]
    constructor
    · intro hC
      by_cases hx : x ∈ C <;> by_cases hy : y ∈ C <;> by_cases hz : z ∈ C
      · right; right; right; right; right; right; right
        ext w; simp only [Finset.mem_insert, Finset.mem_singleton]
        exact ⟨fun hw => hC hw, fun hw => by rcases hw with rfl | rfl | rfl <;> assumption⟩
      · right; right; right; right; left
        ext w; simp only [Finset.mem_insert, Finset.mem_singleton]
        exact ⟨fun hw => by rcases hC hw with rfl | rfl | rfl <;> tauto,
               fun hw => by rcases hw with rfl | rfl <;> assumption⟩
      · right; right; right; right; right; left
        ext w; simp only [Finset.mem_insert, Finset.mem_singleton]
        exact ⟨fun hw => by rcases hC hw with rfl | rfl | rfl <;> tauto,
               fun hw => by rcases hw with rfl | rfl <;> assumption⟩
      · right; left
        ext w; simp only [Finset.mem_singleton]
        exact ⟨fun hw => by rcases hC hw with rfl | rfl | rfl <;> tauto,
               fun hw => by rcases hw with rfl; exact hx⟩
      · right; right; right; right; right; right; left
        ext w; simp only [Finset.mem_insert, Finset.mem_singleton]
        exact ⟨fun hw => by rcases hC hw with rfl | rfl | rfl <;> tauto,
               fun hw => by rcases hw with rfl | rfl <;> assumption⟩
      · right; right; left
        ext w; simp only [Finset.mem_singleton]
        exact ⟨fun hw => by rcases hC hw with rfl | rfl | rfl <;> tauto,
               fun hw => by rcases hw with rfl; exact hy⟩
      · right; right; right; left
        ext w; simp only [Finset.mem_singleton]
        exact ⟨fun hw => by rcases hC hw with rfl | rfl | rfl <;> tauto,
               fun hw => by rcases hw with rfl; exact hz⟩
      · left
        ext w; simp only [Finset.notMem_empty, iff_false]
        intro hw; rcases hC hw with rfl | rfl | rfl <;> tauto
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) w hw
      · simp at hw
      · simp only [Finset.mem_singleton] at hw; subst hw; simp
      · simp only [Finset.mem_singleton] at hw; subst hw; simp
      · simp only [Finset.mem_singleton] at hw; subst hw; simp
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hw ⊢; tauto
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hw ⊢; tauto
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hw ⊢; tauto
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hw; exact hw
  rw [hpow]
  have hs0 : (∅ : Finset α) ∉ ({{x}, {y}, {z}, {x, y}, {x, z}, {y, z}, {x, y, z}} :
      Finset (Finset α)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h
    · exact (Finset.singleton_ne_empty x) h.symm
    · exact (Finset.singleton_ne_empty y) h.symm
    · exact (Finset.singleton_ne_empty z) h.symm
    · exact (Finset.insert_ne_empty x {y}) h.symm
    · exact (Finset.insert_ne_empty x {z}) h.symm
    · exact (Finset.insert_ne_empty y {z}) h.symm
    · exact (Finset.insert_ne_empty x {y, z}) h.symm
  have hs1 : ({x} : Finset α) ∉ ({{y}, {z}, {x, y}, {x, z}, {y, z}, {x, y, z}} :
      Finset (Finset α)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h
    · exact hxy (by simpa using congrArg (x ∈ ·) h)
    · exact hxz (by simpa using congrArg (x ∈ ·) h)
    · exact hxy.symm (by simpa using congrArg (y ∈ ·) h)
    · exact hxz.symm (by simpa using congrArg (z ∈ ·) h)
    · exact hxy (by simpa [hxz] using congrArg (x ∈ ·) h)
    · exact hxy.symm (by simpa using congrArg (y ∈ ·) h)
  have hs2 : ({y} : Finset α) ∉ ({{z}, {x, y}, {x, z}, {y, z}, {x, y, z}} :
      Finset (Finset α)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h
    · exact hyz (by simpa using congrArg (y ∈ ·) h)
    · exact hxy (by simpa using congrArg (x ∈ ·) h)
    · exact hxy (by simpa using congrArg (x ∈ ·) h)
    · exact hyz.symm (by simpa using congrArg (z ∈ ·) h)
    · exact hxy (by simpa using congrArg (x ∈ ·) h)
  have hs3 : ({z} : Finset α) ∉ ({{x, y}, {x, z}, {y, z}, {x, y, z}} :
      Finset (Finset α)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h
    · exact hxz (by simpa using congrArg (x ∈ ·) h)
    · exact hxz (by simpa using congrArg (x ∈ ·) h)
    · exact hyz (by simpa using congrArg (y ∈ ·) h)
    · exact hxz (by simpa using congrArg (x ∈ ·) h)
  have hs4 : ({x, y} : Finset α) ∉ ({{x, z}, {y, z}, {x, y, z}} :
      Finset (Finset α)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨?_, ?_, ?_⟩ <;> intro h
    · exact hyz.symm (by simpa [hxz.symm] using congrArg (z ∈ ·) h)
    · exact hyz.symm (by simpa [hxz.symm] using congrArg (z ∈ ·) h)
    · exact hyz.symm (by simpa [hxz.symm] using congrArg (z ∈ ·) h)
  have hs5 : ({x, z} : Finset α) ∉ ({{y, z}, {x, y, z}} : Finset (Finset α)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨?_, ?_⟩ <;> intro h
    · exact hxy.symm (by simpa [hyz] using congrArg (y ∈ ·) h)
    · exact hxy.symm (by simpa [hyz] using congrArg (y ∈ ·) h)
  have hs6 : ({y, z} : Finset α) ∉ ({{x, y, z}} : Finset (Finset α)) := by
    simp only [Finset.mem_singleton]
    intro h
    exact hxy (by simpa [hxz] using congrArg (x ∈ ·) h)
  rw [Finset.sum_insert hs0, Finset.sum_insert hs1, Finset.sum_insert hs2,
      Finset.sum_insert hs3, Finset.sum_insert hs4, Finset.sum_insert hs5,
      Finset.sum_insert hs6, Finset.sum_singleton]
  have hcxy : ({x, y} : Finset α).card = 2 := Finset.card_pair hxy
  have hcxz : ({x, z} : Finset α).card = 2 := Finset.card_pair hxz
  have hcyz : ({y, z} : Finset α).card = 2 := Finset.card_pair hyz
  unfold bWeight
  rw [h1, hcxy, hcxz, hcyz, Finset.card_empty, Finset.card_singleton]
  norm_num
  nlinarith [sq_nonneg q]

lemma bernoulli_inv_bound {x : ℝ} (_hx0 : 0 ≤ x) (hx1 : x ≤ 1) (d : ℕ) :
    (1 - x) ^ d * (1 + (d : ℝ) * x) ≤ 1 := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h1x : 0 ≤ (1 - x) ^ d := pow_nonneg (by linarith) d
    have hstep : (1 - x) * (1 + ((d + 1 : ℕ) : ℝ) * x) ≤ 1 + (d : ℝ) * x := by
      push_cast
      nlinarith [sq_nonneg x, Nat.cast_nonneg (α := ℝ) d]
    calc
      (1 - x) ^ (d + 1) * (1 + ((d + 1 : ℕ) : ℝ) * x)
          = (1 - x) ^ d * ((1 - x) * (1 + ((d + 1 : ℕ) : ℝ) * x)) := by rw [pow_succ]; ring
      _ ≤ (1 - x) ^ d * (1 + (d : ℝ) * x) := mul_le_mul_of_nonneg_left hstep h1x
      _ ≤ 1 := ih

lemma indicator_le_two_mul_half_pow (k : ℕ) :
    (if k < 2 then (1 : ℝ) else 0) ≤ 2 * (1 / 2 : ℝ) ^ k := by
  by_cases h0 : k = 0
  · subst h0; norm_num
  · by_cases h1 : k = 1
    · subst h1; norm_num
    · have hk2 : ¬ k < 2 := by omega
      rw [if_neg hk2]
      positivity

lemma nat_sq_bound_of_real {b s n t : ℕ} {q : ℝ} (hs : 0 < s) (hn : 0 < n)
    (hq_sq : q ^ 2 = 64 * (s : ℝ) / (n : ℝ)) (hb : (b : ℝ) < 4 * q * (n : ℝ))
    (hnt : n ≤ 4 * s * t) :
    b ^ 2 ≤ 4096 * s ^ 3 * t := by
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have h1 : (b : ℝ) ^ 2 ≤ (4 * q * (n : ℝ)) ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) b]
  have h2 : (4 * q * (n : ℝ)) ^ 2 = 1024 * (s : ℝ) * (n : ℝ) := by
    calc
      (4 * q * (n : ℝ)) ^ 2 = 16 * q ^ 2 * (n : ℝ) ^ 2 := by ring
      _ = 16 * (64 * (s : ℝ) / (n : ℝ)) * (n : ℝ) ^ 2 := by rw [hq_sq]
      _ = 1024 * (s : ℝ) * (n : ℝ) := by field_simp [hnR.ne']; ring
  have h3 : ((b ^ 2 : ℕ) : ℝ) ≤ ((1024 * s * n : ℕ) : ℝ) := by
    push_cast
    linarith
  have hb2 : b ^ 2 ≤ 1024 * s * n := by exact_mod_cast h3
  have hs23 : s ^ 2 ≤ s ^ 3 := by
    have : s ^ 2 * 1 ≤ s ^ 2 * s := Nat.mul_le_mul_left _ hs
    simpa [pow_succ] using this
  calc
    b ^ 2 ≤ 1024 * s * n := hb2
    _ ≤ 1024 * s * (4 * s * t) := Nat.mul_le_mul_left _ hnt
    _ = 4096 * s ^ 2 * t := by ring
    _ ≤ 4096 * s ^ 3 * t := Nat.mul_le_mul_right t (Nat.mul_le_mul_left 4096 hs23)

/- ### Part 4: Main proof of Erdos101.R3.H1 -/

set_option maxHeartbeats 400000 in
lemma main_proof : OMA.R_Erdos101_erdos_101_R3.H1 := by
  intro s hs
  refine ⟨256 * s, ?_⟩
  intro S hS_card _hS_nc hS_dense
  let n : ℕ := S.card
  have hn_ge : 256 * s ≤ n := hS_card
  have hn_pos : 0 < n := by omega
  have hS_fin : (linesWithPointsFor 4 (S : Set ℝ²)).Finite :=
    linesWithPointsFor_finite 4 S
  let L0 : Finset (AffineSubspace ℝ ℝ²) := hS_fin.toFinset
  have hL0_card : L0.card = (linesWithPointsFor 4 (S : Set ℝ²)).ncard := by
    rw [Set.ncard_eq_toFinset_card _ hS_fin]
  have hL0_mem : ∀ L ∈ L0, L ∈ linesWithPointsFor 4 (S : Set ℝ²) := by
    intro L hL
    exact (Set.Finite.mem_toFinset hS_fin).mp hL
  have hL0_dense : n ^ 2 ≤ s * L0.card := by
    simpa [n, hL0_card] using hS_dense
  -- Step 1: Prune S to S1 where every point has degree >= n / (2s)
  obtain ⟨S1, hS1S, hS1_inv, hS1_deg⟩ :=
    exists_pruned_subset S L0 s S (Finset.Subset.refl S) (by
      rw [activeLines_self, Nat.sub_self, zero_mul, add_zero])
  let L1 : Finset (AffineSubspace ℝ ℝ²) := activeLines S L0 S1
  have hL1_sub : L1 ⊆ L0 := Finset.filter_subset _ _
  have hL1_dense : n ^ 2 ≤ 2 * s * L1.card := by
    have h1 : 2 * s * L0.card ≤ 2 * s * L1.card + (n - S1.card) * n := hS1_inv
    have h2 : (n - S1.card) * n ≤ n ^ 2 := by
      rw [sq]
      exact Nat.mul_le_mul_right n (Nat.sub_le n S1.card)
    have h3 : 2 * n ^ 2 ≤ 2 * s * L0.card := by
      calc 2 * n ^ 2 = 2 * (n ^ 2) := rfl
        _ ≤ 2 * (s * L0.card) := Nat.mul_le_mul_left 2 hL0_dense
        _ = 2 * s * L0.card := by ring
    omega
  have hL1_pos : 0 < L1.card := by
    by_contra h
    have h0 : L1.card = 0 := by omega
    rw [h0, mul_zero] at hL1_dense
    have : 0 < n ^ 2 := by positivity
    omega
  -- Step 2: Set Bernoulli probability q = 8 * sqrt(s) / sqrt(n)
  let q : ℝ := 8 * Real.sqrt (s : ℝ) / Real.sqrt (n : ℝ)
  have hsR : (0 : ℝ) < (s : ℝ) := Nat.cast_pos.mpr hs
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  have hq0 : 0 ≤ q := by positivity
  have hq_pos : 0 < q := by positivity
  have hq_half : q ≤ 1 / 2 := by
    dsimp [q]
    rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hnR) (by norm_num : (0 : ℝ) < 2)]
    have hsq : (16 * Real.sqrt (s : ℝ)) ^ 2 ≤ (Real.sqrt (n : ℝ)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hsR.le, Real.sq_sqrt hnR.le]
      have : (256 * (s : ℝ)) ≤ (n : ℝ) := by exact_mod_cast hn_ge
      linarith
    have hle : 16 * Real.sqrt (s : ℝ) ≤ Real.sqrt (n : ℝ) := by
      nlinarith [Real.sqrt_nonneg (s : ℝ), Real.sqrt_nonneg (n : ℝ)]
    linarith
  have hq1 : q ≤ 1 := by linarith
  have hq_sq : q ^ 2 = 64 * (s : ℝ) / (n : ℝ) := by
    dsimp [q]
    rw [div_pow, mul_pow, Real.sq_sqrt hsR.le, Real.sq_sqrt hnR.le]
    ring
  -- Step 3: Define T(B) and lost lines for any B subseteq S1
  let pencil (p : ℝ²) : Finset (AffineSubspace ℝ ℝ²) := L1.filter (fun L => p ∈ L)
  let rest (p : ℝ²) (L : AffineSubspace ℝ ℝ²) : Finset ℝ² := (S1.filter (· ∈ L)).erase p
  let hitCount (B : Finset ℝ²) (p : ℝ²) : ℕ :=
    ((pencil p).filter (fun L => 2 ≤ (B ∩ rest p L).card)).card
  let Tof (B : Finset ℝ²) : Finset ℝ² :=
    B ∪ S1.filter (fun p => 2 ≤ hitCount B p)
  let lost (B : Finset ℝ²) : Finset (AffineSubspace ℝ ℝ²) :=
    L1.filter (fun L => ¬ S.filter (· ∈ L) ⊆ Tof B)
  -- Step 4: Bound P(hitCount B p < 2) <= 2 / 33 for every p in S1
  have hpt_bound : ∀ p ∈ S1,
      ∑ B ∈ S1.powerset, bWeight q S1 B * (if hitCount B p < 2 then (1 : ℝ) else 0) ≤
        (2 : ℝ) / 33 := by
    intro p hpS1
    have hsub_rest : ∀ L ∈ pencil p, rest p L ⊆ S1 := by
      intro L _
      exact (Finset.erase_subset p _).trans (Finset.filter_subset _ _)
    have hpw_rest : ((pencil p : Finset (AffineSubspace ℝ ℝ²)) : Set (AffineSubspace ℝ ℝ²)).PairwiseDisjoint
        (rest p) := by
      intro L₁ hL₁ L₂ hL₂ hne
      rw [Finset.mem_coe, Finset.mem_filter] at hL₁ hL₂
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro x hx₁ hx₂
      have hxp : x ≠ p := (Finset.mem_erase.mp hx₁).1
      have hxL₁ : x ∈ L₁ := (Finset.mem_filter.mp (Finset.mem_erase.mp hx₁).2).2
      have hxL₂ : x ∈ L₂ := (Finset.mem_filter.mp (Finset.mem_erase.mp hx₂).2).2
      have hEq : L₁ = L₂ := determined_lines_eq_of_two_mem
        (hL0_mem L₁ (hL1_sub hL₁.1)).1 (hL0_mem L₂ (hL1_sub hL₂.1)).1
        hxp hxL₁ hL₁.2 hxL₂ hL₂.2
      exact hne hEq
    have hcard_rest : ∀ L ∈ pencil p, (rest p L).card = 3 := by
      intro L hL
      rw [Finset.mem_filter] at hL
      have hL1m := Finset.mem_filter.mp hL.1
      have hfeq : S1.filter (· ∈ L) = S.filter (· ∈ L) := by
        ext x
        simp only [Finset.mem_filter]
        exact ⟨fun ⟨hx1, hxL⟩ => ⟨hS1S hx1, hxL⟩,
               fun ⟨hxS, hxL⟩ => ⟨hL1m.2 (Finset.mem_filter.mpr ⟨hxS, hxL⟩), hxL⟩⟩
      have hc4 : (S1.filter (· ∈ L)).card = 4 := by
        rw [hfeq]
        exact filter_line_card_eq_four (hL0_mem L hL1m.1)
      have hp_mem : p ∈ S1.filter (· ∈ L) := Finset.mem_filter.mpr ⟨hpS1, hL.2⟩
      have := Finset.card_erase_add_one hp_mem
      dsimp [rest]
      omega
    have hprod_eq : ∀ B : Finset ℝ²,
        (1 / 2 : ℝ) ^ hitCount B p =
          ∏ L ∈ pencil p, (if 2 ≤ (B ∩ rest p L).card then (1 / 2 : ℝ) else 1) := by
      intro B
      rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    have hle1 :
        ∑ B ∈ S1.powerset, bWeight q S1 B * (if hitCount B p < 2 then (1 : ℝ) else 0) ≤
        2 * ∑ B ∈ S1.powerset, bWeight q S1 B *
              ∏ L ∈ pencil p, (if 2 ≤ (B ∩ rest p L).card then (1 / 2 : ℝ) else 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro B _
      have hw : 0 ≤ bWeight q S1 B := bWeight_nonneg hq0 hq1 S1 B
      have hind := indicator_le_two_mul_half_pow (hitCount B p)
      rw [hprod_eq B] at hind
      nlinarith
    have hfact := sum_bWeight_prod_disjoint q S1 (pencil p) (rest p)
      (fun _ C => if 2 ≤ C.card then (1 / 2 : ℝ) else 1) hsub_rest hpw_rest
    have hprod_le :
        ∏ L ∈ pencil p, (∑ C ∈ (rest p L).powerset,
          bWeight q (rest p L) C * (if 2 ≤ C.card then (1 / 2 : ℝ) else 1)) ≤
        (1 - q ^ 2) ^ (pencil p).card := by
      rw [← Finset.prod_const]
      apply Finset.prod_le_prod
      · intro L _
        apply Finset.sum_nonneg
        intro C _
        have hw := bWeight_nonneg hq0 hq1 (rest p L) C
        split_ifs <;> positivity
      · intro L hL
        exact sum_bWeight_triple_bound hq0 hq_half (hcard_rest L hL)
    have hqsq0 : 0 ≤ q ^ 2 := sq_nonneg q
    have hqsq1 : q ^ 2 ≤ 1 := by nlinarith
    have hbern := bernoulli_inv_bound hqsq0 hqsq1 (pencil p).card
    have hdeg_nat : n ≤ 2 * s * (pencil p).card := hS1_deg p hpS1
    have hdeg_real : (n : ℝ) ≤ 2 * (s : ℝ) * ((pencil p).card : ℝ) := by
      exact_mod_cast hdeg_nat
    have hprod_ge32 : 32 ≤ ((pencil p).card : ℝ) * q ^ 2 := by
      rw [hq_sq, ← mul_div_assoc, le_div_iff₀ hnR]
      nlinarith
    have h33 : (1 - q ^ 2) ^ (pencil p).card ≤ (1 : ℝ) / 33 := by
      have hpos : (0 : ℝ) < 1 + ((pencil p).card : ℝ) * q ^ 2 := by linarith
      have hdiv : (1 - q ^ 2) ^ (pencil p).card ≤ 1 / (1 + ((pencil p).card : ℝ) * q ^ 2) := by
        rw [le_div_iff₀ hpos]
        exact hbern
      have hcmp : 1 / (1 + ((pencil p).card : ℝ) * q ^ 2) ≤ (1 : ℝ) / 33 := by
        apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 33)
        linarith
      exact hdiv.trans hcmp
    calc
      ∑ B ∈ S1.powerset, bWeight q S1 B * (if hitCount B p < 2 then (1 : ℝ) else 0)
          ≤ 2 * ∑ B ∈ S1.powerset, bWeight q S1 B *
              ∏ L ∈ pencil p, (if 2 ≤ (B ∩ rest p L).card then (1 / 2 : ℝ) else 1) := hle1
      _ = 2 * ∏ L ∈ pencil p, (∑ C ∈ (rest p L).powerset,
            bWeight q (rest p L) C * (if 2 ≤ C.card then (1 / 2 : ℝ) else 1)) :=
          congrArg (2 * ·) hfact
      _ ≤ 2 * (1 - q ^ 2) ^ (pencil p).card := mul_le_mul_of_nonneg_left hprod_le (by norm_num)
      _ ≤ 2 * ((1 : ℝ) / 33) := mul_le_mul_of_nonneg_left h33 (by norm_num)
      _ = (2 : ℝ) / 33 := by ring
  -- Step 5: Bound expected number of lost lines <= (8 / 33) * L1.card
  have hlost_bound :
      ∑ B ∈ S1.powerset, bWeight q S1 B * ((lost B).card : ℝ) ≤
        ((8 : ℝ) / 33) * (L1.card : ℝ) := by
    have hswap :
        ∑ B ∈ S1.powerset, bWeight q S1 B * ((lost B).card : ℝ) =
        ∑ L ∈ L1, ∑ B ∈ S1.powerset, bWeight q S1 B *
          (if ¬ S.filter (· ∈ L) ⊆ Tof B then (1 : ℝ) else 0) := by
      have h1 : ∀ B : Finset ℝ²,
          ((lost B).card : ℝ) =
            ∑ L ∈ L1, (if ¬ S.filter (· ∈ L) ⊆ Tof B then (1 : ℝ) else 0) := by
        intro B
        dsimp [lost]
        rw [Finset.card_filter, Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro L _
        split_ifs <;> simp
      simp_rw [h1, Finset.mul_sum]
      exact Finset.sum_comm
    rw [hswap]
    have hline_le : ∀ L ∈ L1,
        ∑ B ∈ S1.powerset, bWeight q S1 B *
          (if ¬ S.filter (· ∈ L) ⊆ Tof B then (1 : ℝ) else 0) ≤ (8 : ℝ) / 33 := by
      intro L hL
      have hLsub : S.filter (· ∈ L) ⊆ S1 := (Finset.mem_filter.mp hL).2
      have hLcard : (S.filter (· ∈ L)).card = 4 :=
        filter_line_card_eq_four (hL0_mem L (hL1_sub hL))
      have hpt_sum : ∀ B : Finset ℝ²,
          (if ¬ S.filter (· ∈ L) ⊆ Tof B then (1 : ℝ) else 0) ≤
          ∑ p ∈ S.filter (· ∈ L), (if hitCount B p < 2 then (1 : ℝ) else 0) := by
        intro B
        by_cases hsub : S.filter (· ∈ L) ⊆ Tof B
        · rw [if_neg (not_not.mpr hsub)]
          apply Finset.sum_nonneg
          intro p _; split_ifs <;> norm_num
        · rw [if_pos hsub]
          rw [Finset.not_subset] at hsub
          obtain ⟨p, hpL, hpT⟩ := hsub
          have hpS1 : p ∈ S1 := hLsub hpL
          have hbad : hitCount B p < 2 := by
            by_contra hge
            apply hpT
            exact Finset.mem_union_right B (Finset.mem_filter.mpr ⟨hpS1, by omega⟩)
          calc
            (1 : ℝ) = (if hitCount B p < 2 then (1 : ℝ) else 0) := by rw [if_pos hbad]
            _ ≤ ∑ x ∈ S.filter (· ∈ L), (if hitCount B x < 2 then (1 : ℝ) else 0) :=
              Finset.single_le_sum (f := fun x => if hitCount B x < 2 then (1 : ℝ) else 0)
                (fun x _ => by split_ifs <;> norm_num) hpL
      calc
        ∑ B ∈ S1.powerset, bWeight q S1 B *
            (if ¬ S.filter (· ∈ L) ⊆ Tof B then (1 : ℝ) else 0)
            ≤ ∑ B ∈ S1.powerset, bWeight q S1 B *
                ∑ p ∈ S.filter (· ∈ L), (if hitCount B p < 2 then (1 : ℝ) else 0) := by
              apply Finset.sum_le_sum
              intro B _
              exact mul_le_mul_of_nonneg_left (hpt_sum B) (bWeight_nonneg hq0 hq1 S1 B)
        _ = ∑ p ∈ S.filter (· ∈ L),
              ∑ B ∈ S1.powerset, bWeight q S1 B * (if hitCount B p < 2 then (1 : ℝ) else 0) := by
              simp_rw [Finset.mul_sum]
              exact Finset.sum_comm
        _ ≤ ∑ _p ∈ S.filter (· ∈ L), ((2 : ℝ) / 33) := by
              apply Finset.sum_le_sum
              intro p hp
              exact hpt_bound p (hLsub hp)
        _ = (8 : ℝ) / 33 := by
              rw [Finset.sum_const, hLcard]
              norm_num
    calc
      ∑ L ∈ L1, ∑ B ∈ S1.powerset, bWeight q S1 B *
          (if ¬ S.filter (· ∈ L) ⊆ Tof B then (1 : ℝ) else 0)
          ≤ ∑ _L ∈ L1, ((8 : ℝ) / 33) := Finset.sum_le_sum hline_le
      _ = ((8 : ℝ) / 33) * (L1.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- Step 6: Combined expectation < 1 yields good B in S1.powerset
  let Φ (B : Finset ℝ²) : ℝ :=
    (B.card : ℝ) / (4 * q * (n : ℝ)) + 2 * ((lost B).card : ℝ) / (L1.card : ℝ)
  have hL1R : (0 : ℝ) < (L1.card : ℝ) := Nat.cast_pos.mpr hL1_pos
  have h4qn : (0 : ℝ) < 4 * q * (n : ℝ) := by positivity
  have hE_Phi : ∑ B ∈ S1.powerset, bWeight q S1 B * Φ B <
      ∑ B ∈ S1.powerset, bWeight q S1 B * (1 : ℝ) := by
    have hsplit :
        ∑ B ∈ S1.powerset, bWeight q S1 B * Φ B =
        (∑ B ∈ S1.powerset, bWeight q S1 B * (B.card : ℝ)) / (4 * q * (n : ℝ)) +
        2 * (∑ B ∈ S1.powerset, bWeight q S1 B * ((lost B).card : ℝ)) / (L1.card : ℝ) := by
      simp only [Φ, mul_add, Finset.sum_add_distrib]
      congr 1
      · rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro B _; ring
      · rw [Finset.mul_sum, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro B _; ring
    have hterm1 : (∑ B ∈ S1.powerset, bWeight q S1 B * (B.card : ℝ)) / (4 * q * (n : ℝ)) ≤
        (1 : ℝ) / 4 := by
      rw [sum_bWeight_card]
      have hS1le : (S1.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast Finset.card_le_card hS1S
      rw [div_le_div_iff₀ h4qn (by norm_num : (0 : ℝ) < 4)]
      nlinarith
    have hterm2 : 2 * (∑ B ∈ S1.powerset, bWeight q S1 B * ((lost B).card : ℝ)) / (L1.card : ℝ) ≤
        (16 : ℝ) / 33 := by
      rw [div_le_iff₀ hL1R]
      linarith
    have hone : ∑ B ∈ S1.powerset, bWeight q S1 B * (1 : ℝ) = 1 := by
      simp [sum_bWeight]
    rw [hsplit, hone]
    linarith
  obtain ⟨B, hBpow, hBstrict⟩ := Finset.exists_lt_of_sum_lt hE_Phi
  have hBw_pos : 0 < bWeight q S1 B := by
    have hge := bWeight_nonneg hq0 hq1 S1 B
    by_contra hle
    have hzero : bWeight q S1 B = 0 := le_antisymm (not_lt.mp hle) hge
    rw [hzero, zero_mul, zero_mul] at hBstrict
    exact lt_irrefl 0 hBstrict
  have hPhi_lt : Φ B < 1 := by
    by_contra hge
    push Not at hge
    have := mul_le_mul_of_nonneg_left hge hBw_pos.le
    linarith
  have hBsubS1 : B ⊆ S1 := Finset.mem_powerset.mp hBpow
  have hB_small_R : (B.card : ℝ) < 4 * q * (n : ℝ) := by
    have hterm2_nn : 0 ≤ 2 * ((lost B).card : ℝ) / (L1.card : ℝ) := by positivity
    have h1 : (B.card : ℝ) / (4 * q * (n : ℝ)) < 1 := by dsimp [Φ] at hPhi_lt; linarith
    exact (div_lt_one h4qn).mp h1
  have hlost_small_R : 2 * ((lost B).card : ℝ) < (L1.card : ℝ) := by
    have hterm1_nn : 0 ≤ (B.card : ℝ) / (4 * q * (n : ℝ)) := by positivity
    have h2 : 2 * ((lost B).card : ℝ) / (L1.card : ℝ) < 1 := by dsimp [Φ] at hPhi_lt; linarith
    exact (div_lt_one hL1R).mp h2
  have hlost_small : 2 * (lost B).card < L1.card := by exact_mod_cast hlost_small_R
  -- Step 7: Verify all 6 required properties for T := Tof B and B
  let T : Finset ℝ² := Tof B
  have hTS : T ⊆ S :=
    Finset.union_subset (hBsubS1.trans hS1S) ((Finset.filter_subset _ _).trans hS1S)
  have hBT : B ⊆ T := Finset.subset_union_left
  let Lsurv : Finset (AffineSubspace ℝ ℝ²) := L1 \ lost B
  have hLsurv_card : L1.card < 2 * Lsurv.card := by
    have hsub : lost B ⊆ L1 := Finset.filter_subset _ _
    have hc : Lsurv.card = L1.card - (lost B).card := by
      dsimp [Lsurv]
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
    have hle : (lost B).card ≤ L1.card := Finset.card_le_card hsub
    omega
  have hLsurv_mem : ∀ L ∈ Lsurv, L ∈ linesWithPointsFor 4 (T : Set ℝ²) := by
    intro L hL
    rw [Finset.mem_sdiff] at hL
    have hsubT : S.filter (· ∈ L) ⊆ T := by
      by_contra hnot
      exact hL.2 (Finset.mem_filter.mpr ⟨hL.1, hnot⟩)
    exact mem_linesWithPointsFor_of_subset (hL0_mem L (hL1_sub hL.1)) hTS hsubT
  have hLsurv_le_ncard : Lsurv.card ≤ (linesWithPointsFor 4 (T : Set ℝ²)).ncard := by
    have hTfin := linesWithPointsFor_finite 4 T
    have hsub : (Lsurv : Set (AffineSubspace ℝ ℝ²)) ⊆ linesWithPointsFor 4 (T : Set ℝ²) := by
      intro L hL
      exact hLsurv_mem L (Finset.mem_coe.mp hL)
    simpa [Set.ncard_coe_finset] using Set.ncard_le_ncard hsub hTfin
  have hn2_le_surv : n ^ 2 ≤ 4 * s * Lsurv.card := by
    have h1 : n ^ 2 ≤ 2 * s * L1.card := hL1_dense
    have h2 : 2 * s * L1.card ≤ 2 * s * (2 * Lsurv.card) :=
      Nat.mul_le_mul_left (2 * s) hLsurv_card.le
    linarith
  have hT_dense : T.card ^ 2 ≤ 4 * s * (linesWithPointsFor 4 (T : Set ℝ²)).ncard := by
    have hTle : T.card ≤ n := Finset.card_le_card hTS
    calc
      T.card ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hTle 2
      _ ≤ 4 * s * Lsurv.card := hn2_le_surv
      _ ≤ 4 * s * (linesWithPointsFor 4 (T : Set ℝ²)).ncard :=
          Nat.mul_le_mul_left _ hLsurv_le_ncard
  have hS_le_4sT : S.card ≤ 4 * s * T.card := by
    have hLleT2 : Lsurv.card ≤ T.card ^ 2 := card_lines_le_sq hLsurv_mem
    have hs4 : 4 * s ≤ 16 * s ^ 2 := by
      have : 1 ≤ s := hs
      nlinarith
    have hsq : n ^ 2 ≤ (4 * s * T.card) ^ 2 := by
      calc
        n ^ 2 ≤ 4 * s * Lsurv.card := hn2_le_surv
        _ ≤ 4 * s * T.card ^ 2 := Nat.mul_le_mul_left _ hLleT2
        _ ≤ 16 * s ^ 2 * T.card ^ 2 := Nat.mul_le_mul_right _ hs4
        _ = (4 * s * T.card) ^ 2 := by ring
    by_contra hlt
    push Not at hlt
    have hlt' : 4 * s * T.card < n := hlt
    exact absurd (Nat.pow_lt_pow_left hlt' (by norm_num : 2 ≠ 0)) (not_lt.mpr hsq)
  have hB2_le : B.card ^ 2 ≤ 4096 * s ^ 3 * T.card :=
    nat_sq_bound_of_real hs hn_pos hq_sq hB_small_R hS_le_4sT
  have hgen : ∀ p ∈ T, p ∈ B ∨ ∃ a ∈ B, ∃ b ∈ B, ∃ c ∈ B, ∃ d ∈ B,
      a ≠ b ∧ c ≠ d ∧ line[ℝ, a, b] ≠ line[ℝ, c, d] ∧
      p ∈ line[ℝ, a, b] ∧ p ∈ line[ℝ, c, d] := by
    intro p hpT
    rcases Finset.mem_union.mp hpT with hpB | hpF
    · exact Or.inl hpB
    · right
      have hge2 : 2 ≤ hitCount B p := (Finset.mem_filter.mp hpF).2
      have hgt1 : 1 < ((pencil p).filter (fun L => 2 ≤ (B ∩ rest p L).card)).card := by
        dsimp [hitCount] at hge2
        omega
      obtain ⟨La, hLa, Lb, hLb, hLaLb⟩ := Finset.one_lt_card.mp hgt1
      rw [Finset.mem_filter] at hLa hLb
      have hLa_p : p ∈ La := (Finset.mem_filter.mp hLa.1).2
      have hLb_p : p ∈ Lb := (Finset.mem_filter.mp hLb.1).2
      have hLa_L0 : La ∈ L0 := hL1_sub (Finset.mem_filter.mp hLa.1).1
      have hLb_L0 : Lb ∈ L0 := hL1_sub (Finset.mem_filter.mp hLb.1).1
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (B ∩ rest p La).card)
      obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp (by omega : 1 < (B ∩ rest p Lb).card)
      rw [Finset.mem_inter] at ha hb hc hd
      have haLa : a ∈ La := (Finset.mem_filter.mp (Finset.mem_erase.mp ha.2).2).2
      have hbLa : b ∈ La := (Finset.mem_filter.mp (Finset.mem_erase.mp hb.2).2).2
      have hcLb : c ∈ Lb := (Finset.mem_filter.mp (Finset.mem_erase.mp hc.2).2).2
      have hdLb : d ∈ Lb := (Finset.mem_filter.mp (Finset.mem_erase.mp hd.2).2).2
      have hline_ab : line[ℝ, a, b] = La :=
        determined_line_eq_of_two_mem (hL0_mem La hLa_L0).1 hab haLa hbLa
      have hline_cd : line[ℝ, c, d] = Lb :=
        determined_line_eq_of_two_mem (hL0_mem Lb hLb_L0).1 hcd hcLb hdLb
      exact ⟨a, ha.1, b, hb.1, c, hc.1, d, hd.1, hab, hcd,
        by rw [hline_ab, hline_cd]; exact hLaLb,
        by rw [hline_ab]; exact hLa_p,
        by rw [hline_cd]; exact hLb_p⟩
  exact ⟨T, B, hTS, hBT, hS_le_4sT, hB2_le, hT_dense, hgen⟩

end Erdos101R3H1Proof

theorem OMA.solution : OMA.R_Erdos101_erdos_101_R3.H1 :=
  Erdos101R3H1Proof.main_proof
