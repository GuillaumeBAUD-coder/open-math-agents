import FormalConjectures.ErdosProblems.«95»

/-!
Reduction `Erdos95.erdos_95.variants.guth_katz.R1` of the Guth-Katz distance-energy upper bound
(USD 500 Erdős prize problem #95, Guth and Katz [GuKa15], Annals of Mathematics 2015).
Credit: @B221393

- Unconditionally proved inside the reduction:
  1. `four_mul_sum_sq_eq_quadruples`: exact Elekes-Sharir / Guth-Katz energy identity
     `4 * sum_{u in distanceSet P} (distanceMultiplicity P u)^2 = Q(P)`, where `Q(P)` is the
     number of equidistant quadruples `(p1, p2, p3, p4)` in `P.offDiag x P.offDiag`.
  2. `card_translation_quadruples_le`: the number of translation-related quadruples
     (`p3 - p1 = p4 - p2`) is at most `|P|^3` (since `p4 = p2 + p3 - p1` is uniquely determined).
- `H1`: Guth-Katz non-translation quadruple bound in the non-collinear regime (no line contains
  more than `|P| / 2` points of `P`).
- `H2`: Non-translation quadruple bound in the collinear-heavy regime (some line contains strictly
  more than `|P| / 2` points of `P`).
- `main`: Splits equidistant quadruples into translation vs non-translation quadruples, combines
  `card_translation_quadruples_le`, `H1`, and `H2` using `0 < Real.log 2` for `2 <= |P|`, and
  divides by `4` via `four_mul_sum_sq_eq_quadruples`.
-/

namespace OMA.R_Erdos95_erdos_95_variants_guth_katz_R1

open EuclideanGeometry

/-- Guth-Katz non-translation quadruple bound in the generic (non-collinear) regime:
if no line contains more than half the points of `P`, the number of non-translation
equidistant quadruples is at most `C1 * |P|^3 * log |P|`. -/
def H1 : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ P : Finset ℝ², 2 ≤ P.card →
    (∀ L : AffineSubspace ℝ ℝ², Module.finrank ℝ L.direction = 1 →
      ∀ S : Finset ℝ², S ⊆ P → (∀ p ∈ S, p ∈ L) → S.card ≤ P.card / 2) →
    (((P.offDiag ×ˢ P.offDiag).filter
      (fun q => dist q.1.1 q.1.2 = dist q.2.1 q.2.2 ∧
        q.2.1 - q.1.1 ≠ q.2.2 - q.1.2)).card : ℝ) ≤
      C₁ * (P.card : ℝ) ^ 3 * Real.log P.card

/-- Non-translation equidistant quadruple bound in the collinear-heavy regime:
if some line contains more than half the points of `P`, the number of non-translation
equidistant quadruples is still at most `C2 * |P|^3 * log |P|`. -/
def H2 : Prop :=
  ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ P : Finset ℝ², 2 ≤ P.card →
    (∃ L : AffineSubspace ℝ ℝ², Module.finrank ℝ L.direction = 1 ∧
      ∃ S : Finset ℝ², S ⊆ P ∧ (∀ p ∈ S, p ∈ L) ∧ P.card / 2 < S.card) →
    (((P.offDiag ×ˢ P.offDiag).filter
      (fun q => dist q.1.1 q.1.2 = dist q.2.1 q.2.2 ∧
        q.2.1 - q.1.1 ≠ q.2.2 - q.1.2)).card : ℝ) ≤
      C₂ * (P.card : ℝ) ^ 3 * Real.log P.card

lemma four_mul_sum_sq_eq_quadruples (P : Finset ℝ²) :
    4 * ∑ u ∈ distanceSet P, (distanceMultiplicity P u) ^ 2 =
      ((P.offDiag ×ˢ P.offDiag).filter
        (fun q => dist q.1.1 q.1.2 = dist q.2.1 q.2.2)).card := by
  classical
  let F : ℝ → Finset (ℝ² × ℝ²) := fun u => P.offDiag.filter (fun pair => dist pair.1 pair.2 = u)
  have hterm : ∀ u ∈ distanceSet P, 4 * (distanceMultiplicity P u) ^ 2 = (F u ×ˢ F u).card := by
    intro u _
    have heven : Even (F u).card := even_card_offDiag_filter_dist_eq P u
    have hmul2 : 2 * distanceMultiplicity P u = (F u).card := by
      unfold distanceMultiplicity
      rcases heven with ⟨k, hk⟩
      dsimp only [F] at hk ⊢
      omega
    rw [Finset.card_product, ← hmul2]
    ring
  rw [Finset.mul_sum, Finset.sum_congr rfl hterm]
  have hdisj : Set.PairwiseDisjoint (distanceSet P : Set ℝ) (fun u => F u ×ˢ F u) := by
    intro u₁ _ u₂ _ hne
    change Disjoint (F u₁ ×ˢ F u₁) (F u₂ ×ˢ F u₂)
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    have hd1 : dist q.1.1 q.1.2 = u₁ := (Finset.mem_filter.mp (Finset.mem_product.mp hq1).1).2
    have hd2 : dist q.1.1 q.1.2 = u₂ := (Finset.mem_filter.mp (Finset.mem_product.mp hq2).1).2
    exact hne (hd1.symm.trans hd2)
  rw [← Finset.card_biUnion hdisj]
  congr 1
  ext q
  simp only [Finset.mem_biUnion, Finset.mem_product, Finset.mem_filter, F, distanceSet,
    Finset.mem_image]
  constructor
  · rintro ⟨u, _, ⟨hq1, hd1⟩, ⟨hq2, hd2⟩⟩
    exact ⟨⟨hq1, hq2⟩, hd1.trans hd2.symm⟩
  · rintro ⟨⟨hq1, hq2⟩, hdeq⟩
    exact ⟨dist q.1.1 q.1.2, ⟨q.1, hq1, rfl⟩, ⟨hq1, rfl⟩, ⟨hq2, hdeq.symm⟩⟩

lemma card_translation_quadruples_le (P : Finset ℝ²) :
    ((P.offDiag ×ˢ P.offDiag).filter
      (fun q => dist q.1.1 q.1.2 = dist q.2.1 q.2.2 ∧
        q.2.1 - q.1.1 = q.2.2 - q.1.2)).card ≤ P.card ^ 3 := by
  classical
  let S := (P.offDiag ×ˢ P.offDiag).filter
    (fun q => dist q.1.1 q.1.2 = dist q.2.1 q.2.2 ∧ q.2.1 - q.1.1 = q.2.2 - q.1.2)
  let φ : (ℝ² × ℝ²) × (ℝ² × ℝ²) → ℝ² × ℝ² × ℝ² := fun q => (q.1.1, q.1.2, q.2.1)
  have hinj : Set.InjOn φ (S : Set ((ℝ² × ℝ²) × (ℝ² × ℝ²))) := by
    intro q₁ hq₁ q₂ hq₂ hφ
    have htr1 : q₁.2.1 - q₁.1.1 = q₁.2.2 - q₁.1.2 := (Finset.mem_filter.mp hq₁).2.2
    have htr2 : q₂.2.1 - q₂.1.1 = q₂.2.2 - q₂.1.2 := (Finset.mem_filter.mp hq₂).2.2
    have h11 : q₁.1.1 = q₂.1.1 := congrArg (fun t => t.1) hφ
    have h12 : q₁.1.2 = q₂.1.2 := congrArg (fun t => t.2.1) hφ
    have h21 : q₁.2.1 = q₂.2.1 := congrArg (fun t => t.2.2) hφ
    have h22 : q₁.2.2 = q₂.2.2 := by
      have e1 : q₁.2.2 = q₁.2.1 - q₁.1.1 + q₁.1.2 := eq_add_of_sub_eq htr1.symm
      have e2 : q₂.2.2 = q₂.2.1 - q₂.1.1 + q₂.1.2 := eq_add_of_sub_eq htr2.symm
      rw [e1, e2, h11, h12, h21]
    exact Prod.ext (Prod.ext h11 h12) (Prod.ext h21 h22)
  have hsub : S.image φ ⊆ P ×ˢ (P ×ˢ P) := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨q, hq, rfl⟩
    have hmem := (Finset.mem_filter.mp hq).1
    have h1 := (Finset.mem_product.mp hmem).1
    have h2 := (Finset.mem_product.mp hmem).2
    refine Finset.mem_product.mpr ⟨(Finset.mem_offDiag.mp h1).1,
      Finset.mem_product.mpr ⟨(Finset.mem_offDiag.mp h1).2.1, (Finset.mem_offDiag.mp h2).1⟩⟩
  calc S.card = (S.image φ).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (P ×ˢ (P ×ˢ P)).card := Finset.card_le_card hsub
    _ = P.card ^ 3 := by simp [Finset.card_product, pow_three]

theorem main : H1 → H2 → type_of% @Erdos95.erdos_95.variants.guth_katz := by
  intro h1 h2
  rcases h1 with ⟨C₁, hC₁, hgen⟩
  rcases h2 with ⟨C₂, hC₂, hcol⟩
  let C : ℝ := (max C₁ C₂ + (Real.log 2)⁻¹) / 4
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC_pos : 0 < C := by positivity
  refine ⟨C, hC_pos, ?_⟩
  intro P hP2
  have hlogP_ge : Real.log 2 ≤ Real.log (P.card : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hP2)
  have hlogP_pos : 0 < Real.log (P.card : ℝ) := lt_of_lt_of_le hlog2_pos hlogP_ge
  let Q := (P.offDiag ×ˢ P.offDiag).filter (fun q => dist q.1.1 q.1.2 = dist q.2.1 q.2.2)
  let Qtr := (P.offDiag ×ˢ P.offDiag).filter
    (fun q => dist q.1.1 q.1.2 = dist q.2.1 q.2.2 ∧ q.2.1 - q.1.1 = q.2.2 - q.1.2)
  let Qnt := (P.offDiag ×ˢ P.offDiag).filter
    (fun q => dist q.1.1 q.1.2 = dist q.2.1 q.2.2 ∧ q.2.1 - q.1.1 ≠ q.2.2 - q.1.2)
  have hQ_split : Q.card = Qtr.card + Qnt.card := by
    have hdisj : Disjoint Qtr Qnt := by
      rw [Finset.disjoint_left]
      intro q h1' h2'
      exact (Finset.mem_filter.mp h2').2.2 (Finset.mem_filter.mp h1').2.2
    rw [← Finset.card_union_of_disjoint hdisj]
    congr 1
    ext q
    simp only [Q, Qtr, Qnt, Finset.mem_union, Finset.mem_filter]
    by_cases htr : q.2.1 - q.1.1 = q.2.2 - q.1.2 <;> simp [htr]
  have hQnt_le : (Qnt.card : ℝ) ≤ max C₁ C₂ * (P.card : ℝ) ^ 3 * Real.log P.card := by
    by_cases hheavy : ∃ L : AffineSubspace ℝ ℝ², Module.finrank ℝ L.direction = 1 ∧
        ∃ S : Finset ℝ², S ⊆ P ∧ (∀ p ∈ S, p ∈ L) ∧ P.card / 2 < S.card
    · have hle2 := hcol P hP2 hheavy
      have hc : C₂ ≤ max C₁ C₂ := le_max_right _ _
      have hnn : 0 ≤ (P.card : ℝ) ^ 3 * Real.log P.card := by positivity
      calc (Qnt.card : ℝ) ≤ C₂ * (P.card : ℝ) ^ 3 * Real.log P.card := hle2
        _ = C₂ * ((P.card : ℝ) ^ 3 * Real.log P.card) := by ring
        _ ≤ max C₁ C₂ * ((P.card : ℝ) ^ 3 * Real.log P.card) :=
            mul_le_mul_of_nonneg_right hc hnn
        _ = max C₁ C₂ * (P.card : ℝ) ^ 3 * Real.log P.card := by ring
    · push Not at hheavy
      have hle1 := hgen P hP2 hheavy
      have hc : C₁ ≤ max C₁ C₂ := le_max_left _ _
      have hnn : 0 ≤ (P.card : ℝ) ^ 3 * Real.log P.card := by positivity
      calc (Qnt.card : ℝ) ≤ C₁ * (P.card : ℝ) ^ 3 * Real.log P.card := hle1
        _ = C₁ * ((P.card : ℝ) ^ 3 * Real.log P.card) := by ring
        _ ≤ max C₁ C₂ * ((P.card : ℝ) ^ 3 * Real.log P.card) :=
            mul_le_mul_of_nonneg_right hc hnn
        _ = max C₁ C₂ * (P.card : ℝ) ^ 3 * Real.log P.card := by ring
  have hQtr_le : (Qtr.card : ℝ) ≤ (Real.log 2)⁻¹ * (P.card : ℝ) ^ 3 * Real.log P.card := by
    have h1' : (Qtr.card : ℝ) ≤ (P.card : ℝ) ^ 3 := by
      exact_mod_cast card_translation_quadruples_le P
    have h2' : (1 : ℝ) ≤ (Real.log 2)⁻¹ * Real.log (P.card : ℝ) := by
      have := mul_le_mul_of_nonneg_left hlogP_ge (inv_nonneg.mpr (le_of_lt hlog2_pos))
      rwa [inv_mul_cancel₀ (ne_of_gt hlog2_pos)] at this
    have h3' : (P.card : ℝ) ^ 3 ≤ (P.card : ℝ) ^ 3 * ((Real.log 2)⁻¹ * Real.log (P.card : ℝ)) :=
      le_mul_of_one_le_right (by positivity) h2'
    linarith
  have hsum_eq : 4 * ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) ^ 2 = (Q.card : ℝ) := by
    have hnat := four_mul_sum_sq_eq_quadruples P
    exact_mod_cast hnat
  have hQ_real : (Q.card : ℝ) = (Qtr.card : ℝ) + (Qnt.card : ℝ) := by exact_mod_cast hQ_split
  have h4_le : 4 * ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) ^ 2 ≤
      4 * (C * (P.card : ℝ) ^ 3 * Real.log P.card) := by
    rw [hsum_eq, hQ_real]
    dsimp only [C]
    linarith
  linarith

end OMA.R_Erdos95_erdos_95_variants_guth_katz_R1
