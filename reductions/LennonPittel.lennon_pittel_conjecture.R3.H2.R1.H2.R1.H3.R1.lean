import OMAReductions.R_LennonPittel_lennon_pittel_conjecture_R3_H2_R1_H2_R1
import Mathlib

/-! Port of part of the Lennon-Pittel lower-tail proof by Bo Cowgill,
https://github.com/bocowgill/lennon-pittel at commit cf950d0596591bba912b1568aa394f99986f8191,
Copyright 2026 Bo Cowgill, used under the Apache License 2.0.
Changes: modules flattened into one file, comments removed, declarations not needed here dropped,
names adapted to the pinned Mathlib, the marked model renamed and tied to the parent reduction's
definitions (after moon-4's port of the same model for the parent step).
This reduction proves the comparable-anchor residual estimate from two lemmas of the source, kept
as hypotheses: the residual pair mass bound in regular orientation and the logarithmic cycle budget. -/


-- IidScoreRanks
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CompLP
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
theorem ae_injective_iid (n : ℕ) :
    ∀ᵐ x ∂(Measure.pi fun _ : Fin n ↦ μ), Function.Injective (x : Fin n → ℝ) := by
  let law : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n ↦ μ
  have hind : iIndepFun (fun i (x : Fin n → ℝ) ↦ x i) law :=
    iIndepFun_pi (fun _ ↦ aemeasurable_id)
  refine ae_all_iff.2 fun i ↦ ae_all_iff.2 fun j ↦ ?_
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall fun _ _ ↦ hij
  have hi := (measurable_pi_apply i : Measurable (fun x : Fin n → ℝ ↦ x i))
  have hj := (measurable_pi_apply j : Measurable (fun x : Fin n → ℝ ↦ x j))
  
  have hpair : law.map (fun x ↦ (x i, x j)) = μ.prod μ :=
    ((indepFun_iff_map_prod_eq_prod_map_map hi.aemeasurable hj.aemeasurable).1
      (hind.indepFun hij)).trans
        (congrArg₂ Measure.prod (measurePreserving_eval (fun _ : Fin n ↦ μ) i).map_eq
          (measurePreserving_eval (fun _ : Fin n ↦ μ) j).map_eq)
  let diagonal : Set (ℝ × ℝ) := {z | z.1 = z.2}
  have hd : MeasurableSet diagonal := measurableSet_eq_fun measurable_fst measurable_snd
  have hnull : (μ.prod μ) diagonal = 0 := by
    rw [Measure.prod_apply hd]
    have hsection (u : ℝ) : Prod.mk u ⁻¹' diagonal = {u} :=
      Set.ext fun _ ↦ eq_comm
    simp [hsection]
  have hpull : law {x | x i = x j} = 0 := by
    rw [← hpair, Measure.map_apply (hi.prodMk hj) hd] at hnull
    exact hnull
  exact ae_iff.2 (by simpa [hij] using hpull)
end CompLP
end

-- MarkedCounting
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace CompLP
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [Fintype A] [Nonempty A]
private noncomputable def uniformMarkLaw (A : Type*) [MeasurableSpace A] [Fintype A] [Nonempty A] :
    Measure A :=
  (PMF.uniformOfFintype A).toMeasure
private instance uniformMarkLaw_isProbabilityMeasure : IsProbabilityMeasure (uniformMarkLaw A) :=
  inferInstanceAs (IsProbabilityMeasure (PMF.uniformOfFintype A).toMeasure)
private noncomputable def markedLaw (P : Measure Ω) (E : Set (Ω × A)) : Measure (Ω × A) :=
  ProbabilityTheory.cond (P.prod (uniformMarkLaw A)) E
theorem markedLaw_isProbabilityMeasure (P : Measure Ω) [IsProbabilityMeasure P]
    {E : Set (Ω × A)} (hpos : (P.prod (uniformMarkLaw A)) E ≠ 0) :
    IsProbabilityMeasure (markedLaw P E) :=
  ProbabilityTheory.cond_isProbabilityMeasure hpos
variable [MeasurableSingletonClass A]
section StableMarriage
open StableMarriage
scoped instance matchingMeasurableSpace (n : ℕ) : MeasurableSpace (Matching n) := ⊤
scoped instance matchingDiscreteMeasurableSpace (n : ℕ) :
    DiscreteMeasurableSpace (Matching n) :=
  ⟨fun _ ↦ trivial⟩
scoped instance profileDiscreteMeasurableSpace (n : ℕ) : DiscreteMeasurableSpace (Profile n) :=
  ⟨fun _ ↦ trivial⟩
end StableMarriage
end CompLP
end

-- ScoreRanks
section
open Function MeasureTheory Set
namespace CompLP
private noncomputable def scoreImage {n : ℕ} (x : Fin n → ℝ) : Finset ℝ :=
  Finset.univ.image x
private theorem card_scoreImage {n : ℕ} {x : Fin n → ℝ} (hx : Injective x) :
    (scoreImage x).card = n := by
  rw [scoreImage, Finset.card_image_of_injective _ hx, Finset.card_univ, Fintype.card_fin]
private noncomputable def scoreEquiv {n : ℕ} (x : Fin n → ℝ) (hx : Injective x) :
    Fin n ≃ (scoreImage x : Set ℝ) :=
  Equiv.ofBijective (fun i ↦ ⟨x i, Finset.mem_image_of_mem x (Finset.mem_univ i)⟩)
    ⟨fun _ _ h ↦ hx (congrArg Subtype.val h), fun y ↦
      let ⟨i, _, hi⟩ := Finset.mem_image.mp (show y.val ∈ Finset.univ.image x from y.property)
      ⟨i, Subtype.ext hi⟩⟩
private noncomputable def rankPermutation {n : ℕ} (x : Fin n → ℝ) : Equiv.Perm (Fin n) := by
  classical
  exact if h : Injective x then
    (scoreEquiv x h).trans ((scoreImage x).orderIsoOfFin (card_scoreImage h)).symm.toEquiv
  else Equiv.refl _
theorem rankPermutation_lt_iff {n : ℕ} {x : Fin n → ℝ} (hx : Injective x) (i j : Fin n) :
    rankPermutation x i < rankPermutation x j ↔ x i < x j := by
  classical
  unfold rankPermutation
  rw [dif_pos hx]
  exact ((scoreImage x).orderIsoOfFin (card_scoreImage hx)).symm.lt_iff_lt
    (x := scoreEquiv x hx i) (y := scoreEquiv x hx j)
private def rankChamber {n : ℕ} (p : Equiv.Perm (Fin n)) : Set (Fin n → ℝ) :=
  {x | ∀ i j, p i < p j → x i < x j}
private theorem measurableSet_rankChamber {n : ℕ} (p : Equiv.Perm (Fin n)) :
    MeasurableSet (rankChamber p) := by
  unfold rankChamber
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun i ↦ ?_
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun j ↦ ?_
  by_cases h : p i < p j
  · simpa only [h, true_implies] using
      (measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j) :
        MeasurableSet {x : Fin n → ℝ | x i < x j})
  · simp [h]
private theorem measurableSet_injective_row (n : ℕ) :
    MeasurableSet {x : Fin n → ℝ | Injective x} := by
  unfold Injective
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun i ↦ ?_
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun j ↦ ?_
  by_cases h : i = j
  · simp [h]
  · exact ((measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j) :
      MeasurableSet {x : Fin n → ℝ | x i = x j}).compl).congr (by ext x; simp [h])
private theorem rankPermutation_eq_iff {n : ℕ} {x : Fin n → ℝ} (hx : Injective x)
    (p : Equiv.Perm (Fin n)) : rankPermutation x = p ↔ x ∈ rankChamber p := by
  constructor
  · rintro rfl i j hij
    exact (rankPermutation_lt_iff hx i j).mp hij
  · intro hp
    have hmono : StrictMono (rankPermutation x ∘ p.symm) := fun i j hij ↦
      (rankPermutation_lt_iff hx (p.symm i) (p.symm j)).mpr <|
        hp (p.symm i) (p.symm j) (by simpa using hij)
    apply Equiv.ext
    intro i
    simpa only [Function.comp_apply, Equiv.symm_apply_apply, id_eq] using
      le_antisymm (hmono.le_id (p i)) (hmono.id_le (p i))
theorem measurable_rankPermutation (n : ℕ) :
    @Measurable (Fin n → ℝ) (Equiv.Perm (Fin n)) inferInstance ⊤ rankPermutation := by
  classical
  let : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
  apply measurable_to_countable'
  intro p
  have hpre : rankPermutation ⁻¹' {p} =
      ({x : Fin n → ℝ | Injective x} ∩ rankChamber p) ∪
        ({x : Fin n → ℝ | Injective x}ᶜ ∩ {x : Fin n → ℝ | Equiv.refl (Fin n) = p}) := by
    ext x
    by_cases hx : Injective x
    · simpa only [mem_preimage, mem_singleton_iff, mem_union, mem_inter_iff, mem_ofPred_eq,
        mem_compl_iff, hx, not_true_eq_false, true_and, false_and, or_false] using
          rankPermutation_eq_iff hx p
    · simp [rankPermutation, hx]
  rw [hpre]
  exact ((measurableSet_injective_row n).inter (measurableSet_rankChamber p)).union
    ((measurableSet_injective_row n).compl.inter (MeasurableSet.const _))
private abbrev ScoreProfile (n : ℕ) := (Fin n ⊕ Fin n) → Fin n → ℝ
private noncomputable def profileOfScores {n : ℕ} (x : ScoreProfile n) : StableMarriage.Profile n :=
  ⟨fun m ↦ rankPermutation (x (.inl m)), fun w ↦ rankPermutation (x (.inr w))⟩
theorem measurable_profileOfScores (n : ℕ) : Measurable (@profileOfScores n) := by
  let : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
  let : DiscreteMeasurableSpace (Equiv.Perm (Fin n)) :=
    ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩
  have hrow (r : Fin n ⊕ Fin n) (p : Equiv.Perm (Fin n)) :
      MeasurableSet {x : ScoreProfile n | rankPermutation (x r) = p} :=
    ((measurable_rankPermutation n).comp (measurable_pi_apply r)) (measurableSet_singleton p)
  apply measurable_to_countable'
  rintro ⟨men, women⟩
  change MeasurableSet {x | profileOfScores x = ⟨men, women⟩}
  simp only [profileOfScores, StableMarriage.Profile.mk.injEq, funext_iff, Set.ofPred_and,
    Set.ofPred_forall]
  exact (MeasurableSet.iInter fun m ↦ hrow (.inl m) (men m)).inter
    (MeasurableSet.iInter fun w ↦ hrow (.inr w) (women w))
private def IsScoreBlockingPair {n : ℕ} (x : ScoreProfile n) (μ : StableMarriage.Matching n)
    (m w : Fin n) : Prop :=
  μ m ≠ w ∧ x (.inl m) w < x (.inl m) (μ m) ∧ x (.inr w) m < x (.inr w) (μ.symm w)
private def IsScoreStable {n : ℕ} (x : ScoreProfile n) (μ : StableMarriage.Matching n) : Prop :=
  ∀ m w, ¬ IsScoreBlockingPair x μ m w
theorem isBlockingPair_profileOfScores_iff {n : ℕ} {x : ScoreProfile n}
    (hx : ∀ r, Injective (x r)) (μ : StableMarriage.Matching n) (m w : Fin n) :
    StableMarriage.IsBlockingPair (profileOfScores x) μ m w ↔ IsScoreBlockingPair x μ m w := by
  simp only [StableMarriage.IsBlockingPair, profileOfScores, IsScoreBlockingPair,
    rankPermutation_lt_iff (hx (.inl m)), rankPermutation_lt_iff (hx (.inr w))]
theorem isStable_profileOfScores_iff {n : ℕ} {x : ScoreProfile n}
    (hx : ∀ r, Injective (x r)) (μ : StableMarriage.Matching n) :
    StableMarriage.IsStable (profileOfScores x) μ ↔ IsScoreStable x μ := by
  simp only [StableMarriage.IsStable, IsScoreStable, isBlockingPair_profileOfScores_iff hx]
theorem measurableSet_isScoreStable {n : ℕ} (μ : StableMarriage.Matching n) :
    MeasurableSet {x : ScoreProfile n | IsScoreStable x μ} := by
  have hcell (r : Fin n ⊕ Fin n) (a : Fin n) : Measurable (fun x : ScoreProfile n ↦ x r a) :=
    (measurable_pi_apply a).comp (measurable_pi_apply r)
  unfold IsScoreStable
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun m ↦ ?_
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun w ↦ ?_
  by_cases h : μ m = w
  · simp [IsScoreBlockingPair, h]
  · exact ((measurableSet_lt (hcell (.inl m) w) (hcell (.inl m) (μ m))).inter
      (measurableSet_lt (hcell (.inr w) m) (hcell (.inr w) (μ.symm w)))).compl.congr
        (Set.ext fun x ↦ by simp [IsScoreBlockingPair, h])
end CompLP
end

-- ContinuousScoreBridge
section
open scoped BigOperators ENNReal CompLP
open MeasureTheory Set
namespace CompLP
private noncomputable def unitScoreLaw : Measure ℝ :=
  volume.restrict (Icc 0 1)
private instance : IsProbabilityMeasure unitScoreLaw :=
  ⟨by simp [unitScoreLaw, Real.volume_Icc]⟩
private instance : NullSingletonClass unitScoreLaw :=
  Measure.restrict.instNullSingletonClass _
private noncomputable def continuousScoreLaw (n : ℕ) : Measure (ScoreProfile n) :=
  Measure.pi fun _ : Fin n ⊕ Fin n ↦ Measure.pi fun _ : Fin n ↦ unitScoreLaw
private instance (n : ℕ) : IsProbabilityMeasure (continuousScoreLaw n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : Fin n ⊕ Fin n ↦
    Measure.pi fun _ : Fin n ↦ unitScoreLaw))
theorem ae_injective_rows (n : ℕ) :
    ∀ᵐ x ∂continuousScoreLaw n, ∀ r, Function.Injective (x r) :=
  ae_all_iff.2 fun _ ↦ Measure.tendsto_eval_ae_ae.eventually (ae_injective_iid unitScoreLaw n)
end CompLP
end

-- CoexposureGoodScores
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal CompLP
namespace CompLP
variable {n : ℕ}
private def maleSpouseScore (x : ScoreProfile n) (μ : Matching n) (i : Fin n) : ℝ :=
  x (.inl i) (μ i)
private def femaleSpouseScore (x : ScoreProfile n) (μ : Matching n) (j : Fin n) : ℝ :=
  x (.inr j) (μ.symm j)
private def femaleSpouseTotal (x : ScoreProfile n) (μ : Matching n) : ℝ :=
  ∑ j, femaleSpouseScore x μ j
private theorem measurable_scoreCoordinate (r : Fin n ⊕ Fin n) (i : Fin n) :
    Measurable (fun x : ScoreProfile n ↦ x r i) :=
  (measurable_pi_apply i).comp (measurable_pi_apply r)
theorem measurable_maleSpouseScore (μ : Matching n) (i : Fin n) :
    Measurable (fun x : ScoreProfile n ↦ maleSpouseScore x μ i) :=
  measurable_scoreCoordinate (.inl i) (μ i)
theorem measurable_femaleSpouseScore (μ : Matching n) (j : Fin n) :
    Measurable (fun x : ScoreProfile n ↦ femaleSpouseScore x μ j) :=
  measurable_scoreCoordinate (.inr j) (μ.symm j)
theorem measurable_femaleSpouseTotal (μ : Matching n) :
    Measurable (fun x : ScoreProfile n ↦ femaleSpouseTotal x μ) :=
  Finset.measurable_sum _ (fun j _ ↦ measurable_femaleSpouseScore μ j)
theorem ae_unitOpen_scores (n : ℕ) :
    ∀ᵐ x ∂continuousScoreLaw n, ∀ r i, x r i ∈ Ioo (0 : ℝ) 1 := by
  have hopen : ∀ᵐ t ∂unitScoreLaw, t ∈ Ioo (0 : ℝ) 1 := by
    rw [unitScoreLaw, ← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  exact ae_all_iff.2 fun r ↦ ae_all_iff.2 fun i ↦
    (Measure.tendsto_eval_ae_ae (i := r)
      (μ := fun _ : Fin n ⊕ Fin n ↦ Measure.pi fun _ : Fin n ↦ unitScoreLaw)).eventually
      ((Measure.tendsto_eval_ae_ae (i := i) (μ := fun _ : Fin n ↦ unitScoreLaw)).eventually hopen)
end CompLP
end

-- CoexposureScoreEstimates
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal BigOperators Topology
namespace CompLP
end CompLP
end

-- PittelSimplexRadial
section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace CompLP
end CompLP
end

-- CoexposureScoreRow
section
open Set
open scoped BigOperators
namespace CompLP
variable {ι : Type*}
section FiniteRows
variable [Fintype ι] [DecidableEq ι]
end FiniteRows
section SuccessorMass
open MeasureTheory
open scoped ENNReal
end SuccessorMass
end CompLP
end

-- ExposedRotations
section
open StableMarriage
namespace CompLP
variable {n : ℕ}
private def IsEligibleSuccessor (p : Profile n) (μ : Matching n) (m w : Fin n) : Prop :=
  p.manRank m (μ m) < p.manRank m w ∧ p.womanRank w m < p.womanRank w (μ.symm w)
private abbrev premiseOf {A B : Prop} (_ : A → B) := A
private abbrev IsSuccessor (p : Profile n) (μ : Matching n) (m w : Fin n) : Prop :=
  premiseOf (@MarkedLP.IsSuccessor.unique n p μ m w w)
private theorem IsSuccessor.mk {p : Profile n} {μ : Matching n} {m w : Fin n}
    (h₁ : IsEligibleSuccessor p μ m w)
    (h₂ : ∀ w', IsEligibleSuccessor p μ m w' → p.manRank m w ≤ p.manRank m w') :
    IsSuccessor p μ m w := by
  constructor
  · exact h₁
  · exact h₂
private theorem IsSuccessor.eligible {p : Profile n} {μ : Matching n} {m w : Fin n}
    (h : IsSuccessor p μ m w) : IsEligibleSuccessor p μ m w := by
  obtain ⟨h₁, _⟩ := h
  exact h₁
private theorem IsSuccessor.min_rank {p : Profile n} {μ : Matching n} {m w : Fin n}
    (h : IsSuccessor p μ m w) :
    ∀ w', IsEligibleSuccessor p μ m w' → p.manRank m w ≤ p.manRank m w' := by
  obtain ⟨_, h₂⟩ := h
  exact h₂
private abbrev IsExposedRotation (p : Profile n) (μ : Matching n) (ρ : Equiv.Perm (Fin n)) : Prop :=
  premiseOf (@MarkedLP.IsExposedRotation.womanRank_eliminate_le n p μ ρ)
private theorem IsExposedRotation.mk {p : Profile n} {μ : Matching n} {ρ : Equiv.Perm (Fin n)}
    (h₁ : ρ.IsCycle) (h₂ : ∀ m, ρ m ≠ m → IsSuccessor p μ m (μ (ρ m))) :
    IsExposedRotation p μ ρ := by
  constructor
  · exact h₁
  · exact h₂
private theorem IsExposedRotation.isCycle {p : Profile n} {μ : Matching n} {ρ : Equiv.Perm (Fin n)}
    (h : IsExposedRotation p μ ρ) : ρ.IsCycle := by
  obtain ⟨h₁, _⟩ := h
  exact h₁
private theorem IsExposedRotation.successor {p : Profile n} {μ : Matching n} {ρ : Equiv.Perm (Fin n)}
    (h : IsExposedRotation p μ ρ) : ∀ m, ρ m ≠ m → IsSuccessor p μ m (μ (ρ m)) := by
  obtain ⟨_, h₂⟩ := h
  exact h₂
private def eliminateRotation (μ : Matching n) (ρ : Equiv.Perm (Fin n)) : Matching n :=
  ρ.trans μ
@[simp] theorem eliminateRotation_apply (μ : Matching n) (ρ : Equiv.Perm (Fin n)) (m : Fin n) :
    eliminateRotation μ ρ m = μ (ρ m) := rfl
variable {p : Profile n} {μ : Matching n} {ρ : Equiv.Perm (Fin n)}
theorem IsSuccessor.unique {m w w' : Fin n}
    (h : IsSuccessor p μ m w) (h' : IsSuccessor p μ m w') : w = w' :=
  (p.manRank m).injective <| le_antisymm ((IsSuccessor.min_rank h) w' (IsSuccessor.eligible h')) ((IsSuccessor.min_rank h') w (IsSuccessor.eligible h))
theorem IsExposedRotation.manRank_lt_eliminate_of_moved (hρ : IsExposedRotation p μ ρ)
    {m : Fin n} (hm : ρ m ≠ m) :
    p.manRank m (μ m) < p.manRank m (eliminateRotation μ ρ m) :=
  (IsSuccessor.eligible ((IsExposedRotation.successor hρ) m hm)).1
theorem IsExposedRotation.womanRank_eliminate_le (hρ : IsExposedRotation p μ ρ) (w : Fin n) :
    p.womanRank w ((eliminateRotation μ ρ).symm w) ≤ p.womanRank w (μ.symm w) :=
  let ⟨m, hm⟩ := (eliminateRotation μ ρ).surjective w
  have hle : p.womanRank (μ (ρ m)) m ≤ p.womanRank (μ (ρ m)) (ρ m) :=
    if h : ρ m = m then
      (congrArg (p.womanRank (μ (ρ m))) h.symm).le
    else by
      simpa only [Equiv.symm_apply_apply] using (IsSuccessor.eligible ((IsExposedRotation.successor hρ) m h)).2.le
  have htarget : p.womanRank (eliminateRotation μ ρ m)
        ((eliminateRotation μ ρ).symm (eliminateRotation μ ρ m)) ≤
      p.womanRank (eliminateRotation μ ρ m) (μ.symm (eliminateRotation μ ρ m)) := by
    have hinv : (eliminateRotation μ ρ).symm (μ (ρ m)) = m :=
      (eliminateRotation μ ρ).symm_apply_apply m
    simpa only [eliminateRotation_apply, hinv, Equiv.symm_apply_apply] using hle
  hm ▸ htarget
theorem IsExposedRotation.isStable_eliminate (hρ : IsExposedRotation p μ ρ)
    (hμ : IsStable p μ) : IsStable p (eliminateRotation μ ρ) :=
  fun m w hb ↦
    have hwOld : p.womanRank w m < p.womanRank w (μ.symm w) :=
      hb.2.2.trans_le (hρ.womanRank_eliminate_le w)
    have hne : μ m ≠ w := fun h ↦ (ne_of_lt hwOld)
      (congrArg (p.womanRank w) ((μ.symm_apply_apply m).symm.trans (congrArg μ.symm h)))
    have hnot : ¬ p.manRank m w < p.manRank m (μ m) := fun h ↦
      hμ m w ⟨hne, h, hwOld⟩
    if hm : ρ m = m then
      hnot (by simpa only [eliminateRotation_apply, hm] using hb.2.1)
    else
      have hbelow : p.manRank m (μ m) < p.manRank m w :=
        lt_of_le_of_ne (le_of_not_gt hnot) (fun he ↦ hne ((p.manRank m).injective he))
      (not_lt_of_ge ((IsSuccessor.min_rank ((IsExposedRotation.successor hρ) m hm)) w ⟨hbelow, hwOld⟩)) hb.2.1
end CompLP
end

-- CoexposureScoreProduct
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace CompLP
private abbrev ScorePairIndex (n : ℕ) := Fin n × Fin n
private abbrev DiagonalScorePairs (n : ℕ) := {q : ScorePairIndex n // q.1 = q.2} → ℝ × ℝ
private abbrev OffDiagonalScorePairs (n : ℕ) := {q : ScorePairIndex n // q.1 ≠ q.2} → ℝ × ℝ
private def manScoreIndex {n : ℕ} (μ : Matching n) : ScorePairIndex n ≃ ScorePairIndex n :=
  Equiv.prodCongr (Equiv.refl _) μ
private def womanScoreIndex {n : ℕ} (μ : Matching n) : ScorePairIndex n ≃ ScorePairIndex n :=
  (manScoreIndex μ).trans (Equiv.prodComm _ _)
private def scorePairEquiv {n : ℕ} (μ : Matching n) :
    ScoreProfile n ≃ᵐ (ScorePairIndex n → ℝ × ℝ) :=
  ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin n ↦ Fin n → ℝ)).trans
    (((MeasurableEquiv.curry (Fin n) (Fin n) ℝ).symm.trans
      (MeasurableEquiv.piCongrLeft (fun _ : ScorePairIndex n ↦ ℝ) (manScoreIndex μ).symm)).prodCongr
    ((MeasurableEquiv.curry (Fin n) (Fin n) ℝ).symm.trans
      (MeasurableEquiv.piCongrLeft (fun _ : ScorePairIndex n ↦ ℝ)
        (womanScoreIndex μ).symm)))).trans
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (ScorePairIndex n)).symm
private theorem scorePairEquiv_apply {n : ℕ} (μ : Matching n) (x : ScoreProfile n)
    (i j : Fin n) :
    scorePairEquiv μ x (i,j) = (x (.inl i) (μ j), x (.inr (μ j)) i) := by
  change ((MeasurableEquiv.piCongrLeft (fun _ : ScorePairIndex n ↦ ℝ)
      (manScoreIndex μ).symm) (fun q ↦ x (.inl q.1) q.2) (i,j),
    (MeasurableEquiv.piCongrLeft (fun _ : ScorePairIndex n ↦ ℝ)
      (womanScoreIndex μ).symm) (fun q ↦ x (.inr q.1) q.2) (i,j)) = _
  simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast,
    manScoreIndex, womanScoreIndex]
private def splitScorePairs {n : ℕ} (μ : Matching n) :
    ScoreProfile n ≃ᵐ DiagonalScorePairs n × OffDiagonalScorePairs n :=
  (scorePairEquiv μ).trans
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ScorePairIndex n ↦ ℝ × ℝ)
      fun q ↦ q.1 = q.2)
private def diagonalPairAt {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n) : ℝ × ℝ :=
  d ⟨(i,i), rfl⟩
theorem diagonalPairAt_splitScorePairs {n : ℕ} (μ : Matching n) (x : ScoreProfile n)
    (i : Fin n) :
    diagonalPairAt (splitScorePairs μ x).1 i = (x (.inl i) (μ i), x (.inr (μ i)) i) :=
  scorePairEquiv_apply μ x i i
theorem splitScorePairs_offDiagonal_apply {n : ℕ} (μ : Matching n) (x : ScoreProfile n)
    (q : {q : ScorePairIndex n // q.1 ≠ q.2}) :
    (splitScorePairs μ x).2 q =
      (x (.inl q.val.1) (μ q.val.2), x (.inr (μ q.val.2)) q.val.1) :=
  scorePairEquiv_apply μ x q.val.1 q.val.2
end CompLP
end

-- CoexposureSpouseMarginal
section
open Filter MeasureTheory ProbabilityTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace CompLP
private def femaleSpouseByHusband {n : ℕ} (μ : Matching n) (x : ScoreProfile n) : Fin n → ℝ :=
  fun j ↦ femaleSpouseScore x μ (μ j)
theorem femaleSpouseTotal_eq_sum_byHusband {n : ℕ} (μ : Matching n) (x : ScoreProfile n) :
    femaleSpouseTotal x μ = ∑ j, femaleSpouseByHusband μ x j :=
  (Equiv.sum_comp μ (femaleSpouseScore x μ)).symm
end CompLP
end

-- FiniteProductDensity
section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace CompLP
variable {ι : Type*} [Fintype ι] {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
end CompLP
end

-- PivotSpouseProductLower
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace CompLP
private def maleSpouseTotal {n : ℕ} (x : ScoreProfile n) (μ : Matching n) : ℝ :=
  ∑ i, maleSpouseScore x μ i
theorem measurable_maleSpouseTotal {n : ℕ} (μ : Matching n) :
    Measurable (fun x : ScoreProfile n ↦ maleSpouseTotal x μ) :=
  Finset.measurable_sum _ fun i _ ↦ measurable_maleSpouseScore μ i
end CompLP
end

-- PivotForwardRevealCell
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace CompLP
private def forwardEligibleScoreCell (x y : ℝ) : Set (ℝ × ℝ) :=
  Ioi x ×ˢ Iio y
private def forwardScoreCellFlagEvent (x y : ℝ) (b : Bool) : Set (ℝ × ℝ) :=
  if b then forwardEligibleScoreCell x y else (forwardEligibleScoreCell x y)ᶜ
private abbrev OffDiagonalCellIndex (n : ℕ) := {q : ScorePairIndex n // q.1 ≠ q.2}
private def forwardScoreMaskEvent {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) : Set (OffDiagonalScorePairs n) :=
  univ.pi fun q ↦ forwardScoreCellFlagEvent
    (diagonalPairAt d q.val.1).1 (diagonalPairAt d q.val.2).2 (flag q)
private abbrev ForwardActiveCellIndex {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :=
  {q : OffDiagonalCellIndex n // flag q = true}
private abbrev ForwardInactiveCellIndex {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :=
  {q : OffDiagonalCellIndex n // flag q ≠ true}
private def forwardScoreMaskRevealAndInactive {n : ℕ} (flag : OffDiagonalCellIndex n → Bool)
    (z : OffDiagonalScorePairs n) :
    (ForwardActiveCellIndex flag → ℝ) × (ForwardInactiveCellIndex flag → ℝ × ℝ) :=
  (fun q ↦ (z q.val).1, fun q ↦ z q.val)
theorem measurable_forwardScoreMaskRevealAndInactive {n : ℕ}
    (flag : OffDiagonalCellIndex n → Bool) :
    Measurable (forwardScoreMaskRevealAndInactive flag) :=
  (measurable_pi_iff.2 fun q ↦ measurable_fst.comp (measurable_pi_apply q.val)).prodMk
    (measurable_pi_iff.2 fun q ↦ measurable_pi_apply q.val)
private abbrev ForwardInactiveColumnIndex {n : ℕ} (flag : OffDiagonalCellIndex n → Bool)
    (j : Fin n) := {q : ForwardInactiveCellIndex flag // q.val.val.2 = j}
private def forwardInactiveColumnsEquiv {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :
    (ForwardInactiveCellIndex flag → ℝ × ℝ) ≃ᵐ
      ((j : Fin n) → ForwardInactiveColumnIndex flag j → ℝ × ℝ) where
  toFun z _ q := z q.val
  invFun z q := z q.val.val.2 ⟨q, rfl⟩
  left_inv _ := rfl
  right_inv z := by
    funext j q
    obtain ⟨q, rfl⟩ := q
    rfl
  measurable_toFun := measurable_pi_iff.2 fun _ ↦
    measurable_pi_iff.2 fun _ ↦ measurable_pi_apply _
  measurable_invFun := measurable_pi_iff.2 fun q ↦
    (measurable_pi_apply (⟨q, rfl⟩ : ForwardInactiveColumnIndex flag q.val.val.2)).comp
      (measurable_pi_apply q.val.val.2)
end CompLP
end

-- ReverseSuccessorRotation
section
open StableMarriage
namespace CompLP
variable {n : ℕ} {p : Profile n} {μ : Matching n} {ρ : Equiv.Perm (Fin n)}
private def swapProfile (p : Profile n) : Profile n :=
  ⟨p.womanRank, p.manRank⟩
@[simp] theorem swapProfile_swapProfile (p : Profile n) : swapProfile (swapProfile p) = p := rfl
theorem isStable_swapProfile_iff : IsStable (swapProfile p) μ.symm ↔ IsStable p μ := by
  constructor
  · intro h m w hb
    exact h w m
      ⟨fun he ↦ hb.1 ((congrArg μ he).symm.trans (μ.apply_symm_apply w)), hb.2.2, hb.2.1⟩
  · intro h w m hb
    refine h m w ⟨fun he ↦ hb.1 ?_, hb.2.2, hb.2.1⟩
    simpa only [Equiv.symm_apply_apply] using (congrArg μ.symm he).symm
private def reverseRotationCycle (μ : Matching n) (ρ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  μ.symm.trans (ρ.trans μ)
theorem eliminateRotation_swap_reverseCycle (μ : Matching n) (ρ : Equiv.Perm (Fin n)) :
    eliminateRotation (eliminateRotation μ ρ).symm (reverseRotationCycle μ ρ) = μ.symm := by
  ext w
  simp [reverseRotationCycle, eliminateRotation]
theorem reverseRotationCycle_swap_reverseCycle (μ : Matching n) (ρ : Equiv.Perm (Fin n)) :
    reverseRotationCycle (eliminateRotation μ ρ).symm (reverseRotationCycle μ ρ) = ρ := by
  ext m
  simp [reverseRotationCycle, eliminateRotation]
theorem IsExposedRotation.isExposedRotation_swap_eliminate
    (hρ : IsExposedRotation p μ ρ) (hμ : IsStable p μ) :
    IsExposedRotation (swapProfile p) (eliminateRotation μ ρ).symm
      (reverseRotationCycle μ ρ) := by
  refine (IsExposedRotation.mk (?_) (?_))
  · change (μ * ρ * μ⁻¹).IsCycle
    exact (IsExposedRotation.isCycle hρ).conj
  · intro w hw
    obtain ⟨m, rfl⟩ := μ.surjective w
    have hm : ρ m ≠ m := by
      intro he
      apply hw
      simp [reverseRotationCycle, he]
    have hback : ρ (ρ.symm m) ≠ ρ.symm m := by
      intro he
      have he' : m = ρ.symm m := by simpa only [Equiv.apply_symm_apply] using he
      exact hm ((congrArg ρ he').trans (ρ.apply_symm_apply m))
    have hnew : (eliminateRotation μ ρ).symm (reverseRotationCycle μ ρ (μ m)) = m := by
      simp [reverseRotationCycle, eliminateRotation]
    have hcurrent : (eliminateRotation μ ρ).symm (μ m) = ρ.symm m := by
      simp [eliminateRotation]
    refine IsSuccessor.mk ?_ ?_
    · have hprev := (IsSuccessor.eligible ((IsExposedRotation.successor hρ) (ρ.symm m) hback)).2
      have hwlt : p.womanRank (μ m) (ρ.symm m) < p.womanRank (μ m) m := by
        simpa only [Equiv.apply_symm_apply, Equiv.symm_apply_apply] using hprev
      simp only [IsEligibleSuccessor, swapProfile, hnew, hcurrent, Equiv.symm_symm,
        eliminateRotation_apply]
      exact ⟨hwlt, (IsSuccessor.eligible ((IsExposedRotation.successor hρ) m hm)).1⟩
    · intro t ht
      simp only [IsEligibleSuccessor, swapProfile, hcurrent, Equiv.symm_symm,
        eliminateRotation_apply] at ht
      change p.womanRank (μ m) ((eliminateRotation μ ρ).symm
        (reverseRotationCycle μ ρ (μ m))) ≤ p.womanRank (μ m) t
      rw [hnew]
      by_contra hbad
      
      have hwbad := lt_of_not_ge hbad
      have hne : μ t ≠ μ m := fun he ↦
        (ne_of_lt hwbad) (congrArg (p.womanRank (μ m)) (μ.injective he))
      have hnot : ¬ p.manRank t (μ m) < p.manRank t (μ t) := fun ht' ↦
        hμ t (μ m) ⟨hne, ht', by simpa only [Equiv.symm_apply_apply] using hwbad⟩
      have hf : IsEligibleSuccessor p μ t (μ m) :=
        ⟨lt_of_le_of_ne (le_of_not_gt hnot) (fun he ↦ hne ((p.manRank t).injective he)),
          by simpa only [Equiv.symm_apply_apply] using hwbad⟩
      by_cases htfix : ρ t = t
      · exact (not_lt_of_ge hf.1.le) (by simpa only [htfix] using ht.2)
      · exact (not_lt_of_ge ((IsSuccessor.min_rank ((IsExposedRotation.successor hρ) t htfix)) _ hf)) ht.2
end CompLP
end

-- FinitePrerequisites
section
namespace CompLP
theorem mem_family_of_downward_closed {α : Type*} [Finite α] {F : Set (Set α)}
    (hempty : ∅ ∈ F)
    (hinter : ∀ ⦃A B⦄, A ∈ F → B ∈ F → A ∩ B ∈ F)
    (hunion : ∀ ⦃A B⦄, A ∈ F → B ∈ F → A ∪ B ∈ F)
    (hcover : ∀ a : α, ∃ A ∈ F, a ∈ A) {I : Set α}
    (hdown : ∀ ⦃a b : α⦄, (∀ A ∈ F, b ∈ A → a ∈ A) → b ∈ I → a ∈ I) :
    I ∈ F := by
  
  let P (b : α) : Set α := ⋂₀ {A : Set α | A ∈ F ∧ b ∈ A}
  have hInf : InfClosed F := fun _ hA _ hB ↦ hinter hA hB
  have hP (b : α) : P b ∈ F := by
    obtain ⟨A, hA, hbA⟩ := hcover b
    change sInf {A : Set α | A ∈ F ∧ b ∈ A} ∈ F
    exact hInf.sInf_mem_of_nonempty (Set.toFinite _) ⟨A, hA, hbA⟩ fun _ h ↦ h.1
  
  have hEq : I = ⋃ b : I, P b := by
    ext a
    constructor
    · intro ha
      exact Set.mem_iUnion_of_mem ⟨a, ha⟩ (Set.mem_sInter.mpr fun _ h ↦ h.2)
    · intro ha
      obtain ⟨b, hab⟩ := Set.mem_iUnion.mp ha
      exact hdown (fun A hA hb ↦ Set.mem_sInter.mp hab A ⟨hA, hb⟩) b.property
  have hSup : SupClosed F := fun _ hA _ hB ↦ hunion hA hB
  rw [hEq]
  exact hSup.iSup_mem hempty fun b : I ↦ hP b
end CompLP
end

-- RotationDiamond
section
open StableMarriage
namespace CompLP
variable {n : ℕ} {p : Profile n} {μ : Matching n} {ρ σ : Equiv.Perm (Fin n)}
private theorem moved_image {f : Equiv.Perm (Fin n)} {i : Fin n} (hi : f i ≠ i) :
    f (f i) ≠ f i :=
  f.injective.ne hi
private theorem eq_of_common_moved (hρ : IsExposedRotation p μ ρ) (hσ : IsExposedRotation p μ σ)
    {m : Fin n} (hmρ : ρ m ≠ m) (hmσ : σ m ≠ m) : ρ = σ := by
  have hagree (i : Fin n) (hiρ : ρ i ≠ i) (hiσ : σ i ≠ i) : ρ i = σ i :=
    μ.injective (((IsExposedRotation.successor hρ) i hiρ).unique ((IsExposedRotation.successor hσ) i hiσ))
  have horbit (k : ℕ) :
      (ρ ^ k) m = (σ ^ k) m ∧ ρ ((ρ ^ k) m) ≠ (ρ ^ k) m ∧ σ ((σ ^ k) m) ≠ (σ ^ k) m := by
    induction k with
    | zero => simpa using And.intro (rfl : m = m) (And.intro hmρ hmσ)
    | succ k ih =>
      obtain ⟨heq, hmoveρ, hmoveσ⟩ := ih
      have hmoveσ' : σ ((ρ ^ k) m) ≠ (ρ ^ k) m := heq ▸ hmoveσ
      simp only [pow_succ', Equiv.Perm.mul_apply]
      exact ⟨(hagree _ hmoveρ hmoveσ').trans (congrArg σ heq),
        moved_image hmoveρ, moved_image hmoveσ⟩
  apply Equiv.ext
  intro i
  by_cases hi : ρ i ≠ i
  · obtain ⟨k, hk⟩ := (IsExposedRotation.isCycle hρ).exists_pow_eq hmρ hi
    have his : σ i ≠ i := by
      rw [← hk, (horbit k).1]
      exact (horbit k).2.2
    exact hagree i hi his
  · have his : σ i = i := by
      by_contra hsi
      obtain ⟨k, hk⟩ := (IsExposedRotation.isCycle hσ).exists_pow_eq hmσ hsi
      apply hi
      rw [← hk, ← (horbit k).1]
      exact (horbit k).2.1
    exact (not_ne_iff.mp hi).trans his.symm
theorem IsExposedRotation.disjoint_moved (hρ : IsExposedRotation p μ ρ)
    (hσ : IsExposedRotation p μ σ) (hne : ρ ≠ σ) (m : Fin n) (hm : ρ m ≠ m) : σ m = m := by
  by_contra hs
  exact hne (eq_of_common_moved hρ hσ hm hs)
theorem IsExposedRotation.persist_eliminate (hρ : IsExposedRotation p μ ρ)
    (hσ : IsExposedRotation p μ σ) (hne : ρ ≠ σ) :
    IsExposedRotation p (eliminateRotation μ σ) ρ := by
  refine (IsExposedRotation.mk ((IsExposedRotation.isCycle hρ)) (fun m hm ↦ ?_))
  let μ' := eliminateRotation μ σ
  have hold : μ' m = μ m := congrArg μ (hρ.disjoint_moved hσ hne m hm)
  have hnext : μ' (ρ m) = μ (ρ m) :=
    congrArg μ (hρ.disjoint_moved hσ hne (ρ m) (moved_image hm))
  have hs := (IsExposedRotation.successor hρ) m hm
  have helig : IsEligibleSuccessor p μ' m (μ' (ρ m)) := by
    refine ⟨?_, ?_⟩
    · simpa only [hold, hnext] using (IsSuccessor.eligible hs).1
    · rw [Equiv.symm_apply_apply, hnext]
      simpa only [Equiv.symm_apply_apply] using (IsSuccessor.eligible hs).2
  refine (IsSuccessor.mk (helig) (fun w hw ↦ ?_))
  have hman : p.manRank m (μ' m) < p.manRank m w := hw.1
  rw [hold] at hman
  have hbefore : IsEligibleSuccessor p μ m w :=
    ⟨hman, hw.2.trans_le (hσ.womanRank_eliminate_le w)⟩
  change p.manRank m (μ' (ρ m)) ≤ p.manRank m w
  rw [hnext]
  exact (IsSuccessor.min_rank hs) w hbefore
theorem IsExposedRotation.eliminate_comm (hρ : IsExposedRotation p μ ρ)
    (hσ : IsExposedRotation p μ σ) (hne : ρ ≠ σ) :
    eliminateRotation (eliminateRotation μ ρ) σ = eliminateRotation (eliminateRotation μ σ) ρ := by
  apply Equiv.ext
  intro m
  simp only [eliminateRotation_apply]
  by_cases hr : ρ m = m
  · by_cases hs : σ m = m
    · simp only [hr, hs]
    · have hfix := hσ.disjoint_moved hρ hne.symm (σ m) (moved_image hs)
      simp only [hr, hfix]
  · have hfix := hρ.disjoint_moved hσ hne m hr
    have hfix' := hρ.disjoint_moved hσ hne (ρ m) (moved_image hr)
    simp only [hfix, hfix']
end CompLP
end

-- ManOptimal
section
open StableMarriage
open scoped BigOperators
namespace CompLP
variable {n : ℕ}
private def MenWeaklyPrefer (p : Profile n) (μ ν : Matching n) : Prop :=
  ∀ m, p.manRank m (μ m) ≤ p.manRank m (ν m)
private def IsManOptimal (p : Profile n) (μ : Matching n) : Prop :=
  IsStable p μ ∧ ∀ ν, IsStable p ν → MenWeaklyPrefer p μ ν
private def betterPartner (p : Profile n) (μ ν : Matching n) (m : Fin n) : Fin n :=
  if p.manRank m (μ m) ≤ p.manRank m (ν m) then μ m else ν m
private theorem betterPartner_spec (p : Profile n) (μ ν : Matching n) (m : Fin n) :
    (betterPartner p μ ν m = μ m ∨ betterPartner p μ ν m = ν m) ∧
      p.manRank m (betterPartner p μ ν m) ≤ p.manRank m (μ m) ∧
      p.manRank m (betterPartner p μ ν m) ≤ p.manRank m (ν m) := by
  unfold betterPartner
  split
  · rename_i h
    exact ⟨Or.inl rfl, le_rfl, h⟩
  · rename_i h
    exact ⟨Or.inr rfl, le_of_not_ge h, le_rfl⟩
private theorem woman_prefers_husband {p : Profile n} {μ : Matching n}
    (hμ : IsStable p μ) {m w : Fin n}
    (hm : p.manRank m w < p.manRank m (μ m)) :
    p.womanRank w (μ.symm w) < p.womanRank w m := by
  have hneq : μ m ≠ w := fun h ↦ hm.ne (congrArg (p.manRank m) h.symm)
  have hn : ¬ p.womanRank w m < p.womanRank w (μ.symm w) :=
    fun h ↦ hμ m w ⟨hneq, hm, h⟩
  exact lt_of_le_of_ne (le_of_not_gt hn) fun h ↦
    hneq ((Equiv.symm_apply_eq μ).mp ((p.womanRank w).injective h)).symm
private theorem betterPartner_injective {p : Profile n} {μ ν : Matching n}
    (hμ : IsStable p μ) (hν : IsStable p ν) :
    Function.Injective (betterPartner p μ ν) := by
  let f := betterPartner p μ ν
  have hcross (a b : Fin n) (ha : f a = μ a) (hb : f b = ν b) (h : f a = f b) :
      a = b := by
    by_contra hab
    have haw : μ a = f a := ha.symm
    have hbw : ν b = f a := hb.symm.trans h.symm
    have haν : p.manRank a (f a) < p.manRank a (ν a) :=
      lt_of_le_of_ne (betterPartner_spec p μ ν a).2.2 fun e ↦
        hab (ν.injective (((p.manRank a).injective e).symm.trans hbw.symm))
    have hbμ : p.manRank b (f a) < p.manRank b (μ b) :=
      lt_of_le_of_ne (h.symm ▸ (betterPartner_spec p μ ν b).2.1) fun e ↦
        hab (μ.injective (haw.trans ((p.manRank b).injective e)))
    have hμhusband : μ.symm (f a) = a := (Equiv.symm_apply_eq μ).2 ha
    have hνhusband : ν.symm (f a) = b := (Equiv.symm_apply_eq ν).2 hbw.symm
    have hfab : p.womanRank (f a) a < p.womanRank (f a) b :=
      by simpa only [hμhusband] using woman_prefers_husband hμ hbμ
    have hfba : p.womanRank (f a) b < p.womanRank (f a) a :=
      by simpa only [hνhusband] using woman_prefers_husband hν haν
    exact lt_asymm hfab hfba
  intro a b h
  rcases (betterPartner_spec p μ ν a).1 with ha | ha <;>
    rcases (betterPartner_spec p μ ν b).1 with hb | hb
  · exact μ.injective (ha.symm.trans (h.trans hb))
  · exact hcross a b ha hb h
  · exact (hcross b a hb ha h.symm).symm
  · exact ν.injective (ha.symm.trans (h.trans hb))
theorem exists_stable_manRank_min {p : Profile n} {μ ν : Matching n}
    (hμ : IsStable p μ) (hν : IsStable p ν) :
    ∃ τ, IsStable p τ ∧
      ∀ m, p.manRank m (τ m) = min (p.manRank m (μ m)) (p.manRank m (ν m)) := by
  have hinj := betterPartner_injective hμ hν
  let τ : Matching n := Equiv.ofBijective (betterPartner p μ ν)
    ⟨hinj, Finite.surjective_of_injective hinj⟩
  have hleft : MenWeaklyPrefer p τ μ := fun m ↦ (betterPartner_spec p μ ν m).2.1
  have hright : MenWeaklyPrefer p τ ν := fun m ↦ (betterPartner_spec p μ ν m).2.2
  refine ⟨τ, ?_, fun m ↦ ?_⟩
  · intro m w hb
    have conflict (σ : Matching n) (hσ : IsStable p σ) (hpref : MenWeaklyPrefer p τ σ)
        (hsource : τ (τ.symm w) = σ (τ.symm w)) : False := by
      have hhusband : σ.symm w = τ.symm w :=
        (Equiv.symm_apply_eq σ).2 ((τ.apply_symm_apply w).symm.trans hsource)
      have hm : p.manRank m w < p.manRank m (σ m) := hb.2.1.trans_le (hpref m)
      exact hσ m w ⟨fun he ↦ hm.ne (congrArg (p.manRank m) he.symm), hm,
        hhusband.symm ▸ hb.2.2⟩
    exact ((betterPartner_spec p μ ν (τ.symm w)).1).elim (conflict μ hμ hleft)
      (conflict ν hν hright)
  · have hsource : τ m = μ m ∨ τ m = ν m := (betterPartner_spec p μ ν m).1
    rcases hsource with h | h
    · have hle := hright m
      rw [h] at hle ⊢
      exact (min_eq_left hle).symm
    · have hle := hleft m
      rw [h] at hle ⊢
      exact (min_eq_right hle).symm
theorem exists_stable_menWeaklyPrefer {p : Profile n} {μ ν : Matching n}
    (hμ : IsStable p μ) (hν : IsStable p ν) :
    ∃ τ, IsStable p τ ∧ MenWeaklyPrefer p τ μ ∧ MenWeaklyPrefer p τ ν := by
  obtain ⟨τ, hτ, hmin⟩ := exists_stable_manRank_min hμ hν
  exact ⟨τ, hτ, fun m ↦ (hmin m).le.trans (min_le_left _ _),
    fun m ↦ (hmin m).le.trans (min_le_right _ _)⟩
private def manOptimal_swapProfile (p : Profile n) : Profile n :=
  ⟨p.womanRank, p.manRank⟩
private theorem isStable_swap {p : Profile n} {μ : Matching n}
    (hμ : IsStable p μ) : IsStable (manOptimal_swapProfile p) μ.symm := by
  intro w m hb
  exact hμ m w ⟨fun h ↦ hb.1 ((Equiv.symm_apply_eq μ).2 h.symm), hb.2.2, hb.2.1⟩
theorem exists_stable_manRank_max {p : Profile n} {μ ν : Matching n}
    (hμ : IsStable p μ) (hν : IsStable p ν) :
    ∃ τ, IsStable p τ ∧
      ∀ m, p.manRank m (τ m) = max (p.manRank m (μ m)) (p.manRank m (ν m)) := by
  obtain ⟨σ, hσ, hmin⟩ := exists_stable_manRank_min (isStable_swap hμ) (isStable_swap hν)
  let τ := σ.symm
  have hw (w : Fin n) : p.womanRank w (τ.symm w) =
      min (p.womanRank w (μ.symm w)) (p.womanRank w (ν.symm w)) := hmin w
  
  have hworse (δ : Matching n) (hδ : IsStable p δ)
      (hδrank : ∀ w, p.womanRank w (τ.symm w) ≤ p.womanRank w (δ.symm w)) (m : Fin n) :
      p.manRank m (δ m) ≤ p.manRank m (τ m) := by
    by_contra h
    have hh := woman_prefers_husband hδ (lt_of_not_ge h)
    exact (not_lt_of_ge (hδrank (τ m))) (by simpa only [Equiv.symm_apply_apply] using hh)
  refine ⟨τ, isStable_swap hσ, fun m ↦ ?_⟩
  have hchoice : τ m = μ m ∨ τ m = ν m := by
    let w := τ m
    rcases le_total (p.womanRank w (μ.symm w)) (p.womanRank w (ν.symm w)) with h | h
    · have hhusband := (p.womanRank w).injective ((hw w).trans (min_eq_left h))
      exact Or.inl ((Equiv.symm_apply_eq μ).mp (hhusband.symm.trans (τ.symm_apply_apply m)))
    · have hhusband := (p.womanRank w).injective ((hw w).trans (min_eq_right h))
      exact Or.inr ((Equiv.symm_apply_eq ν).mp (hhusband.symm.trans (τ.symm_apply_apply m)))
  rcases hchoice with h | h
  · have hle := hworse ν hν (fun w ↦ (hw w).le.trans (min_le_right _ _)) m
    rw [h] at hle ⊢
    exact (max_eq_left hle).symm
  · have hle := hworse μ hμ (fun w ↦ (hw w).le.trans (min_le_left _ _)) m
    rw [h] at hle ⊢
    exact (max_eq_right hle).symm
private def manOptimal_totalManRank (p : Profile n) (μ : Matching n) : ℕ :=
  ∑ m : Fin n, (p.manRank m (μ m)).val
theorem exists_manOptimal_of_exists_stable {p : Profile n}
    (h : ∃ μ, IsStable p μ) : ∃ μ, IsManOptimal p μ := by
  classical
  let st : Finset (Matching n) := Finset.univ.filter (IsStable p)
  obtain ⟨s, hs⟩ := h
  obtain ⟨μ, hμ, hmin⟩ := st.exists_min_image (manOptimal_totalManRank p)
    ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩⟩
  have hμStable : IsStable p μ := (Finset.mem_filter.mp hμ).2
  refine ⟨μ, hμStable, ?_⟩
  intro ν hν m
  by_contra hbad
  obtain ⟨τ, hτ, hτμ, hτν⟩ := exists_stable_menWeaklyPrefer hμStable hν
  have hlt : manOptimal_totalManRank p τ < manOptimal_totalManRank p μ :=
    Finset.sum_lt_sum (fun i _ ↦ hτμ i)
      ⟨m, Finset.mem_univ _, (hτν m).trans_lt (lt_of_not_ge hbad)⟩
  exact (not_lt_of_ge (hmin τ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hτ⟩))) hlt
end CompLP
end

-- RotationCycle
section
namespace CompLP
open Function
private theorem periodicPt_of_repeat {α : Type*} {f : α → α} {x : α} {i j : ℕ}
    (hij : i < j) (heq : f^[i] x = f^[j] x) :
    f^[i] x ∈ periodicPts f :=
  mk_mem_periodicPts (Nat.sub_pos_of_lt hij)
    (show f^[j - i] (f^[i] x) = f^[i] x by
      rw [← iterate_add_apply, Nat.sub_add_cancel hij.le, ← heq])
private theorem nonempty_periodicPts {α : Type*} [Finite α] [Nonempty α] (f : α → α) :
    (periodicPts f).Nonempty :=
  let x := Classical.choice (inferInstance : Nonempty α)
  have hrepeat : ∃ i j, f^[i] x = f^[j] x ∧ i ≠ j := by
    simpa [Injective] using not_injective_infinite_finite (f^[·] x)
  let ⟨i, j, heq, hne⟩ := hrepeat
  (lt_or_gt_of_ne hne).elim
    (fun h ↦ ⟨_, periodicPt_of_repeat h heq⟩)
    (fun h ↦ ⟨_, periodicPt_of_repeat h heq.symm⟩)
theorem exists_cycle_permutation {α : Type*} [Finite α] {s : Set α} [Nonempty s]
    (f : s → s) (hnf : ∀ x, f x ≠ x) :
    ∃ ρ : Equiv.Perm α, ρ.IsCycle ∧
      ∀ a, ρ a ≠ a → ∃ ha : a ∈ s, ρ a = (f ⟨a, ha⟩).1 := by
  classical
  let ⟨a, ha⟩ := nonempty_periodicPts f
  let hbij := bijOn_periodicPts f
  let e : Equiv.Perm (periodicPts f) := Equiv.ofBijective _ hbij.bijective
  let τ : Equiv.Perm s := Equiv.Perm.ofSubtype e
  let σ : Equiv.Perm α := Equiv.Perm.ofSubtype τ
  have hτ (x : s) (hx : x ∈ periodicPts f) : τ x = f x :=
    Equiv.Perm.ofSubtype_apply_of_mem e hx
  have hσ (x : s) (hx : x ∈ periodicPts f) : σ x.1 = (f x).1 :=
    (Equiv.Perm.ofSubtype_apply_coe τ x).trans (congrArg Subtype.val (hτ x hx))
  have hmove : σ a.1 ≠ a.1 := fun h ↦ hnf a (Subtype.ext ((hσ a ha).symm.trans h))
  exact ⟨σ.cycleOf a.1, σ.isCycle_cycleOf hmove, fun x hne ↦
    have hsame : σ.SameCycle a.1 x := Classical.byContradiction fun h ↦
      hne (Equiv.Perm.cycleOf_apply_of_not_sameCycle h)
    have heq := hsame.cycleOf_apply
    have hσne : σ x ≠ x := fun h ↦ hne (heq.trans h)
    have hx : x ∈ s := Classical.byContradiction fun h ↦
      hσne (Equiv.Perm.ofSubtype_apply_of_not_mem τ h)
    have hper : (⟨x, hx⟩ : s) ∈ periodicPts f := Classical.byContradiction fun h ↦
      hσne <| (Equiv.Perm.ofSubtype_apply_of_mem τ hx).trans <|
        congrArg Subtype.val (Equiv.Perm.ofSubtype_apply_of_not_mem e h)
    ⟨hx, heq.trans (hσ ⟨x, hx⟩ hper)⟩⟩
end CompLP
end

-- TargetSuccessor
section
open StableMarriage
namespace CompLP
variable {n : ℕ} {p : Profile n} {μ ν : Matching n}
private theorem target_partner_eligible (hν : IsStable p ν)
    (hle : ∀ i, p.manRank i (μ i) ≤ p.manRank i (ν i))
    {m : Fin n} (hm : μ m ≠ ν m) : IsEligibleSuccessor p μ m (ν m) :=
  let j := μ.symm (ν m)
  have hjμ : μ j = ν m := μ.apply_symm_apply _
  have hjm : j ≠ m := fun h ↦ hm ((congrArg μ h).symm.trans hjμ)
  have hjν : ν j ≠ ν m := ν.injective.ne hjm
  have hjmove : μ j ≠ ν j := fun h ↦ hjν (h.symm.trans hjμ)
  have hjrank : p.manRank j (μ j) < p.manRank j (ν j) :=
    lt_of_le_of_ne (hle j) ((p.manRank j).injective.ne hjmove)
  have hw : ¬ p.womanRank (ν m) j < p.womanRank (ν m) m := fun h ↦
    hν j (ν m) ⟨hjν, by simpa only [hjμ] using hjrank,
      by simpa only [Equiv.symm_apply_apply] using h⟩
  ⟨lt_of_le_of_ne (hle m) ((p.manRank m).injective.ne hm),
    lt_of_le_of_ne (le_of_not_gt hw) ((p.womanRank (ν m)).injective.ne hjm.symm)⟩
private theorem successor_husband_moves (hν : IsStable p ν) {m w : Fin n}
    (hw : IsEligibleSuccessor p μ m w) (hbound : p.manRank m w ≤ p.manRank m (ν m)) :
    μ (μ.symm w) ≠ ν (μ.symm w) :=
  let j := μ.symm w
  have hjμ : μ j = w := μ.apply_symm_apply w
  have hjm : j ≠ m := fun h ↦
    (ne_of_lt hw.1) (congrArg (p.manRank m) ((congrArg μ h).symm.trans hjμ))
  fun heq ↦
    have hjν : ν j = w := heq.symm.trans hjμ
    have hwm : w ≠ ν m := fun h ↦ hjm (ν.injective (hjν.trans h))
    have hlt : p.manRank m w < p.manRank m (ν m) :=
      lt_of_le_of_ne hbound ((p.manRank m).injective.ne hwm)
    have hjνsymm : ν.symm w = j := by
      simpa only [Equiv.symm_apply_apply] using (congrArg ν.symm hjν).symm
    hν m w ⟨hwm.symm, hlt, by simpa only [hjνsymm] using hw.2⟩
theorem exists_successor_towards_target (_hμ : IsStable p μ) (hν : IsStable p ν)
    (hle : ∀ i, p.manRank i (μ i) ≤ p.manRank i (ν i)) {m : Fin n} (hm : μ m ≠ ν m) :
    ∃ j : Fin n, IsSuccessor p μ m (μ j) ∧ μ j ≠ ν j ∧
      p.manRank m (μ j) ≤ p.manRank m (ν m) := by
  classical
  let candidates := Finset.univ.filter (IsEligibleSuccessor p μ m)
  have htarget : ν m ∈ candidates :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, target_partner_eligible hν hle hm⟩
  obtain ⟨w, hw, hmin⟩ := candidates.exists_min_image (p.manRank m) ⟨ν m, htarget⟩
  have heligible : IsEligibleSuccessor p μ m w := (Finset.mem_filter.mp hw).2
  have hsuccessor : IsSuccessor p μ m w :=
    (IsSuccessor.mk (heligible) (fun v hv ↦ hmin v (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩)))
  have hbound : p.manRank m w ≤ p.manRank m (ν m) := hmin (ν m) htarget
  have hj : μ (μ.symm w) = w := μ.apply_symm_apply w
  exact ⟨μ.symm w, by simpa only [hj] using hsuccessor,
    successor_husband_moves hν heligible hbound,
    by simpa only [hj] using hbound⟩
end CompLP
end

-- RotationReachability
section
open scoped BigOperators
open StableMarriage
namespace CompLP
variable {n : ℕ} {p : Profile n}
private inductive RotationSequence (p : Profile n) :
    Matching n → List (Equiv.Perm (Fin n)) → Matching n → Prop where
  | nil {μ : Matching n} (hμ : IsStable p μ) : RotationSequence p μ [] μ
  | cons {μ ν : Matching n} {ρ : Equiv.Perm (Fin n)} {rs : List (Equiv.Perm (Fin n))}
      (hμ : IsStable p μ) (hρ : IsExposedRotation p μ ρ)
      (rest : RotationSequence p (eliminateRotation μ ρ) rs ν) :
      RotationSequence p μ (ρ :: rs) ν
private def totalManRank (p : Profile n) (μ : Matching n) : ℕ :=
  ∑ m : Fin n, (p.manRank m (μ m) : ℕ)
private theorem totalManRank_le {μ ν : Matching n}
    (hle : ∀ m, p.manRank m (μ m) ≤ p.manRank m (ν m)) :
    totalManRank p μ ≤ totalManRank p ν :=
  Finset.sum_le_sum fun m _ ↦ hle m
private theorem totalManRank_lt_eliminate {μ : Matching n} {ρ : Equiv.Perm (Fin n)}
    (hρ : IsExposedRotation p μ ρ) :
    totalManRank p μ < totalManRank p (eliminateRotation μ ρ) :=
  have hle (m : Fin n) : p.manRank m (μ m) ≤ p.manRank m (eliminateRotation μ ρ m) :=
    if hm : ρ m = m then
      le_of_eq (by simp only [eliminateRotation_apply, hm])
    else (hρ.manRank_lt_eliminate_of_moved hm).le
  let ⟨m, hm, _⟩ := (IsExposedRotation.isCycle hρ)
  Finset.sum_lt_sum (fun i _ ↦ hle i)
    ⟨m, Finset.mem_univ m, hρ.manRank_lt_eliminate_of_moved hm⟩
theorem exists_exposedRotation_towards_target {μ ν : Matching n}
    (hμ : IsStable p μ) (hν : IsStable p ν) (hle : MenWeaklyPrefer p μ ν) (hne : μ ≠ ν) :
    ∃ ρ, IsExposedRotation p μ ρ ∧ MenWeaklyPrefer p (eliminateRotation μ ρ) ν := by
  classical
  obtain ⟨m, hm⟩ : ∃ m, μ m ≠ ν m := by
    simpa only [not_forall] using mt (fun h : ∀ i, μ i = ν i ↦ Equiv.ext h) hne
  let changed : Set (Fin n) := {i | μ i ≠ ν i}
  let : Nonempty changed := ⟨⟨m, hm⟩⟩
  
  choose next hsucc hchanged hbound using fun i : changed ↦
    exists_successor_towards_target hμ hν hle i.property
  let f : changed → changed := fun i ↦ ⟨next i, hchanged i⟩
  have hnf (i : changed) : f i ≠ i := fun h ↦
    have he : next i = i.val := congrArg Subtype.val h
    (lt_irrefl _) (by simpa only [he] using (IsSuccessor.eligible (hsucc i)).1)
  obtain ⟨ρ, hcycle, hedge⟩ := exists_cycle_permutation f hnf
  refine ⟨ρ, (IsExposedRotation.mk (hcycle) (?_)), ?_⟩
  · intro i hi
    obtain ⟨ha, hρ⟩ := hedge i hi
    simpa only [hρ] using hsucc ⟨i, ha⟩
  · intro i
    by_cases hi : ρ i = i
    · simpa only [eliminateRotation_apply, hi] using hle i
    · obtain ⟨ha, hρ⟩ := hedge i hi
      simpa only [eliminateRotation_apply, hρ] using hbound ⟨i, ha⟩
theorem exists_rotationSequence_of_menWeaklyPrefer {μ ν : Matching n}
    (hμ : IsStable p μ) (hν : IsStable p ν) (hle : MenWeaklyPrefer p μ ν) :
    ∃ rs, RotationSequence p μ rs ν := by
  classical
  let gap := fun σ : Matching n ↦ totalManRank p ν - totalManRank p σ
  refine (measure gap).wf.induction
    (C := fun σ ↦ IsStable p σ →
      MenWeaklyPrefer p σ ν →
      ∃ rs, RotationSequence p σ rs ν) μ ?_ hμ hle
  intro σ ih hσ hσν
  by_cases h : σ = ν
  · exact ⟨[], h ▸ RotationSequence.nil hσ⟩
  · obtain ⟨ρ, hρ, hnext⟩ := exists_exposedRotation_towards_target hσ hν hσν h
    have hinc := totalManRank_lt_eliminate hρ
    have hbound := totalManRank_le hnext
    have hdrop : gap (eliminateRotation σ ρ) < gap σ := by
      dsimp only [gap]
      omega
    obtain ⟨rs, hrs⟩ := ih _ hdrop (hρ.isStable_eliminate hσ) hnext
    exact ⟨ρ :: rs, .cons hσ hρ hrs⟩
theorem exists_rotationSequence_of_manOptimal {μ ν : Matching n}
    (hopt : IsManOptimal p μ) (hν : IsStable p ν) :
    ∃ rs, RotationSequence p μ rs ν :=
  exists_rotationSequence_of_menWeaklyPrefer hopt.1 hν (hopt.2 ν hν)
end CompLP
end

-- RotationLabels
section
open StableMarriage
namespace CompLP
variable {n : ℕ} {p : Profile n}
private structure RotationLabel (n : ℕ) where
  cycle : Equiv.Perm (Fin n)
  oldPartner : Fin n → Option (Fin n)
private def rotationLabel (μ : Matching n) (ρ : Equiv.Perm (Fin n)) : RotationLabel n :=
  ⟨ρ, fun m ↦ if ρ m = m then none else some (μ m)⟩
private def rotationLabels : Matching n → List (Equiv.Perm (Fin n)) → List (RotationLabel n)
  | _, [] => []
  | μ, ρ :: rs => rotationLabel μ ρ :: rotationLabels (eliminateRotation μ ρ) rs
theorem rotationLabel_eliminate_of_fixes {μ : Matching n} {ρ σ : Equiv.Perm (Fin n)}
    (hfix : ∀ m, ρ m ≠ m → σ m = m) :
    rotationLabel (eliminateRotation μ σ) ρ = rotationLabel μ ρ := by
  unfold rotationLabel
  congr 1
  funext m
  by_cases hm : ρ m = m
  · simp [hm]
  · simp [hm, hfix m hm]
theorem RotationSequence.menWeaklyPrefer {μ ν : Matching n} {rs : List (Equiv.Perm (Fin n))}
    (h : RotationSequence p μ rs ν) : MenWeaklyPrefer p μ ν := by
  induction h with
  | nil => exact fun _ ↦ le_rfl
  | @cons μ ν ρ rs hμ hρ rest ih =>
    intro m
    by_cases hm : ρ m = m
    · simpa only [eliminateRotation_apply, hm] using ih m
    · exact (hρ.manRank_lt_eliminate_of_moved hm).le.trans (ih m)
theorem IsExposedRotation.partner_ne_of_moved_of_rotationSequence {μ ν : Matching n}
    {ρ : Equiv.Perm (Fin n)} {rs : List (Equiv.Perm (Fin n))}
    (hρ : IsExposedRotation p μ ρ) (hpath : RotationSequence p (eliminateRotation μ ρ) rs ν)
    {m : Fin n} (hm : ρ m ≠ m) : μ m ≠ ν m :=
  fun he ↦ ((hρ.manRank_lt_eliminate_of_moved hm).trans_le
    (hpath.menWeaklyPrefer m)).ne (congrArg (p.manRank m) he)
end CompLP
end

-- RotationPathIndependence
section
open StableMarriage
namespace CompLP
variable {n : ℕ} {p : Profile n}
theorem RotationSequence.pull_rotation_to_front {μ ν : Matching n}
    {rs : List (Equiv.Perm (Fin n))} (hpath : RotationSequence p μ rs ν)
    {ρ : Equiv.Perm (Fin n)} (hρ : IsExposedRotation p μ ρ)
    {m : Fin n} (hm : ρ m ≠ m) (hend : μ m ≠ ν m) :
    ∃ ts, RotationSequence p (eliminateRotation μ ρ) ts ν ∧
      (rotationLabels μ rs).Perm
        (rotationLabel μ ρ :: rotationLabels (eliminateRotation μ ρ) ts) := by
  classical
  induction hpath generalizing ρ with
  | nil _ => exact (hend rfl).elim
  | @cons μ ν σ rs hμ hσ htail ih =>
    by_cases h : ρ = σ
    · subst σ
      exact ⟨rs, htail, List.Perm.refl _⟩
    · have hend' : eliminateRotation μ σ m ≠ ν m := by
        simpa only [eliminateRotation_apply, hρ.disjoint_moved hσ h m hm] using hend
      obtain ⟨ts, hts, hp⟩ := ih (hρ.persist_eliminate hσ h) hm hend'
      have hc := hρ.eliminate_comm hσ h
      have hts' : RotationSequence p (eliminateRotation (eliminateRotation μ ρ) σ) ts ν :=
        hc.symm ▸ hts
      have hlρ := rotationLabel_eliminate_of_fixes (μ := μ) (hρ.disjoint_moved hσ h)
      have hrev : σ ≠ ρ := Ne.symm h
      have hlσ := rotationLabel_eliminate_of_fixes (μ := μ) (hσ.disjoint_moved hρ hrev)
      refine ⟨σ :: ts, .cons (hρ.isStable_eliminate hμ) (hσ.persist_eliminate hρ hrev) hts', ?_⟩
      simp only [rotationLabels, hlσ, hc]
      rw [hlρ] at hp
      exact (List.Perm.cons _ hp).trans (List.Perm.swap _ _ _)
theorem RotationSequence.rotationLabels_perm {μ ν : Matching n}
    {rs ss : List (Equiv.Perm (Fin n))}
    (h : RotationSequence p μ rs ν) (h' : RotationSequence p μ ss ν) :
    (rotationLabels μ rs).Perm (rotationLabels μ ss) := by
  induction h generalizing ss with
  | nil _ =>
    cases h' with
    | nil _ => exact List.Perm.refl _
    | cons _ hσ htail =>
      obtain ⟨m, hm, _⟩ := (IsExposedRotation.isCycle hσ)
      exact ((hσ.partner_ne_of_moved_of_rotationSequence htail hm) rfl).elim
  | cons _ hρ htail ih =>
    obtain ⟨m, hm, _⟩ := (IsExposedRotation.isCycle hρ)
    have hend := hρ.partner_ne_of_moved_of_rotationSequence htail hm
    obtain ⟨ts, hts, hp⟩ := h'.pull_rotation_to_front hρ hm hend
    exact (List.Perm.cons _ (ih hts)).trans hp.symm
end CompLP
end

-- RotationTrace
section
open StableMarriage
namespace CompLP
variable {n : ℕ} {p : Profile n}
private def rotationLabelNewPartner (r : RotationLabel n) (m : Fin n) : Option (Fin n) :=
  r.oldPartner (r.cycle m)
theorem rotationLabelNewPartner_eq {μ : Matching n} {ρ : Equiv.Perm (Fin n)}
    {m : Fin n} (hm : ρ m ≠ m) :
    rotationLabelNewPartner (rotationLabel μ ρ) m = some (eliminateRotation μ ρ m) := by
  have hnext : ρ (ρ m) ≠ ρ m := fun h ↦ hm (ρ.injective h)
  simp [rotationLabelNewPartner, rotationLabel, eliminateRotation_apply, hnext]
namespace RotationSequence
variable {μ ν τ : Matching n} {rs ss : List (Equiv.Perm (Fin n))}
theorem isStable_end (h : RotationSequence p μ rs ν) : IsStable p ν := by
  induction h with
  | nil hμ => exact hμ
  | cons _ _ _ ih => exact ih
theorem append (h : RotationSequence p μ rs ν) (k : RotationSequence p ν ss τ) :
    RotationSequence p μ (rs ++ ss) τ := by
  induction h with
  | nil _ => exact k
  | cons hμ hρ _ ih => exact .cons hμ hρ (ih k)
theorem rotationLabels_append (h : RotationSequence p μ rs ν) :
    rotationLabels μ (rs ++ ss) = rotationLabels μ rs ++ rotationLabels ν ss := by
  induction h with
  | nil _ => rfl
  | cons _ _ _ ih => simp only [List.cons_append, rotationLabels, ih]
theorem label_moves_someone (h : RotationSequence p μ rs ν)
    {r : RotationLabel n} (hr : r ∈ rotationLabels μ rs) : ∃ m, r.cycle m ≠ m := by
  induction h with
  | nil _ => exact (List.not_mem_nil hr).elim
  | cons _ hρ _ ih =>
    rcases List.mem_cons.mp hr with rfl | hr
    · obtain ⟨m, hm, _⟩ := (IsExposedRotation.isCycle hρ)
      exact ⟨m, hm⟩
    · exact ih hr
theorem label_rank_bounds (h : RotationSequence p μ rs ν)
    {r : RotationLabel n} (hr : r ∈ rotationLabels μ rs)
    {m : Fin n} (hm : r.cycle m ≠ m) :
    ∃ old new, r.oldPartner m = some old ∧ rotationLabelNewPartner r m = some new ∧
      p.manRank m (μ m) ≤ p.manRank m old ∧ p.manRank m old < p.manRank m new ∧
      p.manRank m new ≤ p.manRank m (ν m) := by
  induction h with
  | nil _ => exact (List.not_mem_nil hr).elim
  | @cons μ ν ρ rs hμ hρ rest ih =>
    rcases List.mem_cons.mp hr with rfl | hr
    · refine ⟨μ m, eliminateRotation μ ρ m, ?_, rotationLabelNewPartner_eq hm,
        le_rfl, hρ.manRank_lt_eliminate_of_moved hm, rest.menWeaklyPrefer m⟩
      simp [rotationLabel, show ρ m ≠ m from hm]
    · obtain ⟨old, new, hold, hnew, hle, hlt, hend⟩ := ih hr
      have hstep : RotationSequence p μ [ρ] (eliminateRotation μ ρ) :=
        .cons hμ hρ (.nil (hρ.isStable_eliminate hμ))
      exact ⟨old, new, hold, hnew, (hstep.menWeaklyPrefer m).trans hle, hlt, hend⟩
theorem partner_eq_or_label_newPartner (h : RotationSequence p μ rs ν) (m : Fin n) :
    μ m = ν m ∨ ∃ r, r ∈ rotationLabels μ rs ∧ r.cycle m ≠ m ∧
      rotationLabelNewPartner r m = some (ν m) := by
  induction h with
  | nil _ => exact Or.inl rfl
  | @cons μ ν ρ rs _ _ _ ih =>
    rcases ih with he | ⟨r, hr, hm, hnew⟩
    · by_cases hm : ρ m = m
      · exact Or.inl (by simpa only [eliminateRotation_apply, hm] using he)
      · exact Or.inr ⟨rotationLabel μ ρ, List.mem_cons_self, hm,
          (rotationLabelNewPartner_eq hm).trans (congrArg some he)⟩
    · exact Or.inr ⟨r, List.mem_cons_of_mem _ hr, hm, hnew⟩
theorem separating_prefix (h : RotationSequence p μ rs ν) {a b : RotationLabel n}
    (hne : a ≠ b) (hmem : a ∈ rotationLabels μ rs ∨ b ∈ rotationLabels μ rs) :
    ∃ τ ts, RotationSequence p μ ts τ ∧
      ((a ∈ rotationLabels μ ts ∧ b ∉ rotationLabels μ ts) ∨
        (b ∈ rotationLabels μ ts ∧ a ∉ rotationLabels μ ts)) := by
  classical
  induction h with
  | nil _ => exact (hmem.elim (List.not_mem_nil ·) (List.not_mem_nil ·)).elim
  | @cons μ _ ρ _ hμ hρ _ ih =>
    have hstep : RotationSequence p μ [ρ] (eliminateRotation μ ρ) :=
      .cons hμ hρ (.nil (hρ.isStable_eliminate hμ))
    by_cases ha : rotationLabel μ ρ = a
    · exact ⟨_, _, hstep, Or.inl (by simp [rotationLabels, ha, Ne.symm hne])⟩
    · by_cases hb : rotationLabel μ ρ = b
      · exact ⟨_, _, hstep, Or.inr (by simp [rotationLabels, hb, hne])⟩
      · simp only [rotationLabels, List.mem_cons, Ne.symm ha, Ne.symm hb, false_or] at hmem
        obtain ⟨τ, ts, hts, hsep⟩ := ih hmem
        exact ⟨τ, ρ :: ts, .cons hμ hρ hts, by
          simpa only [rotationLabels, List.mem_cons, Ne.symm ha, Ne.symm hb, false_or]⟩
end RotationSequence
end CompLP
end

-- RotationIdeals
section
open StableMarriage
namespace CompLP
variable {n : ℕ} {p : Profile n} {μ₀ : Matching n}
private def Rotation (p : Profile n) (μ₀ : Matching n) :=
  {r : RotationLabel n // ∃ ν rs, RotationSequence p μ₀ rs ν ∧ r ∈ rotationLabels μ₀ rs}
private instance : Finite (RotationLabel n) :=
  Finite.of_injective (fun r : RotationLabel n ↦ (r.cycle, r.oldPartner)) (by
    intro a b h
    cases a
    cases b
    cases h
    rfl)
private instance : Finite (Rotation p μ₀) :=
  Finite.of_injective Subtype.val Subtype.val_injective
private def eliminatedRotations (p : Profile n) (μ₀ ν : Matching n) : Set (Rotation p μ₀) :=
  {r | ∃ rs, RotationSequence p μ₀ rs ν ∧ r.val ∈ rotationLabels μ₀ rs}
theorem RotationSequence.mem_eliminatedRotations_iff {ν : Matching n}
    {rs : List (Equiv.Perm (Fin n))} (h : RotationSequence p μ₀ rs ν)
    {r : Rotation p μ₀} :
    r ∈ eliminatedRotations p μ₀ ν ↔ r.val ∈ rotationLabels μ₀ rs :=
  ⟨fun ⟨_, hs, hr⟩ ↦ (hs.rotationLabels_perm h).mem_iff.mp hr, fun hr ↦ ⟨rs, h, hr⟩⟩
theorem eliminatedRotations_start (h : IsStable p μ₀) :
    eliminatedRotations p μ₀ μ₀ = ∅ := by
  ext r
  simp only [(RotationSequence.nil h).mem_eliminatedRotations_iff, rotationLabels,
    List.not_mem_nil, Set.notMem_empty]
private def Rotation.IsPrerequisite (r s : Rotation p μ₀) : Prop :=
  ∀ ν, s ∈ eliminatedRotations p μ₀ ν → r ∈ eliminatedRotations p μ₀ ν
private instance : PartialOrder (Rotation p μ₀) where
  le := Rotation.IsPrerequisite
  le_refl _ _ hr := hr
  le_trans _ _ _ hrs hst ν ht := hrs ν (hst ν ht)
  le_antisymm r s hrs hsr := by
    classical
    apply Subtype.ext
    by_contra hne
    obtain ⟨ν, rs, h, hr⟩ := r.property
    obtain ⟨τ, ts, ht, hsep⟩ := h.separating_prefix hne (Or.inl hr)
    rcases hsep with ⟨hr', hs'⟩ | ⟨hs', hr'⟩
    · exact hs' (ht.mem_eliminatedRotations_iff.mp
        (hsr τ (ht.mem_eliminatedRotations_iff.mpr hr')))
    · exact hr' (ht.mem_eliminatedRotations_iff.mp
        (hrs τ (ht.mem_eliminatedRotations_iff.mpr hs')))
private theorem RotationSequence.exists_exposed_prefix_of_mem {μ ν : Matching n}
    {rs : List (Equiv.Perm (Fin n))} (h : RotationSequence p μ rs ν)
    {r : RotationLabel n} (hr : r ∈ rotationLabels μ rs) :
    ∃ τ ts us, RotationSequence p μ ts τ ∧ IsExposedRotation p τ r.cycle ∧
      rotationLabel τ r.cycle = r ∧ rs = ts ++ r.cycle :: us := by
  induction h with
  | nil => exact (List.not_mem_nil hr).elim
  | @cons μ ν ρ rs hμ hρ htail ih =>
    rw [rotationLabels, List.mem_cons] at hr
    rcases hr with he | hr
    · subst r
      exact ⟨μ, [], rs, .nil hμ, hρ, rfl, rfl⟩
    · obtain ⟨τ, ts, us, ht, he, hl, hs⟩ := ih hr
      exact ⟨τ, ρ :: ts, us, .cons hμ hρ ht, he, hl, congrArg (ρ :: ·) hs⟩
theorem Rotation.lt_iff_before_exposure (hopt : IsManOptimal p μ₀)
    {r s : Rotation p μ₀} (hne : r ≠ s) :
    r < s ↔ ∀ ν, IsStable p ν → IsExposedRotation p ν s.val.cycle →
      rotationLabel ν s.val.cycle = s.val → r ∈ eliminatedRotations p μ₀ ν := by
  rw [lt_iff_le_and_ne]
  constructor
  · rintro ⟨hrs, _⟩ ν hν he hl
    obtain ⟨ts, ht⟩ := exists_rotationSequence_of_manOptimal hopt hν
    have hstep : RotationSequence p ν [s.val.cycle] (eliminateRotation ν s.val.cycle) :=
      .cons hν he (.nil (he.isStable_eliminate hν))
    have hnext := ht.append hstep
    have hs : s ∈ eliminatedRotations p μ₀ (eliminateRotation ν s.val.cycle) := by
      apply hnext.mem_eliminatedRotations_iff.mpr
      simp [ht.rotationLabels_append, rotationLabels, hl]
    have hr := hnext.mem_eliminatedRotations_iff.mp (hrs _ hs)
    rw [ht.rotationLabels_append, List.mem_append, rotationLabels, rotationLabels, hl,
      List.mem_singleton] at hr
    exact ht.mem_eliminatedRotations_iff.mpr (hr.resolve_right (fun h ↦ hne (Subtype.ext h)))
  · intro hbefore
    refine ⟨fun ν hν ↦ ?_, hne⟩
    obtain ⟨rs, h, hs⟩ := hν
    obtain ⟨τ, ts, us, ht, he, hl, hsplit⟩ := h.exists_exposed_prefix_of_mem hs
    have hr := ht.mem_eliminatedRotations_iff.mp (hbefore τ ht.isStable_end he hl)
    refine h.mem_eliminatedRotations_iff.mpr ?_
    rw [hsplit, ht.rotationLabels_append]
    exact List.mem_append_left _ hr
theorem mem_eliminatedRotations_iff_newRank_le {ν : Matching n} (hopt : IsManOptimal p μ₀)
    (hν : IsStable p ν) {r : Rotation p μ₀} {m w : Fin n} (hm : r.val.cycle m ≠ m)
    (hw : rotationLabelNewPartner r.val m = some w) :
    r ∈ eliminatedRotations p μ₀ ν ↔ p.manRank m w ≤ p.manRank m (ν m) := by
  constructor
  · rintro ⟨rs, h, hr⟩
    obtain ⟨_, w', _, hw', _, _, hle⟩ := h.label_rank_bounds hr hm
    exact (Option.some.inj (hw'.symm.trans hw)) ▸ hle
  · intro hle
    obtain ⟨σ, rs, hσ, hr⟩ := r.property
    
    obtain ⟨τ, hτ, hmax⟩ := exists_stable_manRank_max hν hσ.isStable_end
    obtain ⟨as, ha⟩ := exists_rotationSequence_of_manOptimal hopt hν
    obtain ⟨bs, hb⟩ := exists_rotationSequence_of_menWeaklyPrefer hν hτ (fun i ↦ by
      rw [hmax i]
      exact le_max_left _ _)
    obtain ⟨cs, hc⟩ := exists_rotationSequence_of_menWeaklyPrefer hσ.isStable_end hτ (fun i ↦ by
      rw [hmax i]
      exact le_max_right _ _)
    have hrc : r.val ∈ rotationLabels μ₀ (rs ++ cs) := by
      rw [hσ.rotationLabels_append]
      exact List.mem_append_left _ hr
    have hra := ((hσ.append hc).rotationLabels_perm (ha.append hb)).mem_iff.mp hrc
    rw [ha.rotationLabels_append, List.mem_append] at hra
    rcases hra with hr' | hr'
    · exact ⟨as, ha, hr'⟩
    · 
      obtain ⟨_, w', _, hw', hstart, hstep, _⟩ := hb.label_rank_bounds hr' hm
      have heq := Option.some.inj (hw'.symm.trans hw)
      subst w'
      exact ((hstep.trans_le (hle.trans hstart)).false).elim
private theorem Rotation.exists_newPartner (r : Rotation p μ₀) :
    ∃ m w, r.val.cycle m ≠ m ∧ rotationLabelNewPartner r.val m = some w := by
  obtain ⟨ν, rs, h, hr⟩ := r.property
  obtain ⟨m, hm⟩ := h.label_moves_someone hr
  obtain ⟨_, w, _, hw, _, _, _⟩ := h.label_rank_bounds hr hm
  exact ⟨m, w, hm, hw⟩
theorem exists_eliminatedRotations_inter {μ ν : Matching n} (hopt : IsManOptimal p μ₀)
    (hμ : IsStable p μ) (hν : IsStable p ν) :
    ∃ τ, IsStable p τ ∧
      eliminatedRotations p μ₀ τ = eliminatedRotations p μ₀ μ ∩ eliminatedRotations p μ₀ ν := by
  obtain ⟨τ, hτ, hmin⟩ := exists_stable_manRank_min hμ hν
  refine ⟨τ, hτ, Set.ext fun r ↦ ?_⟩
  obtain ⟨m, w, hm, hw⟩ := r.exists_newPartner
  rw [Set.mem_inter_iff, mem_eliminatedRotations_iff_newRank_le hopt hτ hm hw,
    mem_eliminatedRotations_iff_newRank_le hopt hμ hm hw,
    mem_eliminatedRotations_iff_newRank_le hopt hν hm hw, hmin m, le_min_iff]
theorem exists_eliminatedRotations_union {μ ν : Matching n} (hopt : IsManOptimal p μ₀)
    (hμ : IsStable p μ) (hν : IsStable p ν) :
    ∃ τ, IsStable p τ ∧
      eliminatedRotations p μ₀ τ = eliminatedRotations p μ₀ μ ∪ eliminatedRotations p μ₀ ν := by
  obtain ⟨τ, hτ, hmax⟩ := exists_stable_manRank_max hμ hν
  refine ⟨τ, hτ, Set.ext fun r ↦ ?_⟩
  obtain ⟨m, w, hm, hw⟩ := r.exists_newPartner
  rw [Set.mem_union, mem_eliminatedRotations_iff_newRank_le hopt hτ hm hw,
    mem_eliminatedRotations_iff_newRank_le hopt hμ hm hw,
    mem_eliminatedRotations_iff_newRank_le hopt hν hm hw, hmax m, le_max_iff]
theorem eliminatedRotations_subset_iff {μ ν : Matching n} (hopt : IsManOptimal p μ₀)
    (hμ : IsStable p μ) (hν : IsStable p ν) :
    eliminatedRotations p μ₀ μ ⊆ eliminatedRotations p μ₀ ν ↔ MenWeaklyPrefer p μ ν := by
  constructor
  · intro hsub m
    obtain ⟨rs, h⟩ := exists_rotationSequence_of_manOptimal hopt hμ
    rcases h.partner_eq_or_label_newPartner m with he | ⟨r, hr, hm, hw⟩
    · rw [← he]
      exact hopt.2 ν hν m
    · let r' : Rotation p μ₀ := ⟨r, μ, rs, h, hr⟩
      have hmem : r' ∈ eliminatedRotations p μ₀ μ := ⟨rs, h, hr⟩
      exact (mem_eliminatedRotations_iff_newRank_le hopt hν hm hw).mp (hsub hmem)
  · intro hle r hr
    obtain ⟨m, w, hm, hw⟩ := r.exists_newPartner
    exact (mem_eliminatedRotations_iff_newRank_le hopt hν hm hw).mpr
      (((mem_eliminatedRotations_iff_newRank_le hopt hμ hm hw).mp hr).trans (hle m))
private def stableMatchingToRotationIdeal (ν : {ν : Matching n // IsStable p ν}) :
    LowerSet (Rotation p μ₀) :=
  ⟨eliminatedRotations p μ₀ ν.val, fun _ _ hrs hs ↦ hrs ν.val hs⟩
theorem stableMatchingToRotationIdeal_bijective (hopt : IsManOptimal p μ₀) :
    Function.Bijective (stableMatchingToRotationIdeal (p := p) (μ₀ := μ₀)) := by
  constructor
  · intro μ ν h
    have he : eliminatedRotations p μ₀ μ.val = eliminatedRotations p μ₀ ν.val :=
      congrArg (fun I : LowerSet (Rotation p μ₀) ↦ I.carrier) h
    have hμν := (eliminatedRotations_subset_iff hopt μ.property ν.property).mp he.le
    have hνμ := (eliminatedRotations_subset_iff hopt ν.property μ.property).mp he.ge
    exact Subtype.ext (Equiv.ext fun m ↦ (p.manRank m).injective ((hμν m).antisymm (hνμ m)))
  · intro I
    let F := Set.range fun ν : {ν : Matching n // IsStable p ν} ↦
      eliminatedRotations p μ₀ ν.val
    have hempty : ∅ ∈ F := ⟨⟨μ₀, hopt.1⟩, eliminatedRotations_start hopt.1⟩
    have hinter : ∀ ⦃A B⦄, A ∈ F → B ∈ F → A ∩ B ∈ F := by
      rintro _ _ ⟨μ, rfl⟩ ⟨ν, rfl⟩
      obtain ⟨τ, hτ, he⟩ := exists_eliminatedRotations_inter hopt μ.property ν.property
      exact ⟨⟨τ, hτ⟩, he⟩
    have hunion : ∀ ⦃A B⦄, A ∈ F → B ∈ F → A ∪ B ∈ F := by
      rintro _ _ ⟨μ, rfl⟩ ⟨ν, rfl⟩
      obtain ⟨τ, hτ, he⟩ := exists_eliminatedRotations_union hopt μ.property ν.property
      exact ⟨⟨τ, hτ⟩, he⟩
    have hcover (r : Rotation p μ₀) : ∃ A ∈ F, r ∈ A := by
      obtain ⟨ν, rs, h, hr⟩ := r.property
      exact ⟨_, ⟨⟨ν, h.isStable_end⟩, rfl⟩, ⟨rs, h, hr⟩⟩
    have hdown : ∀ ⦃r s : Rotation p μ₀⦄, (∀ A ∈ F, s ∈ A → r ∈ A) → s ∈ I → r ∈ I := by
      intro r s hrs hs
      refine I.lower (show r ≤ s from fun ν hν ↦ ?_) hs
      obtain ⟨rs, h, hmem⟩ := hν
      exact hrs _ ⟨⟨ν, h.isStable_end⟩, rfl⟩ ⟨rs, h, hmem⟩
    have hI : (I : Set (Rotation p μ₀)) ∈ F :=
      mem_family_of_downward_closed hempty hinter hunion hcover hdown
    obtain ⟨ν, hν⟩ := hI
    exact ⟨ν, LowerSet.ext hν⟩
private noncomputable def stableMatchingEquivRotationIdeals (hopt : IsManOptimal p μ₀) :
    {ν : Matching n // IsStable p ν} ≃ LowerSet (Rotation p μ₀) :=
  Equiv.ofBijective stableMatchingToRotationIdeal (stableMatchingToRotationIdeal_bijective hopt)
end CompLP
end

-- CoexposedRotations
section
open StableMarriage
namespace CompLP
variable {n : ℕ} {p : Profile n} {μ₀ μ : Matching n}
private def rotationOfExposed (hopt : IsManOptimal p μ₀) (hμ : IsStable p μ)
    {ρ : Equiv.Perm (Fin n)} (hρ : IsExposedRotation p μ ρ) : Rotation p μ₀ :=
  ⟨rotationLabel μ ρ, by
    obtain ⟨rs, hrs⟩ := exists_rotationSequence_of_manOptimal hopt hμ
    have hstep : RotationSequence p μ [ρ] (eliminateRotation μ ρ) :=
      .cons hμ hρ (.nil (hρ.isStable_eliminate hμ))
    refine ⟨_, rs ++ [ρ], hrs.append hstep, ?_⟩
    simp [hrs.rotationLabels_append, rotationLabels]⟩
theorem rotationOfExposed_not_mem_eliminatedRotations (hopt : IsManOptimal p μ₀)
    (hμ : IsStable p μ) {ρ : Equiv.Perm (Fin n)} (hρ : IsExposedRotation p μ ρ) :
    rotationOfExposed hopt hμ hρ ∉ eliminatedRotations p μ₀ μ := by
  obtain ⟨m, hm, _⟩ := (IsExposedRotation.isCycle hρ)
  exact fun hr ↦ (not_le_of_gt (hρ.manRank_lt_eliminate_of_moved hm))
    ((mem_eliminatedRotations_iff_newRank_le hopt hμ (m := m) hm
      (rotationLabelNewPartner_eq hm)).mp hr)
end CompLP
end

-- CoexposureCycleMoment
section
open StableMarriage MeasureTheory
open scoped BigOperators ENNReal
namespace CompLP
private def RealizesSuccessorPermutation {n : ℕ} (p : Profile n) (M σ : Matching n) : Prop :=
  ∀ i ∈ σ.support, IsSuccessor p M i (M (σ i))
theorem realizesSuccessorPermutation_iff_factors {n : ℕ}
    {p : Profile n} {M σ : Matching n} :
    RealizesSuccessorPermutation p M σ ↔
      ∀ ρ ∈ σ.cycleFactorsFinset, IsExposedRotation p M ρ := by
  constructor
  · intro h ρ hρ
    obtain ⟨hc, heq⟩ := Equiv.Perm.mem_cycleFactorsFinset_iff.mp hρ
    refine (IsExposedRotation.mk (hc) (fun i hi ↦ ?_))
    have hmem := Equiv.Perm.mem_support.mpr hi
    rw [heq i hmem]
    exact h i (Equiv.Perm.mem_cycleFactorsFinset_support_le hρ hmem)
  · intro h i hi
    obtain ⟨ρ, hρ, hmem⟩ :=
      Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset.mp hi
    rw [← (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hρ).2 i hmem]
    exact (IsExposedRotation.successor (h ρ hρ)) i (Equiv.Perm.mem_support.mp hmem)
theorem card_support_eq_sum_cycleFactors_support {n : ℕ} (σ : Matching n) :
    σ.support.card = ∑ ρ ∈ σ.cycleFactorsFinset, ρ.support.card := by
  have hs : σ.cycleFactorsFinset.biUnion (fun ρ ↦ ρ.support) = σ.support := by
    ext i
    rw [Finset.mem_biUnion]
    exact Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset.symm
  refine (congrArg Finset.card hs.symm).trans (Finset.card_biUnion ?_)
  intro ρ hρ τ hτ hne
  exact Equiv.Perm.disjoint_iff_disjoint_support.mp
    (σ.cycleFactorsFinset_pairwise_disjoint hρ hτ hne)
end CompLP
end

-- RowCompetition
section
open Set
open scoped BigOperators
namespace CompLP
variable {ι : Type*} {J : Finset ι} {a : ι → ℝ} {A b : ℝ}
end CompLP
end

-- ReverseIIDLabelGood
section
open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal
namespace CompLP
section Measures
variable {ι α : Type*} [Fintype ι] [MeasurableSpace α]
variable [Fintype α] [DiscreteMeasurableSpace α]
end Measures
end CompLP
end

-- PivotReverseMaskLowerMoment
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace CompLP
open scoped Classical in
private noncomputable def goodReverseSupportPermutations {n : ℕ} (k : ℕ)
    (A : Finset (Fin n)) (F : Fin n → Finset (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter fun σ ↦ σ.support.card = k ∧
    ∀ i ∈ σ.support, i ∉ A ∧ σ i ∉ F i
theorem mem_goodReverseSupportPermutations {n k : ℕ} {A : Finset (Fin n)}
    {F : Fin n → Finset (Fin n)} {σ : Matching n} :
    σ ∈ goodReverseSupportPermutations k A F ↔ σ.support.card = k ∧
      ∀ i ∈ σ.support, i ∉ A ∧ σ i ∉ F i := by
  classical
  simp [goodReverseSupportPermutations]
private noncomputable def forwardMaskForbiddenTargets {n : ℕ} (μ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (i : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun j ↦ ¬ ∃ q : ForwardInactiveColumnIndex flag (μ.symm i),
    q.val.val.val.1 = μ.symm j
end CompLP
end

-- PivotReverseCompetitorMass
section
open StableMarriage
open scoped BigOperators ENNReal
namespace CompLP
end CompLP
end

-- PivotForwardMaskProbability
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace CompLP
private noncomputable def forwardCellFlag (x y : ℝ) (z : ℝ × ℝ) : Bool := by
  classical
  exact decide (z ∈ forwardEligibleScoreCell x y)
@[simp] theorem forwardCellFlag_eq_true {x y : ℝ} {z : ℝ × ℝ} :
    forwardCellFlag x y z = true ↔ z ∈ forwardEligibleScoreCell x y := by
  classical
  simp [forwardCellFlag]
private noncomputable def forwardMaskOfScores {n : ℕ} (d : DiagonalScorePairs n)
    (z : OffDiagonalScorePairs n) (q : OffDiagonalCellIndex n) : Bool :=
  forwardCellFlag (diagonalPairAt d q.val.1).1 (diagonalPairAt d q.val.2).2 (z q)
theorem forwardMaskOfScores_eq_iff {n : ℕ} (d : DiagonalScorePairs n)
    (z : OffDiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool) :
    forwardMaskOfScores d z = flag ↔ z ∈ forwardScoreMaskEvent d flag := by
  rw [funext_iff, forwardScoreMaskEvent, mem_univ_pi]
  apply forall_congr'
  intro q
  cases flag q with
  | false =>
    simp [forwardScoreCellFlagEvent, forwardMaskOfScores, ← Bool.not_eq_true]
  | true =>
    simp [forwardScoreCellFlagEvent, forwardMaskOfScores]
end CompLP
end

-- PivotForwardRevealRectangle
section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace CompLP
private abbrev ForwardRevealedMaleScores {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :=
  ForwardActiveCellIndex flag → ℝ
private abbrev ForwardInactiveColumns {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :=
  (i : Fin n) → ForwardInactiveColumnIndex flag i → ℝ × ℝ
private def forwardRevealWithColumns {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :
    OffDiagonalScorePairs n → ForwardRevealedMaleScores flag × ForwardInactiveColumns flag :=
  Prod.map id (forwardInactiveColumnsEquiv flag) ∘ forwardScoreMaskRevealAndInactive flag
theorem measurable_forwardRevealWithColumns {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :
    Measurable (forwardRevealWithColumns flag) :=
  (measurable_id.prodMap (forwardInactiveColumnsEquiv flag).measurable).comp
    (measurable_forwardScoreMaskRevealAndInactive flag)
end CompLP
end

-- PivotForwardPivotReadout
section
open MeasureTheory Set StableMarriage
namespace CompLP
private noncomputable def forwardPivotIncrement {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (ρ : Matching n)
    (a : ForwardRevealedMaleScores flag) (m : Fin n) : ℝ :=
  if hm : ρ m ≠ m then
    let q : OffDiagonalCellIndex n := ⟨(m, ρ m), hm.symm⟩
    if hq : flag q = true then a ⟨q, hq⟩ - (diagonalPairAt d m).1 else 0
  else 0
end CompLP
end

-- SingletonIdealAnchor
section
namespace CompLP
variable {α : Type*} [PartialOrder α]
private def singletonAnchorIdeal (r : α) : LowerSet α :=
  ⟨(Set.Ici r)ᶜ, fun _ _ hst ht hrs ↦ ht (hrs.trans hst)⟩
@[simp] theorem mem_singletonAnchorIdeal {r s : α} :
    s ∈ singletonAnchorIdeal r ↔ ¬ r ≤ s :=
  Iff.rfl
theorem lowerSet_eq_singletonAnchorIdeal_iff [Finite α] (I : LowerSet α) (r : α) :
    I = singletonAnchorIdeal r ↔ ∀ s : α, Minimal (fun t : α ↦ t ∉ I) s ↔ s = r :=
  ⟨fun h s ↦ h.symm ▸
    minimal_iff_eq (fun hr ↦ (mem_singletonAnchorIdeal.mp hr) le_rfl)
      (fun _ ht ↦ not_not.mp fun hrt ↦ ht (mem_singletonAnchorIdeal.mpr hrt)),
    fun h ↦ LowerSet.ext (Set.ext fun s ↦
      show s ∈ I ↔ ¬ r ≤ s from
      ⟨fun hs hrs ↦ ((h r).mpr rfl).prop (I.lower hrs hs),
        fun hrs ↦ Classical.byContradiction fun hs ↦
          
          let ⟨t, hts, ht⟩ := Finite.exists_le_minimal (p := fun t : α ↦ t ∉ I) hs
          hrs (by simpa only [(h t).mp ht] using hts)⟩)⟩
end CompLP
end

-- SingletonRotationAnchor
section
open StableMarriage
namespace CompLP
variable {n : ℕ} {p : Profile n} {μ₀ μ : Matching n}
private def Rotation.IsExposedAt (r : Rotation p μ₀) (μ : Matching n) : Prop :=
  IsExposedRotation p μ r.val.cycle ∧ rotationLabel μ r.val.cycle = r.val
theorem Rotation.isExposedAt_iff_minimal (hopt : IsManOptimal p μ₀) (hμ : IsStable p μ)
    (r : Rotation p μ₀) :
    r.IsExposedAt μ ↔ Minimal (fun s ↦ s ∉ eliminatedRotations p μ₀ μ) r := by
  rw [minimal_iff_forall_lt]
  constructor
  · rintro ⟨he, hl⟩
    have hr : rotationOfExposed hopt hμ he = r := Subtype.ext hl
    refine ⟨hr ▸ rotationOfExposed_not_mem_eliminatedRotations hopt hμ he, ?_⟩
    intro s hsr
    exact not_not_intro
      ((Rotation.lt_iff_before_exposure hopt hsr.ne).mp hsr μ hμ he hl)
  · classical
    rintro ⟨hr, hbefore⟩
    let I := stableMatchingToRotationIdeal (μ₀ := μ₀) ⟨μ, hμ⟩
    let J : LowerSet (Rotation p μ₀) :=
      ⟨insert r (I : Set (Rotation p μ₀)), by
        intro s t hst ht
        rcases Set.mem_insert_iff.mp ht with rfl | ht
        · rcases eq_or_lt_of_le hst with rfl | hsr
          · exact Set.mem_insert _ _
          · exact Set.mem_insert_of_mem _ (not_not.mp (hbefore hsr))
        · exact Set.mem_insert_of_mem _ (I.lower hst ht)⟩
    let e := stableMatchingEquivRotationIdeals hopt
    let ν := e.symm J
    have hν : eliminatedRotations p μ₀ ν.val = (J : Set (Rotation p μ₀)) :=
      congrArg (fun K : LowerSet (Rotation p μ₀) ↦ (K : Set (Rotation p μ₀)))
        (e.apply_symm_apply J)
    have hle : eliminatedRotations p μ₀ μ ⊆ eliminatedRotations p μ₀ ν.val := by
      rw [hν]
      exact fun s hs ↦ Set.mem_insert_of_mem _ hs
    have hne : μ ≠ ν.val := by
      intro h
      apply hr
      rw [h, hν]
      exact Set.mem_insert r _
    obtain ⟨ρ, hρ, hnext⟩ := exists_exposedRotation_towards_target hμ ν.property
      ((eliminatedRotations_subset_iff hopt hμ ν.property).mp hle) hne
    let q := rotationOfExposed hopt hμ hρ
    obtain ⟨rs, hrs⟩ := exists_rotationSequence_of_manOptimal hopt hμ
    have hstable := hρ.isStable_eliminate hμ
    have hstep : RotationSequence p μ [ρ] (eliminateRotation μ ρ) :=
      .cons hμ hρ (.nil hstable)
    have hq : q ∈ eliminatedRotations p μ₀ (eliminateRotation μ ρ) := by
      apply (hrs.append hstep).mem_eliminatedRotations_iff.mpr
      simp [hrs.rotationLabels_append, rotationLabels, q, rotationOfExposed]
    have hq' := (eliminatedRotations_subset_iff hopt hstable ν.property).mpr hnext hq
    rw [hν] at hq'
    have hqr : q = r := (Set.mem_insert_iff.mp hq').resolve_right
      (rotationOfExposed_not_mem_eliminatedRotations hopt hμ hρ)
    rw [← hqr]
    exact ⟨hρ, rfl⟩
private noncomputable def singletonRotationAnchor (hopt : IsManOptimal p μ₀) (r : Rotation p μ₀) :
    {ν : Matching n // IsStable p ν} :=
  (stableMatchingEquivRotationIdeals hopt).symm (singletonAnchorIdeal r)
theorem eliminatedRotations_singletonRotationAnchor
    (hopt : IsManOptimal p μ₀) (r : Rotation p μ₀) :
    eliminatedRotations p μ₀ (singletonRotationAnchor hopt r).val = (Set.Ici r)ᶜ :=
  congrArg (fun I : LowerSet (Rotation p μ₀) ↦ (I : Set (Rotation p μ₀)))
    ((stableMatchingEquivRotationIdeals hopt).apply_symm_apply (singletonAnchorIdeal r))
theorem eq_singletonRotationAnchor_iff (hopt : IsManOptimal p μ₀) (r : Rotation p μ₀)
    (ν : {ν : Matching n // IsStable p ν}) :
    ν = singletonRotationAnchor hopt r ↔
      ∀ s : Rotation p μ₀, s.IsExposedAt ν.val ↔ s = r := by
  let e := stableMatchingEquivRotationIdeals hopt
  change ν = e.symm (singletonAnchorIdeal r) ↔ _
  rw [← e.apply_eq_iff_eq, e.apply_symm_apply, lowerSet_eq_singletonAnchorIdeal_iff]
  simp only [Rotation.isExposedAt_iff_minimal hopt ν.property]
  rfl
end CompLP
end

-- UndoableRotations
section
open StableMarriage
namespace CompLP
variable {n : ℕ} {p : Profile n} {μ₀ μ ν : Matching n} {r : Rotation p μ₀}
private def Rotation.IsUndoableAt (r : Rotation p μ₀) (ν : Matching n) : Prop :=
  ∃ μ, IsStable p μ ∧ r.IsExposedAt μ ∧ eliminateRotation μ r.val.cycle = ν
theorem Rotation.IsExposedAt.eliminatedRotations_eliminate
    (he : r.IsExposedAt μ) (hopt : IsManOptimal p μ₀) (hμ : IsStable p μ) :
    eliminatedRotations p μ₀ (eliminateRotation μ r.val.cycle) =
      insert r (eliminatedRotations p μ₀ μ) := by
  obtain ⟨rs, hrs⟩ := exists_rotationSequence_of_manOptimal hopt hμ
  have hstep : RotationSequence p μ [r.val.cycle] (eliminateRotation μ r.val.cycle) :=
    .cons hμ he.1 (.nil (he.1.isStable_eliminate hμ))
  ext s
  rw [(hrs.append hstep).mem_eliminatedRotations_iff, hrs.rotationLabels_append,
    List.mem_append, ← hrs.mem_eliminatedRotations_iff]
  simp only [rotationLabels, List.mem_singleton, he.2, Set.mem_insert_iff]
  constructor
  · rintro (hs | hs)
    · exact Or.inr hs
    · exact Or.inl (Subtype.ext hs)
  · rintro (hs | hs)
    · exact Or.inr (congrArg (fun x : Rotation p μ₀ ↦ x.val) hs)
    · exact Or.inl hs
theorem Rotation.IsExposedAt.eliminatedRotations_eq_diff
    (he : r.IsExposedAt μ) (hopt : IsManOptimal p μ₀) (hμ : IsStable p μ)
    (hstep : eliminateRotation μ r.val.cycle = ν) :
    eliminatedRotations p μ₀ μ = eliminatedRotations p μ₀ ν \ {r} := by
  have hnot := ((r.isExposedAt_iff_minimal hopt hμ).mp he).prop
  rw [← hstep, he.eliminatedRotations_eliminate hopt hμ]
  ext s
  simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact ⟨fun hs ↦ ⟨Or.inr hs, fun h ↦ hnot (h ▸ hs)⟩,
    fun ⟨hs, hne⟩ ↦ hs.resolve_left hne⟩
theorem Rotation.isUndoableAt_iff_maximal (hopt : IsManOptimal p μ₀) (hν : IsStable p ν)
    (r : Rotation p μ₀) :
    r.IsUndoableAt ν ↔ Maximal (fun s ↦ s ∈ eliminatedRotations p μ₀ ν) r := by
  constructor
  · rintro ⟨μ, hμ, he, rfl⟩
    rw [he.eliminatedRotations_eliminate hopt hμ, maximal_iff_forall_gt]
    refine ⟨Set.mem_insert _ _, fun s hrs hs ↦ ?_⟩
    have hold := (Set.mem_insert_iff.mp hs).resolve_left hrs.ne.symm
    exact ((r.isExposedAt_iff_minimal hopt hμ).mp he).prop (hrs.le _ hold)
  · intro hmax
    let I := stableMatchingToRotationIdeal (μ₀ := μ₀) ⟨ν, hν⟩
    let J : LowerSet (Rotation p μ₀) :=
      ⟨(I : Set (Rotation p μ₀)) \ {r}, by
        intro b a hab hb
        refine ⟨I.lower hab hb.1, ?_⟩
        intro ha
        have har : a = r := Set.mem_singleton_iff.mp ha
        subst a
        exact hb.2 (Set.mem_singleton_iff.mpr ((hmax.2 hb.1 hab).antisymm hab))⟩
    let e := stableMatchingEquivRotationIdeals hopt
    let μ := e.symm J
    have hμI : eliminatedRotations p μ₀ μ.val = (J : Set (Rotation p μ₀)) :=
      congrArg (fun K : LowerSet (Rotation p μ₀) ↦ (K : Set (Rotation p μ₀)))
        (e.apply_symm_apply J)
    have he : r.IsExposedAt μ.val := by
      rw [Rotation.isExposedAt_iff_minimal hopt μ.property, minimal_iff_forall_lt, hμI]
      refine ⟨fun h ↦ h.2 (Set.mem_singleton r), fun s hsr hn ↦ hn ?_⟩
      exact ⟨I.lower hsr.le hmax.prop, fun h ↦ hsr.ne (Set.mem_singleton_iff.mp h)⟩
    have hsets : eliminatedRotations p μ₀ (eliminateRotation μ.val r.val.cycle) =
        eliminatedRotations p μ₀ ν := by
      rw [he.eliminatedRotations_eliminate hopt μ.property, hμI]
      change insert r ((I : Set (Rotation p μ₀)) \ {r}) = (I : Set (Rotation p μ₀))
      rw [Set.insert_sdiff_singleton]
      exact Set.insert_eq_of_mem (show r ∈ I from hmax.prop)
    have hstable := he.1.isStable_eliminate μ.property
    have hmatching : (⟨eliminateRotation μ.val r.val.cycle, hstable⟩ :
        {τ : Matching n // IsStable p τ}) = ⟨ν, hν⟩ :=
      (stableMatchingToRotationIdeal_bijective hopt).1 (LowerSet.ext hsets)
    exact ⟨μ.val, μ.property, he, congrArg Subtype.val hmatching⟩
end CompLP
end

-- ReverseRotationIdeals
section
open StableMarriage
namespace CompLP
variable {n : ℕ} {p : Profile n} {μ₀ ν : Matching n} {σ : Equiv.Perm (Fin n)}
private def IsReverseExposedRotation (p : Profile n) (ν : Matching n) (σ : Equiv.Perm (Fin n)) : Prop :=
  IsExposedRotation (swapProfile p) ν.symm σ
private def undoReverseRotation (ν : Matching n) (σ : Equiv.Perm (Fin n)) : Matching n :=
  (eliminateRotation ν.symm σ).symm
theorem IsReverseExposedRotation.undo_stable
    (hσ : IsReverseExposedRotation p ν σ) (hν : IsStable p ν) :
    IsStable p (undoReverseRotation ν σ) := by
  apply isStable_swapProfile_iff.mp
  simpa only [undoReverseRotation, Equiv.symm_symm] using
    (show IsExposedRotation (swapProfile p) ν.symm σ from hσ).isStable_eliminate
      (isStable_swapProfile_iff.mpr hν)
theorem IsReverseExposedRotation.forward_exposed
    (hσ : IsReverseExposedRotation p ν σ) (hν : IsStable p ν) :
    IsExposedRotation p (undoReverseRotation ν σ) (reverseRotationCycle ν.symm σ) := by
  simpa only [undoReverseRotation, swapProfile_swapProfile] using
    (show IsExposedRotation (swapProfile p) ν.symm σ from hσ).isExposedRotation_swap_eliminate
      (isStable_swapProfile_iff.mpr hν)
theorem eliminateRotation_undoReverseRotation (ν : Matching n) (σ : Equiv.Perm (Fin n)) :
    eliminateRotation (undoReverseRotation ν σ) (reverseRotationCycle ν.symm σ) = ν := by
  simpa only [undoReverseRotation, Equiv.symm_symm] using
    eliminateRotation_swap_reverseCycle ν.symm σ
private def reverseExposedRotationLabel (hopt : IsManOptimal p μ₀) (hν : IsStable p ν)
    (σ : {σ : Equiv.Perm (Fin n) // IsReverseExposedRotation p ν σ}) : Rotation p μ₀ :=
  rotationOfExposed hopt (σ.property.undo_stable hν) (σ.property.forward_exposed hν)
theorem eliminatedRotations_undoReverseRotation (hopt : IsManOptimal p μ₀) (hν : IsStable p ν)
    (σ : {σ : Equiv.Perm (Fin n) // IsReverseExposedRotation p ν σ}) :
    eliminatedRotations p μ₀ (undoReverseRotation ν σ.val) =
      eliminatedRotations p μ₀ ν \ {reverseExposedRotationLabel hopt hν σ} :=
  (show (reverseExposedRotationLabel hopt hν σ).IsExposedAt (undoReverseRotation ν σ.val)
    from ⟨σ.property.forward_exposed hν, rfl⟩).eliminatedRotations_eq_diff
      hopt (σ.property.undo_stable hν) (eliminateRotation_undoReverseRotation ν σ.val)
theorem reverseExposedRotationLabel_maximal (hopt : IsManOptimal p μ₀) (hν : IsStable p ν)
    (σ : {σ : Equiv.Perm (Fin n) // IsReverseExposedRotation p ν σ}) :
    Maximal (fun s ↦ s ∈ eliminatedRotations p μ₀ ν)
      (reverseExposedRotationLabel hopt hν σ) :=
  (Rotation.isUndoableAt_iff_maximal hopt hν _).mp
    ⟨undoReverseRotation ν σ.val, σ.property.undo_stable hν,
      ⟨σ.property.forward_exposed hν, rfl⟩, eliminateRotation_undoReverseRotation ν σ.val⟩
private noncomputable def reverseExposedRotationEquivMaximal (hopt : IsManOptimal p μ₀)
    (hν : IsStable p ν) :
    {σ : Equiv.Perm (Fin n) // IsReverseExposedRotation p ν σ} ≃
      {r : Rotation p μ₀ // Maximal (fun s ↦ s ∈ eliminatedRotations p μ₀ ν) r} := by
  let f (σ : {σ : Equiv.Perm (Fin n) // IsReverseExposedRotation p ν σ}) :
      {r : Rotation p μ₀ // Maximal (fun s ↦ s ∈ eliminatedRotations p μ₀ ν) r} :=
    ⟨reverseExposedRotationLabel hopt hν σ, reverseExposedRotationLabel_maximal hopt hν σ⟩
  apply Equiv.ofBijective f
  constructor
  · intro σ τ h
    apply Subtype.ext
    apply Equiv.ext
    intro w
    have he := congrArg
      (fun r : {r : Rotation p μ₀ //
          Maximal (fun s ↦ s ∈ eliminatedRotations p μ₀ ν) r} ↦
        r.val.val.cycle (ν.symm w)) h
    change reverseRotationCycle ν.symm σ.val (ν.symm w) =
      reverseRotationCycle ν.symm τ.val (ν.symm w) at he
    exact ν.symm.injective (by simpa [reverseRotationCycle] using he)
  · rintro ⟨r, hr⟩
    obtain ⟨μ, hμ, he, hstep⟩ := (r.isUndoableAt_iff_maximal hopt hν).mpr hr
    let σ := reverseRotationCycle μ r.val.cycle
    have hσ : IsReverseExposedRotation p ν σ := by
      rw [← hstep]
      exact he.1.isExposedRotation_swap_eliminate hμ
    have hund : undoReverseRotation ν σ = μ := by
      rw [← hstep, undoReverseRotation, eliminateRotation_swap_reverseCycle, Equiv.symm_symm]
    have hcycle : reverseRotationCycle ν.symm σ = r.val.cycle := by
      rw [← hstep]
      exact reverseRotationCycle_swap_reverseCycle μ r.val.cycle
    refine ⟨⟨σ, hσ⟩, Subtype.ext (Subtype.ext ?_)⟩
    change rotationLabel (undoReverseRotation ν σ) (reverseRotationCycle ν.symm σ) = r.val
    rw [hund, hcycle]
    exact he.2
end CompLP
end

-- PivotCrossBlocker
section
open StableMarriage
namespace CompLP
variable {n : ℕ} {p : Profile n} {A N : Matching n} {ρ : Equiv.Perm (Fin n)}
theorem rotationLabel_eq_of_fixed_on_cycle
    (hfixed : ∀ m, ρ m ≠ m → N m = A m) :
    rotationLabel N ρ = rotationLabel A ρ := by
  unfold rotationLabel
  congr 1
  funext m
  by_cases hm : ρ m = m
  · simp [hm]
  · simp [hm, hfixed m hm]
end CompLP
end

-- PivotReversePermutationCompatibility
section
open StableMarriage
namespace CompLP
variable {n : ℕ} {p : Profile n} {μ ρ σ : Matching n}
theorem RealizesSuccessorPermutation.womanRank_eliminate_le
    (hσ : RealizesSuccessorPermutation p μ σ) (w : Fin n) :
    p.womanRank w ((eliminateRotation μ σ).symm w) ≤ p.womanRank w (μ.symm w) :=
  let ⟨m, hm⟩ := (eliminateRotation μ σ).surjective w
  have hle : p.womanRank (μ (σ m)) m ≤ p.womanRank (μ (σ m)) (σ m) :=
    if he : σ m = m then (congrArg (p.womanRank (μ (σ m))) he.symm).le
    else by simpa only [Equiv.symm_apply_apply] using
      (IsSuccessor.eligible (hσ m (Equiv.Perm.mem_support.mpr he))).2.le
  have htarget : p.womanRank (eliminateRotation μ σ m)
      ((eliminateRotation μ σ).symm (eliminateRotation μ σ m)) ≤
        p.womanRank (eliminateRotation μ σ m) (μ.symm (eliminateRotation μ σ m)) := by
    have hinv : (eliminateRotation μ σ).symm (μ (σ m)) = m :=
      (eliminateRotation μ σ).symm_apply_apply m
    simpa only [eliminateRotation_apply, hinv, Equiv.symm_apply_apply] using hle
  hm ▸ htarget
theorem RealizesSuccessorPermutation.isStable_eliminate
    (hσ : RealizesSuccessorPermutation p μ σ) (hμ : IsStable p μ) :
    IsStable p (eliminateRotation μ σ) :=
  fun m w hb ↦
    have hwOld : p.womanRank w m < p.womanRank w (μ.symm w) :=
      hb.2.2.trans_le (hσ.womanRank_eliminate_le w)
    have hne : μ m ≠ w := fun h ↦ (ne_of_lt hwOld)
      (congrArg (p.womanRank w) ((μ.symm_apply_apply m).symm.trans (congrArg μ.symm h)))
    have hnot : ¬ p.manRank m w < p.manRank m (μ m) := fun h ↦
      hμ m w ⟨hne, h, hwOld⟩
    if hm : σ m = m then
      hnot (by simpa only [eliminateRotation_apply, hm] using hb.2.1)
    else
      have hbelow : p.manRank m (μ m) < p.manRank m w :=
        lt_of_le_of_ne (le_of_not_gt hnot) (fun he ↦ hne ((p.manRank m).injective he))
      (not_lt_of_ge ((IsSuccessor.min_rank (hσ m (Equiv.Perm.mem_support.mpr hm))) w ⟨hbelow, hwOld⟩)) hb.2.1
theorem RealizesSuccessorPermutation.undo_stable
    (hσ : RealizesSuccessorPermutation (swapProfile p) μ.symm σ) (hμ : IsStable p μ) :
    IsStable p (undoReverseRotation μ σ) :=
  isStable_swapProfile_iff.mp (hσ.isStable_eliminate (isStable_swapProfile_iff.mpr hμ))
theorem undoReverseRotation_symm_apply (μ σ : Matching n) (w : Fin n) :
    (undoReverseRotation μ σ).symm w = μ.symm (σ w) :=
  rfl
end CompLP
end

-- UndoMaximalSubset
section
open StableMarriage
namespace CompLP
variable {n : ℕ} {p : Profile n} {μ₀ ν : Matching n}
private abbrev MaximalEliminatedRotation (p : Profile n) (μ₀ ν : Matching n) :=
  {r : Rotation p μ₀ // Maximal (fun s ↦ s ∈ eliminatedRotations p μ₀ ν) r}
private def undoMaximalSubsetIdeal (hν : IsStable p ν)
    (D : Set (MaximalEliminatedRotation p μ₀ ν)) : LowerSet (Rotation p μ₀) :=
  ⟨eliminatedRotations p μ₀ ν \ (Subtype.val '' D), by
    let I := stableMatchingToRotationIdeal (μ₀ := μ₀) ⟨ν, hν⟩
    intro b a hab hb
    refine ⟨I.lower hab hb.1, ?_⟩
    rintro ⟨r, hr, rfl⟩
    exact hb.2 ⟨r, hr, hab.antisymm (r.property.2 hb.1 hab)⟩⟩
private theorem mem_undoMaximalSubsetIdeal_iff (hν : IsStable p ν)
    (D : Set (MaximalEliminatedRotation p μ₀ ν)) (r : MaximalEliminatedRotation p μ₀ ν) :
    r.val ∈ undoMaximalSubsetIdeal hν D ↔ r ∉ D := by
  change (r.val ∈ eliminatedRotations p μ₀ ν ∧ r.val ∉ Subtype.val '' D) ↔ r ∉ D
  rw [and_iff_right r.property.1, Subtype.val_injective.mem_set_image]
private def undoMaximalSubsetIdealEmbedding (hν : IsStable p ν) :
    Set (MaximalEliminatedRotation p μ₀ ν) ↪ LowerSet (Rotation p μ₀) :=
  ⟨undoMaximalSubsetIdeal hν, by
    intro D E h
    ext r
    apply not_iff_not.mp
    rw [← mem_undoMaximalSubsetIdeal_iff hν D r,
      ← mem_undoMaximalSubsetIdeal_iff hν E r, h]⟩
private noncomputable def undoMaximalSubsetEmbedding (hopt : IsManOptimal p μ₀) (hν : IsStable p ν) :
    Set (MaximalEliminatedRotation p μ₀ ν) ↪ {μ : Matching n // IsStable p μ} :=
  (undoMaximalSubsetIdealEmbedding hν).trans
    (stableMatchingEquivRotationIdeals hopt).symm.toEmbedding
theorem eliminatedRotations_undoMaximalSubsetEmbedding (hopt : IsManOptimal p μ₀)
    (hν : IsStable p ν) (D : Set (MaximalEliminatedRotation p μ₀ ν)) :
    eliminatedRotations p μ₀ (undoMaximalSubsetEmbedding hopt hν D).val =
      eliminatedRotations p μ₀ ν \ (Subtype.val '' D) :=
  congrArg (fun I : LowerSet (Rotation p μ₀) ↦ (I : Set (Rotation p μ₀)))
    ((stableMatchingEquivRotationIdeals hopt).apply_symm_apply (undoMaximalSubsetIdeal hν D))
end CompLP
end

-- PivotIdealExposure
section
open StableMarriage
namespace CompLP
theorem minimal_compl_diff_maximal_iff {α : Type*} [PartialOrder α]
    (I : LowerSet α) (D : Set α) (hD : ∀ t ∈ D, Maximal (· ∈ I) t) (s : α) :
    Minimal (· ∉ (I : Set α) \ D) s ↔
      s ∈ D ∨ (Minimal (· ∉ I) s ∧ ∀ t ∈ D, ¬ t < s) := by
  simp only [minimal_iff_forall_lt, not_not]
  constructor
  · rintro ⟨hs, hpred⟩
    by_cases hsD : s ∈ D
    · exact Or.inl hsD
    · exact Or.inr ⟨⟨fun hsI ↦ hs ⟨hsI, hsD⟩, fun _ hts ↦ (hpred hts).1⟩,
        fun _ htD hts ↦ (hpred hts).2 htD⟩
  · rintro (hsD | ⟨⟨hsI, hpred⟩, hcompat⟩)
    · have hsI := (hD s hsD).prop
      refine ⟨fun h ↦ h.2 hsD, fun t hts ↦ ⟨I.lower hts.le hsI, ?_⟩⟩
      exact fun htD ↦ hts.not_ge ((hD t htD).2 hsI hts.le)
    · exact ⟨fun h ↦ hsI h.1, fun t hts ↦ ⟨hpred hts, fun htD ↦ hcompat t htD hts⟩⟩
variable {n : ℕ} {p : Profile n} {μ₀ μ : Matching n}
theorem isExposedAt_undoMaximalSubsetEmbedding_iff
    (hopt : IsManOptimal p μ₀) (hμ : IsStable p μ)
    (D : Set (MaximalEliminatedRotation p μ₀ μ)) (s : Rotation p μ₀) :
    s.IsExposedAt (undoMaximalSubsetEmbedding hopt hμ D).val ↔
      s ∈ Subtype.val '' D ∨ (s.IsExposedAt μ ∧ ∀ t ∈ Subtype.val '' D, ¬ t < s) := by
  rw [Rotation.isExposedAt_iff_minimal hopt (undoMaximalSubsetEmbedding hopt hμ D).property,
    Rotation.isExposedAt_iff_minimal hopt hμ,
    eliminatedRotations_undoMaximalSubsetEmbedding]
  let I := stableMatchingToRotationIdeal (μ₀ := μ₀) ⟨μ, hμ⟩
  apply minimal_compl_diff_maximal_iff I
  rintro _ ⟨t, _, rfl⟩
  exact t.property
theorem pivot_isExposedAt_undo_iff (hopt : IsManOptimal p μ₀) (r : Rotation p μ₀)
    (D : Set (MaximalEliminatedRotation p μ₀ (singletonRotationAnchor hopt r).val)) :
    r.IsExposedAt
      (undoMaximalSubsetEmbedding hopt (singletonRotationAnchor hopt r).property D).val ↔
      ∀ s ∈ Subtype.val '' D, ¬ s < r := by
  let A := singletonRotationAnchor hopt r
  have hA : r.IsExposedAt A.val := ((eq_singletonRotationAnchor_iff hopt r A).mp rfl r).mpr rfl
  have hrI : r ∉ eliminatedRotations p μ₀ A.val :=
    ((Rotation.isExposedAt_iff_minimal hopt A.property r).mp hA).prop
  have hrD : r ∉ Subtype.val '' D := by
    rintro ⟨s, _, hs⟩
    exact hrI (hs ▸ s.property.prop)
  rw [isExposedAt_undoMaximalSubsetEmbedding_iff hopt A.property D r]
  exact ⟨fun h ↦ (h.resolve_left hrD).2, fun h ↦ Or.inr ⟨hA, h⟩⟩
theorem isExposedAt_undo_pivot_iff (hopt : IsManOptimal p μ₀) (r : Rotation p μ₀)
    (D : Set (MaximalEliminatedRotation p μ₀ (singletonRotationAnchor hopt r).val))
    (hr : r.IsExposedAt
      (undoMaximalSubsetEmbedding hopt (singletonRotationAnchor hopt r).property D).val)
    (s : Rotation p μ₀) :
    s.IsExposedAt
      (undoMaximalSubsetEmbedding hopt (singletonRotationAnchor hopt r).property D).val ↔
      s = r ∨ s ∈ Subtype.val '' D := by
  let A := singletonRotationAnchor hopt r
  have hcompat := (pivot_isExposedAt_undo_iff hopt r D).mp hr
  rw [isExposedAt_undoMaximalSubsetEmbedding_iff hopt A.property D s,
    (eq_singletonRotationAnchor_iff hopt r A).mp rfl s]
  constructor
  · rintro (hsD | ⟨hsr, _⟩)
    · exact Or.inr hsD
    · exact Or.inl hsr
  · rintro (rfl | hsD)
    · exact Or.inr ⟨rfl, hcompat⟩
    · exact Or.inl hsD
end CompLP
end

-- ReverseRotationPersistence
section
open StableMarriage
namespace CompLP
variable {n : ℕ} {p : Profile n} {μ₀ ν : Matching n} {σ τ : Equiv.Perm (Fin n)}
theorem IsReverseExposedRotation.persist_undo (hτ : IsReverseExposedRotation p ν τ)
    (hσ : IsReverseExposedRotation p ν σ) (hne : τ ≠ σ) :
    IsReverseExposedRotation p (undoReverseRotation ν σ) τ := by
  simpa only [IsReverseExposedRotation, undoReverseRotation, Equiv.symm_symm] using
    (show IsExposedRotation (swapProfile p) ν.symm τ from hτ).persist_eliminate hσ hne
theorem IsReverseExposedRotation.undo_comm (hσ : IsReverseExposedRotation p ν σ)
    (hτ : IsReverseExposedRotation p ν τ) (hne : σ ≠ τ) :
    undoReverseRotation (undoReverseRotation ν σ) τ =
      undoReverseRotation (undoReverseRotation ν τ) σ := by
  simpa only [undoReverseRotation, Equiv.symm_symm] using
    congrArg (fun μ : Matching n ↦ μ.symm)
      ((show IsExposedRotation (swapProfile p) ν.symm σ from hσ).eliminate_comm hτ hne)
theorem reverseExposedRotationLabel_persist_undo (hopt : IsManOptimal p μ₀)
    (hν : IsStable p ν) (hτ : IsReverseExposedRotation p ν τ)
    (hσ : IsReverseExposedRotation p ν σ) (hne : τ ≠ σ) :
    reverseExposedRotationLabel hopt (hσ.undo_stable hν) ⟨τ, hτ.persist_undo hσ hne⟩ =
      reverseExposedRotationLabel hopt hν ⟨τ, hτ⟩ := by
  let a := reverseExposedRotationLabel hopt hν ⟨σ, hσ⟩
  let b := reverseExposedRotationLabel hopt hν ⟨τ, hτ⟩
  let b' := reverseExposedRotationLabel hopt (hσ.undo_stable hν)
    ⟨τ, hτ.persist_undo hσ hne⟩
  have hba : b ≠ a := fun he ↦ hne
    (congrArg Subtype.val ((reverseExposedRotationEquivMaximal hopt hν).injective
      (Subtype.ext he)))
  have hb := (reverseExposedRotationLabel_maximal hopt hν ⟨τ, hτ⟩).prop
  change b' = b
  by_contra hne'
  
  have hbmem :
      b ∈ eliminatedRotations p μ₀ (undoReverseRotation (undoReverseRotation ν σ) τ) := by
    rw [eliminatedRotations_undoReverseRotation hopt (hσ.undo_stable hν)
      ⟨τ, hτ.persist_undo hσ hne⟩,
      eliminatedRotations_undoReverseRotation hopt hν ⟨σ, hσ⟩]
    exact ⟨⟨hb, fun he ↦ hba (Set.mem_singleton_iff.mp he)⟩,
      fun he ↦ hne' (Set.mem_singleton_iff.mp he).symm⟩
  rw [hσ.undo_comm hτ hne.symm,
    eliminatedRotations_undoReverseRotation hopt (hτ.undo_stable hν)
      ⟨σ, hσ.persist_undo hτ hne.symm⟩,
    eliminatedRotations_undoReverseRotation hopt hν ⟨τ, hτ⟩] at hbmem
  exact hbmem.1.2 (Set.mem_singleton _)
end CompLP
end

-- RotationUndoSequences
section
open StableMarriage
namespace CompLP
variable {n : ℕ} {p : Profile n} {μ₀ μ ν : Matching n} {hopt : IsManOptimal p μ₀}
private inductive RotationUndoSequence (hopt : IsManOptimal p μ₀) :
    Matching n → List (Rotation p μ₀) → Matching n → Prop where
  | nil {ν : Matching n} (hν : IsStable p ν) : RotationUndoSequence hopt ν [] ν
  | cons {ν τ : Matching n} {r : Rotation p μ₀} {rs : List (Rotation p μ₀)}
      (hν : IsStable p ν)
      (σ : {σ : Equiv.Perm (Fin n) // IsReverseExposedRotation p ν σ})
      (hlabel : reverseExposedRotationLabel hopt hν σ = r)
      (rest : RotationUndoSequence hopt (undoReverseRotation ν σ.val) rs τ) :
      RotationUndoSequence hopt ν (r :: rs) τ
theorem RotationUndoSequence.isStable_end {rs : List (Rotation p μ₀)}
    (h : RotationUndoSequence hopt ν rs μ) : IsStable p μ := by
  induction h with
  | nil hν => exact hν
  | cons _ _ _ _ ih => exact ih
theorem RotationUndoSequence.eliminatedRotations_end {rs : List (Rotation p μ₀)}
    (h : RotationUndoSequence hopt ν rs μ) :
    eliminatedRotations p μ₀ μ = eliminatedRotations p μ₀ ν \ {r | r ∈ rs} := by
  induction h with
  | nil => simp
  | cons hν σ hlabel _ ih =>
    rw [ih, eliminatedRotations_undoReverseRotation hopt hν σ, hlabel, Set.sdiff_sdiff]
    congr 1
    ext r
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq, List.mem_cons]
private theorem maximal_mem_diff_singleton {α : Type*} [PartialOrder α] {I : Set α} {r s : α}
    (hs : Maximal (fun q ↦ q ∈ I) s) (hne : s ≠ r) :
    Maximal (fun q ↦ q ∈ I \ {r}) s :=
  ⟨⟨hs.prop, fun h ↦ hne (Set.mem_singleton_iff.mp h)⟩, fun _ h hsq ↦ hs.2 h.1 hsq⟩
theorem exists_rotationUndoSequence_of_nodup (hopt : IsManOptimal p μ₀) (hν : IsStable p ν)
    (rs : List (Rotation p μ₀)) (hnd : rs.Nodup)
    (hmax : ∀ r ∈ rs, Maximal (fun q ↦ q ∈ eliminatedRotations p μ₀ ν) r) :
    ∃ μ, RotationUndoSequence hopt ν rs μ := by
  induction rs generalizing ν with
  | nil => exact ⟨ν, .nil hν⟩
  | cons r rs ih =>
    have hr := hmax r List.mem_cons_self
    let e := reverseExposedRotationEquivMaximal hopt hν
    let σ := e.symm ⟨r, hr⟩
    have hlabel : reverseExposedRotationLabel hopt hν σ = r :=
      congrArg Subtype.val (e.apply_symm_apply ⟨r, hr⟩)
    have hstep := eliminatedRotations_undoReverseRotation hopt hν σ
    rw [hlabel] at hstep
    have htail (s : Rotation p μ₀) (hs : s ∈ rs) :
        Maximal
          (fun q ↦ q ∈ eliminatedRotations p μ₀ (undoReverseRotation ν σ.val)) s := by
      rw [hstep]
      exact maximal_mem_diff_singleton (hmax s (List.mem_cons_of_mem r hs))
        (fun h ↦ (List.nodup_cons.mp hnd).1 (h ▸ hs))
    obtain ⟨μ, hpath⟩ :=
      ih (σ.property.undo_stable hν) (List.nodup_cons.mp hnd).2 htail
    exact ⟨μ, .cons hν σ hlabel hpath⟩
theorem rotationUndoSequence_undoMaximalSubsetEmbedding
    (hopt : IsManOptimal p μ₀) (hν : IsStable p ν)
    (D : Set (MaximalEliminatedRotation p μ₀ ν)) (rs : List (Rotation p μ₀))
    (hnd : rs.Nodup) (horder : {r | r ∈ rs} = Subtype.val '' D) :
    RotationUndoSequence hopt ν rs (undoMaximalSubsetEmbedding hopt hν D).val := by
  have hmax (r : Rotation p μ₀) (hr : r ∈ rs) :
      Maximal (fun q ↦ q ∈ eliminatedRotations p μ₀ ν) r := by
    obtain ⟨s, _, rfl⟩ := horder ▸ (show r ∈ {r | r ∈ rs} from hr)
    exact s.property
  obtain ⟨μ, hpath⟩ := exists_rotationUndoSequence_of_nodup hopt hν rs hnd hmax
  have hideal : eliminatedRotations p μ₀ μ =
      eliminatedRotations p μ₀ (undoMaximalSubsetEmbedding hopt hν D).val := by
    rw [hpath.eliminatedRotations_end, horder, eliminatedRotations_undoMaximalSubsetEmbedding]
  have heq : (⟨μ, hpath.isStable_end⟩ : {a : Matching n // IsStable p a}) =
      undoMaximalSubsetEmbedding hopt hν D :=
    (stableMatchingToRotationIdeal_bijective hopt).1 (LowerSet.ext hideal)
  exact congrArg Subtype.val heq ▸ hpath
theorem exists_rotationUndoSequence_of_maximal_subset (hopt : IsManOptimal p μ₀)
    (hν : IsStable p ν) (D : Set (MaximalEliminatedRotation p μ₀ ν)) :
    ∃ rs : List (Rotation p μ₀), rs.Nodup ∧ {r | r ∈ rs} = Subtype.val '' D ∧
      RotationUndoSequence hopt ν rs (undoMaximalSubsetEmbedding hopt hν D).val := by
  classical
  let A : Finset (Rotation p μ₀) := (Subtype.val '' D).toFinite.toFinset
  have horder : {r | r ∈ A.toList} = Subtype.val '' D := by
    ext r
    simp [A]
  exact ⟨A.toList, A.nodup_toList, horder,
    rotationUndoSequence_undoMaximalSubsetEmbedding hopt hν D _ A.nodup_toList horder⟩
private theorem exists_aligned_undo_sequences {α : Type*} (hopt : IsManOptimal p μ₀)
    (hν : IsStable p ν) (rs : List α)
    (cycle : α → Equiv.Perm (Fin n)) (label : α → Rotation p μ₀)
    (hnd : (rs.map cycle).Nodup)
    (he : ∀ x ∈ rs, IsReverseExposedRotation p ν (cycle x))
    (hl : ∀ x (hx : x ∈ rs), reverseExposedRotationLabel hopt hν
      ⟨cycle x, he x hx⟩ = label x) :
    ∃ μ, RotationSequence (swapProfile p) ν.symm (rs.map cycle) μ.symm ∧
      RotationUndoSequence hopt ν (rs.map label) μ := by
  induction rs generalizing ν with
  | nil => exact ⟨ν, .nil (isStable_swapProfile_iff.mpr hν), .nil hν⟩
  | cons a rs ih =>
    have hσ := he a List.mem_cons_self
    have hν' := hσ.undo_stable hν
    have hdistinct (x : α) (hx : x ∈ rs) : cycle x ≠ cycle a := fun heq ↦
      (List.nodup_cons.mp hnd).1 (List.mem_map.mpr ⟨x, hx, heq⟩)
    have hnext (x : α) (hx : x ∈ rs) :
        IsReverseExposedRotation p (undoReverseRotation ν (cycle a)) (cycle x) :=
      (he x (List.mem_cons_of_mem a hx)).persist_undo hσ (hdistinct x hx)
    have hnextLabel (x : α) (hx : x ∈ rs) : reverseExposedRotationLabel hopt hν'
        ⟨cycle x, hnext x hx⟩ = label x :=
      (reverseExposedRotationLabel_persist_undo hopt hν (he x (List.mem_cons_of_mem a hx))
        hσ (hdistinct x hx)).trans (hl x (List.mem_cons_of_mem a hx))
    obtain ⟨μ, hcycles, hlabels⟩ :=
      ih hν' (List.nodup_cons.mp hnd).2 hnext hnextLabel
    refine ⟨μ, .cons (isStable_swapProfile_iff.mpr hν) hσ ?_,
      .cons hν ⟨cycle a, hσ⟩ (hl a List.mem_cons_self) hlabels⟩
    simpa only [undoReverseRotation, Equiv.symm_symm] using hcycles
theorem exists_rotationUndoSequence_of_reverse_cycles
    (hopt : IsManOptimal p μ₀) (hν : IsStable p ν)
    (rs : List {σ : Equiv.Perm (Fin n) // IsReverseExposedRotation p ν σ}) (hnd : rs.Nodup) :
    ∃ μ, RotationSequence (swapProfile p) ν.symm (rs.map Subtype.val) μ.symm ∧
      RotationUndoSequence hopt ν (rs.map (reverseExposedRotationLabel hopt hν)) μ :=
  exists_aligned_undo_sequences hopt hν rs Subtype.val (reverseExposedRotationLabel hopt hν)
    (hnd.map Subtype.val_injective) (fun σ _ ↦ σ.property) (fun _ _ ↦ rfl)
end CompLP
end

-- PivotIncidenceCounting
section
open StableMarriage
open scoped BigOperators
namespace CompLP
variable {n : ℕ} {p : Profile n} {μ₀ ν μ : Matching n} {hopt : IsManOptimal p μ₀}
private def rotationLength (r : Rotation p μ₀) : ℕ :=
  r.val.cycle.support.card
theorem RotationUndoSequence.partner_eq_of_fixed {rs : List (Rotation p μ₀)}
    (h : RotationUndoSequence hopt ν rs μ) (m : Fin n)
    (hm : ∀ r ∈ rs, r.val.cycle m = m) : μ m = ν m := by
  induction h with
  | nil => rfl
  | @cons a b r rs ha σ hlabel rest ih =>
    have hcycle : reverseRotationCycle a.symm σ.val m = m :=
      congrArg (fun q : Rotation p μ₀ ↦ q.val.cycle m) hlabel |>.trans
        (hm r List.mem_cons_self)
    have hstep := congrArg (fun M : Matching n ↦ M m)
      (eliminateRotation_undoReverseRotation a σ.val)
    change eliminateRotation (undoReverseRotation a σ.val)
      (reverseRotationCycle a.symm σ.val) m = a m at hstep
    rw [eliminateRotation_apply, hcycle] at hstep
    exact (ih (fun q hq ↦ hm q (List.mem_cons_of_mem _ hq))).trans hstep
private structure PivotDecoration (hopt : IsManOptimal p μ₀) (K : ℕ) (r : Rotation p μ₀) where
  removed : Finset (MaximalEliminatedRotation p μ₀ (singletonRotationAnchor hopt r).val)
  totalLength_le : (∑ s ∈ removed, rotationLength s.val) ≤ K
  pivot_exposed : r.IsExposedAt
    (undoMaximalSubsetEmbedding hopt (singletonRotationAnchor hopt r).property removed).val
namespace PivotDecoration
variable {K : ℕ} {r : Rotation p μ₀}
private theorem ext_removed {D E : PivotDecoration hopt K r} (h : D.removed = E.removed) :
    D = E := by
  cases D
  cases E
  cases h
  rfl
private noncomputable def matching (D : PivotDecoration hopt K r) : {M : Matching n // IsStable p M} :=
  undoMaximalSubsetEmbedding hopt (singletonRotationAnchor hopt r).property D.removed
theorem isExposedAt_matching_iff (D : PivotDecoration hopt K r) (s : Rotation p μ₀) :
    s.IsExposedAt D.matching.val ↔ s = r ∨ s ∈ Subtype.val ''
      (↑D.removed :
        Set (MaximalEliminatedRotation p μ₀ (singletonRotationAnchor hopt r).val)) :=
  isExposedAt_undo_pivot_iff hopt r D.removed D.pivot_exposed s
theorem long_exposed_iff (D : PivotDecoration hopt K r) (hr : K < rotationLength r)
    (s : Rotation p μ₀) :
    (s.IsExposedAt D.matching.val ∧ K < rotationLength s) ↔ s = r := by
  constructor
  · rintro ⟨he, hl⟩
    rcases (D.isExposedAt_matching_iff s).mp he with hs | ⟨t, ht, rfl⟩
    · exact hs
    · have ht' : t ∈ D.removed := ht
      exact (not_lt_of_ge ((Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) ht').trans
        D.totalLength_le) hl).elim
  · rintro rfl
    exact ⟨D.pivot_exposed, hr⟩
end PivotDecoration
private abbrev LongPivot (p : Profile n) (μ₀ : Matching n) (K : ℕ) :=
  {r : Rotation p μ₀ // K < rotationLength r}
private noncomputable def pivotDecorationEmbedding (hopt : IsManOptimal p μ₀) (K : ℕ) :
    (Σ r : LongPivot p μ₀ K, PivotDecoration hopt K r.val) ↪
      {M : Matching n // IsStable p M} :=
  ⟨fun a ↦ a.2.matching, by
    rintro ⟨r, D⟩ ⟨s, E⟩ h
    change D.matching = E.matching at h
    have he : r.val.IsExposedAt E.matching.val := by
      rw [← h]
      exact D.pivot_exposed
    have hrs : r = s := Subtype.ext ((E.long_exposed_iff s.property r.val).mp ⟨he, r.property⟩)
    subst s
    let e := undoMaximalSubsetEmbedding hopt (singletonRotationAnchor hopt r.val).property
    have hsets : (↑D.removed : Set _) = ↑E.removed := e.injective h
    have hDE : D = E := PivotDecoration.ext_removed (Finset.coe_injective hsets)
    cases hDE
    rfl⟩
end CompLP
end

-- PivotReversePermutationDecoration
section
open StableMarriage
open scoped BigOperators
namespace CompLP
variable {n : ℕ} {p : Profile n} {μ₀ μ ν : Matching n}
private theorem RotationSequence.eq_mul_listProd {rs : List (Equiv.Perm (Fin n))}
    (h : RotationSequence p μ rs ν) : ν = μ * rs.prod := by
  induction h with
  | nil => simp
  | cons _ _ _ ih =>
    rw [List.prod_cons, ← mul_assoc]
    simpa only [eliminateRotation, Equiv.Perm.mul_def] using ih
theorem reverseExposedRotationLabel_length (hopt : IsManOptimal p μ₀) (hμ : IsStable p μ)
    (σ : {σ : Equiv.Perm (Fin n) // IsReverseExposedRotation p μ σ}) :
    rotationLength (reverseExposedRotationLabel hopt hμ σ) = σ.val.support.card := by
  change (μ⁻¹ * σ.val * (μ⁻¹)⁻¹).support.card = _
  exact Equiv.Perm.card_support_conj
private def reverseFactorEmbedding {σ : Matching n}
    (hσ : RealizesSuccessorPermutation (swapProfile p) μ.symm σ) :
    (↥σ.cycleFactorsFinset) ↪ {τ : Equiv.Perm (Fin n) // IsReverseExposedRotation p μ τ} :=
  ⟨fun τ ↦ ⟨τ.val, realizesSuccessorPermutation_iff_factors.mp hσ τ.val τ.property⟩,
    fun _ _ h ↦ Subtype.ext (congrArg
      (fun t : {τ : Equiv.Perm (Fin n) // IsReverseExposedRotation p μ τ} ↦ t.val) h)⟩
private noncomputable def realizedReverseRemovedLabels (hopt : IsManOptimal p μ₀) (hμ : IsStable p μ)
    {σ : Matching n} (hσ : RealizesSuccessorPermutation (swapProfile p) μ.symm σ) :
    Finset (MaximalEliminatedRotation p μ₀ μ) :=
  σ.cycleFactorsFinset.attach.map
    ((reverseFactorEmbedding hσ).trans (reverseExposedRotationEquivMaximal hopt hμ).toEmbedding)
theorem realizedReverseRemovedLabels_totalLength (hopt : IsManOptimal p μ₀)
    (hμ : IsStable p μ) {σ : Matching n}
    (hσ : RealizesSuccessorPermutation (swapProfile p) μ.symm σ) :
    (∑ t ∈ realizedReverseRemovedLabels hopt hμ hσ, rotationLength t.val) =
      σ.support.card := by
  rw [realizedReverseRemovedLabels, Finset.sum_map, card_support_eq_sum_cycleFactors_support]
  calc
    _ = ∑ t ∈ σ.cycleFactorsFinset.attach, t.val.support.card :=
      Finset.sum_congr rfl fun t _ ↦ reverseExposedRotationLabel_length hopt hμ
        (reverseFactorEmbedding hσ t)
    _ = _ := Finset.sum_attach σ.cycleFactorsFinset
      (fun t : Equiv.Perm (Fin n) ↦ t.support.card)
theorem realizedReverseRemovedLabels_short_card (hopt : IsManOptimal p μ₀) (hμ : IsStable p μ)
    {σ : Matching n} (hσ : RealizesSuccessorPermutation (swapProfile p) μ.symm σ) (L : ℕ) :
    ((realizedReverseRemovedLabels hopt hμ hσ).filter
      (fun r ↦ rotationLength r.val ≤ L)).card = (σ.cycleType.filter (· ≤ L)).card := by
  rw [realizedReverseRemovedLabels, Finset.filter_map, Finset.card_map]
  have hlen (t : σ.cycleFactorsFinset) :
      rotationLength (((reverseFactorEmbedding hσ).trans
        (reverseExposedRotationEquivMaximal hopt hμ).toEmbedding) t).val = t.val.support.card :=
    reverseExposedRotationLabel_length hopt hμ (reverseFactorEmbedding hσ t)
  simp only [Function.comp_def, hlen, Equiv.Perm.cycleType_def, Multiset.filter_map, Multiset.card_map]
  rw [Finset.filter_attach (fun t : Matching n ↦ t.support.card ≤ L), Finset.card_map,
    Finset.card_attach]
  rfl
theorem undoMaximalSubsetEmbedding_realizedReverseRemovedLabels (hopt : IsManOptimal p μ₀)
    (hμ : IsStable p μ) {σ : Matching n}
    (hσ : RealizesSuccessorPermutation (swapProfile p) μ.symm σ) :
    (undoMaximalSubsetEmbedding hopt hμ (realizedReverseRemovedLabels hopt hμ hσ)).val =
      undoReverseRotation μ σ := by
  classical
  let S := σ.cycleFactorsFinset
  let f := reverseFactorEmbedding hσ
  let rs := S.attach.toList.map f
  have hnd : rs.Nodup := S.attach.nodup_toList.map f.injective
  have hset : (rs.map Subtype.val).toFinset = S := by
    ext τ
    simp only [List.mem_toFinset, List.mem_map, rs, Finset.mem_toList]
    constructor
    · rintro ⟨_, ⟨t, _, rfl⟩, rfl⟩
      exact t.property
    · intro ht
      exact ⟨f ⟨τ, ht⟩, ⟨⟨τ, ht⟩, Finset.mem_attach S _, rfl⟩, rfl⟩
  have hprod : (rs.map Subtype.val).prod = σ := by
    let L := rs.map Subtype.val
    have hc : (↑L.toFinset : Set (Matching n)).Pairwise (Function.onFun Commute id) := by
      rw [show L.toFinset = S from hset]
      exact σ.cycleFactorsFinset_mem_commute
    calc
      _ = L.toFinset.noncommProd id hc := by
        simpa only [List.map_id] using
          (Finset.noncommProd_toFinset L id hc (hnd.map Subtype.val_injective)).symm
      _ = S.noncommProd id σ.cycleFactorsFinset_mem_commute :=
        Finset.noncommProd_congr hset (fun _ _ ↦ rfl) hc
      _ = σ := σ.cycleFactorsFinset_noncommProd
  obtain ⟨M, hseq, hpath⟩ := exists_rotationUndoSequence_of_reverse_cycles hopt hμ rs hnd
  have hM : M = undoReverseRotation μ σ := by
    have he := hseq.eq_mul_listProd
    rw [hprod] at he
    change M.symm = eliminateRotation μ.symm σ at he
    exact congrArg Equiv.symm he
  let D := realizedReverseRemovedLabels hopt hμ hσ
  let N := undoMaximalSubsetEmbedding hopt hμ D
  let e := f.trans (reverseExposedRotationEquivMaximal hopt hμ).toEmbedding
  have hD : D = S.attach.map e := rfl
  have hlabels : {q | q ∈ rs.map (reverseExposedRotationLabel hopt hμ)} =
      Subtype.val '' (D : Set (MaximalEliminatedRotation p μ₀ μ)) := by
    ext q
    constructor
    · intro hq
      obtain ⟨t, ht, he⟩ := List.mem_map.mp hq
      obtain ⟨s, _, rfl⟩ := List.mem_map.mp ht
      refine ⟨e s, ?_, he⟩
      change e s ∈ D
      rw [hD]
      exact Finset.mem_map.mpr ⟨s, Finset.mem_attach S _, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      change t ∈ D at ht
      rw [hD] at ht
      obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp ht
      exact List.mem_map.mpr ⟨f s, List.mem_map.mpr ⟨s, Finset.mem_toList.mpr hs, rfl⟩, rfl⟩
  have hMI : eliminatedRotations p μ₀ M = eliminatedRotations p μ₀ N.val := by
    rw [hpath.eliminatedRotations_end, hlabels, eliminatedRotations_undoMaximalSubsetEmbedding]
  have hMN : M = N.val :=
    congrArg Subtype.val ((stableMatchingToRotationIdeal_bijective hopt).1
      (LowerSet.ext hMI : stableMatchingToRotationIdeal ⟨M, hpath.isStable_end⟩ =
        stableMatchingToRotationIdeal N))
  exact hMN.symm.trans hM
private abbrev IsCompatibleReversePermutation (hopt : IsManOptimal p μ₀) (K : ℕ)
    (r : Rotation p μ₀) (σ : Matching n) : Prop :=
  let A := singletonRotationAnchor hopt r
  RealizesSuccessorPermutation (swapProfile p) A.val.symm σ ∧
    σ.support.card ≤ K ∧
    (∀ m ∈ r.val.cycle.support, A.val m ∉ σ.support) ∧
    IsExposedRotation p (undoReverseRotation A.val σ) r.val.cycle
private abbrev CompatibleReversePermutation (hopt : IsManOptimal p μ₀) (K : ℕ)
    (r : Rotation p μ₀) :=
  {σ : Matching n // IsCompatibleReversePermutation hopt K r σ}
private noncomputable def compatibleReversePermutationToDecoration (hopt : IsManOptimal p μ₀)
    (K : ℕ) (r : Rotation p μ₀) (σ : CompatibleReversePermutation hopt K r) :
    PivotDecoration hopt K r := by
  let A := singletonRotationAnchor hopt r
  let D := realizedReverseRemovedLabels hopt A.property σ.property.1
  have hN : (undoMaximalSubsetEmbedding hopt A.property D).val =
      undoReverseRotation A.val σ.val :=
    undoMaximalSubsetEmbedding_realizedReverseRemovedLabels hopt A.property σ.property.1
  have hfix (m : Fin n) (hm : r.val.cycle m ≠ m) :
      undoReverseRotation A.val σ.val m = A.val m := by
    have hsm : σ.val (A.val m) = A.val m := by
      by_contra hn
      exact σ.property.2.2.1 m (Equiv.Perm.mem_support.mpr hm) (Equiv.Perm.mem_support.mpr hn)
    apply (undoReverseRotation A.val σ.val).symm.injective
    rw [Equiv.symm_apply_apply]
    change m = A.val.symm (σ.val (A.val m))
    rw [hsm, Equiv.symm_apply_apply]
  have hpivot := ((eq_singletonRotationAnchor_iff hopt r A).mp rfl r).mpr rfl
  refine ⟨D, (realizedReverseRemovedLabels_totalLength hopt A.property σ.property.1).le.trans
    σ.property.2.1, ?_⟩
  change r.IsExposedAt (undoMaximalSubsetEmbedding hopt A.property D).val
  rw [hN]
  exact ⟨σ.property.2.2.2, (rotationLabel_eq_of_fixed_on_cycle hfix).trans hpivot.2⟩
theorem compatibleReversePermutationToDecoration_removed (hopt : IsManOptimal p μ₀)
    (K : ℕ) (r : Rotation p μ₀) (σ : CompatibleReversePermutation hopt K r) :
    (compatibleReversePermutationToDecoration hopt K r σ).removed =
      realizedReverseRemovedLabels hopt (singletonRotationAnchor hopt r).property σ.property.1 :=
  rfl
theorem compatibleReversePermutationToDecoration_matching (hopt : IsManOptimal p μ₀)
    (K : ℕ) (r : Rotation p μ₀) (σ : CompatibleReversePermutation hopt K r) :
    (compatibleReversePermutationToDecoration hopt K r σ).matching.val =
      undoReverseRotation (singletonRotationAnchor hopt r).val σ.val :=
  undoMaximalSubsetEmbedding_realizedReverseRemovedLabels hopt
    (singletonRotationAnchor hopt r).property σ.property.1
private noncomputable def compatibleReversePermutationEmbedding (hopt : IsManOptimal p μ₀)
    (K : ℕ) (r : Rotation p μ₀) :
    CompatibleReversePermutation hopt K r ↪ PivotDecoration hopt K r :=
  ⟨compatibleReversePermutationToDecoration hopt K r, by
    intro σ τ h
    have he := congrArg (fun D : PivotDecoration hopt K r ↦ D.matching.val) h
    change (compatibleReversePermutationToDecoration hopt K r σ).matching.val =
      (compatibleReversePermutationToDecoration hopt K r τ).matching.val at he
    rw [compatibleReversePermutationToDecoration_matching,
      compatibleReversePermutationToDecoration_matching] at he
    apply Subtype.ext
    apply Equiv.ext
    intro w
    exact (singletonRotationAnchor hopt r).val.symm.injective
      (congrArg (fun ν : Matching n ↦ ν.symm w) he)⟩
end CompLP
end

-- PivotCompatibleLowerMoment
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace CompLP
private def memFinset {α : Type} {S : Finset α} {Q : α → Prop} (_ : ∀ {σ}, σ ∈ S ↔ Q σ) := S
private noncomputable def compatibleReversePermutations {n : ℕ} (S : Finset (Matching n))
    (p : Profile n) (μ ρ : Matching n) : Finset (Matching n) :=
  memFinset (@MarkedLP.mem_compatibleReversePermutations n S p μ ρ)
private def premise {A B : Prop} (_ : A → B) := A
private abbrev SourceSuccessor {n} (p : Profile n) (μ : Matching n) (m w : Fin n) : Prop :=
  premise (@MarkedLP.IsSuccessor.unique n p μ m w w)
private lemma sourceSuccessor_iff {n} (p : Profile n) (μ : Matching n) (m w : Fin n) :
    SourceSuccessor p μ m w ↔ IsSuccessor p μ m w := by
  constructor
  · rintro ⟨he,hm⟩
    exact (IsSuccessor.mk (he) (hm))
  · rintro ⟨he,hm⟩
    constructor <;> assumption
private abbrev SourceExposed {n} (p : Profile n) (μ ρ : Matching n) : Prop :=
  premise (@MarkedLP.IsExposedRotation.womanRank_eliminate_le n p μ ρ)
private lemma sourceExposed_iff {n} (p : Profile n) (μ ρ : Matching n) :
    SourceExposed p μ ρ ↔ IsExposedRotation p μ ρ := by
  constructor
  · rintro ⟨hc,hs⟩
    exact (IsExposedRotation.mk (hc) (fun m hm => (sourceSuccessor_iff ..).mp (hs m hm)))
  · rintro ⟨hc,hs⟩
    constructor
    · exact hc
    · exact fun m hm => (sourceSuccessor_iff ..).mpr (hs m hm)
theorem mem_compatibleReversePermutations {n : ℕ} {S : Finset (Matching n)}
    {p : Profile n} {μ ρ σ : Matching n} : σ ∈ compatibleReversePermutations S p μ ρ ↔
    σ ∈ S ∧ RealizesSuccessorPermutation (swapProfile p) μ.symm σ ∧
      IsExposedRotation p (undoReverseRotation μ σ) ρ := by
  apply (MarkedLP.mem_compatibleReversePermutations (S:=S) (p:=p) (μ:=μ) (ρ:=ρ) (σ:=σ)).trans
  apply and_congr_right
  intro _
  refine and_congr ?_ (sourceExposed_iff ..)
  exact forall_congr' fun i => forall_congr' fun _ => sourceSuccessor_iff ..
private noncomputable def compatibleReverseSupportFamily {n : ℕ} (μ ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (k : ℕ) (p : Profile n) : Finset (Matching n) :=
  compatibleReversePermutations
    (goodReverseSupportPermutations k (ρ.support.map μ.toEmbedding)
      (forwardMaskForbiddenTargets μ flag)) p μ ρ
end CompLP
end

-- PivotReverseIncrementFilter
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace CompLP
private def reverseScoreIncrement {n : ℕ} (x : ScoreProfile n) (μ : Matching n)
    (w j : Fin n) : ℝ := x (.inr w) j - x (.inr w) (μ.symm w)
theorem measurable_reverseScoreIncrement {n : ℕ} (μ : Matching n) (w j : Fin n) :
    Measurable (fun x : ScoreProfile n ↦ reverseScoreIncrement x μ w j) := by
  have hrow : Measurable (fun x : ScoreProfile n ↦ x (.inr w)) := measurable_pi_apply _
  exact ((measurable_pi_apply j).comp hrow).sub ((measurable_pi_apply (μ.symm w)).comp hrow)
private noncomputable def reverseIncrementCutoff (n : ℕ) (X : ℝ) : ℝ := 16 * Real.log (n : ℝ) / X
end CompLP
end

-- PivotReverseFilteredCount
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace CompLP
private def shortCycleCapBad (L : ℕ) (T : Multiset ℕ) : Prop :=
  (3 / 2 : ℝ) * Real.log (L : ℝ) < ((T.filter (· ≤ L)).card : ℝ)
private def reverseCollectionIncrementGood {n : ℕ} (x : ScoreProfile n) (μ σ : Matching n)
    (t : ℝ) : Prop :=
  ∀ w ∈ σ.support, reverseScoreIncrement x μ w (μ.symm (σ w)) ≤ t
private noncomputable def filteredReverseSupportFamily {n : ℕ} (μ ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (k L : ℕ) (t : ℝ) (x : ScoreProfile n) :
    Finset (Matching n) := by
  classical
  exact (compatibleReverseSupportFamily μ ρ flag k (profileOfScores x)).filter fun σ ↦
    (¬ shortCycleCapBad L σ.cycleType) ∧ reverseCollectionIncrementGood x μ σ t
theorem measurable_finsetCard_of_mem {Ω α : Type*} [MeasurableSpace Ω] [Fintype α]
    (F : Ω → Finset α) (hF : ∀ a, MeasurableSet {z | a ∈ F z}) :
    Measurable (fun z ↦ ((F z).card : ℝ≥0∞)) := by
  classical
  let G (a : α) := ({z | a ∈ F z} : Set Ω).indicator (fun _ ↦ (1 : ℝ≥0∞))
  have hG (a : α) : Measurable (G a) := measurable_const.indicator (hF a)
  have he : (fun z ↦ ((F z).card : ℝ≥0∞)) = fun z ↦ ∑ a, G a z := by
    funext z
    have hs : Finset.univ.filter (fun a ↦ a ∈ F z) = F z := by ext a; simp
    simp only [G, indicator_apply, mem_ofPred_eq, ← Finset.sum_filter, hs]
    simp
  rw [he]
  exact Finset.measurable_sum _ fun a _ ↦ hG a
end CompLP
end

-- ShortCycleChebyshev
section
open scoped BigOperators ENNReal
namespace CompLP
end CompLP
end

-- UniformShortCycleMoments
section
open Equiv Equiv.Perm
open scoped BigOperators
namespace CompLP
variable {α : Type*} [Fintype α] [DecidableEq α]
end CompLP
end

-- PivotScoreLock
section
open StableMarriage
namespace CompLP
variable {n : ℕ} {p : Profile n} {μ₀ μ ν : Matching n} {r : Rotation p μ₀}
theorem RotationSequence.womanRank_end_le {rs : List (Equiv.Perm (Fin n))}
    (hpath : RotationSequence p μ rs ν) (j : Fin n) :
    p.womanRank j (ν.symm j) ≤ p.womanRank j (μ.symm j) := by
  induction hpath with
  | nil => exact le_rfl
  | cons _ hρ _ ih => exact ih.trans (hρ.womanRank_eliminate_le j)
theorem femaleSpouseTotal_le_of_eliminatedRotations_subset {x : ScoreProfile n}
    {μ₀ μ ν : Matching n} (ht : ∀ row, Function.Injective (x row))
    (hopt : IsManOptimal (profileOfScores x) μ₀)
    (hμ : IsStable (profileOfScores x) μ) (hν : IsStable (profileOfScores x) ν)
    (hsub : eliminatedRotations (profileOfScores x) μ₀ μ ⊆
      eliminatedRotations (profileOfScores x) μ₀ ν) :
    femaleSpouseTotal x ν ≤ femaleSpouseTotal x μ := by
  obtain ⟨_, hpath⟩ := exists_rotationSequence_of_menWeaklyPrefer hμ hν
    ((eliminatedRotations_subset_iff hopt hμ hν).mp hsub)
  refine Finset.sum_le_sum fun j _ ↦ le_of_not_gt fun hgt ↦ ?_
  exact (not_lt_of_ge (hpath.womanRank_end_le j))
    ((rankPermutation_lt_iff (ht (.inr j)) (μ.symm j) (ν.symm j)).mpr hgt)
end CompLP
end

-- PivotForwardExposureReveal
section
open MeasureTheory Set StableMarriage
namespace CompLP
private theorem forwardEligible_iff_flag {n : ℕ} (μ : Matching n) (x : ScoreProfile n)
    (flag : OffDiagonalCellIndex n → Bool) (ht : ∀ r, Function.Injective (x r))
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    (i j : Fin n) (hij : i ≠ j) :
    IsEligibleSuccessor (profileOfScores x) μ i (μ j) ↔ flag ⟨(i, j), hij⟩ = true := by
  let q : OffDiagonalCellIndex n := ⟨(i, j), hij⟩
  let d := (splitScorePairs μ x).1
  let z := (splitScorePairs μ x).2
  have he : IsEligibleSuccessor (profileOfScores x) μ i (μ j) ↔
      z q ∈ forwardEligibleScoreCell (diagonalPairAt d i).1 (diagonalPairAt d j).2 := by
    dsimp only [z, d]
    rw [splitScorePairs_offDiagonal_apply, diagonalPairAt_splitScorePairs,
      diagonalPairAt_splitScorePairs]
    simp only [IsEligibleSuccessor, forwardEligibleScoreCell, mem_prod, mem_Ioi, mem_Iio,
      Equiv.symm_apply_apply, profileOfScores, rankPermutation_lt_iff (ht (.inl i)),
      rankPermutation_lt_iff (ht (.inr (μ j))), q]
  have hh : z q ∈ forwardScoreCellFlagEvent (diagonalPairAt d i).1 (diagonalPairAt d j).2
      (flag q) := mem_pi.mp hmask q (mem_univ _)
  change _ ↔ flag q = true
  rw [he]
  by_cases hq : flag q = true
  · simp only [hq, forwardScoreCellFlagEvent] at hh
    simp only [hq, iff_true]
    exact hh
  · simp only [forwardScoreCellFlagEvent, if_neg hq, mem_compl_iff] at hh
    exact ⟨fun h ↦ (hh h).elim, fun h ↦ (hq h).elim⟩
private def forwardRevealExposureEvent {n : ℕ} (ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) : Set (ForwardRevealedMaleScores flag) :=
  {v | ρ.IsCycle ∧ ∀ m, ρ m ≠ m →
    ∃ q : ForwardActiveCellIndex flag, q.val.val = (m, ρ m) ∧
      ∀ t : ForwardActiveCellIndex flag, t.val.val.1 = m → v q ≤ v t}
theorem isExposedRotation_iff_forwardRevealExposureEvent {n : ℕ} (μ ρ : Matching n)
    (x : ScoreProfile n) (flag : OffDiagonalCellIndex n → Bool)
    (ht : ∀ r, Function.Injective (x r))
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag) :
    IsExposedRotation (profileOfScores x) μ ρ ↔
      (forwardRevealWithColumns flag (splitScorePairs μ x).2).1 ∈
        forwardRevealExposureEvent ρ flag := by
  let v := (forwardRevealWithColumns flag (splitScorePairs μ x).2).1
  let p := profileOfScores x
  have hscore (q : ForwardActiveCellIndex flag) :
      v q = x (.inl q.val.val.1) (μ q.val.val.2) :=
    congrArg Prod.fst (splitScorePairs_offDiagonal_apply μ x q.val)
  have hle (m j k : Fin n) :
      p.manRank m (μ j) ≤ p.manRank m (μ k) ↔ x (.inl m) (μ j) ≤ x (.inl m) (μ k) := by
    rw [← not_lt, ← not_lt]
    exact not_congr (rankPermutation_lt_iff (ht (.inl m)) _ _)
  constructor
  · intro h
    refine ⟨(IsExposedRotation.isCycle h), fun m hm ↦ ?_⟩
    let q₀ : OffDiagonalCellIndex n := ⟨(m, ρ m), hm.symm⟩
    let q : ForwardActiveCellIndex flag := ⟨q₀,
      (forwardEligible_iff_flag μ x flag ht hmask m (ρ m) hm.symm).mp (IsSuccessor.eligible ((IsExposedRotation.successor h) m hm))⟩
    refine ⟨q, rfl, fun t htm ↦ ?_⟩
    have htne : m ≠ t.val.val.2 := htm.symm ▸ t.val.property
    have hteq : (⟨(m, t.val.val.2), htne⟩ : OffDiagonalCellIndex n) = t.val :=
      Subtype.ext (Prod.ext htm.symm rfl)
    have hflag : flag ⟨(m, t.val.val.2), htne⟩ = true := by rw [hteq]; exact t.property
    have htel := (forwardEligible_iff_flag μ x flag ht hmask m t.val.val.2 htne).mpr hflag
    change v q ≤ v t
    rw [hscore q, hscore t, htm]
    exact (hle m (ρ m) t.val.val.2).mp ((IsSuccessor.min_rank ((IsExposedRotation.successor h) m hm)) _ htel)
  · rintro ⟨hcyc, htest⟩
    refine (IsExposedRotation.mk (hcyc) (fun m hm ↦ ?_))
    obtain ⟨q, hq, hmin⟩ := htest m hm
    have hq' : (⟨(m, ρ m), hm.symm⟩ : OffDiagonalCellIndex n) = q.val := Subtype.ext hq.symm
    refine (IsSuccessor.mk ((forwardEligible_iff_flag μ x flag ht hmask m (ρ m) hm.symm).mpr
      (hq' ▸ q.property)) (?_))
    intro w hwel
    let j := μ.symm w
    have hjw : μ j = w := μ.apply_symm_apply w
    have hj : m ≠ j := fun h ↦ (lt_irrefl _ (by simpa only [← hjw, ← h] using hwel.1))
    let t : ForwardActiveCellIndex flag := ⟨⟨(m, j), hj⟩,
      (forwardEligible_iff_flag μ x flag ht hmask m j hj).mp (hjw.symm ▸ hwel)⟩
    have h := hmin t rfl
    change v q ≤ v t at h
    rw [hscore q, hscore t, hq] at h
    exact hjw ▸ (hle m (ρ m) j).mpr h
theorem measurableSet_forwardRevealExposureEvent {n : ℕ} (ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) : MeasurableSet (forwardRevealExposureEvent ρ flag) := by
  unfold forwardRevealExposureEvent
  simp only [ofPred_and, ofPred_forall, ofPred_exists]
  refine (MeasurableSet.const _).inter (MeasurableSet.iInter fun (m : Fin n) ↦
    MeasurableSet.iInter fun (_ : ρ m ≠ m) ↦ MeasurableSet.iUnion
      fun (q : ForwardActiveCellIndex flag) ↦ (MeasurableSet.const _).inter
        (MeasurableSet.iInter fun (t : ForwardActiveCellIndex flag) ↦
          MeasurableSet.iInter fun (_ : t.val.val.1 = m) ↦ ?_))
  exact measurableSet_le (measurable_pi_apply q) (measurable_pi_apply t)
end CompLP
end

-- PivotPairToggle
section
open StableMarriage
open scoped BigOperators
namespace CompLP
variable {n : ℕ} {p : Profile n} {μ₀ : Matching n} {hopt : IsManOptimal p μ₀}
  {K : ℕ} {r : Rotation p μ₀}
namespace PivotDecoration
private def removedLabels (D : PivotDecoration hopt K r) : Set (Rotation p μ₀) :=
  Subtype.val '' (↑D.removed :
    Set (MaximalEliminatedRotation p μ₀ (singletonRotationAnchor hopt r).val))
theorem matching_eliminated (D : PivotDecoration hopt K r) :
    eliminatedRotations p μ₀ D.matching.val =
      eliminatedRotations p μ₀ (singletonRotationAnchor hopt r).val \ D.removedLabels :=
  eliminatedRotations_undoMaximalSubsetEmbedding hopt
    (singletonRotationAnchor hopt r).property D.removed
private noncomputable def eraseRemovedLabel (D : PivotDecoration hopt K r) (γ : Rotation p μ₀) :
    PivotDecoration hopt K r := by
  classical
  let E := D.removed.filter (fun s ↦ s.val ≠ γ)
  have hE : E ⊆ D.removed := Finset.filter_subset _ _
  refine ⟨E, ?_, ?_⟩
  · exact (Finset.sum_le_sum_of_subset_of_nonneg hE
      (fun _ _ _ ↦ Nat.zero_le _)).trans D.totalLength_le
  · apply (pivot_isExposedAt_undo_iff hopt r E).mpr
    rintro _ ⟨s, hs, rfl⟩
    exact (pivot_isExposedAt_undo_iff hopt r D.removed).mp D.pivot_exposed _
      ⟨s, hE hs, rfl⟩
@[simp] theorem mem_eraseRemovedLabel (D : PivotDecoration hopt K r) (γ : Rotation p μ₀)
    (s : MaximalEliminatedRotation p μ₀ (singletonRotationAnchor hopt r).val) :
    s ∈ (D.eraseRemovedLabel γ).removed ↔ s ∈ D.removed ∧ s.val ≠ γ := by
  classical
  exact Finset.mem_filter
theorem eraseRemovedLabel_subset (D : PivotDecoration hopt K r) (γ : Rotation p μ₀) :
    (D.eraseRemovedLabel γ).removed ⊆ D.removed :=
  fun s hs ↦ ((mem_eraseRemovedLabel D γ s).mp hs).1
theorem notMem_removedLabels_eraseRemovedLabel (D : PivotDecoration hopt K r)
    (γ : Rotation p μ₀) : γ ∉ (D.eraseRemovedLabel γ).removedLabels := by
  rintro ⟨s, hs, hsg⟩
  exact ((mem_eraseRemovedLabel D γ s).mp hs).2 hsg
private theorem mem_removedLabels_iff (D : PivotDecoration hopt K r)
    (s : MaximalEliminatedRotation p μ₀ (singletonRotationAnchor hopt r).val) :
    s.val ∈ D.removedLabels ↔ s ∈ D.removed := by
  constructor
  · rintro ⟨t, ht, hts⟩
    exact Subtype.ext hts ▸ ht
  · intro hs
    exact ⟨s, hs, rfl⟩
theorem eq_of_eraseRemovedLabel_eq {D E : PivotDecoration hopt K r} (γ : Rotation p μ₀)
    (h : D.eraseRemovedLabel γ = E.eraseRemovedLabel γ)
    (hbit : γ ∈ D.removedLabels ↔ γ ∈ E.removedLabels) : D = E := by
  have hsets : D.removed = E.removed := by
    ext s
    by_cases hs : s.val = γ
    · rw [← mem_removedLabels_iff, ← mem_removedLabels_iff, hs]
      exact hbit
    · have he : s ∈ (D.eraseRemovedLabel γ).removed ↔
          s ∈ (E.eraseRemovedLabel γ).removed := by rw [h]
      simpa only [mem_eraseRemovedLabel, and_iff_left hs] using he
  cases D
  cases E
  cases hsets
  rfl
end PivotDecoration
private abbrev PivotCode (hopt : IsManOptimal p μ₀) (K : ℕ) :=
  Σ r : LongPivot p μ₀ K, PivotDecoration hopt K r.val
private structure ResidualPivotPair (hopt : IsManOptimal p μ₀) (K : ℕ) where
  early : PivotCode hopt K
  late : PivotCode hopt K
  pivot_lt : early.1.val < late.1.val
  shared : ∃ γ ∈ late.2.removedLabels,
    γ ∈ eliminatedRotations p μ₀ (singletonRotationAnchor hopt early.1.val).val
private abbrev IncomparableStableMatchingPair (p : Profile n) (μ₀ : Matching n) :=
  {MN : {M : Matching n // IsStable p M} × {N : Matching n // IsStable p N} //
    (¬ eliminatedRotations p μ₀ MN.1.val ⊆ eliminatedRotations p μ₀ MN.2.val) ∧
    (¬ eliminatedRotations p μ₀ MN.2.val ⊆ eliminatedRotations p μ₀ MN.1.val)}
namespace ResidualPivotPair
private noncomputable def sharedLabel (R : ResidualPivotPair hopt K) : Rotation p μ₀ :=
  Classical.choose R.shared
theorem sharedLabel_mem_late (R : ResidualPivotPair hopt K) :
    R.sharedLabel ∈ R.late.2.removedLabels :=
  (Classical.choose_spec R.shared).1
theorem sharedLabel_mem_early_anchor (R : ResidualPivotPair hopt K) :
    R.sharedLabel ∈
      eliminatedRotations p μ₀ (singletonRotationAnchor hopt R.early.1.val).val :=
  (Classical.choose_spec R.shared).2
private noncomputable def toggledEarly (R : ResidualPivotPair hopt K) : PivotCode hopt K :=
  ⟨R.early.1, R.early.2.eraseRemovedLabel R.sharedLabel⟩
private noncomputable def toggleImage (R : ResidualPivotPair hopt K) :
    IncomparableStableMatchingPair p μ₀ := by
  refine ⟨(R.toggledEarly.2.matching, R.late.2.matching), ?_, ?_⟩
  · intro h
    have he : R.sharedLabel ∈ eliminatedRotations p μ₀ R.toggledEarly.2.matching.val := by
      rw [PivotDecoration.matching_eliminated]
      exact ⟨R.sharedLabel_mem_early_anchor,
        R.early.2.notMem_removedLabels_eraseRemovedLabel R.sharedLabel⟩
    have hl := h he
    rw [PivotDecoration.matching_eliminated] at hl
    exact hl.2 R.sharedLabel_mem_late
  · intro h
    have hl : R.early.1.val ∈ eliminatedRotations p μ₀ R.late.2.matching.val :=
      (Rotation.lt_iff_before_exposure hopt R.pivot_lt.ne).mp R.pivot_lt
        _ R.late.2.matching.property R.late.2.pivot_exposed.1 R.late.2.pivot_exposed.2
    have he := h hl
    rw [PivotDecoration.matching_eliminated, eliminatedRotations_singletonRotationAnchor] at he
    apply he.1
    change R.toggledEarly.1.val ≤ R.early.1.val
    exact le_rfl
theorem early_anchor_ideal_subset_late_anchor (R : ResidualPivotPair hopt K) :
    eliminatedRotations p μ₀ (singletonRotationAnchor hopt R.early.1.val).val ⊆
      eliminatedRotations p μ₀ (singletonRotationAnchor hopt R.late.1.val).val := by
  rw [eliminatedRotations_singletonRotationAnchor,
    eliminatedRotations_singletonRotationAnchor]
  exact fun _ hs hls ↦ hs (R.pivot_lt.le.trans hls)
theorem toggle_early_ideal_diff_late (R : ResidualPivotPair hopt K) :
    eliminatedRotations p μ₀ R.toggledEarly.2.matching.val \
        eliminatedRotations p μ₀ R.late.2.matching.val =
      (R.late.2.removedLabels ∩
        eliminatedRotations p μ₀ (singletonRotationAnchor hopt R.early.1.val).val) \
          R.toggledEarly.2.removedLabels := by
  rw [PivotDecoration.matching_eliminated, PivotDecoration.matching_eliminated]
  ext s
  simp only [Set.mem_sdiff, Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨ha, he⟩, hn⟩
    refine ⟨⟨?_, ha⟩, he⟩
    by_contra h
    exact hn ⟨R.early_anchor_ideal_subset_late_anchor ha, h⟩
  · rintro ⟨⟨hl, ha⟩, he⟩
    exact ⟨⟨ha, he⟩, fun h ↦ h.2 hl⟩
theorem isExposedAt_late_of_mem_toggle_early_ideal_diff_late (R : ResidualPivotPair hopt K)
    {s : Rotation p μ₀} (hs : s ∈ eliminatedRotations p μ₀ R.toggledEarly.2.matching.val \
      eliminatedRotations p μ₀ R.late.2.matching.val) :
    s.IsExposedAt R.late.2.matching.val := by
  rw [R.toggle_early_ideal_diff_late] at hs
  exact (R.late.2.isExposedAt_matching_iff s).mpr (Or.inr hs.1.1)
private noncomputable def shortOrientationLabels (R : ResidualPivotPair hopt K) :
    Finset (Rotation p μ₀) := by
  classical
  exact (R.late.2.removed.filter fun s ↦
    s.val ∈ eliminatedRotations p μ₀ (singletonRotationAnchor hopt R.early.1.val).val ∧
    s.val ∉ R.toggledEarly.2.removedLabels).map ⟨Subtype.val, Subtype.val_injective⟩
theorem coe_shortOrientationLabels (R : ResidualPivotPair hopt K) :
    (↑R.shortOrientationLabels : Set (Rotation p μ₀)) =
      eliminatedRotations p μ₀ R.toggledEarly.2.matching.val \
        eliminatedRotations p μ₀ R.late.2.matching.val := by
  classical
  rw [R.toggle_early_ideal_diff_late]
  ext s
  simp only [shortOrientationLabels, Finset.mem_coe, Finset.mem_map, Finset.mem_filter,
    Function.Embedding.coeFn_mk, Set.mem_sdiff, Set.mem_inter_iff]
  constructor
  · rintro ⟨t, ⟨ht, ha, he⟩, rfl⟩
    exact ⟨⟨⟨t, ht, rfl⟩, ha⟩, he⟩
  · rintro ⟨⟨⟨t, ht, rfl⟩, ha⟩, he⟩
    exact ⟨t, ⟨ht, ha, he⟩, rfl⟩
theorem sum_rotationLength_shortOrientationLabels_le (R : ResidualPivotPair hopt K) :
    (∑ s ∈ R.shortOrientationLabels, rotationLength s) ≤ K := by
  classical
  rw [shortOrientationLabels, Finset.sum_map]
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ ↦ Nat.zero_le _)).trans R.late.2.totalLength_le
private noncomputable def shortOrientationMen (R : ResidualPivotPair hopt K) : Finset (Fin n) :=
  Finset.univ.filter fun m ↦
    p.manRank m (R.late.2.matching.val m) < p.manRank m (R.toggledEarly.2.matching.val m)
private noncomputable def longOrientationMen (R : ResidualPivotPair hopt K) : Finset (Fin n) :=
  Finset.univ.filter fun m ↦
    p.manRank m (R.toggledEarly.2.matching.val m) < p.manRank m (R.late.2.matching.val m)
private theorem exists_diff_label_moving_of_rank_lt {A B : Matching n}
    (hopt : IsManOptimal p μ₀) (hA : IsStable p A) (hB : IsStable p B)
    (hAB : MenWeaklyPrefer p A B) {m : Fin n}
    (hm : p.manRank m (A m) < p.manRank m (B m)) :
    ∃ s : Rotation p μ₀,
      s ∈ eliminatedRotations p μ₀ B \ eliminatedRotations p μ₀ A ∧
        s.val.cycle m ≠ m ∧ rotationLabelNewPartner s.val m = some (B m) := by
  obtain ⟨us, hfirst⟩ := exists_rotationSequence_of_manOptimal hopt hA
  obtain ⟨vs, hnext⟩ := exists_rotationSequence_of_menWeaklyPrefer hA hB hAB
  rcases hnext.partner_eq_or_label_newPartner m with he | ⟨l, hl, hmove, hnew⟩
  · exact (hm.ne (congrArg (p.manRank m) he)).elim
  · have hall := hfirst.append hnext
    have hlall : l ∈ rotationLabels μ₀ (us ++ vs) := by
      rw [hfirst.rotationLabels_append]
      exact List.mem_append_right _ hl
    let s : Rotation p μ₀ := ⟨l, B, us ++ vs, hall, hlall⟩
    refine ⟨s, ⟨hall.mem_eliminatedRotations_iff.mpr hlall, ?_⟩, hmove, hnew⟩
    intro hmem
    exact hm.not_ge ((mem_eliminatedRotations_iff_newRank_le hopt hA hmove hnew).mp hmem)
theorem shortOrientationMen_subset (R : ResidualPivotPair hopt K) :
    R.shortOrientationMen ⊆ R.shortOrientationLabels.biUnion (fun s ↦ s.val.cycle.support) := by
  classical
  intro m hm
  let A := R.toggledEarly.2.matching
  let B := R.late.2.matching
  obtain ⟨J, hJ, hIJ⟩ := exists_eliminatedRotations_union hopt A.property B.property
  have hAJ : MenWeaklyPrefer p A.val J := (eliminatedRotations_subset_iff hopt A.property hJ).mp
    (by rw [hIJ]; exact Set.subset_union_left)
  have hBJ : MenWeaklyPrefer p B.val J := (eliminatedRotations_subset_iff hopt B.property hJ).mp
    (by rw [hIJ]; exact Set.subset_union_right)
  have hm' : p.manRank m (B.val m) < p.manRank m (A.val m) := (Finset.mem_filter.mp hm).2
  obtain ⟨s, hs, hmove, _⟩ := exists_diff_label_moving_of_rank_lt hopt B.property hJ hBJ
    (hm'.trans_le (hAJ m))
  rw [hIJ] at hs
  have hmem : s ∈ eliminatedRotations p μ₀ A.val \ eliminatedRotations p μ₀ B.val :=
    ⟨hs.1.resolve_right hs.2, hs.2⟩
  exact Finset.mem_biUnion.mpr
    ⟨s, by simpa only [← Finset.mem_coe, R.coe_shortOrientationLabels] using hmem,
      Equiv.Perm.mem_support.mpr hmove⟩
theorem card_shortOrientationMen_le (R : ResidualPivotPair hopt K) :
    R.shortOrientationMen.card ≤ K := by
  classical
  exact (Finset.card_le_card R.shortOrientationMen_subset).trans
    (Finset.card_biUnion_le.trans R.sum_rotationLength_shortOrientationLabels_le)
theorem earlierPivot_support_subset_longOrientationMen (R : ResidualPivotPair hopt K) :
    R.early.1.val.val.cycle.support ⊆ R.longOrientationMen := by
  intro m hm
  have hmove := Equiv.Perm.mem_support.mp hm
  let A := R.toggledEarly.2.matching
  let B := R.late.2.matching
  have hE : R.early.1.val.IsExposedAt A.val := R.toggledEarly.2.pivot_exposed
  have hB : R.early.1.val ∈ eliminatedRotations p μ₀ B.val :=
    (Rotation.lt_iff_before_exposure hopt R.pivot_lt.ne).mp R.pivot_lt
      _ B.property R.late.2.pivot_exposed.1 R.late.2.pivot_exposed.2
  have hnew := rotationLabelNewPartner_eq (μ := A.val) hmove
  rw [hE.2] at hnew
  have hle := (mem_eliminatedRotations_iff_newRank_le hopt B.property hmove hnew).mp hB
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, (hE.1.manRank_lt_eliminate_of_moved hmove).trans_le hle⟩
theorem rotationLength_early_le_card_longOrientationMen (R : ResidualPivotPair hopt K) :
    rotationLength R.early.1.val ≤ R.longOrientationMen.card :=
  Finset.card_le_card R.earlierPivot_support_subset_longOrientationMen
private theorem exists_rank_max_and_eliminated_union {A B : Matching n}
    (hopt : IsManOptimal p μ₀) (hA : IsStable p A) (hB : IsStable p B) :
    ∃ J, IsStable p J ∧ (∀ m, p.manRank m (J m) =
      max (p.manRank m (A m)) (p.manRank m (B m))) ∧
      eliminatedRotations p μ₀ J =
        eliminatedRotations p μ₀ A ∪ eliminatedRotations p μ₀ B := by
  obtain ⟨J, hJ, hIJ⟩ := exists_eliminatedRotations_union hopt hA hB
  obtain ⟨L, hL, hLrank⟩ := exists_stable_manRank_max hA hB
  have hAL : MenWeaklyPrefer p A L := fun m ↦ by rw [hLrank]; exact le_max_left _ _
  have hBL : MenWeaklyPrefer p B L := fun m ↦ by rw [hLrank]; exact le_max_right _ _
  have hJL : MenWeaklyPrefer p J L := (eliminatedRotations_subset_iff hopt hJ hL).mp
    (by
      rw [hIJ]
      exact Set.union_subset ((eliminatedRotations_subset_iff hopt hA hL).mpr hAL)
        ((eliminatedRotations_subset_iff hopt hB hL).mpr hBL))
  have hAJ : MenWeaklyPrefer p A J := (eliminatedRotations_subset_iff hopt hA hJ).mp
    (by rw [hIJ]; exact Set.subset_union_left)
  have hBJ : MenWeaklyPrefer p B J := (eliminatedRotations_subset_iff hopt hB hJ).mp
    (by rw [hIJ]; exact Set.subset_union_right)
  refine ⟨J, hJ, fun m ↦ le_antisymm ?_ (max_le (hAJ m) (hBJ m)), hIJ⟩
  simpa only [hLrank] using hJL m
private noncomputable def relativePermutation (R : ResidualPivotPair hopt K) : Equiv.Perm (Fin n) :=
  R.toggledEarly.2.matching.val.trans R.late.2.matching.val.symm
theorem relativePermutation_apply_of_mem_shortLabel (R : ResidualPivotPair hopt K)
    {s : Rotation p μ₀} (hs : s ∈ R.shortOrientationLabels)
    {m : Fin n} (hm : s.val.cycle m ≠ m) :
    R.relativePermutation m = s.val.cycle m := by
  let A := R.toggledEarly.2.matching
  let B := R.late.2.matching
  have hsD : s ∈ eliminatedRotations p μ₀ A.val \ eliminatedRotations p μ₀ B.val :=
    R.coe_shortOrientationLabels ▸ (Finset.mem_coe.mpr hs)
  have hE : s.IsExposedAt B.val := R.isExposedAt_late_of_mem_toggle_early_ideal_diff_late hsD
  obtain ⟨J, hJ, hJrank, hIJ⟩ := exists_rank_max_and_eliminated_union hopt A.property B.property
  have hBJ : MenWeaklyPrefer p B.val J := (eliminatedRotations_subset_iff hopt B.property hJ).mp
    (by rw [hIJ]; exact Set.subset_union_right)
  have hJmem : s ∈ eliminatedRotations p μ₀ J := hIJ ▸ Or.inl hsD.1
  have hnew := rotationLabelNewPartner_eq (μ := B.val) hm
  rw [hE.2] at hnew
  have hle := (mem_eliminatedRotations_iff_newRank_le hopt hJ hm hnew).mp hJmem
  have hlt := (hE.1.manRank_lt_eliminate_of_moved hm).trans_le hle
  obtain ⟨t, ht, htm, htn⟩ := exists_diff_label_moving_of_rank_lt hopt B.property hJ hBJ hlt
  rw [hIJ] at ht
  have hEt : t.IsExposedAt B.val :=
    R.isExposedAt_late_of_mem_toggle_early_ideal_diff_late ⟨ht.1.resolve_right ht.2, ht.2⟩
  have heq : t = s := by
    by_contra hts
    have hcycles : s.val.cycle ≠ t.val.cycle := fun he ↦ hts (Subtype.ext
      (hEt.2.symm.trans ((congrArg (rotationLabel B.val) he).symm.trans hE.2)))
    exact htm (hE.1.disjoint_moved hEt.1 hcycles m hm)
  rw [heq] at htn
  have hJpartner : eliminateRotation B.val s.val.cycle m = J m :=
    Option.some.inj (hnew.symm.trans htn)
  rw [hJrank] at hlt
  have hAgt : p.manRank m (B.val m) < p.manRank m (A.val m) :=
    (lt_max_iff.mp hlt).resolve_right (lt_irrefl _)
  have hApartner : A.val m = J m := (p.manRank m).injective (by
    rw [hJrank, max_eq_left hAgt.le])
  change B.val.symm (A.val m) = _
  rw [hApartner, ← hJpartner, eliminateRotation_apply, Equiv.symm_apply_apply]
theorem cycle_mem_relativePermutation_cycleFactors (R : ResidualPivotPair hopt K)
    {s : Rotation p μ₀} (hs : s ∈ R.shortOrientationLabels) :
    s.val.cycle ∈ R.relativePermutation.cycleFactorsFinset := by
  have hsD : s ∈ eliminatedRotations p μ₀ R.toggledEarly.2.matching.val \
      eliminatedRotations p μ₀ R.late.2.matching.val :=
    R.coe_shortOrientationLabels ▸ (Finset.mem_coe.mpr hs)
  have hE := R.isExposedAt_late_of_mem_toggle_early_ideal_diff_late hsD
  exact Equiv.Perm.mem_cycleFactorsFinset_iff.mpr ⟨(IsExposedRotation.isCycle hE.1), fun _ hm ↦
    (R.relativePermutation_apply_of_mem_shortLabel hs (Equiv.Perm.mem_support.mp hm)).symm⟩
theorem exists_shortLabel_of_cycleFactor (R : ResidualPivotPair hopt K)
    {c : Equiv.Perm (Fin n)} (hc : c ∈ R.relativePermutation.cycleFactorsFinset)
    {m : Fin n} (hm : m ∈ c.support) (hmshort : m ∈ R.shortOrientationMen) :
    ∃ s ∈ R.shortOrientationLabels, s.val.cycle = c := by
  classical
  obtain ⟨s, hs, hms⟩ := Finset.mem_biUnion.mp (R.shortOrientationMen_subset hmshort)
  exact ⟨s, hs, (Equiv.Perm.cycle_is_cycleOf hms
    (R.cycle_mem_relativePermutation_cycleFactors hs)).trans
      (Equiv.Perm.cycle_is_cycleOf hm hc).symm⟩
private noncomputable def toggleBit (R : ResidualPivotPair hopt K) : Bool := by
  classical
  exact decide (R.sharedLabel ∈ R.early.2.removedLabels)
private theorem eq_of_toggled_codes_and_bit {R S : ResidualPivotPair hopt K}
    (hA : R.toggledEarly = S.toggledEarly) (hB : R.late = S.late)
    (hbit : R.toggleBit = S.toggleBit) : R = S := by
  classical
  rcases R with ⟨⟨a, D⟩, L, hlt, hshared⟩
  rcases S with ⟨⟨b, E⟩, L', hlt', hshared'⟩
  have hab : a = b := congrArg Sigma.fst hA
  subst b
  change L = L' at hB
  subst L'
  let γ := Classical.choose hshared
  change (⟨a, D.eraseRemovedLabel γ⟩ : PivotCode hopt K) =
    ⟨a, E.eraseRemovedLabel γ⟩ at hA
  change decide (γ ∈ D.removedLabels) = decide (γ ∈ E.removedLabels) at hbit
  have hdec : γ ∈ D.removedLabels ↔ γ ∈ E.removedLabels := by
    simpa using hbit
  have hDE : D = E := PivotDecoration.eq_of_eraseRemovedLabel_eq γ
    (eq_of_heq (Sigma.mk.inj_iff.mp hA).2) hdec
  subst E
  rfl
theorem toggledEarly_preserves (R : ResidualPivotPair hopt K)
    (F : ∀ a : LongPivot p μ₀ K, PivotDecoration hopt K a.val → Prop)
    (hF : ∀ (a : LongPivot p μ₀ K) (D E : PivotDecoration hopt K a.val),
      E.removed ⊆ D.removed → F a D → F a E)
    (h : F R.early.1 R.early.2) : F R.toggledEarly.1 R.toggledEarly.2 :=
  hF _ _ _ (R.early.2.eraseRemovedLabel_subset R.sharedLabel) h
private noncomputable def toggleEmbedding (hopt : IsManOptimal p μ₀) (K : ℕ) :
    ResidualPivotPair hopt K ↪ IncomparableStableMatchingPair p μ₀ × Bool :=
  ⟨fun R ↦ (R.toggleImage, R.toggleBit), by
    intro R S h
    have hpair := congrArg (fun z : IncomparableStableMatchingPair p μ₀ × Bool ↦ z.1.val) h
    have hA : R.toggledEarly = S.toggledEarly :=
      (pivotDecorationEmbedding hopt K).injective (congrArg Prod.fst hpair)
    have hB : R.late = S.late :=
      (pivotDecorationEmbedding hopt K).injective (congrArg Prod.snd hpair)
    exact eq_of_toggled_codes_and_bit hA hB (congrArg Prod.snd h)⟩
private instance (hopt : IsManOptimal p μ₀) (K : ℕ) : Finite (ResidualPivotPair hopt K) :=
  Finite.of_injective (toggleEmbedding hopt K) (toggleEmbedding hopt K).injective
private noncomputable def toggleEmbedding_restrict
    {P : ResidualPivotPair hopt K → Prop} {Q : IncomparableStableMatchingPair p μ₀ → Prop}
    (hQ : ∀ R, P R → Q R.toggleImage) :
    {R // P R} ↪ {MN // Q MN} × Bool :=
  ⟨fun R ↦ (⟨R.val.toggleImage, hQ R.val R.property⟩, R.val.toggleBit),
    fun _ _ h ↦ Subtype.ext ((toggleEmbedding hopt K).injective
      (congrArg (fun z : {MN // Q MN} × Bool ↦ (z.1.val, z.2)) h))⟩
theorem card_le_twice_incomparable_restrict
    {P : ResidualPivotPair hopt K → Prop} {Q : IncomparableStableMatchingPair p μ₀ → Prop}
    (hQ : ∀ R, P R → Q R.toggleImage) :
    Nat.card {R // P R} ≤ 2 * Nat.card {MN // Q MN} := by
  have h := Nat.card_le_card_of_injective (toggleEmbedding_restrict hQ)
    (toggleEmbedding_restrict hQ).injective
  simpa [Nat.card_prod, mul_comm] using h
end ResidualPivotPair
end CompLP
end

-- PivotFilteredDecoration
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace CompLP
variable {n : ℕ} {x : ScoreProfile n} {μ₀ : Matching n}
  {hopt : IsManOptimal (profileOfScores x) μ₀} {K : ℕ}
  {r : Rotation (profileOfScores x) μ₀}
open scoped Classical in
private def PivotDecoration.PassesReverseFilters (D : PivotDecoration hopt K r) (L : ℕ) (t : ℝ) : Prop :=
  ((D.removed.filter (fun s ↦ rotationLength s.val ≤ L)).card : ℝ) ≤
    (3 / 2 : ℝ) * Real.log (L : ℝ) ∧
  ∀ w, femaleSpouseScore x D.matching.val w -
    femaleSpouseScore x (singletonRotationAnchor hopt r).val w ≤ t
private abbrev FilteredPivotDecoration (hopt : IsManOptimal (profileOfScores x) μ₀) (K : ℕ)
    (r : Rotation (profileOfScores x) μ₀) (L : ℕ) (t : ℝ) :=
  {D : PivotDecoration hopt K r // D.PassesReverseFilters L t}
theorem PivotDecoration.PassesReverseFilters.of_removed_subset {D E : PivotDecoration hopt K r}
    {L : ℕ} {t : ℝ} (hD : D.PassesReverseFilters L t) (hsub : E.removed ⊆ D.removed)
    (hties : ∀ row, Function.Injective (x row)) : E.PassesReverseFilters L t := by
  classical
  constructor
  · exact (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter _ hsub))).trans hD.1
  · have hI : eliminatedRotations (profileOfScores x) μ₀ D.matching.val ⊆
        eliminatedRotations (profileOfScores x) μ₀ E.matching.val := by
      rw [PivotDecoration.matching_eliminated, PivotDecoration.matching_eliminated]
      exact fun _ hs ↦ ⟨hs.1, fun he ↦ hs.2 (Set.image_mono hsub he)⟩
    obtain ⟨rs, hpath⟩ := exists_rotationSequence_of_menWeaklyPrefer
      D.matching.property E.matching.property
      ((eliminatedRotations_subset_iff hopt D.matching.property E.matching.property).mp hI)
    intro w
    have hscore : femaleSpouseScore x E.matching.val w ≤ femaleSpouseScore x D.matching.val w :=
      le_of_not_gt fun hw ↦ (not_lt_of_ge (hpath.womanRank_end_le w))
        ((rankPermutation_lt_iff (hties (.inr w)) _ _).mpr hw)
    exact (sub_le_sub_right hscore _).trans (hD.2 w)
theorem ResidualPivotPair.toggledEarly_passesReverseFilters
    (R : ResidualPivotPair hopt K) (L : ℕ)
    (t : LongPivot (profileOfScores x) μ₀ K → ℝ)
    (hties : ∀ row, Function.Injective (x row))
    (h : R.early.2.PassesReverseFilters L (t R.early.1)) :
    R.toggledEarly.2.PassesReverseFilters L (t R.toggledEarly.1) :=
  R.toggledEarly_preserves (fun a D ↦ D.PassesReverseFilters L (t a))
    (fun _ _ _ hsub hD ↦ hD.of_removed_subset hsub hties) h
theorem compatibleReversePermutationToDecoration_passesReverseFilters
    (σ : CompatibleReversePermutation hopt K r) {L : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (hcap : ¬ shortCycleCapBad L σ.val.cycleType)
    (hinc : reverseCollectionIncrementGood x (singletonRotationAnchor hopt r).val σ.val t) :
    (compatibleReversePermutationToDecoration hopt K r σ).PassesReverseFilters L t := by
  classical
  let A := singletonRotationAnchor hopt r
  constructor
  · rw [compatibleReversePermutationToDecoration_removed, realizedReverseRemovedLabels_short_card]
    exact not_lt.mp hcap
  · intro w
    rw [compatibleReversePermutationToDecoration_matching]
    change x (.inr w) ((undoReverseRotation A.val σ.val).symm w) -
      x (.inr w) (A.val.symm w) ≤ t
    rw [undoReverseRotation_symm_apply]
    by_cases hw : w ∈ σ.val.support
    · exact hinc w hw
    · rw [Equiv.Perm.notMem_support.mp hw, sub_self]
      exact ht
theorem FilteredPivotDecoration.shortExposed_card_le {L : ℕ} {t : ℝ}
    (D : FilteredPivotDecoration hopt K r L t) (hL : L ≤ K) (hr : K < rotationLength r) :
    (Nat.card {s : Rotation (profileOfScores x) μ₀ //
      s.IsExposedAt D.val.matching.val ∧ rotationLength s ≤ L} : ℝ) ≤
      (3 / 2 : ℝ) * Real.log (L : ℝ) := by
  classical
  let S := D.val.removed.filter (fun s ↦ rotationLength s.val ≤ L)
  let f (s : S) : {q : Rotation (profileOfScores x) μ₀ //
      q.IsExposedAt D.val.matching.val ∧ rotationLength q ≤ L} :=
    ⟨s.val.val, (D.val.isExposedAt_matching_iff s.val.val).mpr
      (Or.inr ⟨s.val, (Finset.mem_filter.mp s.property).1, rfl⟩),
      (Finset.mem_filter.mp s.property).2⟩
  have hf : Function.Surjective f := by
    intro q
    rcases (D.val.isExposedAt_matching_iff q.val).mp q.property.1 with hq | ⟨s, hs, he⟩
    · exact (not_lt_of_ge (hL.trans' (hq ▸ q.property.2)) hr).elim
    · have hs' : s ∈ S := Finset.mem_filter.mpr ⟨hs, he ▸ q.property.2⟩
      exact ⟨⟨s, hs'⟩, Subtype.ext he⟩
  have hcard := Nat.card_le_card_of_surjective f hf
  rw [Nat.card_eq_finsetCard] at hcard
  exact (Nat.cast_le.mpr hcard).trans D.property.1
private theorem PivotDecoration.exists_changedWomen_cover
    (D : PivotDecoration hopt K r) :
    let A := (singletonRotationAnchor hopt r).val
    ∃ S : Finset (Fin n), S.card ≤ K ∧
      ∀ w ∉ S, D.matching.val.symm w = A.symm w := by
  classical
  intro A
  let B := D.removed.biUnion (fun s ↦ s.val.val.cycle.support)
  let S := B.map A.toEmbedding
  have hB : B.card ≤ K := Finset.card_biUnion_le.trans D.totalLength_le
  refine ⟨S, (Finset.card_map _).trans_le hB, ?_⟩
  intro w hw
  let m := A.symm w
  have hm : m ∉ B := fun hm ↦ hw (Finset.mem_map.mpr ⟨m, hm, A.apply_symm_apply w⟩)
  obtain ⟨rs, _, hrs, hpath⟩ := exists_rotationUndoSequence_of_maximal_subset hopt
    (singletonRotationAnchor hopt r).property D.removed
  have hfix : D.matching.val m = A m := by
    apply hpath.partner_eq_of_fixed m
    intro q hq
    obtain ⟨s, hs, rfl⟩ := hrs ▸ (show q ∈ {q | q ∈ rs} from hq)
    exact Equiv.Perm.notMem_support.mp fun hmem ↦ hm (Finset.mem_biUnion.mpr ⟨s, hs, hmem⟩)
  exact (D.matching.val.symm_apply_eq).mpr ((A.apply_symm_apply w).symm.trans hfix.symm)
theorem FilteredPivotDecoration.scoreGeometry {L : ℕ} {t d : ℝ}
    (D : FilteredPivotDecoration hopt K r L t)
    (hties : ∀ row, Function.Injective (x row)) (ht : 0 ≤ t)
    (hY : 0 < femaleSpouseTotal x (singletonRotationAnchor hopt r).val)
    (hy : ∀ w, 0 ≤ femaleSpouseScore x (singletonRotationAnchor hopt r).val w)
    (htd : t ≤ d * femaleSpouseTotal x (singletonRotationAnchor hopt r).val)
    (hKd : (K : ℝ) * d ≤ 1) :
    let A := (singletonRotationAnchor hopt r).val
    let N := D.val.matching.val
    (∀ i, maleSpouseScore x N i ≤ maleSpouseScore x A i) ∧
      (femaleSpouseTotal x A ≤ femaleSpouseTotal x N ∧
        femaleSpouseTotal x N ≤ 2 * femaleSpouseTotal x A) ∧
      (∀ w, femaleSpouseScore x N w / femaleSpouseTotal x N ≤
        femaleSpouseScore x A w / femaleSpouseTotal x A + d) := by
  intro A N
  let Y := femaleSpouseTotal x A
  have hsub : eliminatedRotations (profileOfScores x) μ₀ N ⊆
      eliminatedRotations (profileOfScores x) μ₀ A := by
    change eliminatedRotations (profileOfScores x) μ₀
      (undoMaximalSubsetEmbedding hopt (singletonRotationAnchor hopt r).property
        D.val.removed).val ⊆ _
    rw [eliminatedRotations_undoMaximalSubsetEmbedding]
    exact Set.sdiff_subset
  have hmen := (eliminatedRotations_subset_iff hopt D.val.matching.property
    (singletonRotationAnchor hopt r).property).mp hsub
  have hYle : Y ≤ femaleSpouseTotal x N := femaleSpouseTotal_le_of_eliminatedRotations_subset
    hties hopt D.val.matching.property (singletonRotationAnchor hopt r).property hsub
  obtain ⟨S, hS, hfix⟩ := D.val.exists_changedWomen_cover
  have hinc (w : Fin n) : femaleSpouseScore x N w - femaleSpouseScore x A w ≤ t :=
    D.property.2 w
  have hsum : femaleSpouseTotal x N - Y ≤ (K : ℝ) * t := by
    change (∑ j, femaleSpouseScore x N j) - (∑ j, femaleSpouseScore x A j) ≤ _
    have hzero (w : Fin n) (hw : w ∉ S) :
        femaleSpouseScore x N w - femaleSpouseScore x A w = 0 :=
      sub_eq_zero.mpr (congrArg (x (.inr w)) (hfix w hw))
    rw [← Finset.sum_sub_distrib, ← Finset.sum_subset (Finset.subset_univ S) (fun w _ ↦ hzero w)]
    calc
      _ ≤ ∑ _w ∈ S, t := Finset.sum_le_sum fun w _ ↦ hinc w
      _ = (S.card : ℝ) * t := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hS) ht
  have hKt : (K : ℝ) * t ≤ Y := calc
    _ ≤ (K : ℝ) * (d * Y) := mul_le_mul_of_nonneg_left htd (Nat.cast_nonneg _)
    _ = ((K : ℝ) * d) * Y := (mul_assoc ..).symm
    _ ≤ 1 * Y := mul_le_mul_of_nonneg_right hKd hY.le
    _ = Y := one_mul _
  refine ⟨?_, ⟨hYle, ?_⟩, ?_⟩
  · intro i
    exact le_of_not_gt fun hi ↦ (not_lt_of_ge (hmen i))
      ((rankPermutation_lt_iff (hties (.inl i)) _ _).mpr hi)
  · linarith only [hsum, hKt]
  · intro w
    calc
      _ ≤ (femaleSpouseScore x A w + t) / femaleSpouseTotal x N :=
        div_le_div_of_nonneg_right (sub_le_iff_le_add'.mp (hinc w)) (hY.le.trans hYle)
      _ ≤ (femaleSpouseScore x A w + t) / Y :=
        div_le_div_of_nonneg_left (add_nonneg (hy w) ht) hY hYle
      _ = femaleSpouseScore x A w / Y + t / Y := add_div _ _ _
      _ ≤ _ := add_le_add le_rfl ((div_le_iff₀ hY).mpr htd)
end CompLP
end

-- PivotEligibleRevealControls
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace CompLP
private def reverseDiagonalMaleTotal {n : ℕ} (d : DiagonalScorePairs n) : ℝ :=
  ∑ i, (diagonalPairAt d i).1
private def eligiblePivotRevealSet {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (ρ : Matching n) (D : ℝ) :
    Set (ForwardRevealedMaleScores flag) :=
  {v | (∀ τ : Matching n, v ∈ forwardRevealExposureEvent τ flag ↔ τ = ρ) ∧
    (∀ m ∈ ρ.support, 0 ≤ forwardPivotIncrement d flag ρ v m) ∧
    (∑ m ∈ ρ.support, forwardPivotIncrement d flag ρ v m) ≤ D}
namespace ReverseMaskGeometry
variable {n : ℕ} {d : DiagonalScorePairs n} {flag : OffDiagonalCellIndex n → Bool}
  {μ ρ : Matching n} {s u p : ℝ}
end ReverseMaskGeometry
end CompLP
end

-- PivotSpouseBandMask
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace CompLP
private def pivotDiagonalFemaleTotal {n : ℕ} (d : DiagonalScorePairs n) : ℝ :=
  ∑ i, (diagonalPairAt d i).2
private def pivotBaseDiagonalBand (n : ℕ) : Set (DiagonalScorePairs n) :=
  {d | let X := reverseDiagonalMaleTotal d
       let Y := pivotDiagonalFemaleTotal d
       (∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1 ∧ (diagonalPairAt d i).2 ∈ Ico 0 1) ∧
       2 ≤ Y ∧ Y ≤ (n : ℝ) ^ (2 / 5 : ℝ) ∧ (n : ℝ) / 128 ≤ X * Y ∧
       (∀ i, (diagonalPairAt d i).2 / Y ≤ 12 * Real.log n / n) ∧
       ∀ i, (diagonalPairAt d i).1 ≤ 8 * Real.log n / (Y - 1)}
end CompLP
end

-- ForestDeterministic
section
open scoped BigOperators Classical
namespace CompLP
end CompLP
end

-- ForwardSuccessorRowLaw
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace CompLP
end CompLP
end

-- ForwardSuccessorOutcome
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace CompLP
end CompLP
end

-- PivotForwardRowDeficit
section
open Filter MeasureTheory Set
open scoped BigOperators ENNReal
namespace CompLP
end CompLP
end

-- PivotForwardForest
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace CompLP
private def IsSoleForwardExposedRotation {n : ℕ} (p : Profile n) (μ σ : Matching n) : Prop :=
  IsExposedRotation p μ σ ∧ ∀ τ, IsExposedRotation p μ τ → τ = σ
end CompLP
end

-- PivotLocalEligibility
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace CompLP
private def certifiedSet {α : Type} [MeasurableSpace α] {t : Set α} (_ : MeasurableSet t) := t
private def LocalPivotGeometry {n : ℕ} (b A B : ℝ) (μ ρ : Matching n)
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool) : Prop :=
  d ∈ certifiedSet (MarkedLP.measurableSet_localPivotGeometry b A B μ ρ flag)
private theorem LocalPivotGeometry.length_lower {n : ℕ} {b A B : ℝ} {μ ρ : Matching n}
    {d : DiagonalScorePairs n} {flag : OffDiagonalCellIndex n → Bool}
    (h : LocalPivotGeometry b A B μ ρ d flag) : b * Real.sqrt (n : ℝ) ≤ (ρ.support.card : ℝ) := by
  obtain ⟨_,_,he,_,_,_,_,_⟩ := h
  exact he
private theorem LocalPivotGeometry.base {n : ℕ} {b A B : ℝ} {μ ρ : Matching n}
    {d : DiagonalScorePairs n} {flag : OffDiagonalCellIndex n → Bool}
    (h : LocalPivotGeometry b A B μ ρ d flag) : d ∈ pivotBaseDiagonalBand n := by
  obtain ⟨he,_,_,_,_,_,_,_⟩ := h
  exact he
private theorem LocalPivotGeometry.lower_band {n : ℕ} {b A B : ℝ} {μ ρ : Matching n}
    {d : DiagonalScorePairs n} {flag : OffDiagonalCellIndex n → Bool}
    (h : LocalPivotGeometry b A B μ ρ d flag) : (n : ℝ) ^ (1 / 10 : ℝ) ≤ pivotDiagonalFemaleTotal d := by
  obtain ⟨_,he,_,_,_,_,_,_⟩ := h
  exact he
private noncomputable def localPivotIncrementCap {n : ℕ} (B : ℝ) (d : DiagonalScorePairs n) : ℝ :=
  B * Real.sqrt (n : ℝ) / pivotDiagonalFemaleTotal d
private def IsLocallyEligiblePivot {n : ℕ} (b A B : ℝ) (x : ScoreProfile n)
    (μ ρ : Matching n) : Prop :=
  let z := splitScorePairs μ x
  let flag := forwardMaskOfScores z.1 z.2
  LocalPivotGeometry b A B μ ρ z.1 flag ∧
    (forwardRevealWithColumns flag z.2).1 ∈
      eligiblePivotRevealSet z.1 flag ρ (localPivotIncrementCap B z.1)
theorem IsLocallyEligiblePivot.isSoleForwardExposed {n : ℕ} {b A B : ℝ}
    {x : ScoreProfile n} {μ ρ : Matching n}
    (h : IsLocallyEligiblePivot b A B x μ ρ)
    (ht : ∀ row, Function.Injective (x row)) :
    IsSoleForwardExposedRotation (profileOfScores x) μ ρ := by
  let z := splitScorePairs μ x
  let flag := forwardMaskOfScores z.1 z.2
  have hmask : z.2 ∈ forwardScoreMaskEvent z.1 flag :=
    (forwardMaskOfScores_eq_iff _ _ _).mp rfl
  have he (τ : Matching n) := (isExposedRotation_iff_forwardRevealExposureEvent μ τ x flag ht
    hmask).trans (h.2.1 τ)
  exact ⟨(he ρ).mpr rfl, fun τ hτ ↦ (he τ).mp hτ⟩
theorem reverseDiagonalMaleTotal_splitScorePairs {n : ℕ}
    (μ : Matching n) (x : ScoreProfile n) :
    reverseDiagonalMaleTotal (splitScorePairs μ x).1 = maleSpouseTotal x μ :=
  Finset.sum_congr rfl fun i _ ↦ congrArg Prod.fst (diagonalPairAt_splitScorePairs μ x i)
theorem pivotDiagonalFemaleTotal_splitScorePairs {n : ℕ}
    (μ : Matching n) (x : ScoreProfile n) :
    pivotDiagonalFemaleTotal (splitScorePairs μ x).1 = femaleSpouseTotal x μ := by
  rw [femaleSpouseTotal_eq_sum_byHusband]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [diagonalPairAt_splitScorePairs, femaleSpouseByHusband, femaleSpouseScore,
    Equiv.symm_apply_apply]
private theorem measurable_diagonalMaleScore {n : ℕ} (i : Fin n) :
    Measurable (fun d : DiagonalScorePairs n ↦ (diagonalPairAt d i).1) :=
  (measurable_pi_apply _).fst
private theorem measurable_diagonalFemaleScore {n : ℕ} (i : Fin n) :
    Measurable (fun d : DiagonalScorePairs n ↦ (diagonalPairAt d i).2) :=
  (measurable_pi_apply _).snd
private theorem measurable_pivotDiagonalFemaleTotal (n : ℕ) :
    Measurable (@pivotDiagonalFemaleTotal n) :=
  Finset.measurable_sum _ fun i _ ↦ measurable_diagonalFemaleScore i
theorem measurableSet_localPivotGeometry {n : ℕ} (b A B : ℝ) (μ ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) :
    MeasurableSet {d : DiagonalScorePairs n | LocalPivotGeometry b A B μ ρ d flag} := MarkedLP.measurableSet_localPivotGeometry b A B μ ρ flag

private theorem measurable_jointForwardPivotIncrement {n : ℕ}
    (flag : OffDiagonalCellIndex n → Bool) (ρ : Matching n) (m : Fin n) :
    Measurable (fun z : DiagonalScorePairs n × ForwardRevealedMaleScores flag ↦
      forwardPivotIncrement z.1 flag ρ z.2 m) := by
  by_cases hm : ρ m ≠ m
  · let q : OffDiagonalCellIndex n := ⟨(m, ρ m), hm.symm⟩
    by_cases hq : flag q = true
    · have hq' : flag (⟨(m, ρ m), hm.symm⟩ : OffDiagonalCellIndex n) = true := hq
      simp only [forwardPivotIncrement, dif_pos hm, dif_pos hq']
      exact (((measurable_pi_apply (⟨q, hq⟩ : ForwardActiveCellIndex flag)).comp
          (measurable_snd : Measurable (@Prod.snd (DiagonalScorePairs n) _))).sub
          ((measurable_diagonalMaleScore m).comp measurable_fst))
    · have hq' : flag (⟨(m, ρ m), hm.symm⟩ : OffDiagonalCellIndex n) ≠ true := hq
      simp only [forwardPivotIncrement, dif_pos hm, dif_neg hq']
      exact measurable_const
  · simp only [forwardPivotIncrement, dif_neg hm]
    exact measurable_const
theorem measurableSet_jointEligiblePivotReveal {n : ℕ}
    (B : ℝ) (flag : OffDiagonalCellIndex n → Bool) (ρ : Matching n) :
    MeasurableSet {z : DiagonalScorePairs n × ForwardRevealedMaleScores flag |
      z.2 ∈ eligiblePivotRevealSet z.1 flag ρ (localPivotIncrementCap B z.1)} := by
  have hs : MeasurableSet {v : ForwardRevealedMaleScores flag |
      ∀ τ : Matching n, v ∈ forwardRevealExposureEvent τ flag ↔ τ = ρ} := by
    rw [ofPred_forall]
    refine MeasurableSet.iInter fun τ ↦ ?_
    by_cases ht : τ = ρ
    · simpa only [ht, iff_true, ofPred_mem_eq] using
        measurableSet_forwardRevealExposureEvent ρ flag
    · simpa only [ht, iff_false, ← mem_compl_iff, ofPred_mem_eq] using
        (measurableSet_forwardRevealExposureEvent τ flag).compl
  have hcap : Measurable (fun z : DiagonalScorePairs n × ForwardRevealedMaleScores flag ↦
      localPivotIncrementCap B z.1) :=
    measurable_const.div ((measurable_pivotDiagonalFemaleTotal n).comp measurable_fst)
  have hnonneg : MeasurableSet {z : DiagonalScorePairs n × ForwardRevealedMaleScores flag |
      ∀ m ∈ ρ.support, 0 ≤ forwardPivotIncrement z.1 flag ρ z.2 m} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun m ↦ MeasurableSet.iInter fun _ ↦
      measurableSet_le measurable_const (measurable_jointForwardPivotIncrement flag ρ m)
  have hsum : MeasurableSet {z : DiagonalScorePairs n × ForwardRevealedMaleScores flag |
      (∑ m ∈ ρ.support, forwardPivotIncrement z.1 flag ρ z.2 m) ≤
        localPivotIncrementCap B z.1} :=
    measurableSet_le (Finset.measurable_sum _ fun m _ ↦
      measurable_jointForwardPivotIncrement flag ρ m) hcap
  exact (measurable_snd hs).inter (hnonneg.inter hsum)
theorem measurable_jointForwardMaskOfScores (n : ℕ) :
    Measurable (fun z : DiagonalScorePairs n × OffDiagonalScorePairs n ↦
      forwardMaskOfScores z.1 z.2) := by
  apply measurable_pi_iff.2
  intro q
  apply measurable_to_bool
  have hz : Measurable (fun z : DiagonalScorePairs n × OffDiagonalScorePairs n ↦ z.2 q) :=
    (measurable_pi_apply q).comp measurable_snd
  have he : (fun z : DiagonalScorePairs n × OffDiagonalScorePairs n ↦
      forwardMaskOfScores z.1 z.2 q) ⁻¹' {true} =
      {z | (diagonalPairAt z.1 q.val.1).1 < (z.2 q).1} ∩
      {z | (z.2 q).2 < (diagonalPairAt z.1 q.val.2).2} := by
    ext z
    exact forwardCellFlag_eq_true.trans Set.mem_prod
  rw [he]
  exact (measurableSet_lt ((measurable_diagonalMaleScore _).comp measurable_fst) hz.fst).inter
    (measurableSet_lt hz.snd ((measurable_diagonalFemaleScore _).comp measurable_fst))
theorem measurableSet_isLocallyEligiblePivot {n : ℕ} (b A B : ℝ) (μ ρ : Matching n) :
    MeasurableSet {x : ScoreProfile n | IsLocallyEligiblePivot b A B x μ ρ} := by
  let Z := splitScorePairs μ
  let mask (x : ScoreProfile n) := forwardMaskOfScores (Z x).1 (Z x).2
  let E (flag : OffDiagonalCellIndex n → Bool) := {x : ScoreProfile n | mask x = flag ∧
    LocalPivotGeometry b A B μ ρ (Z x).1 flag ∧
    (forwardRevealWithColumns flag (Z x).2).1 ∈
      eligiblePivotRevealSet (Z x).1 flag ρ (localPivotIncrementCap B (Z x).1)}
  have hmask : Measurable mask := (measurable_jointForwardMaskOfScores n).comp Z.measurable
  have hE : {x : ScoreProfile n | IsLocallyEligiblePivot b A B x μ ρ} = ⋃ flag, E flag := by
    ext x
    refine ⟨fun h ↦ mem_iUnion.mpr ⟨mask x, rfl, h.1, h.2⟩, fun h ↦ ?_⟩
    obtain ⟨f, hf, hg, hv⟩ := mem_iUnion.mp h
    subst f
    exact ⟨hg, hv⟩
  rw [hE]
  refine MeasurableSet.iUnion fun flag ↦ (hmask (measurableSet_singleton flag)).inter
    ((((measurable_fst.comp Z.measurable) (measurableSet_localPivotGeometry b A B μ ρ flag))).inter ?_)
  exact (measurableSet_jointEligiblePivotReveal B flag ρ).preimage
    ((measurable_fst.comp Z.measurable).prodMk
      (measurable_fst.comp ((measurable_forwardRevealWithColumns flag).comp
        (measurable_snd.comp Z.measurable))))
end CompLP
end

-- PivotMarkedDecorationCount
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace CompLP
variable {n : ℕ}
private noncomputable def markedFilteredChoices (μ ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (K L : ℕ) (t : ℝ) (x : ScoreProfile n) :
    Finset (Matching n) := by
  classical
  exact Finset.univ.filter fun σ ↦ σ.support.card ≤ K ∧
    σ ∈ filteredReverseSupportFamily μ ρ flag σ.support.card L t x
theorem mem_markedFilteredChoices {μ ρ σ : Matching n} {flag : OffDiagonalCellIndex n → Bool}
    {K L : ℕ} {t : ℝ} {x : ScoreProfile n} :
    σ ∈ markedFilteredChoices μ ρ flag K L t x ↔ σ.support.card ≤ K ∧
      σ ∈ filteredReverseSupportFamily μ ρ flag σ.support.card L t x := by
  classical
  simp [markedFilteredChoices]
theorem measurableSet_mem_markedFilteredChoices (μ ρ σ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (K L : ℕ)
    {t : ScoreProfile n → ℝ} (ht : Measurable t) :
    MeasurableSet {x : ScoreProfile n | σ ∈ markedFilteredChoices μ ρ flag K L (t x) x} := by
  classical
  have hinc :
      MeasurableSet {x : ScoreProfile n | reverseCollectionIncrementGood x μ σ (t x)} := by
    have he : {x : ScoreProfile n | reverseCollectionIncrementGood x μ σ (t x)} =
        ⋂ w : σ.support, {x : ScoreProfile n |
          reverseScoreIncrement x μ w.val (μ.symm (σ w.val)) ≤ t x} := by
      ext x
      exact ⟨fun h ↦ mem_iInter.mpr fun w ↦ h w.val w.property,
        fun h w hw ↦ mem_iInter.mp h ⟨w, hw⟩⟩
    rw [he]
    exact MeasurableSet.iInter fun w ↦
      measurableSet_le (measurable_reverseScoreIncrement μ w.val (μ.symm (σ w.val))) ht
  have hcomp : MeasurableSet {x : ScoreProfile n |
      σ ∈ compatibleReverseSupportFamily μ ρ flag σ.support.card (profileOfScores x)} :=
    measurable_profileOfScores n (MeasurableSet.of_discrete : MeasurableSet
      {p : Profile n | σ ∈ compatibleReverseSupportFamily μ ρ flag σ.support.card p})
  simp only [mem_markedFilteredChoices, filteredReverseSupportFamily, Finset.mem_filter,
    ofPred_and]
  exact (MeasurableSet.const _).inter (hcomp.inter ((MeasurableSet.const _).inter hinc))
theorem measurable_card_markedFilteredChoices (μ ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (K L : ℕ)
    {t : ScoreProfile n → ℝ} (ht : Measurable t) :
    Measurable (fun x ↦ ((markedFilteredChoices μ ρ flag K L (t x) x).card : ℝ)) := by
  have h := measurable_finsetCard_of_mem (fun x ↦ markedFilteredChoices μ ρ flag K L (t x) x)
    (fun σ ↦ measurableSet_mem_markedFilteredChoices μ ρ σ flag K L ht)
  simpa only [Function.comp_def, ENNReal.toReal_natCast] using
    ENNReal.measurable_toReal.comp h
private noncomputable def localFilteredDecorationCount (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n)
    (x : ScoreProfile n) : ℝ := by
  classical
  exact if IsLocallyEligiblePivot b A B x μ ρ then
    ((markedFilteredChoices μ ρ (forwardMaskOfScores (splitScorePairs μ x).1
      (splitScorePairs μ x).2) K L (reverseIncrementCutoff n (maleSpouseTotal x μ)) x).card : ℝ)
    else 0
private theorem measurable_mask_switch {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [Countable β] [MeasurableSingletonClass β] {M : α → β}
    (hM : Measurable M) {f : β → α → γ} (hf : ∀ j, Measurable (f j)) :
    Measurable (fun x ↦ f (M x) x) := by
  intro s hs
  let E (j : β) := {x : α | M x = j ∧ f j x ∈ s}
  have he : (fun x ↦ f (M x) x) ⁻¹' s = ⋃ j, E j := by
    ext x
    change f (M x) x ∈ s ↔ x ∈ ⋃ j, E j
    simp only [mem_iUnion, E, mem_ofPred_eq]
    exact ⟨fun hx ↦ ⟨M x, rfl, hx⟩, fun ⟨j, hj, hx⟩ ↦ hj.symm ▸ hx⟩
  rw [he]
  exact MeasurableSet.iUnion fun j ↦ (hM (measurableSet_singleton j)).inter (hf j hs)
theorem measurable_localFilteredDecorationCount (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n) :
    Measurable (localFilteredDecorationCount b A B K L μ ρ) := by
  classical
  let M (x : ScoreProfile n) :=
    forwardMaskOfScores (splitScorePairs μ x).1 (splitScorePairs μ x).2
  let t (x : ScoreProfile n) := reverseIncrementCutoff n (maleSpouseTotal x μ)
  let f (flag : OffDiagonalCellIndex n → Bool) (x : ScoreProfile n) :=
    ((markedFilteredChoices μ ρ flag K L (t x) x).card : ℝ)
  have hM : Measurable M :=
    (measurable_jointForwardMaskOfScores n).comp (splitScorePairs μ).measurable
  have ht : Measurable t := measurable_const.div (measurable_maleSpouseTotal μ)
  have hf (flag : OffDiagonalCellIndex n → Bool) : Measurable (f flag) :=
    measurable_card_markedFilteredChoices μ ρ flag K L ht
  exact (measurable_mask_switch hM hf).ite (measurableSet_isLocallyEligiblePivot b A B μ ρ)
    measurable_const
theorem localFilteredDecorationCount_nonneg (b A B : ℝ) (K L : ℕ)
    (μ ρ : Matching n) (x : ScoreProfile n) :
    0 ≤ localFilteredDecorationCount b A B K L μ ρ x := by
  classical
  unfold localFilteredDecorationCount
  split <;> positivity
theorem localFilteredDecorationCount_le_factorial (b A B : ℝ) (K L : ℕ)
    (μ ρ : Matching n) (x : ScoreProfile n) :
    localFilteredDecorationCount b A B K L μ ρ x ≤ (n.factorial : ℝ) := by
  classical
  unfold localFilteredDecorationCount
  split
  · apply Nat.cast_le.mpr
    simpa only [Fintype.card_perm, Fintype.card_fin] using
      Finset.card_le_univ (markedFilteredChoices μ ρ
        (forwardMaskOfScores (splitScorePairs μ x).1 (splitScorePairs μ x).2)
        K L (reverseIncrementCutoff n (maleSpouseTotal x μ)) x)
  · positivity
section MatchingEndpoints
variable {x : ScoreProfile n} {μ₀ μ ρ σ : Matching n}
  {flag : OffDiagonalCellIndex n → Bool} {K L : ℕ} {t : ℝ}
theorem isCompatibleReversePermutation_of_mem_markedFilteredChoices
    (hopt : IsManOptimal (profileOfScores x) μ₀) (r : Rotation (profileOfScores x) μ₀)
    (hμ : (singletonRotationAnchor hopt r).val = μ) (hρ : r.val.cycle = ρ)
    (hσ : σ ∈ markedFilteredChoices μ ρ flag K L t x) :
    IsCompatibleReversePermutation hopt K r σ := by
  classical
  obtain ⟨hcap, hm⟩ := mem_markedFilteredChoices.mp hσ
  have hc := mem_compatibleReversePermutations.mp (Finset.mem_filter.mp hm).1
  have hg := (mem_goodReverseSupportPermutations.mp hc.1).2
  change RealizesSuccessorPermutation (swapProfile (profileOfScores x))
    (singletonRotationAnchor hopt r).val.symm σ ∧ σ.support.card ≤ K ∧
    (∀ m ∈ r.val.cycle.support, (singletonRotationAnchor hopt r).val m ∉ σ.support) ∧
    IsExposedRotation (profileOfScores x)
      (undoReverseRotation (singletonRotationAnchor hopt r).val σ) r.val.cycle
  rw [hμ, hρ]
  exact ⟨hc.2.1, hcap, fun m hm hmem ↦ (hg _ hmem).1
    (Finset.mem_map.mpr ⟨m, hm, rfl⟩), hc.2.2⟩
private noncomputable def markedFilteredChoicesEmbedding
    (hopt : IsManOptimal (profileOfScores x) μ₀) (r : Rotation (profileOfScores x) μ₀)
    (hμ : (singletonRotationAnchor hopt r).val = μ) (hρ : r.val.cycle = ρ)
    (ht : 0 ≤ t) :
    (↥(markedFilteredChoices μ ρ flag K L t x)) ↪ FilteredPivotDecoration hopt K r L t := by
  classical
  let f (σ : ↥(markedFilteredChoices μ ρ flag K L t x)) :
      CompatibleReversePermutation hopt K r :=
    ⟨σ.val, isCompatibleReversePermutation_of_mem_markedFilteredChoices hopt r hμ hρ
      σ.property⟩
  let e := compatibleReversePermutationEmbedding hopt K r
  refine ⟨fun σ ↦ ⟨e (f σ), ?_⟩, ?_⟩
  · have hf := (Finset.mem_filter.mp (mem_markedFilteredChoices.mp σ.property).2).2
    exact compatibleReversePermutationToDecoration_passesReverseFilters (f σ) ht hf.1
      (by rw [hμ]; exact hf.2)
  · intro σ τ he
    exact Subtype.ext (congrArg (fun a : CompatibleReversePermutation hopt K r ↦ a.val)
      (e.injective (congrArg Subtype.val he)))
end MatchingEndpoints
theorem exists_singletonRotationAnchor_of_soleForwardExposed {p : Profile n}
    {μ₀ μ ρ : Matching n} (hopt : IsManOptimal p μ₀) (hμ : IsStable p μ)
    (hsole : IsSoleForwardExposedRotation p μ ρ) :
    ∃ r : Rotation p μ₀, (singletonRotationAnchor hopt r).val = μ ∧ r.val.cycle = ρ := by
  let r := rotationOfExposed hopt hμ hsole.1
  refine ⟨r, ?_, rfl⟩
  have hanchor := (eq_singletonRotationAnchor_iff hopt r ⟨μ, hμ⟩).mpr fun s ↦ by
    constructor
    · intro hs
      exact Subtype.ext (hs.2.symm.trans (congrArg (rotationLabel μ) (hsole.2 _ hs.1)))
    · rintro rfl
      exact ⟨hsole.1, rfl⟩
  exact (congrArg Subtype.val hanchor).symm
theorem markedFilteredChoices_endpoint_injective {x : ScoreProfile n}
    {μ₀ μ μ' ρ ρ' σ σ' : Matching n}
    {flag flag' : OffDiagonalCellIndex n → Bool} {K L L' : ℕ} {t t' : ℝ}
    (hopt : IsManOptimal (profileOfScores x) μ₀)
    (hμ : IsStable (profileOfScores x) μ) (hμ' : IsStable (profileOfScores x) μ')
    (hs : IsSoleForwardExposedRotation (profileOfScores x) μ ρ)
    (hs' : IsSoleForwardExposedRotation (profileOfScores x) μ' ρ')
    (hl : K < ρ.support.card) (hl' : K < ρ'.support.card)
    (hσ : σ ∈ markedFilteredChoices μ ρ flag K L t x)
    (hσ' : σ' ∈ markedFilteredChoices μ' ρ' flag' K L' t' x)
    (he : undoReverseRotation μ σ = undoReverseRotation μ' σ') :
    μ = μ' ∧ ρ = ρ' ∧ σ = σ' := by
  obtain ⟨r, hrμ, hrρ⟩ := exists_singletonRotationAnchor_of_soleForwardExposed hopt hμ hs
  obtain ⟨r', hrμ', hrρ'⟩ :=
    exists_singletonRotationAnchor_of_soleForwardExposed hopt hμ' hs'
  let a : CompatibleReversePermutation hopt K r :=
    ⟨σ, isCompatibleReversePermutation_of_mem_markedFilteredChoices hopt r hrμ hrρ hσ⟩
  let a' : CompatibleReversePermutation hopt K r' :=
    ⟨σ', isCompatibleReversePermutation_of_mem_markedFilteredChoices hopt r' hrμ' hrρ' hσ'⟩
  let q : LongPivot (profileOfScores x) μ₀ K :=
    ⟨r, by simpa only [rotationLength, hrρ] using hl⟩
  let q' : LongPivot (profileOfScores x) μ₀ K :=
    ⟨r', by simpa only [rotationLength, hrρ'] using hl'⟩
  let f := pivotDecorationEmbedding hopt K
  have hf : f ⟨q, compatibleReversePermutationToDecoration hopt K r a⟩ =
      f ⟨q', compatibleReversePermutationToDecoration hopt K r' a'⟩ := by
    apply Subtype.ext
    change (compatibleReversePermutationToDecoration hopt K r a).matching.val =
      (compatibleReversePermutationToDecoration hopt K r' a').matching.val
    rw [compatibleReversePermutationToDecoration_matching,
      compatibleReversePermutationToDecoration_matching, hrμ, hrμ']
    exact he
  have hr : r = r' :=
    congrArg (fun z : Σ s : LongPivot (profileOfScores x) μ₀ K, PivotDecoration hopt K s.val ↦
      z.1.val) (f.injective hf)
  have hm : μ = μ' :=
    hrμ.symm.trans ((congrArg (fun s ↦ (singletonRotationAnchor hopt s).val) hr).trans hrμ')
  refine ⟨hm, hrρ.symm.trans ((congrArg (fun s : Rotation (profileOfScores x) μ₀ ↦
    s.val.cycle) hr).trans hrρ'), ?_⟩
  rw [← hm] at he
  apply Equiv.ext
  intro w
  exact μ.symm.injective (by
    simpa only [undoReverseRotation_symm_apply] using
      congrArg (fun ν : Matching n ↦ ν.symm w) he)
theorem IsLocallyEligiblePivot.supportCap_lt {b A B κ : ℝ} {K : ℕ} {x : ScoreProfile n}
    {μ ρ : Matching n} (h : IsLocallyEligiblePivot b A B x μ ρ)
    (hn : 0 < n) (hκ : κ < b) (hK : (K : ℝ) ≤ κ * Real.sqrt (n : ℝ)) :
    K < ρ.support.card := by
  have hr : (K : ℝ) < (ρ.support.card : ℝ) :=
    hK.trans_lt ((mul_lt_mul_of_pos_right hκ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))).trans_le
      (LocalPivotGeometry.length_lower h.1))
  exact_mod_cast hr
end CompLP
end

-- PivotSharedReverse
section
open StableMarriage
namespace CompLP
variable {n : ℕ} {p : Profile n} {μ₀ μ ν : Matching n}
theorem reverseExposedRotationLabel_mem_earlier_iff_unchanged
    (hopt : IsManOptimal p μ₀) (hμ : IsStable p μ) (hν : IsStable p ν)
    (hle : MenWeaklyPrefer p μ ν)
    (σ : {σ : Equiv.Perm (Fin n) // IsReverseExposedRotation p ν σ})
    {w : Fin n} (hw : w ∈ σ.val.support) :
    reverseExposedRotationLabel hopt hν σ ∈ eliminatedRotations p μ₀ μ ↔
      μ.symm w = ν.symm w := by
  let r := reverseExposedRotationLabel hopt hν σ
  let m := ν.symm w
  have hm : r.val.cycle m ≠ m := by
    intro h
    change ν.symm (σ.val (ν m)) = m at h
    exact (Equiv.Perm.mem_support.mp hw) (by simpa [m] using congrArg ν h)
  have hnew : rotationLabelNewPartner r.val m = some (ν m) := by
    change rotationLabelNewPartner
      (rotationLabel (undoReverseRotation ν σ.val) (reverseRotationCycle ν.symm σ.val)) m = _
    have hm' : reverseRotationCycle ν.symm σ.val m ≠ m := hm
    rw [rotationLabelNewPartner_eq hm', eliminateRotation_undoReverseRotation]
  constructor
  · intro hr
    have hle' := (mem_eliminatedRotations_iff_newRank_le hopt hμ hm hnew).mp hr
    have he := (p.manRank m).injective (le_antisymm (hle m) hle')
    apply μ.injective
    simpa only [m, Equiv.apply_symm_apply] using he.symm
  · intro hsame
    by_contra hnot
    have hsub : eliminatedRotations p μ₀ μ ⊆
        eliminatedRotations p μ₀ (undoReverseRotation ν σ.val) := by
      rw [eliminatedRotations_undoReverseRotation hopt hν σ]
      intro s hs
      refine ⟨(eliminatedRotations_subset_iff hopt hμ hν).mpr hle hs, ?_⟩
      intro he
      exact hnot ((Set.mem_singleton_iff.mp he) ▸ hs)
    have hundo := σ.property.undo_stable hν
    obtain ⟨_, hpath⟩ := exists_rotationSequence_of_menWeaklyPrefer hμ hundo
      ((eliminatedRotations_subset_iff hopt hμ hundo).mp hsub)
    have hstrict : p.womanRank w (ν.symm w) <
        p.womanRank w ((undoReverseRotation ν σ.val).symm w) :=
      (IsSuccessor.eligible ((IsExposedRotation.successor σ.property) w (Equiv.Perm.mem_support.mp hw))).1
    exact hstrict.not_ge (by simpa only [hsame] using hpath.womanRank_end_le w)
theorem exists_realizedReverseRemovedLabel_mem_earlier_iff
    (hopt : IsManOptimal p μ₀) (hμ : IsStable p μ) (hν : IsStable p ν)
    (hle : MenWeaklyPrefer p μ ν) {σ : Matching n}
    (hσ : RealizesSuccessorPermutation (swapProfile p) ν.symm σ) :
    (∃ γ ∈ Subtype.val '' (↑(realizedReverseRemovedLabels hopt hν hσ) :
      Set (MaximalEliminatedRotation p μ₀ ν)),
      γ ∈ eliminatedRotations p μ₀ μ) ↔
    ∃ w ∈ σ.support, μ.symm w = ν.symm w := by
  classical
  constructor
  · rintro ⟨γ, ⟨a, ha, rfl⟩, hγ⟩
    change a ∈ realizedReverseRemovedLabels hopt hν hσ at ha
    rw [realizedReverseRemovedLabels] at ha
    obtain ⟨c, -, rfl⟩ := Finset.mem_map.mp ha
    let τ : {τ : Matching n // IsReverseExposedRotation p ν τ} :=
      ⟨c.val, realizesSuccessorPermutation_iff_factors.mp hσ c.val c.property⟩
    obtain ⟨w, hw⟩ := Finset.card_pos.mp
      ((by decide : 0 < 2).trans_le (IsExposedRotation.isCycle τ.property).two_le_card_support)
    exact ⟨w, Equiv.Perm.mem_cycleFactorsFinset_support_le c.property hw,
      (reverseExposedRotationLabel_mem_earlier_iff_unchanged hopt hμ hν hle τ hw).mp hγ⟩
  · rintro ⟨w, hw, hsame⟩
    obtain ⟨c, hc, hwc⟩ :=
      Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset.mp hw
    let τ : {τ : Matching n // IsReverseExposedRotation p ν τ} :=
      ⟨c, realizesSuccessorPermutation_iff_factors.mp hσ c hc⟩
    refine ⟨reverseExposedRotationLabel hopt hν τ,
      ⟨reverseExposedRotationEquivMaximal hopt hν τ, ?_, rfl⟩,
      (reverseExposedRotationLabel_mem_earlier_iff_unchanged hopt hμ hν hle τ hwc).mpr hsame⟩
    change reverseExposedRotationEquivMaximal hopt hν τ ∈
      realizedReverseRemovedLabels hopt hν hσ
    rw [realizedReverseRemovedLabels]
    exact Finset.mem_map.mpr ⟨⟨c, hc⟩, Finset.mem_attach _ _, rfl⟩
theorem menWeaklyPrefer_singletonRotationAnchor_iff
    (hopt : IsManOptimal p μ₀) (r s : Rotation p μ₀) :
    MenWeaklyPrefer p (singletonRotationAnchor hopt r).val (singletonRotationAnchor hopt s).val
      ↔ r ≤ s := by
  rw [← eliminatedRotations_subset_iff hopt (singletonRotationAnchor hopt r).property
      (singletonRotationAnchor hopt s).property,
    eliminatedRotations_singletonRotationAnchor, eliminatedRotations_singletonRotationAnchor]
  constructor
  · intro h
    by_contra hrs
    exact (h (show s ∈ (Set.Ici r)ᶜ from hrs)) (Set.mem_Ici.mpr le_rfl)
  · exact fun h _ ha hb ↦ ha (h.trans hb)
section MarkedChoices
variable {x : ScoreProfile n} {hopt : IsManOptimal (profileOfScores x) μ₀}
  {K L : ℕ} {t₁ t₂ : ℝ} {ρ η : Matching n}
  {flag₁ flag₂ : OffDiagonalCellIndex n → Bool}
theorem markedFilteredChoicesEmbedding_shared_iff
    (r s : Rotation (profileOfScores x) μ₀) (hμ : (singletonRotationAnchor hopt r).val = μ)
    (hν : (singletonRotationAnchor hopt s).val = ν) (hη : s.val.cycle = η)
    (hrs : r ≤ s) (ht₂ : 0 ≤ t₂)
    (τ : ↥(markedFilteredChoices ν η flag₂ K L t₂ x)) :
    (∃ γ ∈ (markedFilteredChoicesEmbedding hopt s hν hη ht₂ τ).val.removedLabels,
      γ ∈ eliminatedRotations (profileOfScores x) μ₀ μ) ↔
    ∃ w ∈ τ.val.support, μ.symm w = ν.symm w := by
  let A := singletonRotationAnchor hopt r
  let B := singletonRotationAnchor hopt s
  let hτ :=
    (isCompatibleReversePermutation_of_mem_markedFilteredChoices hopt s hν hη τ.property).1
  have hle := (menWeaklyPrefer_singletonRotationAnchor_iff hopt r s).mpr hrs
  have h := exists_realizedReverseRemovedLabel_mem_earlier_iff hopt A.property B.property hle hτ
  rw [← hμ]
  calc
    _ ↔ ∃ w ∈ τ.val.support, A.val.symm w = B.val.symm w := h
    _ ↔ _ := by
      dsimp only [A, B]
      rw [hν]
theorem markedFilteredChoicesEmbedding_matching
    (r : Rotation (profileOfScores x) μ₀) (hμ : (singletonRotationAnchor hopt r).val = μ)
    (hρ : r.val.cycle = ρ) (ht₁ : 0 ≤ t₁)
    (σ : ↥(markedFilteredChoices μ ρ flag₁ K L t₁ x)) :
    (markedFilteredChoicesEmbedding hopt r hμ hρ ht₁ σ).val.matching.val =
      undoReverseRotation μ σ.val := by
  let a : CompatibleReversePermutation hopt K r :=
    ⟨σ.val,
      isCompatibleReversePermutation_of_mem_markedFilteredChoices hopt r hμ hρ σ.property⟩
  change (compatibleReversePermutationToDecoration hopt K r a).matching.val = _
  rw [compatibleReversePermutationToDecoration_matching, hμ]
private noncomputable def residualPivotPairOfMarkedChoices
    (r s : LongPivot (profileOfScores x) μ₀ K) (hrs : r.val < s.val)
    (hμ : (singletonRotationAnchor hopt r.val).val = μ)
    (hν : (singletonRotationAnchor hopt s.val).val = ν)
    (hρ : r.val.val.cycle = ρ) (hη : s.val.val.cycle = η)
    (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂)
    (σ : ↥(markedFilteredChoices μ ρ flag₁ K L t₁ x))
    (τ : ↥(markedFilteredChoices ν η flag₂ K L t₂ x))
    (hw : ∃ w ∈ τ.val.support, μ.symm w = ν.symm w) :
    ResidualPivotPair hopt K :=
  ⟨⟨r, (markedFilteredChoicesEmbedding hopt r.val hμ hρ ht₁ σ).val⟩,
    ⟨s, (markedFilteredChoicesEmbedding hopt s.val hν hη ht₂ τ).val⟩, hrs, by
      rw [hμ]
      exact
        (markedFilteredChoicesEmbedding_shared_iff r.val s.val hμ hν hη hrs.le ht₂ τ).mpr hw⟩
end MarkedChoices
section GlobalMarkedPairs
variable {x : ScoreProfile n} {K L : ℕ}
  {flag : Matching n → Matching n → OffDiagonalCellIndex n → Bool}
  {t : Matching n → Matching n → ℝ}
private structure LongMarkedChoice (x : ScoreProfile n) (K L : ℕ)
    (flag : Matching n → Matching n → OffDiagonalCellIndex n → Bool)
    (t : Matching n → Matching n → ℝ) where
  anchor : Matching n
  cycle : Matching n
  reverse : Matching n
  stable : IsStable (profileOfScores x) anchor
  sole : IsSoleForwardExposedRotation (profileOfScores x) anchor cycle
  long : K < cycle.support.card
  cutoff_nonneg : 0 ≤ t anchor cycle
  mem_choices : reverse ∈
    markedFilteredChoices anchor cycle (flag anchor cycle) K L (t anchor cycle) x
namespace LongMarkedChoice
variable (a : LongMarkedChoice x K L flag t) (hopt : IsManOptimal (profileOfScores x) μ₀)
private noncomputable def pivot : LongPivot (profileOfScores x) μ₀ K := by
  let h := exists_singletonRotationAnchor_of_soleForwardExposed hopt a.stable a.sole
  exact ⟨Classical.choose h,
    by simpa only [rotationLength, (Classical.choose_spec h).2] using a.long⟩
theorem pivot_anchor : (singletonRotationAnchor hopt (a.pivot hopt).val).val = a.anchor :=
  (Classical.choose_spec
    (exists_singletonRotationAnchor_of_soleForwardExposed hopt a.stable a.sole)).1
theorem pivot_cycle : (a.pivot hopt).val.val.cycle = a.cycle :=
  (Classical.choose_spec
    (exists_singletonRotationAnchor_of_soleForwardExposed hopt a.stable a.sole)).2
theorem eq_of_endpoint_eq (hopt : IsManOptimal (profileOfScores x) μ₀)
    {a' : LongMarkedChoice x K L flag t}
    (h : undoReverseRotation a.anchor a.reverse = undoReverseRotation a'.anchor a'.reverse) :
    a = a' := by
  obtain ⟨ha, hc, hr⟩ := markedFilteredChoices_endpoint_injective hopt a.stable a'.stable
    a.sole a'.sole a.long a'.long a.mem_choices a'.mem_choices h
  cases a
  cases a'
  cases ha
  cases hc
  cases hr
  rfl
end LongMarkedChoice
private structure ResidualMarkedPair (x : ScoreProfile n) (K L : ℕ)
    (flag : Matching n → Matching n → OffDiagonalCellIndex n → Bool)
    (t : Matching n → Matching n → ℝ) where
  early : LongMarkedChoice x K L flag t
  late : LongMarkedChoice x K L flag t
  prefer : MenWeaklyPrefer (profileOfScores x) early.anchor late.anchor
  ne : early.anchor ≠ late.anchor
  shared : ∃ w ∈ late.reverse.support, early.anchor.symm w = late.anchor.symm w
namespace ResidualMarkedPair
variable (a : ResidualMarkedPair x K L flag t) (hopt : IsManOptimal (profileOfScores x) μ₀)
private theorem pivot_lt : (a.early.pivot hopt).val < (a.late.pivot hopt).val := by
  apply lt_of_le_of_ne
  · apply (menWeaklyPrefer_singletonRotationAnchor_iff hopt _ _).mp
    rw [a.early.pivot_anchor hopt, a.late.pivot_anchor hopt]
    exact a.prefer
  · intro h
    have heq := congrArg (fun s ↦ (singletonRotationAnchor hopt s).val) h
    exact a.ne ((a.early.pivot_anchor hopt).symm.trans (heq.trans (a.late.pivot_anchor hopt)))
private noncomputable def toResidualPivotPair : ResidualPivotPair hopt K :=
  residualPivotPairOfMarkedChoices (a.early.pivot hopt) (a.late.pivot hopt)
    (by exact a.pivot_lt hopt) (a.early.pivot_anchor hopt) (a.late.pivot_anchor hopt)
    (a.early.pivot_cycle hopt) (a.late.pivot_cycle hopt)
    a.early.cutoff_nonneg a.late.cutoff_nonneg
    ⟨a.early.reverse, a.early.mem_choices⟩ ⟨a.late.reverse, a.late.mem_choices⟩ a.shared
theorem toResidualPivotPair_early_endpoint :
    (a.toResidualPivotPair hopt).early.2.matching.val =
      undoReverseRotation a.early.anchor a.early.reverse :=
  markedFilteredChoicesEmbedding_matching (a.early.pivot hopt).val (a.early.pivot_anchor hopt)
    (a.early.pivot_cycle hopt) a.early.cutoff_nonneg ⟨a.early.reverse, a.early.mem_choices⟩
theorem toResidualPivotPair_late_endpoint :
    (a.toResidualPivotPair hopt).late.2.matching.val =
      undoReverseRotation a.late.anchor a.late.reverse :=
  markedFilteredChoicesEmbedding_matching (a.late.pivot hopt).val (a.late.pivot_anchor hopt)
    (a.late.pivot_cycle hopt) a.late.cutoff_nonneg ⟨a.late.reverse, a.late.mem_choices⟩
theorem toResidualPivotPair_toggledEarly_passesReverseFilters
    (hties : ∀ row, Function.Injective (x row)) :
    (a.toResidualPivotPair hopt).toggledEarly.2.PassesReverseFilters L
      (t a.early.anchor a.early.cycle) :=
  (a.toResidualPivotPair hopt).toggledEarly_passesReverseFilters L
    (fun _ ↦ t a.early.anchor a.early.cycle) hties
    (markedFilteredChoicesEmbedding hopt (a.early.pivot hopt).val (a.early.pivot_anchor hopt)
      (a.early.pivot_cycle hopt) a.early.cutoff_nonneg
      ⟨a.early.reverse, a.early.mem_choices⟩).property
theorem toResidualPivotPair_late_passesReverseFilters :
    (a.toResidualPivotPair hopt).late.2.PassesReverseFilters L
      (t a.late.anchor a.late.cycle) :=
  (markedFilteredChoicesEmbedding hopt (a.late.pivot hopt).val (a.late.pivot_anchor hopt)
    (a.late.pivot_cycle hopt) a.late.cutoff_nonneg
    ⟨a.late.reverse, a.late.mem_choices⟩).property
theorem toResidualPivotPair_injective (hopt : IsManOptimal (profileOfScores x) μ₀) :
    Function.Injective
      (fun a : ResidualMarkedPair x K L flag t ↦ a.toResidualPivotPair hopt) := by
  intro a a' h
  have he := congrArg (fun R : ResidualPivotPair hopt K ↦ R.early.2.matching.val) h
  have hl := congrArg (fun R : ResidualPivotPair hopt K ↦ R.late.2.matching.val) h
  dsimp only at he hl
  rw [a.toResidualPivotPair_early_endpoint hopt, a'.toResidualPivotPair_early_endpoint hopt] at he
  rw [a.toResidualPivotPair_late_endpoint hopt, a'.toResidualPivotPair_late_endpoint hopt] at hl
  have hae := a.early.eq_of_endpoint_eq hopt he
  have hal := a.late.eq_of_endpoint_eq hopt hl
  cases a
  cases a'
  cases hae
  cases hal
  rfl
theorem card_le_twice_incomparable_restrict (hopt : IsManOptimal (profileOfScores x) μ₀)
    {Q : IncomparableStableMatchingPair (profileOfScores x) μ₀ → Prop}
    (hQ : ∀ a : ResidualMarkedPair x K L flag t, Q (a.toResidualPivotPair hopt).toggleImage) :
    Nat.card (ResidualMarkedPair x K L flag t) ≤ 2 * Nat.card {MN // Q MN} := by
  let P (R : ResidualPivotPair hopt K) :=
    ∃ a : ResidualMarkedPair x K L flag t, a.toResidualPivotPair hopt = R
  let e (a : ResidualMarkedPair x K L flag t) : {R // P R} :=
    ⟨a.toResidualPivotPair hopt, ⟨a, rfl⟩⟩
  have he : Function.Injective e := fun _ _ h ↦
    toResidualPivotPair_injective hopt (congrArg Subtype.val h)
  refine (Nat.card_le_card_of_injective e he).trans
    (ResidualPivotPair.card_le_twice_incomparable_restrict ?_)
  rintro _ ⟨a, rfl⟩
  exact hQ a
end ResidualMarkedPair
end GlobalMarkedPairs
end CompLP
end

-- PivotResidualImageGeometry
section
open Filter MeasureTheory Set StableMarriage
open scoped Topology
namespace CompLP
variable {n : ℕ}
private def InResidualEndpointScoreDomain (x : ScoreProfile n) (μ : Matching n) : Prop :=
  (n : ℝ) ^ (1 / 10 : ℝ) ≤ femaleSpouseTotal x μ ∧
  femaleSpouseTotal x μ ≤ 2 * (n : ℝ) ^ (2 / 5 : ℝ) ∧
  (∀ w, femaleSpouseScore x μ w / femaleSpouseTotal x μ ≤ 2060 * Real.log n / n) ∧
  ∀ m, maleSpouseScore x μ m ≤ 16 * Real.log n / (n : ℝ) ^ (1 / 10 : ℝ)
theorem measurableSet_inResidualEndpointScoreDomain (μ : Matching n) :
    MeasurableSet {x : ScoreProfile n | InResidualEndpointScoreDomain x μ} := by
  unfold InResidualEndpointScoreDomain
  simp only [ofPred_and, ofPred_forall]
  exact (measurableSet_le measurable_const (measurable_femaleSpouseTotal μ)).inter <|
    (measurableSet_le (measurable_femaleSpouseTotal μ) measurable_const).inter <|
    (MeasurableSet.iInter fun w ↦ measurableSet_le
      ((measurable_femaleSpouseScore μ w).div (measurable_femaleSpouseTotal μ))
      measurable_const).inter <|
    MeasurableSet.iInter fun m ↦ measurableSet_le (measurable_maleSpouseScore μ m) measurable_const
theorem eventually_residualEndpointIncrementBudget (κ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ K : ℕ, (K : ℝ) ≤ κ * Real.sqrt (n : ℝ) →
      (K : ℝ) * (2048 * Real.log n / n) ≤ 1 := by
  have hlog := (((isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num)).const_mul_left
    (2048 * κ)).comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))).eventuallyLE
  filter_upwards [hlog, eventually_gt_atTop (0 : ℕ)] with n hlog hn K hK
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hlog₀ : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have habs : |2048 * κ * Real.log n| ≤ |(n : ℝ) ^ (1 / 2 : ℝ)| := hlog
  rw [← Real.sqrt_eq_rpow, abs_of_nonneg (Real.sqrt_nonneg _)] at habs
  have hbound := (le_abs_self _).trans habs
  calc
    _ ≤ (κ * Real.sqrt (n : ℝ)) * (2048 * Real.log n / n) :=
      mul_le_mul_of_nonneg_right hK (by positivity)
    _ = (Real.sqrt (n : ℝ) * (2048 * κ * Real.log n)) / n := by ring
    _ ≤ (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) / n :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg _)) hnR.le
    _ = _ := by rw [← pow_two, Real.sq_sqrt hnR.le, div_self hnR.ne']
theorem FilteredPivotDecoration.inResidualEndpointScoreDomain
    {x : ScoreProfile n} {μ₀ μ ρ : Matching n} {K L : ℕ} {b A B t : ℝ}
    {hopt : IsManOptimal (profileOfScores x) μ₀} {r : Rotation (profileOfScores x) μ₀}
    (D : FilteredPivotDecoration hopt K r L t)
    (hties : ∀ row, Function.Injective (x row)) (hn : 0 < n)
    (hK : (K : ℝ) * (2048 * Real.log n / n) ≤ 1)
    (hμ : (singletonRotationAnchor hopt r).val = μ)
    (ht : t = reverseIncrementCutoff n (maleSpouseTotal x μ))
    (hE : IsLocallyEligiblePivot b A B x μ ρ) :
    InResidualEndpointScoreDomain x D.val.matching.val := by
  let d := (splitScorePairs μ x).1
  let X := maleSpouseTotal x μ
  let Y := femaleSpouseTotal x μ
  let R : ℝ := (n : ℝ) ^ (1 / 10 : ℝ)
  have hX : reverseDiagonalMaleTotal d = X := reverseDiagonalMaleTotal_splitScorePairs μ x
  have hY : pivotDiagonalFemaleTotal d = Y := pivotDiagonalFemaleTotal_splitScorePairs μ x
  have hdiag (i : Fin n) :
      diagonalPairAt d i = (maleSpouseScore x μ i, femaleSpouseScore x μ (μ i)) := by
    rw [show d = (splitScorePairs μ x).1 from rfl, diagonalPairAt_splitScorePairs,
      femaleSpouseScore, maleSpouseScore, Equiv.symm_apply_apply]
  have hgeom := hE.1
  obtain ⟨hunit, hY2, hYhi, hXY, hshare, hmale⟩ := (LocalPivotGeometry.base hgeom)
  rw [hY] at hY2 hYhi hXY hshare hmale
  rw [hX] at hXY
  have hYlo := (LocalPivotGeometry.lower_band hgeom)
  change R ≤ pivotDiagonalFemaleTotal d at hYlo
  rw [hY] at hYlo
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hYpos : 0 < Y := lt_of_lt_of_le (by norm_num) hY2
  have hXpos : 0 < X := pos_of_mul_pos_left ((by positivity : 0 < (n : ℝ) / 128).trans_le hXY)
    hYpos.le
  have hRpos : 0 < R := Real.rpow_pos_of_pos hnR _
  have hnonneg (w : Fin n) : 0 ≤ femaleSpouseScore x μ w := by
    have hw := (hunit (μ.symm w)).2.1
    rwa [hdiag, Equiv.apply_symm_apply] at hw
  have ht₀ : 0 ≤ t := by
    rw [ht, reverseIncrementCutoff]
    exact div_nonneg (mul_nonneg (by norm_num) hlog) hXpos.le
  have htY : t ≤ (2048 * Real.log n / n) * Y := by
    rw [ht, reverseIncrementCutoff]
    apply (div_le_iff₀ hXpos).2
    calc
      16 * Real.log n = (2048 * Real.log n / n) * ((n : ℝ) / 128) := by
        field_simp
        ring
      _ ≤ (2048 * Real.log n / n) * (X * Y) :=
        mul_le_mul_of_nonneg_left hXY (div_nonneg (by positivity) hnR.le)
      _ = (2048 * Real.log n / n) * Y * X := by ring
  obtain ⟨hm, hYmove, hy⟩ := D.scoreGeometry hties ht₀
    (by rw [hμ]; exact hYpos) (by rw [hμ]; exact hnonneg) (by rw [hμ]; exact htY) hK
  rw [hμ] at hm hYmove hy
  refine ⟨hYlo.trans hYmove.1, hYmove.2.trans (mul_le_mul_of_nonneg_left hYhi (by norm_num)),
    ?_, ?_⟩
  · intro w
    have hs := hshare (μ.symm w)
    rw [hdiag, Equiv.apply_symm_apply] at hs
    change femaleSpouseScore x μ w / femaleSpouseTotal x μ ≤ _ at hs
    exact (hy w).trans (by
      calc
        _ ≤ 12 * Real.log n / n + 2048 * Real.log n / n := add_le_add hs le_rfl
        _ = _ := by ring)
  · intro m
    have hs := hmale m
    rw [hdiag] at hs
    exact (hm m).trans (hs.trans (by
      have hhalf : R / 2 ≤ Y - 1 := by linarith only [hY2, hYlo]
      calc
        _ ≤ 8 * Real.log n / (R / 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hhalf
        _ = _ := by ring))
private def worsePartnerMen (p : Profile n) (μ ν : Matching n) : Finset (Fin n) :=
  Finset.univ.filter fun m ↦ p.manRank m (ν m) < p.manRank m (μ m)
private def relativeMenPermutation (μ ν : Matching n) : Matching n := μ.trans ν.symm
theorem union_worsePartnerMen_eq_support (p : Profile n) (μ ν : Matching n) :
    worsePartnerMen p μ ν ∪ worsePartnerMen p ν μ = (relativeMenPermutation μ ν).support := by
  ext m
  simp only [worsePartnerMen, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
    Equiv.Perm.mem_support, relativeMenPermutation, Equiv.trans_apply, ← ne_iff_lt_or_gt]
  rw [(p.manRank m).injective.ne_iff]
  exact ne_comm.trans (not_congr ν.symm_apply_eq).symm
private noncomputable def exposedShortCycles (p : Profile n) (ν : Matching n) (L : ℕ) :
    Finset (Matching n) := by
  classical
  exact Finset.univ.filter fun c ↦ IsExposedRotation p ν c ∧ c.support.card ≤ L
theorem FilteredPivotDecoration.exposedShortCycles_card_le
    {x : ScoreProfile n} {μ₀ : Matching n} {K L : ℕ} {t : ℝ}
    {hopt : IsManOptimal (profileOfScores x) μ₀} {r : Rotation (profileOfScores x) μ₀}
    (D : FilteredPivotDecoration hopt K r L t) (hL : L ≤ K) (hr : K < rotationLength r) :
    ((exposedShortCycles (profileOfScores x) D.val.matching.val L).card : ℝ) ≤
      (3 / 2 : ℝ) * Real.log L := by
  classical
  let f (c : ↥(exposedShortCycles (profileOfScores x) D.val.matching.val L)) :
      {s : Rotation (profileOfScores x) μ₀ //
        s.IsExposedAt D.val.matching.val ∧ rotationLength s ≤ L} :=
    let hc := (Finset.mem_filter.mp c.property).2
    ⟨rotationOfExposed hopt D.val.matching.property hc.1, ⟨hc.1, rfl⟩, hc.2⟩
  have hf : Function.Injective f := fun _ _ h ↦
    Subtype.ext (congrArg (fun s ↦ s.val.val.cycle) h)
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_finsetCard] at hcard
  exact (Nat.cast_le.mpr hcard).trans (D.shortExposed_card_le hL hr)
private structure IsResidualPairRankGeometry (b : ℝ) (K L : ℕ) (p : Profile n)
    (μ ν : Matching n) : Prop where
  stable_early : IsStable p μ
  stable_late : IsStable p ν
  short_nonempty : (worsePartnerMen p μ ν).Nonempty
  long_nonempty : (worsePartnerMen p ν μ).Nonempty
  short_size : (worsePartnerMen p μ ν).card ≤ K
  long_size : b * Real.sqrt (n : ℝ) ≤ ((worsePartnerMen p ν μ).card : ℝ)
  cycle_partition : ∀ c ∈ (relativeMenPermutation μ ν).cycleFactorsFinset,
    (c.support ⊆ worsePartnerMen p μ ν ∧ IsExposedRotation p ν c) ∨
      c.support ⊆ worsePartnerMen p ν μ
  short_exposure_cap : ((exposedShortCycles p ν L).card : ℝ) ≤ (3 / 2 : ℝ) * Real.log L
theorem IsResidualPairRankGeometry.self_ {n : ℕ} {b : ℝ} {K L : ℕ} {p : Profile n} {μ ν : Matching n} (h : IsResidualPairRankGeometry b K L p μ ν) : IsResidualPairRankGeometry b K L p μ ν := h
namespace IsResidualPairRankGeometry
variable {b : ℝ} {K L : ℕ} {p : Profile n} {μ ν : Matching n}
end IsResidualPairRankGeometry
private structure IsResidualPairGeometry (b : ℝ) (K L : ℕ) (x : ScoreProfile n)
    (μ ν : Matching n) : Prop where
  rank : IsResidualPairRankGeometry b K L (profileOfScores x) μ ν
  early_scores : InResidualEndpointScoreDomain x μ
  late_scores : InResidualEndpointScoreDomain x ν
theorem IsResidualPairGeometry.self_ {n : ℕ} {b : ℝ} {K L : ℕ} {x : ScoreProfile n} {μ ν : Matching n} (h : IsResidualPairGeometry b K L x μ ν) : IsResidualPairGeometry b K L x μ ν := h
theorem measurableSet_isResidualPairGeometry (b : ℝ) (K L : ℕ) (μ ν : Matching n) :
    MeasurableSet {x : ScoreProfile n | IsResidualPairGeometry b K L x μ ν} := by
  have h : MeasurableSet {x : ScoreProfile n |
      IsResidualPairRankGeometry b K L (profileOfScores x) μ ν} :=
    measurable_profileOfScores n (MeasurableSet.of_discrete :
      MeasurableSet {p : Profile n | IsResidualPairRankGeometry b K L p μ ν})
  exact (h.inter ((measurableSet_inResidualEndpointScoreDomain μ).inter
    (measurableSet_inResidualEndpointScoreDomain ν))).congr (Set.ext fun _ ↦
      ⟨fun h ↦ ⟨h.1, h.2.1, h.2.2⟩, fun h ↦ ⟨h.rank, h.early_scores, h.late_scores⟩⟩)
namespace ResidualPivotPair
variable {p : Profile n} {μ₀ : Matching n} {K : ℕ} {hopt : IsManOptimal p μ₀}
private theorem orientations_nonempty (R : ResidualPivotPair hopt K) :
    R.shortOrientationMen.Nonempty ∧ R.longOrientationMen.Nonempty := by
  let A := R.toggledEarly.2.matching
  let B := R.late.2.matching
  constructor
  · by_contra hn
    apply R.toggleImage.property.1
    apply (eliminatedRotations_subset_iff hopt A.property B.property).mpr
    intro m
    exact le_of_not_gt fun hm ↦ hn ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩⟩
  · by_contra hn
    apply R.toggleImage.property.2
    apply (eliminatedRotations_subset_iff hopt B.property A.property).mpr
    intro m
    exact le_of_not_gt fun hm ↦ hn ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩⟩
theorem cycle_partition (R : ResidualPivotPair hopt K)
    {c : Matching n} (hc : c ∈ R.relativePermutation.cycleFactorsFinset) :
    (c.support ⊆ R.shortOrientationMen ∧ IsExposedRotation p R.late.2.matching.val c) ∨
      c.support ⊆ R.longOrientationMen := by
  classical
  by_cases h : ∃ m ∈ c.support, m ∈ R.shortOrientationMen
  · obtain ⟨m, hm, hshort⟩ := h
    obtain ⟨s, hs, rfl⟩ := R.exists_shortLabel_of_cycleFactor hc hm hshort
    have hs' : s ∈ eliminatedRotations p μ₀ R.toggledEarly.2.matching.val \
        eliminatedRotations p μ₀ R.late.2.matching.val :=
      R.coe_shortOrientationLabels ▸ (Finset.mem_coe.mpr hs)
    have he := (R.isExposedAt_late_of_mem_toggle_early_ideal_diff_late hs').1
    refine Or.inl ⟨fun m hm ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, he⟩
    have hmove := Equiv.Perm.mem_support.mp hm
    have hp := R.relativePermutation_apply_of_mem_shortLabel hs hmove
    have heq : eliminateRotation R.late.2.matching.val s.val.cycle m =
        R.toggledEarly.2.matching.val m := by
      rw [eliminateRotation_apply, ← hp]
      exact R.late.2.matching.val.apply_symm_apply _
    exact heq ▸ he.manRank_lt_eliminate_of_moved hmove
  · right
    intro m hm
    have hs := Equiv.Perm.mem_cycleFactorsFinset_support_le hc hm
    change m ∈ (relativeMenPermutation R.toggledEarly.2.matching.val
      R.late.2.matching.val).support at hs
    rw [← union_worsePartnerMen_eq_support p R.toggledEarly.2.matching.val
      R.late.2.matching.val] at hs
    exact (Finset.mem_union.mp hs).resolve_left fun hms ↦ h ⟨m, hm, hms⟩
end ResidualPivotPair
namespace ResidualMarkedPair
variable {x : ScoreProfile n} {μ₀ : Matching n} {K L : ℕ}
  {flag : Matching n → Matching n → OffDiagonalCellIndex n → Bool}
  {t : Matching n → Matching n → ℝ}
theorem toggleImage_geometry (a : ResidualMarkedPair x K L flag t)
    (hopt : IsManOptimal (profileOfScores x) μ₀)
    (hties : ∀ row, Function.Injective (x row)) (hn : 0 < n) (hL : L ≤ K)
    (hK : (K : ℝ) * (2048 * Real.log n / n) ≤ 1)
    (ht : ∀ μ ρ, t μ ρ = reverseIncrementCutoff n (maleSpouseTotal x μ))
    {b A B : ℝ}
    (hEarly : IsLocallyEligiblePivot b A B x a.early.anchor a.early.cycle)
    (hLate : IsLocallyEligiblePivot b A B x a.late.anchor a.late.cycle) :
    IsResidualPairGeometry b K L x (a.toResidualPivotPair hopt).toggleImage.val.1.val
      (a.toResidualPivotPair hopt).toggleImage.val.2.val := by
  let R := a.toResidualPivotPair hopt
  let D₁ : FilteredPivotDecoration hopt K R.early.1.val L (t a.early.anchor a.early.cycle) :=
    ⟨R.toggledEarly.2, a.toResidualPivotPair_toggledEarly_passesReverseFilters hopt hties⟩
  let D₂ : FilteredPivotDecoration hopt K R.late.1.val L (t a.late.anchor a.late.cycle) :=
    ⟨R.late.2, a.toResidualPivotPair_late_passesReverseFilters hopt⟩
  refine ⟨⟨D₁.val.matching.property, D₂.val.matching.property,
    R.orientations_nonempty.1, R.orientations_nonempty.2, R.card_shortOrientationMen_le,
    ?_, fun c hc ↦ R.cycle_partition hc, D₂.exposedShortCycles_card_le hL R.late.1.property⟩,
    D₁.inResidualEndpointScoreDomain hties hn hK (a.early.pivot_anchor hopt) (ht _ _) hEarly,
    D₂.inResidualEndpointScoreDomain hties hn hK (a.late.pivot_anchor hopt) (ht _ _) hLate⟩
  have hlen : a.early.cycle.support.card ≤ R.longOrientationMen.card := by
    have h := R.rotationLength_early_le_card_longOrientationMen
    change rotationLength (a.early.pivot hopt).val ≤ _ at h
    simpa only [rotationLength, a.early.pivot_cycle hopt] using h
  exact hEarly.1.length_lower.trans (Nat.cast_le.mpr hlen)
end ResidualMarkedPair
end CompLP
end

-- DeferredAcceptanceTranscript
section
open StableMarriage
open scoped BigOperators
namespace CompLP
private structure DAState (n : ℕ) where
  
  count : Fin n → ℕ
  
  held : Fin n → Option (Fin n)
namespace DAState
variable {n : ℕ}
private def Free (s : DAState n) (m : Fin n) : Prop := ∀ w, s.held w ≠ some m
private def initial (n : ℕ) : DAState n := ⟨fun _ ↦ 0, fun _ ↦ none⟩
private def proposalTarget (rank : Fin n → Equiv.Perm (Fin n)) (s : DAState n)
    (m : Fin n) (h : s.count m < n) : Fin n := (rank m).symm ⟨s.count m, h⟩
private def chosenHolder (s : DAState n) (m w : Fin n) (accept : Bool) : Fin n :=
  if accept then m else (s.held w).getD m
private def applyDecision (s : DAState n) (m w : Fin n) (accept : Bool) : DAState n :=
  ⟨Function.update s.count m (s.count m + 1),
    Function.update s.held w (some (s.chosenHolder m w accept))⟩
private def proposalAccepted (p : Profile n) (s : DAState n) (m w : Fin n) : Bool :=
  (s.held w).elim true fun a ↦ decide (p.womanRank w m < p.womanRank w a)
private structure Valid (p : Profile n) (s : DAState n) : Prop where
  count_le : ∀ m, s.count m ≤ n
  held_unique : ∀ {u v m}, s.held u = some m → s.held v = some m → u = v
  held_last : ∀ {w m}, s.held w = some m → (p.manRank m w).val + 1 = s.count m
  preferred_holder : ∀ {m w}, (p.manRank m w).val < s.count m →
    ∃ a, s.held w = some a ∧ p.womanRank w a ≤ p.womanRank w m
  not_rejected : ∀ (ν : Matching n), IsStable p ν → ∀ m,
    (p.manRank m (ν m)).val < s.count m → s.held (ν m) = some m
theorem initial_valid (p : Profile n) : Valid p (initial n) := by
  constructor
  · simp [initial]
  · simp [initial]
  · simp [initial]
  · simp [initial]
  · simp [initial]
private theorem chosenHolder_spec (p : Profile n) (s : DAState n) (m w : Fin n) :
    let b := s.chosenHolder m w (proposalAccepted p s m w)
    (b = m ∨ s.held w = some b) ∧ p.womanRank w b ≤ p.womanRank w m ∧
      ∀ a, s.held w = some a → p.womanRank w b ≤ p.womanRank w a := by
  cases h : s.held w with
  | none => simp [chosenHolder, proposalAccepted, h]
  | some a =>
    by_cases ha : p.womanRank w m < p.womanRank w a
    · simp [chosenHolder, proposalAccepted, h, ha, ha.le]
    · simp [chosenHolder, proposalAccepted, h, ha, le_of_not_gt ha]
theorem Valid.apply_proposal {p : Profile n} {s : DAState n}
    (hs : Valid p s) {m w : Fin n} (hm : s.Free m)
    (hnew : (p.manRank m w).val = s.count m) :
    Valid p (s.applyDecision m w (proposalAccepted p s m w)) := by
  let b := s.chosenHolder m w (proposalAccepted p s m w)
  let t := s.applyDecision m w (proposalAccepted p s m w)
  have hspec : (b = m ∨ s.held w = some b) ∧
      p.womanRank w b ≤ p.womanRank w m ∧
      ∀ a, s.held w = some a → p.womanRank w b ≤ p.womanRank w a :=
    chosenHolder_spec p s m w
  have htCount : t.count m = s.count m + 1 := by simp [t, applyDecision]
  have htCount' {i : Fin n} (hi : i ≠ m) : t.count i = s.count i := by
    simp [t, applyDecision, hi]
  have htHeld : t.held w = some b := by simp [t, b, applyDecision]
  have htHeld' {v : Fin n} (hv : v ≠ w) : t.held v = s.held v := by
    simp [t, applyDecision, hv]
  have hsHeld_ne {v i : Fin n} (hi : s.held v = some i) : i ≠ m := by
    rintro rfl
    exact hm v hi
  have no_other_hold {v : Fin n} (hv : v ≠ w) (h : s.held v = some b) : False := by
    rcases hspec.1 with hbm | hbw
    · exact hm v (hbm ▸ h)
    · exact hv (hs.held_unique h hbw)
  have old_proposal {i v : Fin n} (hv : v ≠ w)
      (hi : (p.manRank i v).val < t.count i) : (p.manRank i v).val < s.count i := by
    by_cases him : i = m
    · subst i
      rw [htCount, ← hnew] at hi
      have hne : (p.manRank m v).val ≠ (p.manRank m w).val :=
        fun h ↦ hv ((p.manRank m).injective (Fin.ext h))
      rw [← hnew]
      omega
    · exact htCount' him ▸ hi
  have winner_prefers {ν : Matching n} (hν : IsStable p ν) :
      p.manRank b w ≤ p.manRank b (ν b) := by
    by_contra! hlt
    have hlt' : (p.manRank b (ν b)).val < (p.manRank b w).val := hlt
    rcases hspec.1 with hbm | hbw
    · rw [hbm, hnew] at hlt'
      exact hm (ν m) (hs.not_rejected ν hν m hlt')
    · have hp : (p.manRank b (ν b)).val < s.count b := by
        have := hs.held_last hbw
        omega
      have heq := hs.held_unique (hs.not_rejected ν hν b hp) hbw
      exact (not_lt_of_ge (le_of_eq (congrArg (p.manRank b) heq.symm))) hlt
  have proposed_dominance {i : Fin n} (hi : (p.manRank i w).val < t.count i) :
      p.womanRank w b ≤ p.womanRank w i := by
    by_cases him : i = m
    · exact him ▸ hspec.2.1
    · have hprop : (p.manRank i w).val < s.count i := htCount' him ▸ hi
      obtain ⟨a, ha, hpref⟩ := hs.preferred_holder hprop
      exact (hspec.2.2 a ha).trans hpref
  change Valid p t
  constructor
  · intro i
    by_cases h : i = m
    · subst i
      rw [htCount, ← hnew]
      exact Nat.succ_le_of_lt (p.manRank m w).isLt
    · exact (htCount' h).trans_le (hs.count_le i)
  · intro u v i hu hv
    by_cases huw : u = w
    · subst u
      have hbi : b = i := Option.some.inj (htHeld.symm.trans hu)
      subst i
      by_contra hvw
      exact no_other_hold (Ne.symm hvw) ((htHeld' (Ne.symm hvw)).symm.trans hv)
    · by_cases hvw : v = w
      · subst v
        have hbi : b = i := Option.some.inj (htHeld.symm.trans hv)
        subst i
        exact False.elim (no_other_hold huw ((htHeld' huw).symm.trans hu))
      · exact hs.held_unique ((htHeld' huw).symm.trans hu) ((htHeld' hvw).symm.trans hv)
  · intro v i hvi
    by_cases hv : v = w
    · subst v
      have hbi : b = i := Option.some.inj (htHeld.symm.trans hvi)
      subst i
      rcases hspec.1 with hbm | hbw
      · rw [hbm, htCount, hnew]
      · exact (hs.held_last hbw).trans (htCount' (hsHeld_ne hbw)).symm
    · have h := (htHeld' hv).symm.trans hvi
      exact (hs.held_last h).trans (htCount' (hsHeld_ne h)).symm
  · intro i v hi
    by_cases hv : v = w
    · subst v
      exact ⟨b, htHeld, proposed_dominance hi⟩
    · obtain ⟨a, ha, hle⟩ := hs.preferred_holder (old_proposal hv hi)
      exact ⟨a, (htHeld' hv).trans ha, hle⟩
  · intro ν hν i hi
    by_cases hw : ν i = w
    · rw [hw] at hi ⊢
      by_contra h
      have hbi : b ≠ i := fun e ↦ h (e ▸ htHeld)
      have hbν : ν b ≠ w := fun e ↦ hbi (ν.injective (e.trans hw.symm))
      have hbPref : p.manRank b w < p.manRank b (ν b) :=
        lt_of_le_of_ne (winner_prefers hν) fun e ↦ hbν ((p.manRank b).injective e).symm
      have hwPref : p.womanRank w b < p.womanRank w (ν.symm w) := by
        rw [← hw, ν.symm_apply_apply, hw]
        exact lt_of_le_of_ne (proposed_dominance hi) fun e ↦ hbi ((p.womanRank w).injective e)
      exact hν b w ⟨hbν, hbPref, hwPref⟩
    · exact (htHeld' hw).trans (hs.not_rejected ν hν i (old_proposal hw hi))
theorem Valid.free_count_lt {p : Profile n} {s : DAState n} (hs : Valid p s)
    {m : Fin n} (hm : s.Free m) : s.count m < n := by
  classical
  by_contra! h
  have hheld (w : Fin n) : ∃ a, s.held w = some a := by
    obtain ⟨a, ha, _⟩ := hs.preferred_holder ((p.manRank m w).isLt.trans_le h)
    exact ⟨a, ha⟩
  let holder (w : Fin n) := Classical.choose (hheld w)
  have hholder (w : Fin n) : s.held w = some (holder w) := Classical.choose_spec (hheld w)
  have hi : Function.Injective holder := fun u v huv ↦
    hs.held_unique (hholder u) (by rw [huv]; exact hholder v)
  obtain ⟨w, hw⟩ := Finite.surjective_of_injective hi m
  exact hm w (hw ▸ hholder w)
private def Complete (s : DAState n) : Prop := ∀ m, ∃ w, s.held w = some m
private noncomputable def toMatching (s : DAState n) (hc : s.Complete) : Matching n := by
  let wife (m : Fin n) := Classical.choose (hc m)
  have hw (m : Fin n) : s.held (wife m) = some m := Classical.choose_spec (hc m)
  have hi : Function.Injective wife := by
    intro m a h
    exact Option.some.inj ((hw m).symm.trans (h ▸ hw a))
  exact Equiv.ofBijective wife ⟨hi, Finite.surjective_of_injective hi⟩
private def readyMen (s : DAState n) : Finset (Fin n) :=
  Finset.univ.filter fun m ↦ (∀ w, s.held w ≠ some m) ∧ s.count m < n
theorem mem_readyMen {s : DAState n} {m : Fin n} :
    m ∈ s.readyMen ↔ s.Free m ∧ s.count m < n := by
  simp [readyMen, Free]
private def nextProposal (rank : Fin n → Equiv.Perm (Fin n)) (s : DAState n) :
    Option (Fin n × Fin n) :=
  if h : s.readyMen.Nonempty then
    let m := s.readyMen.min' h
    let hm := mem_readyMen.mp (Finset.min'_mem _ h)
    some (m, s.proposalTarget rank m hm.2)
  else none
theorem nextProposal_some {rank : Fin n → Equiv.Perm (Fin n)} {s : DAState n}
    {m w : Fin n} (h : s.nextProposal rank = some (m, w)) :
    s.Free m ∧ (rank m w).val = s.count m := by
  unfold nextProposal at h
  split at h
  · rename_i hne
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨(mem_readyMen.mp (Finset.min'_mem _ hne)).1, by simp [proposalTarget]⟩
  · contradiction
theorem Valid.complete_of_nextProposal_none {p : Profile n} {s : DAState n}
    (hs : Valid p s) (hd : s.nextProposal p.manRank = none) : s.Complete := by
  classical
  intro m
  by_contra! hm
  have hfree : s.Free m := hm
  have hne : s.readyMen.Nonempty := ⟨m, mem_readyMen.mpr ⟨hfree, hs.free_count_lt hfree⟩⟩
  simp [nextProposal, hne] at hd
private def advance (p : Profile n) (s : DAState n) : DAState n :=
  match s.nextProposal p.manRank with
  | none => s
  | some (m, w) => s.applyDecision m w (proposalAccepted p s m w)
theorem Valid.advance {p : Profile n} {s : DAState n} (hs : Valid p s) :
    Valid p (advance p s) := by
  cases h : s.nextProposal p.manRank with
  | none => simpa only [DAState.advance, h] using hs
  | some a =>
    obtain ⟨m, w⟩ := a
    have hp := nextProposal_some h
    simpa only [DAState.advance, h] using hs.apply_proposal hp.1 hp.2
private def proposalCount (s : DAState n) : ℕ := ∑ m, s.count m
private theorem proposalCount_applyDecision (s : DAState n) (m w : Fin n) (accept : Bool) :
    (s.applyDecision m w accept).proposalCount = s.proposalCount + 1 := by
  let t := s.applyDecision m w accept
  have hm : m ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
  have he :
      ∑ i ∈ Finset.univ.erase m, t.count i = ∑ i ∈ Finset.univ.erase m, s.count i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [t, applyDecision, (Finset.mem_erase.mp hi).1]
  change t.proposalCount = _
  unfold proposalCount
  rw [← Finset.sum_erase_add _ t.count hm, ← Finset.sum_erase_add _ s.count hm, he]
  simp [t, applyDecision, add_assoc]
theorem proposalCount_advance_of_some {p : Profile n} {s : DAState n} {a : Fin n × Fin n}
    (h : s.nextProposal p.manRank = some a) :
    (advance p s).proposalCount = s.proposalCount + 1 := by
  obtain ⟨m, w⟩ := a
  rw [advance, h]
  exact proposalCount_applyDecision s m w _
theorem Valid.proposalCount_le {p : Profile n} {s : DAState n} (hs : Valid p s) :
    s.proposalCount ≤ n * n := by
  calc
    _ ≤ ∑ _ : Fin n, n := Finset.sum_le_sum fun m _ ↦ hs.count_le m
    _ = _ := by simp
private def run (p : Profile n) : ℕ → DAState n
  | 0 => initial n
  | k + 1 => advance p (run p k)
theorem valid_run (p : Profile n) (k : ℕ) : Valid p (run p k) := by
  induction k with
  | zero => exact initial_valid p
  | succ k ih => exact ih.advance
private theorem le_proposalCount_run_of_next {p : Profile n} {k : ℕ}
    (h : (run p k).nextProposal p.manRank ≠ none) : k ≤ (run p k).proposalCount := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    cases hprev : (run p k).nextProposal p.manRank with
    | none =>
      have he : run p (k + 1) = run p k := by simp only [run, advance, hprev]
      exact False.elim (h (he ▸ hprev))
    | some a =>
      have hcount := proposalCount_advance_of_some hprev
      change k + 1 ≤ (advance p (run p k)).proposalCount
      rw [hcount]
      exact Nat.succ_le_succ (ih (by rw [hprev]; exact Option.some_ne_none _))
theorem nextProposal_run_sq_eq_none (p : Profile n) :
    (run p (n * n)).nextProposal p.manRank = none := by
  cases h : (run p (n * n)).nextProposal p.manRank with
  | none => rfl
  | some a =>
    have hl := le_proposalCount_run_of_next (p := p) (k := n * n)
      (by rw [h]; exact Option.some_ne_none _)
    have hu := (valid_run p (n * n + 1)).proposalCount_le
    change (advance p (run p (n * n))).proposalCount ≤ n * n at hu
    rw [proposalCount_advance_of_some h] at hu
    omega
theorem complete_run_sq (p : Profile n) : (run p (n * n)).Complete :=
  (valid_run p (n * n)).complete_of_nextProposal_none (nextProposal_run_sq_eq_none p)
private noncomputable def matching (p : Profile n) : Matching n :=
  (run p (n * n)).toMatching (complete_run_sq p)
end DAState
end CompLP
end

-- DAStreamSimulation
section
open StableMarriage
namespace CompLP
private structure DAStreamState (n : ℕ) where
  da : DAState n
  observed : Fin n → List (Fin n)
namespace DAStreamState
variable {n T : ℕ}
private def initial (n : ℕ) : DAStreamState n := ⟨DAState.initial n, fun _ ↦ []⟩
end DAStreamState
end CompLP
end

-- CycleSupportCount
section
open Equiv.Perm Finset
open scoped BigOperators Classical
namespace CompLP
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end CompLP
end

-- PivotAggregateMean
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology
namespace CompLP
variable {n : ℕ}
private noncomputable def pivotDecorationSupportCap (κ : ℝ) (n : ℕ) : ℕ :=
  ⌊κ * Real.sqrt (n : ℝ)⌋₊
theorem eventually_pivotDecorationSupportCap_bounds {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ pivotDecorationSupportCap κ n ∧
      (pivotDecorationSupportCap κ n : ℝ) ≤ κ * Real.sqrt (n : ℝ) ∧
      κ * Real.sqrt (n : ℝ) / 2 ≤ ((pivotDecorationSupportCap κ n - 1 : ℕ) : ℝ) := by
  have ht : Tendsto (fun n : ℕ ↦ κ * Real.sqrt (n : ℝ)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hκ
  filter_upwards [ht.eventually_ge_atTop 4] with n hn
  let t := κ * Real.sqrt (n : ℝ)
  let K := pivotDecorationSupportCap κ n
  change 4 ≤ t at hn
  have hK : t < (K : ℝ) + 1 := Nat.lt_floor_add_one t
  have hK' : (K : ℝ) ≤ t := Nat.floor_le (by positivity)
  have h₂ : 2 ≤ K := by
    exact_mod_cast (show (2 : ℝ) ≤ K by linarith)
  refine ⟨h₂, hK', ?_⟩
  rw [Nat.cast_sub (by omega : 1 ≤ K)]
  push_cast
  linarith
end CompLP
end

-- PivotDecorationRevealInvariance
section
open MeasureTheory Set StableMarriage
namespace CompLP
variable {n : ℕ} {μ ρ σ : Matching n} {x y : ScoreProfile n}
  {flag : OffDiagonalCellIndex n → Bool}
private structure SameReverseReveal (μ : Matching n) (flag : OffDiagonalCellIndex n → Bool)
    (x y : ScoreProfile n) : Prop where
  diagonal : (splitScorePairs μ x).1 = (splitScorePairs μ y).1
  observed : forwardRevealWithColumns flag (splitScorePairs μ x).2 =
    forwardRevealWithColumns flag (splitScorePairs μ y).2
theorem SameReverseReveal.symm (h : SameReverseReveal μ flag x y) :
    SameReverseReveal μ flag y x := ⟨h.diagonal.symm, h.observed.symm⟩
end CompLP
end

-- PivotLaterRevealReplay
section
open MeasureTheory Set StableMarriage
namespace CompLP
variable {n : ℕ}
private def ScoreForwardEligible (x : ScoreProfile n) (A : Matching n) (m w : Fin n) : Prop :=
  x (.inl m) (A m) < x (.inl m) w ∧ x (.inr w) m < x (.inr w) (A.symm w)
private def ScorePairAgrees (x y : ScoreProfile n) (m w : Fin n) : Prop :=
  x (.inl m) w = y (.inl m) w ∧ x (.inr w) m = y (.inr w) m
private structure FullForwardRevealAgrees (x y : ScoreProfile n) (A : Matching n) : Prop where
  spouse : ∀ m, ScorePairAgrees x y m (A m)
  eligible_iff : ∀ m w, ScoreForwardEligible x A m w ↔ ScoreForwardEligible y A m w
  cell : ∀ m w, ScoreForwardEligible x A m w → ScorePairAgrees x y m w
variable {x y : ScoreProfile n} {A B : Matching n}
theorem FullForwardRevealAgrees.symm (h : FullForwardRevealAgrees x y A) :
    FullForwardRevealAgrees y x A where
  spouse m := ⟨(h.spouse m).1.symm, (h.spouse m).2.symm⟩
  eligible_iff m w := (h.eligible_iff m w).symm
  cell m w hw :=
    let hc := h.cell m w ((h.eligible_iff m w).mpr hw)
    ⟨hc.1.symm, hc.2.symm⟩
end CompLP
end

-- PivotMovedCenteredTest
section
open Filter MeasureTheory Set StableMarriage
namespace CompLP
variable {n : ℕ}
private def IsStrictLaterStable (x : ScoreProfile n) (μ ν : Matching n) : Prop :=
  IsScoreStable x ν ∧ μ ≠ ν ∧ MenWeaklyPrefer (profileOfScores x) μ ν
theorem measurableSet_isStrictLaterStable (μ ν : Matching n) :
    MeasurableSet {x : ScoreProfile n | IsStrictLaterStable x μ ν} :=
  (measurableSet_isScoreStable ν).inter ((MeasurableSet.const _).inter
    (measurable_profileOfScores n (MeasurableSet.of_discrete :
      MeasurableSet {p : Profile n | MenWeaklyPrefer p μ ν})))
private noncomputable def markedMovedChoices (μ ν σ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (K L : ℕ) (t : ℝ) (x : ScoreProfile n) :
    Finset (Matching n) := by
  classical
  exact (markedFilteredChoices ν σ flag K L t x).filter
    (fun τ ↦ ∀ w ∈ τ.support, ν.symm w ≠ μ.symm w)
theorem mem_markedMovedChoices {μ ν σ τ : Matching n} {flag : OffDiagonalCellIndex n → Bool}
    {K L : ℕ} {t : ℝ} {x : ScoreProfile n} :
    τ ∈ markedMovedChoices μ ν σ flag K L t x ↔
      τ ∈ markedFilteredChoices ν σ flag K L t x ∧
        ∀ w ∈ τ.support, ν.symm w ≠ μ.symm w := by
  classical
  simp only [markedMovedChoices, Finset.mem_filter]
private noncomputable def localMovedDecorationCount (b A B : ℝ) (K L : ℕ)
    (μ ν σ : Matching n) (x : ScoreProfile n) : ℝ := by
  classical
  exact if IsLocallyEligiblePivot b A B x ν σ then
    ((markedMovedChoices μ ν σ (forwardMaskOfScores (splitScorePairs ν x).1
      (splitScorePairs ν x).2) K L (reverseIncrementCutoff n (maleSpouseTotal x ν)) x).card : ℝ)
    else 0
theorem localMovedDecorationCount_nonneg (b A B : ℝ) (K L : ℕ) (μ ν σ : Matching n)
    (x : ScoreProfile n) : 0 ≤ localMovedDecorationCount b A B K L μ ν σ x := by
  classical
  unfold localMovedDecorationCount
  split <;> positivity
theorem localMovedDecorationCount_le (b A B : ℝ) (K L : ℕ) (μ ν σ : Matching n)
    (x : ScoreProfile n) :
    localMovedDecorationCount b A B K L μ ν σ x ≤ localFilteredDecorationCount b A B K L ν σ x := by
  classical
  by_cases h : IsLocallyEligiblePivot b A B x ν σ
  · simp only [localMovedDecorationCount, localFilteredDecorationCount, if_pos h, Nat.cast_le]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  · simp only [localMovedDecorationCount, localFilteredDecorationCount, if_neg h, le_refl]
private theorem measurable_moved_mask_switch {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [Countable β]
    [MeasurableSingletonClass β] {M : α → β} (hM : Measurable M)
    {f : β → α → γ} (hf : ∀ j, Measurable (f j)) :
    Measurable (fun x ↦ f (M x) x) := by
  intro s hs
  let E (j : β) := {x : α | M x = j ∧ f j x ∈ s}
  have he : (fun x ↦ f (M x) x) ⁻¹' s = ⋃ j, E j := by
    ext x
    change f (M x) x ∈ s ↔ x ∈ ⋃ j, E j
    simp only [mem_iUnion, E, mem_ofPred_eq]
    exact ⟨fun hx ↦ ⟨M x, rfl, hx⟩, fun ⟨j, hj, hx⟩ ↦ hj.symm ▸ hx⟩
  rw [he]
  exact MeasurableSet.iUnion fun j ↦ (hM (measurableSet_singleton j)).inter (hf j hs)
theorem measurable_localMovedDecorationCount (b A B : ℝ) (K L : ℕ) (μ ν σ : Matching n) :
    Measurable (localMovedDecorationCount b A B K L μ ν σ) := by
  classical
  let M (x : ScoreProfile n) :=
    forwardMaskOfScores (splitScorePairs ν x).1 (splitScorePairs ν x).2
  let t (x : ScoreProfile n) := reverseIncrementCutoff n (maleSpouseTotal x ν)
  let f (flag : OffDiagonalCellIndex n → Bool) (x : ScoreProfile n) :=
    ((markedMovedChoices μ ν σ flag K L (t x) x).card : ℝ)
  have hM : Measurable M := (measurable_jointForwardMaskOfScores n).comp
    (splitScorePairs ν).measurable
  have ht : Measurable t := measurable_const.div (measurable_maleSpouseTotal ν)
  have hf (flag : OffDiagonalCellIndex n → Bool) : Measurable (f flag) := by
    have hmem (τ : Matching n) :
        MeasurableSet {x : ScoreProfile n | τ ∈ markedMovedChoices μ ν σ flag K L (t x) x} := by
      simp only [mem_markedMovedChoices, ofPred_and]
      exact (measurableSet_mem_markedFilteredChoices ν σ τ flag K L ht).inter
        (MeasurableSet.const _)
    simpa only [Function.comp_def, ENNReal.toReal_natCast] using
      ENNReal.measurable_toReal.comp (measurable_finsetCard_of_mem _ hmem)
  exact (measurable_moved_mask_switch hM hf).ite
    (measurableSet_isLocallyEligiblePivot b A B ν σ) measurable_const
end CompLP
end

-- PivotComparableCentered
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace CompLP
private structure PivotCountParameters where
  lowerLength : ℝ
  upperLength : ℝ
  geometryBudget : ℝ
  supportCap : ℕ
  shortCutoff : ℕ
private abbrev PivotMark (n : ℕ) := Matching n × Matching n
theorem integrable_of_ae_abs_le_real {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsFiniteMeasure ν] {f : Ω → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ᵐ x ∂ν, |f x| ≤ C) : Integrable f ν :=
  (integrable_const C).mono' hf.aestronglyMeasurable <|
    hC.mono fun x hx ↦ by simpa only [Real.norm_eq_abs] using hx
theorem integrable_mul_of_ae_abs_le_real {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsFiniteMeasure ν] {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    {C D : ℝ} (hC : 0 ≤ C) (hf' : ∀ᵐ x ∂ν, |f x| ≤ C) (hg' : ∀ᵐ x ∂ν, |g x| ≤ D) :
    Integrable (f * g) ν := by
  apply integrable_of_ae_abs_le_real (hf.mul hg) (C := C * D)
  filter_upwards [hf', hg'] with x hx hy
  rw [Pi.mul_apply, abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) hC
namespace PivotCountParameters
variable {n : ℕ}
private noncomputable def localCount (q : PivotCountParameters) (i : PivotMark n) :
    ScoreProfile n → ℝ :=
  localFilteredDecorationCount q.lowerLength q.upperLength q.geometryBudget
    q.supportCap q.shortCutoff i.1 i.2
private noncomputable def onStableMark (i : PivotMark n) (f : ScoreProfile n → ℝ) :
    ScoreProfile n → ℝ :=
  {x | IsScoreStable x i.1}.indicator f
private noncomputable def count (q : PivotCountParameters) (i : PivotMark n) :
    ScoreProfile n → ℝ :=
  onStableMark i (q.localCount i)
theorem measurable_localCount (q : PivotCountParameters) (i : PivotMark n) :
    Measurable (q.localCount i) :=
  measurable_localFilteredDecorationCount _ _ _ _ _ _ _
theorem measurable_onStableMark (i : PivotMark n) {f : ScoreProfile n → ℝ} (hf : Measurable f) :
    Measurable (onStableMark i f) := hf.indicator (measurableSet_isScoreStable i.1)
theorem measurable_count (q : PivotCountParameters) (i : PivotMark n) : Measurable (q.count i) :=
  measurable_onStableMark i (q.measurable_localCount i)
theorem localCount_mem_Icc (q : PivotCountParameters) (i : PivotMark n) (x : ScoreProfile n) :
    q.localCount i x ∈ Icc (0 : ℝ) (n.factorial : ℝ) :=
  ⟨localFilteredDecorationCount_nonneg _ _ _ _ _ _ _ _,
    localFilteredDecorationCount_le_factorial _ _ _ _ _ _ _ _⟩
theorem count_mem_Icc (q : PivotCountParameters) (i : PivotMark n) (x : ScoreProfile n) :
    q.count i x ∈ Icc (0 : ℝ) (n.factorial : ℝ) := by
  by_cases h : x ∈ {y | IsScoreStable y i.1}
  · simpa only [count, onStableMark, indicator_of_mem h] using q.localCount_mem_Icc i x
  · simp [count, onStableMark, h]
private noncomputable def localLaterResidual (q : PivotCountParameters) (i j : PivotMark n)
    (x : ScoreProfile n) : ℝ := by
  classical
  exact if IsStrictLaterStable x i.1 j.1 then q.localCount j x -
    localMovedDecorationCount q.lowerLength q.upperLength q.geometryBudget q.supportCap
      q.shortCutoff i.1 j.1 j.2 x else 0
theorem localLaterResidual_mem_Icc (q : PivotCountParameters) (i j : PivotMark n)
    (x : ScoreProfile n) : q.localLaterResidual i j x ∈ Icc (0 : ℝ) (n.factorial : ℝ) := by
  classical
  unfold localLaterResidual
  split
  · exact ⟨sub_nonneg.mpr (localMovedDecorationCount_le _ _ _ _ _ _ _ _ _),
      (sub_le_self _ (localMovedDecorationCount_nonneg _ _ _ _ _ _ _ _ _)).trans
        (q.localCount_mem_Icc j x).2⟩
  · simp
theorem measurable_localLaterResidual (q : PivotCountParameters) (i j : PivotMark n) :
    Measurable (q.localLaterResidual i j) :=
  ((q.measurable_localCount j).sub (measurable_localMovedDecorationCount _ _ _ _ _ _ _ _)).ite
    (measurableSet_isStrictLaterStable i.1 j.1) measurable_const
private noncomputable def comparableResidualTerm (q : PivotCountParameters) (i j : PivotMark n)
    (x : ScoreProfile n) : ℝ :=
  q.count i x * q.localLaterResidual i j x
theorem integrable_comparableResidualTerm (q : PivotCountParameters) (i j : PivotMark n) :
    Integrable (q.comparableResidualTerm i j) (continuousScoreLaw n) :=
  integrable_mul_of_ae_abs_le_real (q.measurable_count i) (q.measurable_localLaterResidual i j)
    (by positivity) (Eventually.of_forall fun x ↦
      (abs_of_nonneg (q.count_mem_Icc i x).1).symm ▸ (q.count_mem_Icc i x).2)
    (Eventually.of_forall fun x ↦
      (abs_of_nonneg (q.localLaterResidual_mem_Icc i j x).1).symm ▸
        (q.localLaterResidual_mem_Icc i j x).2)
end PivotCountParameters
end CompLP
end

-- PivotCenteredReduction
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators
namespace CompLP
variable {n : ℕ}
private def IncomparableAnchors (p : Profile n) (μ ν : Matching n) : Prop :=
  ¬ MenWeaklyPrefer p μ ν ∧ ¬ MenWeaklyPrefer p ν μ
theorem measurableSet_incomparableAnchors (μ ν : Matching n) :
    MeasurableSet {x : ScoreProfile n | IncomparableAnchors (profileOfScores x) μ ν} :=
  measurable_profileOfScores n (MeasurableSet.of_discrete :
    MeasurableSet {p : Profile n | IncomparableAnchors p μ ν})
namespace PivotCountParameters
private noncomputable def comparableResidualMass (q : PivotCountParameters) (x : ScoreProfile n) : ℝ :=
  ∑ i : PivotMark n, ∑ j : PivotMark n, q.comparableResidualTerm i j x
end PivotCountParameters
end CompLP
end

-- PivotResidualCountBridge
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators
namespace CompLP
namespace PivotCountParameters
variable {n : ℕ}
private noncomputable def residualChoiceFlag (x : ScoreProfile n) (μ _ : Matching n) :
    OffDiagonalCellIndex n → Bool :=
  forwardMaskOfScores (splitScorePairs μ x).1 (splitScorePairs μ x).2
private noncomputable def residualChoiceCutoff (x : ScoreProfile n) (μ _ : Matching n) : ℝ :=
  reverseIncrementCutoff n (maleSpouseTotal x μ)
private noncomputable def choices (q : PivotCountParameters) (x : ScoreProfile n)
    (i : PivotMark n) : Finset (Matching n) :=
  markedFilteredChoices i.1 i.2 (residualChoiceFlag x i.1 i.2)
    q.supportCap q.shortCutoff (residualChoiceCutoff x i.1 i.2) x
private noncomputable def eligibleChoices (q : PivotCountParameters) (x : ScoreProfile n)
    (i : PivotMark n) : Finset (Matching n) := by
  classical
  exact if IsScoreStable x i.1 ∧
    IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x i.1 i.2
    then q.choices x i else ∅
private noncomputable def residualLaterChoices (q : PivotCountParameters) (x : ScoreProfile n)
    (i j : PivotMark n) : Finset (Matching n) := by
  classical
  exact if IsStrictLaterStable x i.1 j.1 ∧
    IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x j.1 j.2 then
    (q.choices x j).filter (fun τ ↦ ¬ ∀ w ∈ τ.support, j.1.symm w ≠ i.1.symm w)
    else ∅
theorem count_eq_card_eligibleChoices (q : PivotCountParameters) (x : ScoreProfile n)
    (i : PivotMark n) : q.count i x = (q.eligibleChoices x i).card := by
  classical
  by_cases hs : IsScoreStable x i.1 <;>
    by_cases he : IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x i.1 i.2 <;>
    simp [count, onStableMark, localCount, localFilteredDecorationCount,
      eligibleChoices, choices, residualChoiceFlag, residualChoiceCutoff, hs, he]
private theorem localLaterResidual_eq_card (q : PivotCountParameters) (x : ScoreProfile n)
    (i j : PivotMark n) : q.localLaterResidual i j x = (q.residualLaterChoices x i j).card := by
  classical
  by_cases ho : IsStrictLaterStable x i.1 j.1
  · by_cases he : IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x j.1 j.2
    · let p (τ : Matching n) := ∀ w ∈ τ.support, j.1.symm w ≠ i.1.symm w
      have h := Finset.card_filter_add_card_filter_not (s := q.choices x j) p
      have hc : (((q.choices x j).filter p).card : ℝ) +
          (((q.choices x j).filter (fun τ ↦ ¬ p τ)).card : ℝ) =
          ((q.choices x j).card : ℝ) := by exact_mod_cast h
      rw [localLaterResidual, if_pos ho, localCount, localFilteredDecorationCount, if_pos he,
        localMovedDecorationCount, if_pos he, residualLaterChoices, if_pos ⟨ho, he⟩]
      change ((q.choices x j).card : ℝ) - (((q.choices x j).filter p).card : ℝ) =
        (((q.choices x j).filter (fun τ ↦ ¬ p τ)).card : ℝ)
      linarith only [hc]
    · simp [localLaterResidual, localCount, localFilteredDecorationCount,
        localMovedDecorationCount, residualLaterChoices, ho, he]
  · simp [localLaterResidual, residualLaterChoices, ho]
private noncomputable def residualChoicePairs (q : PivotCountParameters) (x : ScoreProfile n) :
    Finset (Σ _ : PivotMark n × PivotMark n, Matching n × Matching n) :=
  Finset.univ.sigma fun ij ↦ (q.eligibleChoices x ij.1).product
    (q.residualLaterChoices x ij.1 ij.2)
theorem comparableResidualMass_eq_card (q : PivotCountParameters) (x : ScoreProfile n) :
    q.comparableResidualMass x = (q.residualChoicePairs x).card := by
  rw [residualChoicePairs, Finset.card_sigma, Nat.cast_sum, Fintype.sum_prod_type]
  unfold comparableResidualMass
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  change q.comparableResidualTerm i j x =
    (((q.eligibleChoices x i).product (q.residualLaterChoices x i j)).card : ℝ)
  rw [Finset.product_eq_sprod, Finset.card_product, Nat.cast_mul, comparableResidualTerm,
    q.count_eq_card_eligibleChoices, q.localLaterResidual_eq_card]
private theorem data_of_eligibleChoices {q : PivotCountParameters} {x : ScoreProfile n}
    {i : PivotMark n} {a : Matching n} (h : a ∈ q.eligibleChoices x i) :
    IsScoreStable x i.1 ∧
      IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x i.1 i.2 ∧
      a ∈ q.choices x i := by
  classical
  unfold eligibleChoices at h
  split at h
  · rename_i hi
    exact ⟨hi.1, hi.2, h⟩
  · exact (Finset.notMem_empty _ h).elim
private theorem data_of_residualLaterChoices {q : PivotCountParameters} {x : ScoreProfile n}
    {i j : PivotMark n} {a : Matching n} (h : a ∈ q.residualLaterChoices x i j) :
    IsStrictLaterStable x i.1 j.1 ∧
      IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x j.1 j.2 ∧
      a ∈ q.choices x j ∧ ∃ w ∈ a.support, i.1.symm w = j.1.symm w := by
  classical
  unfold residualLaterChoices at h
  split at h
  · rename_i hj
    obtain ⟨ha, hnot⟩ := Finset.mem_filter.mp h
    push Not at hnot
    obtain ⟨w, hw, heq⟩ := hnot
    exact ⟨hj.1, hj.2, ha, w, hw, heq.symm⟩
  · exact (Finset.notMem_empty _ h).elim
theorem residualChoicePair_eligible (q : PivotCountParameters) {x : ScoreProfile n}
    (a : ↥(q.residualChoicePairs x)) :
    IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x a.val.1.1.1 a.val.1.1.2 ∧
      IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x
        a.val.1.2.1 a.val.1.2.2 := by
  have h := Finset.mem_product.mp (Finset.mem_sigma.mp a.property).2
  exact ⟨(data_of_eligibleChoices h.1).2.1, (data_of_residualLaterChoices h.2).2.1⟩
private noncomputable def residualMarkedPairOfChoice (q : PivotCountParameters) {x : ScoreProfile n}
    (hties : ∀ row, Function.Injective (x row))
    (hlong : ∀ i : PivotMark n,
      IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x i.1 i.2 →
        q.supportCap < i.2.support.card)
    (hcut : ∀ i : PivotMark n, 0 ≤ residualChoiceCutoff x i.1 i.2)
    (a : ↥(q.residualChoicePairs x)) :
    ResidualMarkedPair x q.supportCap q.shortCutoff (residualChoiceFlag x) (residualChoiceCutoff x) :=
  let h := Finset.mem_product.mp (Finset.mem_sigma.mp a.property).2
  let he := data_of_eligibleChoices h.1
  let hl := data_of_residualLaterChoices h.2
  ⟨⟨a.val.1.1.1, a.val.1.1.2, a.val.2.1, (isStable_profileOfScores_iff hties _).mpr he.1,
      he.2.1.isSoleForwardExposed hties, hlong _ he.2.1, hcut _, he.2.2⟩,
    ⟨a.val.1.2.1, a.val.1.2.2, a.val.2.2, (isStable_profileOfScores_iff hties _).mpr hl.1.1,
      hl.2.1.isSoleForwardExposed hties, hlong _ hl.2.1, hcut _, hl.2.2.1⟩,
    hl.1.2.2, hl.1.2.1, hl.2.2.2⟩
theorem residualMarkedPairOfChoice_eligible (q : PivotCountParameters) {x : ScoreProfile n}
    (hties : ∀ row, Function.Injective (x row)) (hlong) (hcut)
    (a : ↥(q.residualChoicePairs x)) :
    let R := q.residualMarkedPairOfChoice hties hlong hcut a
    IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget
        x R.early.anchor R.early.cycle ∧
      IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget
        x R.late.anchor R.late.cycle :=
  q.residualChoicePair_eligible a
theorem residualMarkedPairOfChoice_injective (q : PivotCountParameters) {x : ScoreProfile n}
    (hties : ∀ row, Function.Injective (x row)) (hlong) (hcut) :
    Function.Injective (q.residualMarkedPairOfChoice hties hlong hcut) := by
  intro a b hab
  apply Subtype.ext
  exact congrArg (fun R ↦ (⟨((R.early.anchor, R.early.cycle), (R.late.anchor, R.late.cycle)),
    (R.early.reverse, R.late.reverse)⟩ :
      Σ _ : PivotMark n × PivotMark n, Matching n × Matching n)) hab
theorem comparableResidualMass_le_twice_restrict (q : PivotCountParameters)
    {x : ScoreProfile n} {μ₀ : Matching n} (hopt : IsManOptimal (profileOfScores x) μ₀)
    (hties : ∀ row, Function.Injective (x row)) (hlong) (hcut)
    {Q : IncomparableStableMatchingPair (profileOfScores x) μ₀ → Prop}
    (hQ : ∀ a : ↥(q.residualChoicePairs x),
      Q ((q.residualMarkedPairOfChoice hties hlong hcut a).toResidualPivotPair hopt).toggleImage) :
    q.comparableResidualMass x ≤ 2 * (Nat.card {MN // Q MN} : ℝ) := by
  let f (a : ↥(q.residualChoicePairs x)) :=
    (q.residualMarkedPairOfChoice hties hlong hcut a).toResidualPivotPair hopt
  let P (R : ResidualPivotPair hopt q.supportCap) := ∃ a, f a = R
  let e (a : ↥(q.residualChoicePairs x)) : {R // P R} := ⟨f a, ⟨a, rfl⟩⟩
  have hinj : Function.Injective f :=
    (ResidualMarkedPair.toResidualPivotPair_injective hopt).comp
      (q.residualMarkedPairOfChoice_injective hties hlong hcut)
  have hcard := Nat.card_le_card_of_injective e
    (fun _ _ h ↦ hinj (congrArg Subtype.val h))
  have ht : Nat.card {R // P R} ≤ 2 * Nat.card {MN // Q MN} := by
    apply ResidualPivotPair.card_le_twice_incomparable_restrict
    rintro _ ⟨a, rfl⟩
    exact hQ a
  rw [q.comparableResidualMass_eq_card]
  rw [Nat.card_eq_finsetCard] at hcard
  exact_mod_cast hcard.trans ht
end PivotCountParameters
end CompLP
end

-- PivotIncomparableScoreCount
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators
namespace CompLP
variable {n : ℕ}
private def scoreIncomparablePairEvent (Q : ScoreProfile n → Matching n → Matching n → Prop)
    (μ ν : Matching n) : Set (ScoreProfile n) :=
  {x | IsScoreStable x μ ∧ IsScoreStable x ν ∧
    IncomparableAnchors (profileOfScores x) μ ν ∧ Q x μ ν}
theorem measurableSet_scoreIncomparablePairEvent
    {Q : ScoreProfile n → Matching n → Matching n → Prop}
    (hQ : ∀ μ ν, MeasurableSet {x | Q x μ ν}) (μ ν : Matching n) :
    MeasurableSet (scoreIncomparablePairEvent Q μ ν) :=
  (measurableSet_isScoreStable μ).inter ((measurableSet_isScoreStable ν).inter
    ((measurableSet_incomparableAnchors μ ν).inter (hQ μ ν)))
private noncomputable def incomparableScorePairs
    (Q : ScoreProfile n → Matching n → Matching n → Prop)
    (x : ScoreProfile n) : Finset (Matching n × Matching n) := by
  classical
  exact Finset.univ.filter (fun mn ↦ x ∈ scoreIncomparablePairEvent Q mn.1 mn.2)
private noncomputable def incomparableScorePairCount
    (Q : ScoreProfile n → Matching n → Matching n → Prop) (x : ScoreProfile n) : ℝ :=
  (incomparableScorePairs Q x).card
theorem incomparableScorePairCount_eq_sum
    (Q : ScoreProfile n → Matching n → Matching n → Prop) (x : ScoreProfile n) :
    incomparableScorePairCount Q x =
      ∑ mn : Matching n × Matching n,
        (scoreIncomparablePairEvent Q mn.1 mn.2).indicator (fun _ ↦ (1 : ℝ)) x := by
  classical
  simp only [incomparableScorePairCount, incomparableScorePairs, indicator_apply]
  rw [← Finset.sum_filter]
  simp
theorem integrable_incomparableScorePairCount
    {Q : ScoreProfile n → Matching n → Matching n → Prop}
    (hQ : ∀ μ ν, MeasurableSet {x | Q x μ ν}) :
    Integrable (incomparableScorePairCount Q) (continuousScoreLaw n) := by
  have h (mn : Matching n × Matching n) :
      Integrable ((scoreIncomparablePairEvent Q mn.1 mn.2).indicator (fun _ ↦ (1 : ℝ)))
        (continuousScoreLaw n) :=
    (integrable_const _).indicator (measurableSet_scoreIncomparablePairEvent hQ mn.1 mn.2)
  exact (integrable_finsetSum _ fun mn _ ↦ h mn).congr
    (Eventually.of_forall fun x ↦ (incomparableScorePairCount_eq_sum Q x).symm)
theorem integral_incomparableScorePairCount
    {Q : ScoreProfile n → Matching n → Matching n → Prop}
    (hQ : ∀ μ ν, MeasurableSet {x | Q x μ ν}) :
    (∫ x, incomparableScorePairCount Q x ∂continuousScoreLaw n) =
      ∑ μ : Matching n, ∑ ν : Matching n,
        (continuousScoreLaw n).real (scoreIncomparablePairEvent Q μ ν) := by
  simp_rw [incomparableScorePairCount_eq_sum]
  rw [integral_finsetSum _ (fun mn _ ↦ (integrable_const _).indicator
    (measurableSet_scoreIncomparablePairEvent hQ mn.1 mn.2)), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun μ _ ↦ Finset.sum_congr rfl fun ν _ ↦ ?_
  rw [integral_indicator_const _ (measurableSet_scoreIncomparablePairEvent hQ μ ν), smul_eq_mul,
    mul_one]
private theorem card_incomparableStableMatchingPair_restrict_le
    {Q : ScoreProfile n → Matching n → Matching n → Prop} {x : ScoreProfile n}
    (hties : ∀ row, Function.Injective (x row)) {μ₀ : Matching n}
    (hopt : IsManOptimal (profileOfScores x) μ₀) :
    Nat.card {MN : IncomparableStableMatchingPair (profileOfScores x) μ₀ //
        Q x MN.val.1.val MN.val.2.val} ≤ (incomparableScorePairs Q x).card := by
  classical
  let f (z : {MN : IncomparableStableMatchingPair (profileOfScores x) μ₀ //
      Q x MN.val.1.val MN.val.2.val}) : ↥(incomparableScorePairs Q x) := by
    let a := z.val.val.1
    let b := z.val.val.2
    refine ⟨(a.val, b.val), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨(isStable_profileOfScores_iff hties _).mp a.property,
      (isStable_profileOfScores_iff hties _).mp b.property,
      ⟨fun h ↦ z.val.property.1 ((eliminatedRotations_subset_iff hopt a.property b.property).mpr h),
        fun h ↦ z.val.property.2 ((eliminatedRotations_subset_iff hopt b.property a.property).mpr h)⟩,
      z.property⟩
  have h : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    have hp := congrArg Subtype.val hab
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hp)) (Subtype.ext (congrArg Prod.snd hp))
  simpa only [Nat.card_eq_finsetCard] using Nat.card_le_card_of_injective f h
namespace PivotCountParameters
theorem residualChoiceCutoff_nonneg {x : ScoreProfile n}
    (hx : ∀ r i, 0 ≤ x r i) (i : PivotMark n) :
    0 ≤ residualChoiceCutoff x i.1 i.2 := by
  unfold residualChoiceCutoff reverseIncrementCutoff
  exact div_nonneg (mul_nonneg (by norm_num) (Real.log_natCast_nonneg _))
    (Finset.sum_nonneg fun m _ ↦ hx (.inl m) (i.1 m))
theorem comparableResidualMass_le_twice_scorePairCount (q : PivotCountParameters)
    {Q : ScoreProfile n → Matching n → Matching n → Prop} {x : ScoreProfile n}
    (hties : ∀ row, Function.Injective (x row)) (hlong) (hcut)
    (hQ : ∀ μ₀ (hopt : IsManOptimal (profileOfScores x) μ₀) (a : ↥(q.residualChoicePairs x)),
      Q x ((q.residualMarkedPairOfChoice hties hlong hcut a).toResidualPivotPair hopt).toggleImage.val.1.val
        ((q.residualMarkedPairOfChoice hties hlong hcut a).toResidualPivotPair hopt).toggleImage.val.2.val) :
    q.comparableResidualMass x ≤ 2 * incomparableScorePairCount Q x := by
  classical
  by_cases h : Nonempty ↥(q.residualChoicePairs x)
  · let a := Classical.choice h
    let R := q.residualMarkedPairOfChoice hties hlong hcut a
    obtain ⟨μ₀, hopt⟩ := exists_manOptimal_of_exists_stable ⟨R.early.anchor, R.early.stable⟩
    have hc := q.comparableResidualMass_le_twice_restrict hopt hties hlong hcut
      (Q := fun MN ↦ Q x MN.val.1.val MN.val.2.val) (hQ μ₀ hopt)
    exact hc.trans (mul_le_mul_of_nonneg_left
      (Nat.cast_le.mpr (card_incomparableStableMatchingPair_restrict_le (Q := Q) hties hopt))
      (by norm_num))
  · have hz : (q.residualChoicePairs x).card = 0 := by
      rw [Finset.card_eq_zero]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      exact fun _ hm ↦ h ⟨⟨_, hm⟩⟩
    rw [q.comparableResidualMass_eq_card, hz, Nat.cast_zero]
    exact mul_nonneg (by norm_num) (Nat.cast_nonneg _)
theorem integral_comparableResidualMass_le_twice_sum (q : PivotCountParameters)
    {Q : ScoreProfile n → Matching n → Matching n → Prop}
    (hQ : ∀ μ ν, MeasurableSet {x | Q x μ ν})
    (h : q.comparableResidualMass ≤ᵐ[continuousScoreLaw n]
      fun x ↦ 2 * incomparableScorePairCount Q x) :
    (∫ x, q.comparableResidualMass x ∂continuousScoreLaw n) ≤
      2 * ∑ μ : Matching n, ∑ ν : Matching n,
        (continuousScoreLaw n).real (scoreIncomparablePairEvent Q μ ν) := by
  have hR : Integrable (q.comparableResidualMass (n := n)) (continuousScoreLaw n) :=
    integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
      q.integrable_comparableResidualTerm i j
  have hi := integral_mono_ae hR ((integrable_incomparableScorePairCount hQ).const_mul 2) h
  rw [integral_const_mul, integral_incomparableScorePairCount hQ] at hi
  exact hi
end PivotCountParameters
end CompLP
end

-- PivotTwoCycleForest
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace CompLP
end CompLP
end

-- CommonForwardCycleMoments
section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace CompLP
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
section RowLaws
variable [MeasurableSpace (Option ι)]
variable [MeasurableSingletonClass (Option ι)]
end RowLaws
section ReferenceWeights
end ReferenceWeights
section NearRankOne
variable [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]
end NearRankOne
end CompLP
end

-- TwoStablePairSizeSums
section
open Finset
namespace CompLP
end CompLP
end

-- PivotBackgroundGeometry
section
open Set StableMarriage
open scoped BigOperators
namespace CompLP
private noncomputable def backgroundMaleCeiling (n : ℕ) : ℝ :=
  16 * Real.log n / (n : ℝ) ^ (1 / 10 : ℝ)
private noncomputable def backgroundWeightCeiling (n : ℕ) : ℝ :=
  2060 * Real.log n / n
private noncomputable def backgroundLabelBudget (n L : ℕ) : ℝ :=
  ((L.choose 2 : ℝ) + L * (2 * n / (Real.log n) ^ 3)) * backgroundWeightCeiling n
private structure BackgroundCycleBudget (n L : ℕ) : Prop where
  cutoff_two : 2 ≤ L
  log_cutoff : 100 ≤ Real.log (L : ℝ)
  arc : ∀ Y : ℝ, (n : ℝ) ^ (1 / 10 : ℝ) ≤ Y →
    (L : ℝ) * (backgroundMaleCeiling n + 1 / Y) ≤ 1 / 100
  label : backgroundLabelBudget n L ≤ 1 / 100
theorem BackgroundCycleBudget.self_ {n L : ℕ} (h : BackgroundCycleBudget n L) : BackgroundCycleBudget n L := h
end CompLP
end

-- LogarithmicCutoffs
section
open Filter
open scoped Topology BigOperators
namespace CompLP
private noncomputable def logarithmicCycleCutoff (n : ℕ) : ℕ := ⌊Real.log (n : ℝ)⌋₊
theorem logarithmicCycleCutoff_cast_le (n : ℕ) :
    (logarithmicCycleCutoff n : ℝ) ≤ Real.log (n : ℝ) :=
  Nat.floor_le (Real.log_natCast_nonneg n)
theorem tendsto_logarithmicCycleCutoff : Tendsto logarithmicCycleCutoff atTop atTop :=
  tendsto_nat_floor_atTop.comp
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
theorem tendsto_log_logarithmicCycleCutoff :
    Tendsto (fun n : ℕ ↦ Real.log (logarithmicCycleCutoff n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp tendsto_logarithmicCycleCutoff)
theorem tendsto_inv_log_logarithmicCycleCutoff :
    Tendsto (fun n : ℕ ↦ (Real.log (logarithmicCycleCutoff n : ℝ))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_log_logarithmicCycleCutoff
theorem tendsto_log_pow_div_nat_rpow (k : ℕ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n : ℕ ↦ (Real.log (n : ℝ)) ^ k / (n : ℝ) ^ s) atTop (𝓝 0) := by
  have h := ((isLittleO_log_rpow_rpow_atTop (k : ℝ) hs).tendsto_div_nhds_zero).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [Function.comp_def, Real.rpow_natCast] using h
theorem eventually_logarithmicCycleCutoff_le_supportCap {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ n : ℕ in atTop, logarithmicCycleCutoff n ≤ pivotDecorationSupportCap κ n := by
  have h := tendsto_log_pow_div_nat_rpow 1 (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [(tendsto_order.mp h).2 (κ / 2) (by positivity),
    eventually_pivotDecorationSupportCap_bounds hκ, eventually_gt_atTop (0 : ℕ)]
    with n hn hK hn0
  have hs : 0 < (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn0) _
  have hbound : Real.log (n : ℝ) ≤ κ * Real.sqrt (n : ℝ) / 2 := by
    rw [pow_one] at hn
    have hh := (div_le_iff₀ hs).1 hn.le
    rw [Real.sqrt_eq_rpow]
    linarith only [hh]
  have hKm : ((pivotDecorationSupportCap κ n - 1 : ℕ) : ℝ) ≤
      pivotDecorationSupportCap κ n := Nat.cast_le.mpr (Nat.sub_le _ _)
  exact_mod_cast (logarithmicCycleCutoff_cast_le n).trans (hbound.trans (hK.2.2.trans hKm))
private class LPHypD : Prop where
  bound : ∀ᶠ n : ℕ in atTop, BackgroundCycleBudget n (logarithmicCycleCutoff n)
theorem eventually_logarithmic_cycle_budget [h : LPHypD] :
    ∀ᶠ n : ℕ in atTop, BackgroundCycleBudget n (logarithmicCycleCutoff n) :=
  h.bound
end CompLP
end

-- PivotPairEnvelopeScale
section
open Filter
open scoped Topology
namespace CompLP
private noncomputable def residualPairEnvelope (C : ℝ) (n L : ℕ) : ℝ :=
  2 * (C * (1 + Real.log n)) *
    (2 * (n : ℝ) ^ 2 * (2 + 4 * Real.log (Real.log n)) +
      (1600 / Real.log (L : ℝ)) * ((n : ℝ) ^ 2 * (1 + Real.log n)))
private theorem residualPairEnvelope_le {C : ℝ} (hC : 0 ≤ C) {n L : ℕ}
    (ht : 1 ≤ Real.log (n : ℝ)) (hL : 0 < Real.log (L : ℝ)) :
    residualPairEnvelope C n L ≤
      C * (16 / Real.log n + 32 * (Real.log (Real.log n) / Real.log n) +
        12800 / Real.log (L : ℝ)) * ((n : ℝ) * Real.log n) ^ 2 := by
  let t := Real.log (n : ℝ)
  let u := Real.log (L : ℝ)
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hu : 0 < u := hL
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
  have htwo : 1 + t ≤ 2 * t := by change 1 ≤ t at ht; linarith only [ht]
  calc
    _ ≤ 2 * (C * (2 * t)) * (2 * (n : ℝ) ^ 2 * (2 + 4 * Real.log t) +
          (1600 / u) * ((n : ℝ) ^ 2 * (2 * t))) := by
      unfold residualPairEnvelope
      change 2 * (C * (1 + t)) * (2 * (n : ℝ) ^ 2 * (2 + 4 * Real.log t) +
        (1600 / u) * ((n : ℝ) ^ 2 * (1 + t))) ≤ _
      gcongr
    _ = _ := by
      dsimp only [t, u] at *
      field_simp
      ring
private theorem tendsto_log_marketSize : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
theorem eventually_residualPairEnvelope_le {C e : ℝ} (hC : 0 ≤ C) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, residualPairEnvelope C n (logarithmicCycleCutoff n) ≤
      e * ((n : ℝ) * Real.log n) ^ 2 := by
  have h1 := (tendsto_inv_atTop_zero.comp tendsto_log_marketSize).const_mul 16
  have h2 := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    tendsto_log_marketSize).const_mul 32
  have h3 := tendsto_inv_log_logarithmicCycleCutoff.const_mul 12800
  have hlim : Tendsto (fun n : ℕ ↦ C * (16 / Real.log n +
      32 * (Real.log (Real.log n) / Real.log n) +
      12800 / Real.log (logarithmicCycleCutoff n : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero, Function.comp_def, id_eq, div_eq_mul_inv] using
      ((h1.add h2).add h3).const_mul C
  filter_upwards [(tendsto_order.mp hlim).2 e he, tendsto_log_marketSize.eventually_ge_atTop 1,
    tendsto_log_logarithmicCycleCutoff.eventually_gt_atTop 0] with n h ht hL
  exact (residualPairEnvelope_le hC ht hL).trans (mul_le_mul_of_nonneg_right h.le (sq_nonneg _))
end CompLP
end

-- TwoStableScoreProduct
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace CompLP
variable {n : ℕ}
end CompLP
end

-- TwoStableCommonRows
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace CompLP
section FiniteOutcomes
variable {n : ℕ} {μ ν : Matching n} [MeasurableSpace (Option (Fin n))]
variable [MeasurableSingletonClass (Option (Fin n))]
end FiniteOutcomes
end CompLP
end

-- PivotResidualEstimate
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators
namespace CompLP
namespace PivotCountParameters
variable {n : ℕ}
theorem ae_comparableResidualMass_le_scoreGeometry (q : PivotCountParameters)
    {κ : ℝ} (hn : 0 < n) (hκ : κ < q.lowerLength)
    (hcap : (q.supportCap : ℝ) ≤ κ * Real.sqrt (n : ℝ))
    (hL : q.shortCutoff ≤ q.supportCap)
    (hK : (q.supportCap : ℝ) * (2048 * Real.log n / n) ≤ 1) :
    q.comparableResidualMass ≤ᵐ[continuousScoreLaw n] fun x ↦
      2 * incomparableScorePairCount
        (IsResidualPairGeometry q.lowerLength q.supportCap q.shortCutoff) x := by
  filter_upwards [ae_injective_rows n, ae_unitOpen_scores n] with x ht hx
  let hlong (i : PivotMark n) (h : IsLocallyEligiblePivot q.lowerLength q.upperLength
      q.geometryBudget x i.1 i.2) : q.supportCap < i.2.support.card :=
    h.supportCap_lt hn hκ hcap
  let hcut (i : PivotMark n) : 0 ≤ residualChoiceCutoff x i.1 i.2 :=
    residualChoiceCutoff_nonneg (fun r i ↦ (hx r i).1.le) i
  apply q.comparableResidualMass_le_twice_scorePairCount ht hlong hcut
  intro μ₀ hopt a
  have ha := q.residualMarkedPairOfChoice_eligible ht hlong hcut a
  exact (q.residualMarkedPairOfChoice ht hlong hcut a).toggleImage_geometry
    hopt ht hn hL hK (fun _ _ ↦ rfl) ha.1 ha.2
theorem integral_comparableResidualMass_le_geometry (q : PivotCountParameters)
    {κ : ℝ} (hn : 0 < n) (hκ : κ < q.lowerLength)
    (hcap : (q.supportCap : ℝ) ≤ κ * Real.sqrt (n : ℝ))
    (hL : q.shortCutoff ≤ q.supportCap)
    (hK : (q.supportCap : ℝ) * (2048 * Real.log n / n) ≤ 1) :
    (∫ x, q.comparableResidualMass x ∂continuousScoreLaw n) ≤
      2 * ∑ μ : Matching n, ∑ ν : Matching n, (continuousScoreLaw n).real
        (scoreIncomparablePairEvent
          (IsResidualPairGeometry q.lowerLength q.supportCap q.shortCutoff) μ ν) :=
  q.integral_comparableResidualMass_le_twice_sum
    (measurableSet_isResidualPairGeometry q.lowerLength q.supportCap q.shortCutoff)
    (q.ae_comparableResidualMass_le_scoreGeometry hn hκ hcap hL hK)
end PivotCountParameters
variable {n : ℕ}
end CompLP
end

-- TwoStableBackgroundCycleTail
section
open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace CompLP
variable {n : ℕ} {μ ν : Matching n}
end CompLP
end

-- TwoStablePairDensity
section
open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace CompLP
end CompLP
end

-- TwoStableBetaIntegral
section
open MeasureTheory Set
open scoped ENNReal
namespace CompLP
end CompLP
end

-- TwoStableOrientationCounting
section
open Equiv Equiv.Perm Finset StableMarriage
open scoped BigOperators ENNReal
namespace CompLP
variable {n : ℕ}
namespace LabeledPairOrientation
variable {μ ν : Matching n} {U V : Finset (Fin n)}
end LabeledPairOrientation
end CompLP
end

-- TwoStableFixedPairBound
section
open MeasureTheory Set StableMarriage
open scoped ENNReal
namespace CompLP
end CompLP
end

-- PivotBackgroundPairBound
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal
namespace CompLP
variable {n : ℕ} {μ ν : Matching n}
end CompLP
end

-- TwoStablePairMassSums
section
open Filter Finset MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal
namespace CompLP
variable {n : ℕ}
end CompLP
end

-- TwoStablePairPerSizeBounds
section
open Filter MeasureTheory Set StableMarriage
open scoped ENNReal
namespace CompLP
variable {n : ℕ}
end CompLP
end

-- PivotPairEnvelopeBounds
section
open Filter MeasureTheory Set StableMarriage Asymptotics
open scoped BigOperators
namespace CompLP
variable {n : ℕ}
private class LPHypC : Prop where
  bound : ∀ {n L : ℕ} (hn : 0 < n)
    (hbudget : BackgroundCycleBudget n L) (hLt : (L : ℝ) ≤ Real.log n) (b : ℝ) (K : ℕ),
    (∑ μ : Matching n, ∑ ν : Matching n, (continuousScoreLaw n).real
      (scoreIncomparablePairEvent (IsResidualPairGeometry b K L) μ ν)) ≤
      (Real.exp 72 * (1 + Real.log n)) *
        (2 * (n : ℝ) ^ 2 * (2 + 4 * Real.log (Real.log n)) +
          (1600 / Real.log (L : ℝ)) * ((n : ℝ) ^ 2 * (1 + Real.log n)))
theorem sum_residualPairMass_le_regularOrientation [h : LPHypC] {n L : ℕ} (hn : 0 < n)
    (hbudget : BackgroundCycleBudget n L) (hLt : (L : ℝ) ≤ Real.log n) (b : ℝ) (K : ℕ) :
    (∑ μ : Matching n, ∑ ν : Matching n, (continuousScoreLaw n).real
      (scoreIncomparablePairEvent (IsResidualPairGeometry b K L) μ ν)) ≤
      (Real.exp 72 * (1 + Real.log n)) *
        (2 * (n : ℝ) ^ 2 * (2 + 4 * Real.log (Real.log n)) +
          (1600 / Real.log (L : ℝ)) * ((n : ℝ) ^ 2 * (1 + Real.log n))) :=
  h.bound hn hbudget hLt b K
theorem PivotCountParameters.integral_comparableResidualMass_le_envelope [LPHypC]
    (q : PivotCountParameters) {n : ℕ} {κ : ℝ} (hn : 0 < n)
    (hκb : κ < q.lowerLength) (hcap : (q.supportCap : ℝ) ≤ κ * Real.sqrt (n : ℝ))
    (hLK : q.shortCutoff ≤ q.supportCap)
    (hinc : (q.supportCap : ℝ) * (2048 * Real.log n / n) ≤ 1)
    (hbudget : BackgroundCycleBudget n q.shortCutoff)
    (hLt : (q.shortCutoff : ℝ) ≤ Real.log n) :
    (∫ x, q.comparableResidualMass x ∂continuousScoreLaw n) ≤
      residualPairEnvelope (Real.exp 72) n q.shortCutoff := by
  have h := q.integral_comparableResidualMass_le_geometry hn hκb hcap hLK hinc
  exact h.trans ((mul_le_mul_of_nonneg_left
    (sum_residualPairMass_le_regularOrientation hn hbudget hLt q.lowerLength q.supportCap)
    (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by unfold residualPairEnvelope; ring))
private theorem comparableResidualMass_nonneg (q : PivotCountParameters)
    {n : ℕ} (x : ScoreProfile n) : 0 ≤ q.comparableResidualMass x := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (q.count_mem_Icc i x).1 (q.localLaterResidual_mem_Icc i j x).1
end CompLP
end

noncomputable section
open MeasureTheory Filter CompLP Asymptotics
open scoped Topology CompLP
private def params (b A B κ : ℝ) (n : ℕ) : PivotCountParameters :=
  ⟨b,A,B,pivotDecorationSupportCap κ n,logarithmicCycleCutoff n⟩

private def admissible (b A B κ : ℝ) : Prop :=
  0 < b ∧ b ≤ 1 ∧ 1 ≤ A ∧ 0 < B ∧ 0 < κ ∧ κ < b ∧
    24*κ^2/2 + (B+1)*κ ≤ 1/4 ∧
    Real.exp (κ*(2*(1+B))) * (2*κ*(B/(1/128))) ≤ 3/32

private theorem comparable_estimate [LPHypC] [LPHypD] : ∀ b A B κ : ℝ, admissible b A B κ →
  (fun n : ℕ => ∫ x, (params b A B κ n).comparableResidualMass x ∂continuousScoreLaw n) =o[atTop]
    (fun n : ℕ => ((n:ℝ)*Real.log n)^2) := by
  intro b A B κ hq
  obtain ⟨hb, -, -, -, hκ, hκb, -, -⟩ := hq
  apply isLittleO_iff.mpr
  intro e he
  filter_upwards [eventually_logarithmic_cycle_budget,
    eventually_logarithmicCycleCutoff_le_supportCap hκ,
    eventually_pivotDecorationSupportCap_bounds hκ,
    eventually_residualEndpointIncrementBudget κ,
    eventually_gt_atTop (0 : ℕ),
    eventually_residualPairEnvelope_le (Real.exp_pos 72).le he] with n hbudget hL hK hinc hn hsmall
  let q : PivotCountParameters := params b A B κ n
  have hp := q.integral_comparableResidualMass_le_envelope hn hκb hK.2.1 hL
      (hinc _ hK.2.1) hbudget (logarithmicCycleCutoff_cast_le n)
  have hnon : 0 ≤ ∫ x, q.comparableResidualMass x ∂continuousScoreLaw n :=
    integral_nonneg fun x => comparableResidualMass_nonneg q x
  change ‖∫ x, q.comparableResidualMass x ∂continuousScoreLaw n‖ ≤ e * ‖((n:ℝ)*Real.log n)^2‖
  simpa only [Real.norm_eq_abs, abs_of_nonneg hnon,
    abs_of_nonneg (sq_nonneg ((n:ℝ)*Real.log n))] using hp.trans hsmall
end


noncomputable section
namespace OMA.R_LennonPittel_lennon_pittel_conjecture_R3_H2_R1_H2_R1_H3_R1
open MeasureTheory Filter CompLP Asymptotics StableMarriage
open scoped Topology ENNReal CompLP

/-- Cowgill's bound for the probability mass of residual comparable pair geometries in regular orientation. -/
def H1 : Prop := ∀ {n L : ℕ} (hn : 0 < n)
    (hbudget : BackgroundCycleBudget n L) (hLt : (L : ℝ) ≤ Real.log n) (b : ℝ) (K : ℕ),
    (∑ μ : Matching n, ∑ ν : Matching n, (continuousScoreLaw n).real
      (scoreIncomparablePairEvent (IsResidualPairGeometry b K L) μ ν)) ≤
      (Real.exp 72 * (1 + Real.log n)) *
        (2 * (n : ℝ) ^ 2 * (2 + 4 * Real.log (Real.log n)) +
          (1600 / Real.log (L : ℝ)) * ((n : ℝ) ^ 2 * (1 + Real.log n)))

/-- The logarithmic cycle cutoff eventually meets Cowgill's background cycle budget. -/
def H2 : Prop := ∀ᶠ n : ℕ in atTop, BackgroundCycleBudget n (logarithmicCycleCutoff n)

theorem main : H1 → H2 → OMA.R_LennonPittel_lennon_pittel_conjecture_R3_H2_R1_H2_R1.H3 := by
  intro h1 h2
  haveI : LPHypC := ⟨h1⟩
  haveI : LPHypD := ⟨h2⟩
  exact comparable_estimate

end OMA.R_LennonPittel_lennon_pittel_conjecture_R3_H2_R1_H2_R1_H3_R1
end
