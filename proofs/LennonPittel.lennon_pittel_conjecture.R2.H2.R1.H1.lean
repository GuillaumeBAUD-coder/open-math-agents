import OMAReductions.R_LennonPittel_lennon_pittel_conjecture_R2_H2_R1


-- Port of Bo Cowgill, bocowgill/lennon-pittel @cf950d059659, Apache-2.0.

-- Cowgill formalizes Pittel’s 1989 first-moment asymptotic. The final argument
-- extends its positive lower bound over the finitely many smaller market sizes.
-- Credit: @marcusbuffett

section

open MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace LennonPittelFormalization

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

private theorem perm_eq_of_lt_iff {n : ℕ} {p q : Equiv.Perm (Fin n)}
    (h : ∀ i j, p i < p j ↔ q i < q j) : p = q := by
  let f := fun i ↦ q (p.symm i)
  have hf : StrictMono f := fun i j hij ↦ (h (p.symm i) (p.symm j)).1
    (by simpa using hij)
  exact Equiv.ext fun i ↦ by
    simpa [f] using (hf.id_le (p i)).antisymm (hf.le_id (p i))

theorem measurePreserving_rank_of_iid {n : ℕ}
    [MeasurableSpace (Equiv.Perm (Fin n))] [MeasurableSingletonClass (Equiv.Perm (Fin n))]
    {r : (Fin n → ℝ) → Equiv.Perm (Fin n)} (hr : Measurable r)
    (hcmp : ∀ x, Function.Injective x → ∀ i j, r x i < r x j ↔ x i < x j) :
    MeasurePreserving r (Measure.pi fun _ : Fin n ↦ μ)
      (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure := by
  let law : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n ↦ μ
  let ν : Measure (Equiv.Perm (Fin n)) := law.map r
  have : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hr.aemeasurable
  
  have hequal (p q : Equiv.Perm (Fin n)) : ν {p} = ν {q} := by
    let e : Equiv.Perm (Fin n) := q.trans p.symm
    let reindex := MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ ℝ) e.symm
    have hm : MeasurePreserving reindex law law :=
      measurePreserving_piCongrLeft (fun _ : Fin n ↦ μ) e.symm
    have he (x : Fin n → ℝ) (i : Fin n) : reindex x i = x (e i) := by
      simp [reindex, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    have hcongr : r ⁻¹' ({p} : Set (Equiv.Perm (Fin n))) =ᶠ[ae law] reindex ⁻¹' (r ⁻¹' {q}) :=
      (ae_injective_iid μ n).mono fun x hx ↦ by
        have hre : r (reindex x) = e.trans (r x) := perm_eq_of_lt_iff fun i j ↦
          (hcmp (reindex x) (by
            simpa only [Function.Injective, Function.comp_apply, he] using hx.comp e.injective) i j).trans
            (by simpa only [he, Equiv.trans_apply] using (hcmp x hx (e i) (e j)).symm)
        apply propext
        change (r x = p) ↔ r (reindex x) = q
        rw [hre]
        constructor
        · rintro rfl
          simp [e, Equiv.trans_assoc]
        · intro h
          apply Equiv.ext
          intro i
          have hi := DFunLike.congr_fun h (e.symm i)
          simpa [e] using hi
    change law.map r {p} = law.map r {q}
    rw [Measure.map_apply hr (measurableSet_singleton p),
      Measure.map_apply hr (measurableSet_singleton q)]
    exact (measure_congr hcongr).trans
      (hm.measure_preimage (hr (measurableSet_singleton q)).nullMeasurableSet)
  refine ⟨hr, Measure.ext_of_singleton fun p ↦ ?_⟩
  
  have hsum : ν {p} * (Fintype.card (Equiv.Perm (Fin n)) : ℝ≥0∞) = 1 := by
    calc
      _ = ∑' q : Equiv.Perm (Fin n), ν {q} := by
        rw [tsum_fintype, Finset.sum_congr rfl (fun q _ ↦ hequal q p), Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, mul_comm]
      _ = 1 := by simpa only [Measure.toPMF_apply] using ν.toPMF.tsum_coe
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton p), PMF.uniformOfFintype_apply]
  exact ENNReal.eq_inv_of_mul_eq_one_left hsum

end LennonPittelFormalization

end

section

open MeasureTheory Set

open scoped BigOperators ENNReal

namespace LennonPittelFormalization

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [Fintype A] [Nonempty A]

noncomputable def uniformMarkLaw (A : Type*) [MeasurableSpace A] [Fintype A] [Nonempty A] :
    Measure A :=
  (PMF.uniformOfFintype A).toMeasure

instance uniformMarkLaw_isProbabilityMeasure : IsProbabilityMeasure (uniformMarkLaw A) :=
  inferInstanceAs (IsProbabilityMeasure (PMF.uniformOfFintype A).toMeasure)

noncomputable def markedLaw (P : Measure Ω) (E : Set (Ω × A)) : Measure (Ω × A) :=
  ProbabilityTheory.cond (P.prod (uniformMarkLaw A)) E

noncomputable def markedNormalizer (P : Measure Ω) (E : Set (Ω × A)) : ℝ≥0∞ :=
  ∫⁻ ω, ∑ a, E.indicator 1 (ω, a) ∂P

theorem markedLaw_isProbabilityMeasure (P : Measure Ω) [IsProbabilityMeasure P]
    {E : Set (Ω × A)} (hpos : (P.prod (uniformMarkLaw A)) E ≠ 0) :
    IsProbabilityMeasure (markedLaw P E) :=
  ProbabilityTheory.cond_isProbabilityMeasure hpos

variable [MeasurableSingletonClass A]

private theorem lintegral_restrict_uniformMarkLaw (P : Measure Ω)
    {E : Set (Ω × A)} (hE : MeasurableSet E) {f : Ω × A → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z in E, f z ∂P.prod (uniformMarkLaw A)) =
      (Fintype.card A : ℝ≥0∞)⁻¹ * (∫⁻ ω, ∑ a, E.indicator f (ω, a) ∂P) := by
  rw [← lintegral_indicator hE, lintegral_prod _ (hf.indicator hE).aemeasurable]
  simp only [lintegral_fintype, uniformMarkLaw, PMF.toMeasure_apply_singleton _ _
    (measurableSet_singleton _), PMF.uniformOfFintype_apply, ← Finset.sum_mul]
  rw [lintegral_mul_const' _ _ (by simp [Fintype.card_ne_zero]), mul_comm]

theorem uniform_mark_event_mass (P : Measure Ω) {E : Set (Ω × A)} (hE : MeasurableSet E) :
    (P.prod (uniformMarkLaw A)) E = (Fintype.card A : ℝ≥0∞)⁻¹ * markedNormalizer P E := by
  simpa [markedNormalizer] using
    lintegral_restrict_uniformMarkLaw P hE (f := 1) measurable_const

theorem marked_counting_identity (P : Measure Ω) [IsProbabilityMeasure P]
    {E : Set (Ω × A)} (hE : MeasurableSet E)
    (hpos : (P.prod (uniformMarkLaw A)) E ≠ 0)
    {f : Ω × A → ℝ≥0∞} (hf : Measurable f) :
    markedNormalizer P E * (∫⁻ z, f z ∂markedLaw P E) =
      ∫⁻ ω, ∑ a, E.indicator f (ω, a) ∂P := by
  have hscaled : (Fintype.card A : ℝ≥0∞) * (P.prod (uniformMarkLaw A)) E =
      markedNormalizer P E := by
    rw [uniform_mark_event_mass P hE, ← mul_assoc,
      ENNReal.mul_inv_cancel (by simp [Fintype.card_ne_zero]) (by simp), one_mul]
  rw [← hscaled, markedLaw, ProbabilityTheory.cond, lintegral_smul_measure, smul_eq_mul,
    lintegral_restrict_uniformMarkLaw P hE hf]
  rw [mul_assoc, ← mul_assoc ((P.prod (uniformMarkLaw A)) E),
    ENNReal.mul_inv_cancel hpos (measure_lt_top _ _).ne, one_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (by simp [Fintype.card_ne_zero]) (by simp), one_mul]

section StableMarriage

open StableMarriage


scoped instance matchingMeasurableSpace (n : ℕ) : MeasurableSpace (Matching n) := ⊤

scoped instance matchingDiscreteMeasurableSpace (n : ℕ) :
    DiscreteMeasurableSpace (Matching n) :=
  ⟨fun _ ↦ trivial⟩

scoped instance profileDiscreteMeasurableSpace (n : ℕ) : DiscreteMeasurableSpace (Profile n) :=
  ⟨fun _ ↦ trivial⟩

def stableMarkEvent (n : ℕ) : Set (Profile n × Matching n) :=
  {z | IsStable z.1 z.2}

theorem measurableSet_stableMarkEvent (n : ℕ) : MeasurableSet (stableMarkEvent n) :=
  .of_discrete

theorem sum_stableMarkEvent_indicator_one {n : ℕ} (p : Profile n) :
    (∑ a : Matching n, (stableMarkEvent n).indicator 1 (p, a)) =
      (numStableMatchings p : ℝ≥0∞) := by
  classical
  change (∑ a : Matching n, if IsStable p a then (1 : ℝ≥0∞) else 0) =
    (Fintype.card {a : Matching n // IsStable p a} : ℝ≥0∞)
  rw [Fintype.card_subtype, ← Finset.sum_filter]
  simp

theorem markedNormalizer_stableMarkEvent (n : ℕ) :
    markedNormalizer (uniformProfile n).toMeasure (stableMarkEvent n) =
      ENNReal.ofReal (expectedNumStableMatchings n) := by
  rw [expectedNumStableMatchings, ofReal_integral_eq_lintegral_ofReal
    (memLp_one_iff_integrable.mp MemLp.of_discrete)
    (Filter.Eventually.of_forall fun _ ↦ Nat.cast_nonneg _)]
  simp [markedNormalizer, sum_stableMarkEvent_indicator_one]

theorem uniform_profile_stable_mark_ne_zero (n : ℕ) :
    ((uniformProfile n).toMeasure.prod (uniformMarkLaw (Matching n))) (stableMarkEvent n) ≠ 0 := by
  let p : Profile n := ⟨fun _ ↦ Equiv.refl _, fun _ ↦ Equiv.refl _⟩
  let m : Matching n := Equiv.refl _
  have hm : IsStable p m := fun _ _ hb ↦ lt_asymm hb.2.1 hb.2.2
  exact ne_of_gt <| calc
    0 < ((uniformProfile n).toMeasure.prod (uniformMarkLaw (Matching n))) {(p, m)} := by
      rw [← Set.singleton_prod_singleton, Measure.prod_prod]
      simp only [uniformProfile, uniformMarkLaw, PMF.toMeasure_apply_singleton _ _
        (measurableSet_singleton _), PMF.uniformOfFintype_apply]
      simp [pos_iff_ne_zero]
    _ ≤ ((uniformProfile n).toMeasure.prod (uniformMarkLaw (Matching n))) (stableMarkEvent n) :=
      measure_mono (Set.singleton_subset_iff.mpr hm)

end StableMarriage

end LennonPittelFormalization

end

section

open Function MeasureTheory Set

namespace LennonPittelFormalization

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

noncomputable def rankPermutation {n : ℕ} (x : Fin n → ℝ) : Equiv.Perm (Fin n) := by
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

abbrev ScoreProfile (n : ℕ) := (Fin n ⊕ Fin n) → Fin n → ℝ

noncomputable def profileOfScores {n : ℕ} (x : ScoreProfile n) : StableMarriage.Profile n :=
  ⟨fun m ↦ rankPermutation (x (.inl m)), fun w ↦ rankPermutation (x (.inr w))⟩

def IsScoreBlockingPair {n : ℕ} (x : ScoreProfile n) (μ : StableMarriage.Matching n)
    (m w : Fin n) : Prop :=
  μ m ≠ w ∧ x (.inl m) w < x (.inl m) (μ m) ∧ x (.inr w) m < x (.inr w) (μ.symm w)

def IsScoreStable {n : ℕ} (x : ScoreProfile n) (μ : StableMarriage.Matching n) : Prop :=
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

theorem measurableSet_scoreStableEvent (n : ℕ) [MeasurableSpace (StableMarriage.Matching n)]
    [MeasurableSingletonClass (StableMarriage.Matching n)] :
    MeasurableSet {z : ScoreProfile n × StableMarriage.Matching n | IsScoreStable z.1 z.2} :=
  (measurable_from_prod_countable_left fun μ ↦
    measurableSet_setOfPred.mp (measurableSet_isScoreStable μ)).setOf

end LennonPittelFormalization

end

section

open scoped BigOperators ENNReal LennonPittelFormalization

open MeasureTheory Set

namespace LennonPittelFormalization

noncomputable def unitScoreLaw : Measure ℝ :=
  volume.restrict (Icc 0 1)

instance : IsProbabilityMeasure unitScoreLaw :=
  ⟨by simp [unitScoreLaw, Real.volume_Icc]⟩

instance : NullSingletonClass unitScoreLaw :=
  Measure.restrict.instNullSingletonClass _

private noncomputable def rankRowsEquiv (n : ℕ) :
    ((Fin n ⊕ Fin n) → Equiv.Perm (Fin n)) ≃ StableMarriage.Profile n where
  toFun p := ⟨p ∘ Sum.inl, p ∘ Sum.inr⟩
  invFun p := Sum.elim p.manRank p.womanRank
  left_inv _ := funext fun i ↦ Sum.rec (fun _ ↦ rfl) (fun _ ↦ rfl) i
  right_inv := fun ⟨_, _⟩ ↦ rfl

private theorem measurePreserving_rankRowsEquiv (n : ℕ) :
    MeasurePreserving (rankRowsEquiv n)
      (Measure.pi fun _ : Fin n ⊕ Fin n ↦
        (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure)
      (StableMarriage.uniformProfile n).toMeasure := by
  refine ⟨measurable_of_countable _, Measure.ext_of_singleton fun p ↦ ?_⟩
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton p)]
  rw [show (rankRowsEquiv n) ⁻¹' {p} = {(rankRowsEquiv n).symm p} by
    ext x
    simp [← Equiv.eq_symm_apply]]
  rw [StableMarriage.uniformProfile, PMF.toMeasure_apply_singleton _ p (measurableSet_singleton _)]
  simp [← Fintype.card_congr (rankRowsEquiv n), ENNReal.inv_pow]

noncomputable def continuousScoreLaw (n : ℕ) : Measure (ScoreProfile n) :=
  Measure.pi fun _ : Fin n ⊕ Fin n ↦ Measure.pi fun _ : Fin n ↦ unitScoreLaw

instance (n : ℕ) : IsProbabilityMeasure (continuousScoreLaw n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : Fin n ⊕ Fin n ↦
    Measure.pi fun _ : Fin n ↦ unitScoreLaw))

theorem ae_injective_rows (n : ℕ) :
    ∀ᵐ x ∂continuousScoreLaw n, ∀ r, Function.Injective (x r) :=
  ae_all_iff.2 fun _ ↦ Measure.tendsto_eval_ae_ae.eventually (ae_injective_iid unitScoreLaw n)

theorem measurePreserving_profileOfScores (n : ℕ) :
    MeasurePreserving (@profileOfScores n) (continuousScoreLaw n)
      (StableMarriage.uniformProfile n).toMeasure :=
  (measurePreserving_rankRowsEquiv n).comp
    (measurePreserving_pi _ _ fun _ ↦
      measurePreserving_rank_of_iid unitScoreLaw (measurable_rankPermutation n)
        (fun _ hx ↦ rankPermutation_lt_iff hx))

def scoreMarkEvent (n : ℕ) : Set (ScoreProfile n × StableMarriage.Matching n) :=
  {z | IsScoreStable z.1 z.2}

private theorem measurableSet_scoreMarkEvent (n : ℕ) :
    MeasurableSet (scoreMarkEvent n) :=
  measurableSet_scoreStableEvent n

theorem measurePreserving_scoreAndMark (n : ℕ) :
    MeasurePreserving (Prod.map (@profileOfScores n) id)
      ((continuousScoreLaw n).prod (uniformMarkLaw (StableMarriage.Matching n)))
      ((StableMarriage.uniformProfile n).toMeasure.prod
        (uniformMarkLaw (StableMarriage.Matching n))) :=
  (measurePreserving_profileOfScores n).prod (MeasurePreserving.id _)

theorem score_mark_event_ae_eq (n : ℕ) :
    scoreMarkEvent n =ᵐ[((continuousScoreLaw n).prod
      (uniformMarkLaw (StableMarriage.Matching n)))]
      (Prod.map (@profileOfScores n) id) ⁻¹' stableMarkEvent n :=
  ((Measure.quasiMeasurePreserving_fst
    (μ := continuousScoreLaw n) (ν := uniformMarkLaw (StableMarriage.Matching n))).ae
      (ae_injective_rows n)).mono fun z hz ↦
    propext (isStable_profileOfScores_iff hz z.2).symm

theorem score_mark_event_mass_eq (n : ℕ) :
    ((continuousScoreLaw n).prod (uniformMarkLaw (StableMarriage.Matching n))) (scoreMarkEvent n) =
    ((StableMarriage.uniformProfile n).toMeasure.prod
      (uniformMarkLaw (StableMarriage.Matching n))) (stableMarkEvent n) :=
  (measure_congr (score_mark_event_ae_eq n)).trans
    ((measurePreserving_scoreAndMark n).measure_preimage
      (measurableSet_stableMarkEvent n).nullMeasurableSet)

noncomputable def scoreMarkedLaw (n : ℕ) :
    Measure (ScoreProfile n × StableMarriage.Matching n) :=
  markedLaw (continuousScoreLaw n) (scoreMarkEvent n)

instance (n : ℕ) : IsProbabilityMeasure (scoreMarkedLaw n) :=
  markedLaw_isProbabilityMeasure (continuousScoreLaw n)
    ((score_mark_event_mass_eq n).trans_ne (uniform_profile_stable_mark_ne_zero n))

theorem markedNormalizer_scoreMarkEvent (n : ℕ) :
    markedNormalizer (continuousScoreLaw n) (scoreMarkEvent n) =
      ENNReal.ofReal (StableMarriage.expectedNumStableMatchings n) := by
  have h := congrArg ((Fintype.card (StableMarriage.Matching n) : ℝ≥0∞) * ·)
    (score_mark_event_mass_eq n)
  simpa only [uniform_mark_event_mass _ (measurableSet_scoreMarkEvent n),
    uniform_mark_event_mass _ (measurableSet_stableMarkEvent n), ← mul_assoc,
    ENNReal.mul_inv_cancel (a := (Fintype.card (StableMarriage.Matching n) : ℝ≥0∞))
      (by simp [Fintype.card_ne_zero]) (by simp), one_mul,
    markedNormalizer_stableMarkEvent] using h

theorem continuous_mark_counting_identity (n : ℕ)
    {f : ScoreProfile n × StableMarriage.Matching n → ℝ≥0∞} (hf : Measurable f) :
    ENNReal.ofReal (StableMarriage.expectedNumStableMatchings n) *
      (∫⁻ z, f z ∂scoreMarkedLaw n) =
      ∫⁻ x, ∑ m, (scoreMarkEvent n).indicator f (x, m) ∂continuousScoreLaw n := by
  simpa only [markedNormalizer_scoreMarkEvent, scoreMarkedLaw] using
    marked_counting_identity (continuousScoreLaw n) (measurableSet_scoreMarkEvent n)
      ((score_mark_event_mass_eq n).trans_ne (uniform_profile_stable_mark_ne_zero n)) hf

end LennonPittelFormalization

end

section

open Filter MeasureTheory Set StableMarriage

open scoped BigOperators ENNReal LennonPittelFormalization

namespace LennonPittelFormalization

variable {n : ℕ}

def maleSpouseScore (x : ScoreProfile n) (μ : Matching n) (i : Fin n) : ℝ :=
  x (.inl i) (μ i)

def femaleSpouseScore (x : ScoreProfile n) (μ : Matching n) (j : Fin n) : ℝ :=
  x (.inr j) (μ.symm j)

end LennonPittelFormalization

end

section

open Filter MeasureTheory Set StableMarriage

open scoped ENNReal BigOperators Topology

namespace LennonPittelFormalization

def scoreSimplex (n : ℕ) (s : ℝ) : Set (Fin n → ℝ) :=
  {y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ s}

theorem measurableSet_scoreSimplex (n : ℕ) (s : ℝ) :
    MeasurableSet (scoreSimplex n s) := by
  unfold scoreSimplex
  rw [ofPred_and, ofPred_forall]
  exact (MeasurableSet.iInter fun i ↦ measurableSet_le measurable_const (measurable_pi_apply i)).inter
    (measurableSet_le (Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i) measurable_const)

theorem volume_scoreSimplex (n : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    volume (scoreSimplex n s) = ENNReal.ofReal (s ^ n / (n.factorial : ℝ)) := by
  induction n generalizing s with
  | zero =>
    simp [scoreSimplex, hs, volume_pi]
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0
    let S : Set (ℝ × (Fin n → ℝ)) :=
      {a | 0 ≤ a.1 ∧ a.2 ∈ scoreSimplex n (s - a.1)}
    have heq : e ⁻¹' S = scoreSimplex (n + 1) s := by
      ext y
      simp only [e, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply,
        Fin.removeNth, Fin.succAbove_zero, Set.mem_preimage, S, scoreSimplex, mem_ofPred_eq,
        Fin.forall_fin_succ, Fin.sum_univ_succ]
      exact ⟨fun h ↦ ⟨⟨h.1, h.2.1⟩, by linarith [h.2.2]⟩,
        fun h ↦ ⟨h.1.1, h.1.2, by linarith [h.2]⟩⟩
    have hS : MeasurableSet S :=
      e.measurableSet_preimage.mp (heq.symm ▸ measurableSet_scoreSimplex _ _)
    have he : MeasurePreserving e volume volume :=
      volume_preserving_piFinSuccAbove _ _
    rw [← heq, he.measure_preimage_emb e.measurableEmbedding]
    change ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) S = _
    rw [Measure.prod_apply hS]
    let f (t : ℝ) : ℝ := (s - t) ^ n / (n.factorial : ℝ)
    have hslice (t : ℝ) :
        volume (Prod.mk t ⁻¹' S) = (Icc 0 s).indicator (fun t ↦ ENNReal.ofReal (f t)) t := by
      by_cases ht : t ∈ Icc 0 s
      · rw [indicator_of_mem ht, ← ih (sub_nonneg.mpr ht.2)]
        congr 1
        ext y
        change (0 ≤ t ∧ y ∈ scoreSimplex n (s - t)) ↔ y ∈ scoreSimplex n (s - t)
        exact and_iff_right ht.1
      · rw [indicator_of_notMem ht]
        have hempty : Prod.mk t ⁻¹' S = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro y hy
          change 0 ≤ t ∧ (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ s - t at hy
          have hsum : 0 ≤ ∑ i, y i := Finset.sum_nonneg fun i _ ↦ hy.2.1 i
          exact ht ⟨hy.1, by linarith [hy.2.2]⟩
        rw [hempty, measure_empty]
    rw [lintegral_congr hslice, lintegral_indicator measurableSet_Icc]
    have hfi : IntegrableOn f (Icc 0 s) := (by fun_prop : Continuous f).integrableOn_Icc
    rw [← ofReal_integral_eq_lintegral_ofReal hfi
      ((ae_restrict_mem measurableSet_Icc).mono fun t ht ↦ by
        dsimp only [f]
        exact div_nonneg (pow_nonneg (sub_nonneg.mpr ht.2) _) (Nat.cast_nonneg _))]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs]
    congr 1
    dsimp only [f]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_sub_left (fun x : ℝ ↦ x ^ n) s, sub_self,
      sub_zero, integral_pow, zero_pow (by omega : n + 1 ≠ 0), sub_zero, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_succ]
    simp [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm]

end LennonPittelFormalization

end

section

open Set

open scoped BigOperators

namespace LennonPittelFormalization

variable {ι : Type*}

noncomputable def scoreRowKernel (J : Finset ι) (y : ι → ℝ) (x : ℝ) : ℝ :=
  ∏ j ∈ J, (1 - x * y j)

noncomputable def scoreRowMass (J : Finset ι) (y : ι → ℝ) (a b : ℝ) : ℝ :=
  ∫ x in a..b, scoreRowKernel J y x

theorem continuous_scoreRowKernel (J : Finset ι) (y : ι → ℝ) :
    Continuous (scoreRowKernel J y) := by
  unfold scoreRowKernel
  fun_prop

private theorem scoreRowKernel_nonneg {J : Finset ι} {y : ι → ℝ}
    (hy₀ : ∀ j ∈ J, 0 ≤ y j) (hy₁ : ∀ j ∈ J, y j ≤ 1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ scoreRowKernel J y x := by
  unfold scoreRowKernel
  exact Finset.prod_nonneg fun j hj ↦ sub_nonneg.mpr (calc
    x * y j ≤ 1 * y j := mul_le_mul_of_nonneg_right hx.2 (hy₀ j hj)
    _ ≤ 1 := by simpa using hy₁ j hj)

theorem scoreRowKernel_le_exp {J : Finset ι} {y : ι → ℝ}
    (hy₀ : ∀ j ∈ J, 0 ≤ y j) (hy₁ : ∀ j ∈ J, y j ≤ 1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    scoreRowKernel J y x ≤ Real.exp (-(∑ j ∈ J, y j) * x) := by
  unfold scoreRowKernel
  rw [show -(∑ j ∈ J, y j) * x = ∑ j ∈ J, -(x * y j) by
    calc
      -(∑ j ∈ J, y j) * x = -(x * ∑ j ∈ J, y j) := by ring
      _ = _ := by rw [Finset.mul_sum, Finset.sum_neg_distrib], Real.exp_sum]
  exact Finset.prod_le_prod
    (fun j hj ↦ sub_nonneg.mpr (calc
      x * y j ≤ 1 * y j := mul_le_mul_of_nonneg_right hx.2 (hy₀ j hj)
      _ ≤ 1 := by simpa using hy₁ j hj))
    (fun j _ ↦ Real.one_sub_le_exp_neg _)

private theorem integral_exp_neg_mul {r a b : ℝ} (hr : 0 < r) :
    (∫ x in a..b, Real.exp (-r * x)) = (Real.exp (-r * a) - Real.exp (-r * b)) / r := by
  have h := intervalIntegral.mul_integral_comp_mul_left (a := a) (b := b) (f := Real.exp) (-r)
  rw [integral_exp] at h
  apply (eq_div_iff hr.ne').2
  linarith only [h]


theorem scoreRowMass_le_exp_tail {J : Finset ι} {y : ι → ℝ}
    (hy₀ : ∀ j ∈ J, 0 ≤ y j) (hy₁ : ∀ j ∈ J, y j ≤ 1)
    {r a b : ℝ} (hr : 0 < r) (hrsum : r ≤ ∑ j ∈ J, y j)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    scoreRowMass J y a b ≤ Real.exp (-r * a) / r := by
  calc
    scoreRowMass J y a b ≤ ∫ x in a..b, Real.exp (-r * x) := by
      unfold scoreRowMass
      refine intervalIntegral.integral_mono_on hab
        ((continuous_scoreRowKernel J y).intervalIntegrable _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _) fun x hx ↦ ?_
      have hx' : x ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hx.1, hx.2.trans hb⟩
      exact (scoreRowKernel_le_exp hy₀ hy₁ hx').trans (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (neg_le_neg hrsum) hx'.1))
    _ = (Real.exp (-r * a) - Real.exp (-r * b)) / r := integral_exp_neg_mul hr
    _ ≤ Real.exp (-r * a) / r :=
      div_le_div_of_nonneg_right (sub_le_self _ (Real.exp_pos _).le) hr.le

theorem scoreRowMass_le_finite_exp {J : Finset ι} {y : ι → ℝ}
    (hy₀ : ∀ j ∈ J, 0 ≤ y j) (hy₁ : ∀ j ∈ J, y j ≤ 1)
    {s c : ℝ} (hs : 0 < s) (hc : 0 ≤ c) (hsum : s - c ≤ ∑ j ∈ J, y j) :
    scoreRowMass J y 0 1 ≤ Real.exp c * ((1 - Real.exp (-s)) / s) := by
  calc
    scoreRowMass J y 0 1 ≤ ∫ x in (0 : ℝ)..1, Real.exp c * Real.exp (-s * x) := by
      unfold scoreRowMass
      refine intervalIntegral.integral_mono_on (by norm_num)
        ((continuous_scoreRowKernel J y).intervalIntegrable _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _) fun x hx ↦ ?_
      refine (scoreRowKernel_le_exp hy₀ hy₁ hx).trans ?_
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h₁ := mul_le_mul_of_nonneg_right (neg_le_neg hsum) hx.1
      have h₂ := mul_le_mul_of_nonneg_left hx.2 hc
      nlinarith only [h₁, h₂]
    _ = _ := by rw [intervalIntegral.integral_const_mul, integral_exp_neg_mul hs]; simp

section FiniteRows

variable [Fintype ι] [DecidableEq ι]

private theorem sum_erase_eq_total_sub (y : ι → ℝ) (i : ι) :
    ∑ j ∈ Finset.univ.erase i, y j = (∑ j, y j) - y i := by
  linarith only [Finset.sum_erase_add Finset.univ y (Finset.mem_univ i)]

theorem scoreRowMass_erase_le_inv (y : ι → ℝ) (i : ι)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (hs : 2 ≤ ∑ j, y j) :
    scoreRowMass (Finset.univ.erase i) y 0 1 ≤ 1 / ((∑ j, y j) - y i) := by
  have hr : 0 < (∑ j, y j) - y i := by linarith [(hy i).2]
  simpa using scoreRowMass_le_exp_tail
    (J := Finset.univ.erase i) (y := y)
    (fun j _ ↦ (hy j).1) (fun j _ ↦ (hy j).2) hr
    (sum_erase_eq_total_sub y i).ge le_rfl (by norm_num) le_rfl

theorem scoreRowMass_erase_le_finite_exp (y : ι → ℝ) (i : ι)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (hs : 0 < ∑ j, y j) :
    scoreRowMass (Finset.univ.erase i) y 0 1 ≤
      Real.exp (y i) * ((1 - Real.exp (-(∑ j, y j))) / (∑ j, y j)) :=
  scoreRowMass_le_finite_exp (fun j _ ↦ (hy j).1) (fun j _ ↦ (hy j).2)
    hs (hy i).1 (sum_erase_eq_total_sub y i).ge

theorem scoreRowMass_prod_le_finite_exp (y : ι → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (hs : 0 < ∑ j, y j) :
    (∏ i, scoreRowMass (Finset.univ.erase i) y 0 1) ≤
      Real.exp (∑ j, y j) * ((1 - Real.exp (-(∑ j, y j))) / (∑ j, y j)) ^
        Fintype.card ι := by
  calc
    _ ≤ ∏ i, Real.exp (y i) * ((1 - Real.exp (-(∑ j, y j))) / (∑ j, y j)) :=
      Finset.prod_le_prod (fun _ _ ↦ intervalIntegral.integral_nonneg (by norm_num)
        fun _ hx ↦ scoreRowKernel_nonneg (fun j _ ↦ (hy j).1) (fun j _ ↦ (hy j).2) hx)
        (fun i _ ↦ scoreRowMass_erase_le_finite_exp y i hy hs)
    _ = _ := by rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.prod_const,
      Finset.card_univ]

theorem scoreRowMass_prod_le_inv_pow (y : ι → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (hs : 2 ≤ ∑ j, y j) :
    (∏ i, scoreRowMass (Finset.univ.erase i) y 0 1) ≤
      Real.exp 2 / (∑ j, y j) ^ Fintype.card ι := by
  let s := ∑ j, y j
  have hs₀ : 0 < s := by dsimp [s]; linarith
  have hi (i : ι) : 1 / (s - y i) ≤ Real.exp (2 * (y i / s)) / s := by
    let z := y i / s
    have hz₀ : 0 ≤ z := div_nonneg (hy i).1 hs₀.le
    have hz₁ : z ≤ 1 / 2 := by
      dsimp [z]
      rw [div_le_iff₀ hs₀]
      dsimp [s]
      linarith [(hy i).2]
    have hprod : 1 ≤ (1 + 2 * z) * (1 - z) := by
      have hmul := mul_nonneg hz₀ (show 0 ≤ 1 - 2 * z by linarith)
      nlinarith only [hmul]
    have hlinear : 1 + 2 * z ≤ Real.exp (2 * z) := by
      simpa only [add_comm] using Real.add_one_le_exp (2 * z)
    have hexp : 1 ≤ Real.exp (2 * z) * (1 - z) :=
      hprod.trans (mul_le_mul_of_nonneg_right hlinear (by linarith))
    have hsi : 0 < s - y i := by dsimp [s]; linarith [(hy i).2]
    have heq : (s - y i) / s = 1 - z := by rw [sub_div, div_self hs₀.ne']
    rw [div_le_div_iff₀ hsi hs₀, one_mul]
    calc
      s = 1 * s := (one_mul s).symm
      _ ≤ Real.exp (2 * (y i / s)) * (s - y i) := (le_div_iff₀ hs₀).mp (by
        change 1 ≤ (Real.exp (2 * z) * (s - y i)) / s
        rw [mul_div_assoc, heq]
        exact hexp)
  calc
    _ ≤ ∏ i, Real.exp (2 * (y i / s)) / s :=
      Finset.prod_le_prod (fun _ _ ↦ intervalIntegral.integral_nonneg (by norm_num)
        fun _ hx ↦ scoreRowKernel_nonneg (fun j _ ↦ (hy j).1) (fun j _ ↦ (hy j).2) hx)
        (fun i _ ↦ (scoreRowMass_erase_le_inv y i hy hs).trans (hi i))
    _ = _ := by
      rw [Finset.prod_div_distrib, ← Real.exp_sum, ← Finset.mul_sum, ← Finset.sum_div]
      simp [show (∑ j, y j) / s = 1 by dsimp [s]; exact div_self hs₀.ne']
      rfl

end FiniteRows

section SuccessorMass

open MeasureTheory

open scoped ENNReal

noncomputable def rowNonblockingLaw (x y : ℝ) : Measure (ℝ × ℝ) :=
  (unitScoreLaw.prod unitScoreLaw).restrict (Iio x ×ˢ Iio y)ᶜ

instance (x y : ℝ) : IsFiniteMeasure (rowNonblockingLaw x y) := by
  unfold rowNonblockingLaw
  infer_instance

end SuccessorMass

end LennonPittelFormalization

end

section

open StableMarriage

namespace LennonPittelFormalization

variable {n : ℕ}

variable {p : Profile n} {μ : Matching n} {ρ : Equiv.Perm (Fin n)}

end LennonPittelFormalization

end

section

open MeasureTheory Set StableMarriage

open scoped BigOperators ENNReal

namespace LennonPittelFormalization

abbrev ScorePairIndex (n : ℕ) := Fin n × Fin n

abbrev DiagonalScorePairs (n : ℕ) := {q : ScorePairIndex n // q.1 = q.2} → ℝ × ℝ

abbrev OffDiagonalScorePairs (n : ℕ) := {q : ScorePairIndex n // q.1 ≠ q.2} → ℝ × ℝ

noncomputable def unitScorePairLaw : Measure (ℝ × ℝ) :=
  unitScoreLaw.prod unitScoreLaw

instance : IsProbabilityMeasure unitScorePairLaw :=
  inferInstanceAs (IsProbabilityMeasure (unitScoreLaw.prod unitScoreLaw))

noncomputable def diagonalScoreLaw (n : ℕ) : Measure (DiagonalScorePairs n) :=
  Measure.pi fun _ ↦ unitScorePairLaw

instance (n : ℕ) : IsProbabilityMeasure (diagonalScoreLaw n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : {q : ScorePairIndex n // q.1 = q.2} ↦
    unitScorePairLaw))

noncomputable def offDiagonalScoreLaw (n : ℕ) : Measure (OffDiagonalScorePairs n) :=
  Measure.pi fun _ ↦ unitScorePairLaw

instance (n : ℕ) : IsProbabilityMeasure (offDiagonalScoreLaw n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : {q : ScorePairIndex n // q.1 ≠ q.2} ↦
    unitScorePairLaw))

private theorem measurePreserving_scoreUncurry (n : ℕ) :
    MeasurePreserving (MeasurableEquiv.curry (Fin n) (Fin n) ℝ).symm
      (Measure.pi fun _ : Fin n ↦ Measure.pi fun _ : Fin n ↦ unitScoreLaw)
      (Measure.pi fun _ : ScorePairIndex n ↦ unitScoreLaw) := by
  refine ⟨(MeasurableEquiv.curry (Fin n) (Fin n) ℝ).symm.measurable, ?_⟩
  refine (Measure.pi_eq fun s hs ↦ ?_).symm
  rw [MeasurableEquiv.map_apply]
  rw [show (MeasurableEquiv.curry (Fin n) (Fin n) ℝ).symm ⁻¹' (Set.univ.pi s) =
      Set.univ.pi (fun i ↦ Set.univ.pi fun j ↦ s (i,j)) by
    ext x
    simp [Set.mem_pi, Prod.forall]]
  simp_rw [Measure.pi_pi]
  rw [← Finset.prod_product']
  simp

def manScoreIndex {n : ℕ} (μ : Matching n) : ScorePairIndex n ≃ ScorePairIndex n :=
  Equiv.prodCongr (Equiv.refl _) μ

def womanScoreIndex {n : ℕ} (μ : Matching n) : ScorePairIndex n ≃ ScorePairIndex n :=
  (manScoreIndex μ).trans (Equiv.prodComm _ _)

def scorePairEquiv {n : ℕ} (μ : Matching n) :
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

private theorem measurePreserving_scorePairEquiv {n : ℕ} (μ : Matching n) :
    MeasurePreserving (scorePairEquiv μ) (continuousScoreLaw n)
      (Measure.pi fun _ : ScorePairIndex n ↦ unitScorePairLaw) := by
  exact ((measurePreserving_arrowProdEquivProdArrow ℝ ℝ (ScorePairIndex n)
    (fun _ ↦ unitScoreLaw) (fun _ ↦ unitScoreLaw)).symm).comp
    ((((measurePreserving_piCongrLeft (fun _ ↦ unitScoreLaw) (manScoreIndex μ).symm).comp
      (measurePreserving_scoreUncurry n)).prod
      ((measurePreserving_piCongrLeft (fun _ ↦ unitScoreLaw) (womanScoreIndex μ).symm).comp
        (measurePreserving_scoreUncurry n))).comp
      (measurePreserving_sumPiEquivProdPi (fun _ ↦ Measure.pi fun _ : Fin n ↦ unitScoreLaw)))

def splitScorePairs {n : ℕ} (μ : Matching n) :
    ScoreProfile n ≃ᵐ DiagonalScorePairs n × OffDiagonalScorePairs n :=
  (scorePairEquiv μ).trans
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ScorePairIndex n ↦ ℝ × ℝ)
      fun q ↦ q.1 = q.2)

theorem measurePreserving_splitScorePairs {n : ℕ} (μ : Matching n) :
    MeasurePreserving (splitScorePairs μ) (continuousScoreLaw n)
      ((diagonalScoreLaw n).prod (offDiagonalScoreLaw n)) :=
  (measurePreserving_piEquivPiSubtypeProd (fun _ ↦ unitScorePairLaw)
    fun q : ScorePairIndex n ↦ q.1 = q.2).comp
    (measurePreserving_scorePairEquiv μ)

def diagonalPairAt {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n) : ℝ × ℝ :=
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

theorem unitScoreLaw_Iio_of_mem_Icc {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    unitScoreLaw (Set.Iio x) = ENNReal.ofReal x := by
  rw [unitScoreLaw, Measure.restrict_apply measurableSet_Iio]
  rw [show Set.Iio x ∩ Set.Icc 0 1 = Set.Ico 0 x by
    ext t
    exact ⟨fun ⟨hlt, hlo, _⟩ ↦ ⟨hlo, hlt⟩,
      fun ⟨hlo, hlt⟩ ↦ ⟨hlt, hlo, hlt.le.trans hx.2⟩⟩]
  rw [Real.volume_Ico, sub_zero]

def nonblockingScoreCell (x y : ℝ) : Set (ℝ × ℝ) :=
  (Set.Iio x ×ˢ Set.Iio y)ᶜ

theorem unitScorePairLaw_nonblockingScoreCell (x y : ℝ) :
    unitScorePairLaw (nonblockingScoreCell x y) =
      1 - unitScoreLaw (Set.Iio x) * unitScoreLaw (Set.Iio y) := by
  rw [nonblockingScoreCell, measure_compl (measurableSet_Iio.prod measurableSet_Iio)
    (measure_ne_top _ _), measure_univ, unitScorePairLaw, Measure.prod_prod]

theorem unitScorePairLaw_nonblockingScoreCell_of_mem_Icc {x y : ℝ}
    (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) :
    unitScorePairLaw (nonblockingScoreCell x y) = ENNReal.ofReal (1 - x * y) := by
  rw [unitScorePairLaw_nonblockingScoreCell, unitScoreLaw_Iio_of_mem_Icc hx,
    unitScoreLaw_Iio_of_mem_Icc hy, ← ENNReal.ofReal_mul hx.1, ENNReal.ofReal_sub _]
  · rw [ENNReal.ofReal_one]
  · exact mul_nonneg hx.1 hy.1

def offDiagonalNonblocking {n : ℕ} (d : DiagonalScorePairs n) :
    Set (OffDiagonalScorePairs n) :=
  Set.univ.pi fun q ↦
    nonblockingScoreCell (diagonalPairAt d q.val.1).1 (diagonalPairAt d q.val.2).2

theorem offDiagonalScoreLaw_nonblocking {n : ℕ} (d : DiagonalScorePairs n) :
    offDiagonalScoreLaw n (offDiagonalNonblocking d) =
      ∏ q : {q : ScorePairIndex n // q.1 ≠ q.2},
        unitScorePairLaw
          (nonblockingScoreCell (diagonalPairAt d q.val.1).1 (diagonalPairAt d q.val.2).2) :=
  Measure.pi_pi _ _

theorem offDiagonalScoreLaw_nonblocking_of_mem_Icc {n : ℕ} (d : DiagonalScorePairs n)
    (hd : ∀ i, (diagonalPairAt d i).1 ∈ Set.Icc 0 1 ∧
      (diagonalPairAt d i).2 ∈ Set.Icc 0 1) :
    offDiagonalScoreLaw n (offDiagonalNonblocking d) =
      ∏ q : {q : ScorePairIndex n // q.1 ≠ q.2},
        ENNReal.ofReal (1 - (diagonalPairAt d q.val.1).1 * (diagonalPairAt d q.val.2).2) := by
  rw [offDiagonalScoreLaw_nonblocking]
  exact Finset.prod_congr rfl fun q _ ↦
    unitScorePairLaw_nonblockingScoreCell_of_mem_Icc (hd q.val.1).1 (hd q.val.2).2

theorem isScoreStable_iff_splitScorePairs {n : ℕ} (μ : Matching n) (x : ScoreProfile n) :
    IsScoreStable x μ ↔ (splitScorePairs μ x).2 ∈
      offDiagonalNonblocking (splitScorePairs μ x).1 := by
  constructor
  · intro h q _
    simp only [nonblockingScoreCell, Set.mem_compl_iff, Set.mem_prod, Set.mem_Iio,
      splitScorePairs_offDiagonal_apply, diagonalPairAt_splitScorePairs]
    exact fun ⟨hm, hw⟩ ↦ h q.val.1 (μ q.val.2)
      ⟨μ.injective.ne q.property, hm, by simpa only [Equiv.symm_apply_apply] using hw⟩
  · intro h i w hw
    let j := μ.symm w
    have hj : μ j = w := μ.apply_symm_apply w
    have hij : i ≠ j := fun he ↦ hw.1 ((congrArg μ he).trans hj)
    have hcell := h (i := ⟨(i,j), hij⟩) (Set.mem_univ _)
    simp only [nonblockingScoreCell, Set.mem_compl_iff, Set.mem_prod, Set.mem_Iio,
      splitScorePairs_offDiagonal_apply, diagonalPairAt_splitScorePairs] at hcell
    apply hcell
    exact ⟨by simpa only [hj] using hw.2.1, by simpa only [hj] using hw.2.2⟩

private def diagonalIndexEquiv (n : ℕ) :
    {q : ScorePairIndex n // q.1 = q.2} ≃ Fin n where
  toFun q := q.val.1
  invFun i := ⟨(i,i), rfl⟩
  left_inv q := Subtype.ext (Prod.ext rfl q.property)
  right_inv _ := rfl

theorem measurePreserving_diagonalScoreVectors (n : ℕ) :
    MeasurePreserving (fun d : DiagonalScorePairs n ↦
      ((fun i ↦ (diagonalPairAt d i).1), (fun i ↦ (diagonalPairAt d i).2)))
      (diagonalScoreLaw n)
      ((Measure.pi fun _ : Fin n ↦ unitScoreLaw).prod
        (Measure.pi fun _ : Fin n ↦ unitScoreLaw)) := by
  exact (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)
    (fun _ ↦ unitScoreLaw) (fun _ ↦ unitScoreLaw)).comp
    (measurePreserving_piCongrLeft (fun _ ↦ unitScorePairLaw) (diagonalIndexEquiv n))

theorem ae_diagonalPairAt_mem_Icc (n : ℕ) :
    ∀ᵐ d ∂diagonalScoreLaw n, ∀ i, (diagonalPairAt d i).1 ∈ Set.Icc 0 1 ∧
      (diagonalPairAt d i).2 ∈ Set.Icc 0 1 := by
  have hu : ∀ᵐ t ∂unitScoreLaw, t ∈ Set.Icc 0 1 := ae_restrict_mem measurableSet_Icc
  have hp : ∀ᵐ z ∂unitScorePairLaw, z.1 ∈ Set.Icc 0 1 ∧ z.2 ∈ Set.Icc 0 1 :=
    ((Measure.quasiMeasurePreserving_fst (μ := unitScoreLaw)
      (ν := unitScoreLaw)).ae hu).and
      ((Measure.quasiMeasurePreserving_snd (μ := unitScoreLaw)
        (ν := unitScoreLaw)).ae hu)
  exact ae_all_iff.2 fun i ↦ (Measure.tendsto_eval_ae_ae
    (μ := fun _ : {q : ScorePairIndex n // q.1 = q.2} ↦ unitScorePairLaw)
    (i := ⟨(i,i), rfl⟩)).eventually hp

theorem continuousScoreLaw_stable_and_diagonal {n : ℕ} (μ : Matching n)
    {C : Set (DiagonalScorePairs n)} (hC : MeasurableSet C) :
    continuousScoreLaw n {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C} =
      ∫⁻ d, C.indicator (fun d ↦ offDiagonalScoreLaw n (offDiagonalNonblocking d)) d
        ∂diagonalScoreLaw n := by
  let E : Set (DiagonalScorePairs n × OffDiagonalScorePairs n) :=
    {z | z.1 ∈ C ∧ z.2 ∈ offDiagonalNonblocking z.1}
  have hE_pre : E = (splitScorePairs μ).symm ⁻¹'
      {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C} := by
    ext z
    have h := isScoreStable_iff_splitScorePairs μ ((splitScorePairs μ).symm z)
    simpa [E, and_comm] using
      (and_congr_right fun _ : z.1 ∈ C ↦ h.symm)
  have hE : MeasurableSet E := hE_pre ▸
    (((measurableSet_isScoreStable μ).inter
      ((measurable_fst.comp (splitScorePairs μ).measurable) hC)).preimage
      (splitScorePairs μ).symm.measurable)
  calc
    _ = (continuousScoreLaw n) ((splitScorePairs μ) ⁻¹' E) := by
      congr 1
      ext x
      simp [E, ← isScoreStable_iff_splitScorePairs, and_comm]
    _ = (diagonalScoreLaw n).prod (offDiagonalScoreLaw n) E :=
      (measurePreserving_splitScorePairs μ).measure_preimage hE.nullMeasurableSet
    _ = _ := by
      rw [Measure.prod_apply hE]
      refine lintegral_congr fun d ↦ ?_
      by_cases hd : d ∈ C
      · rw [Set.indicator_of_mem hd]
        congr 1
        ext v
        simp [E, hd]
      · rw [Set.indicator_of_notMem hd]
        have hempty : Prod.mk d ⁻¹' E = ∅ := by
          ext v
          simp [E, hd]
        rw [hempty, measure_empty]

theorem continuousScoreLaw_stable_and_diagonal_prod {n : ℕ} (μ : Matching n)
    {C : Set (DiagonalScorePairs n)} (hC : MeasurableSet C) :
    continuousScoreLaw n {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C} =
      ∫⁻ d, C.indicator (fun d ↦ ∏ q : {q : ScorePairIndex n // q.1 ≠ q.2},
        ENNReal.ofReal (1 - (diagonalPairAt d q.val.1).1 * (diagonalPairAt d q.val.2).2)) d
        ∂diagonalScoreLaw n := by
  rw [continuousScoreLaw_stable_and_diagonal μ hC]
  apply lintegral_congr_ae
  filter_upwards [ae_diagonalPairAt_mem_Icc n] with d hd
  by_cases hc : d ∈ C
  · simpa only [Set.indicator_of_mem hc] using offDiagonalScoreLaw_nonblocking_of_mem_Icc d hd
  · simp only [Set.indicator_of_notMem hc]

noncomputable def stableScoreRowLaw {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n) :
    Measure ({j : Fin n // i ≠ j} → ℝ × ℝ) :=
  Measure.pi fun j ↦ unitScorePairLaw.restrict
    (nonblockingScoreCell (diagonalPairAt d i).1 (diagonalPairAt d j.val).2)

instance {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n) :
    IsFiniteMeasure (stableScoreRowLaw d i) :=
  inferInstanceAs (IsFiniteMeasure (Measure.pi fun j : {j : Fin n // i ≠ j} ↦
    unitScorePairLaw.restrict
      (nonblockingScoreCell (diagonalPairAt d i).1 (diagonalPairAt d j.val).2)))

end LennonPittelFormalization

end

section

open Filter MeasureTheory ProbabilityTheory Set StableMarriage

open scoped BigOperators ENNReal Topology

namespace LennonPittelFormalization

noncomputable def spouseVectorLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ ↦ unitScoreLaw

instance (n : ℕ) : IsProbabilityMeasure (spouseVectorLaw n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : Fin n ↦ unitScoreLaw))

theorem spouseVectorLaw_eq_restrict_volume (n : ℕ) :
    spouseVectorLaw n =
      (volume : Measure (Fin n → ℝ)).restrict (univ.pi fun _ ↦ Icc (0 : ℝ) 1) := by
  rw [volume_pi, Measure.restrict_pi_pi]
  rfl

def femaleSpouseByHusband {n : ℕ} (μ : Matching n) (x : ScoreProfile n) : Fin n → ℝ :=
  fun j ↦ femaleSpouseScore x μ (μ j)

noncomputable def femaleSpouseStabilityDensity {n : ℕ} (y : Fin n → ℝ) : ℝ≥0∞ :=
  ∏ i : Fin n, ENNReal.ofReal (scoreRowMass (Finset.univ.erase i) y 0 1)

theorem measurable_femaleSpouseStabilityDensity (n : ℕ) :
    Measurable (@femaleSpouseStabilityDensity n) := by
  unfold femaleSpouseStabilityDensity
  refine Finset.measurable_prod _ fun i _ ↦ Measurable.ennreal_ofReal ?_
  have h : Measurable (fun z : (Fin n → ℝ) × ℝ ↦
      scoreRowKernel (Finset.univ.erase i) z.1 z.2) := by
    unfold scoreRowKernel
    refine Finset.measurable_prod _ fun j _ ↦ measurable_const.sub ?_
    exact measurable_snd.mul ((measurable_pi_apply j).comp measurable_fst)
  convert (h.stronglyMeasurable.integral_prod_right' (ν := unitScoreLaw)).measurable using 1
  funext y
  rw [unitScoreLaw, scoreRowMass, intervalIntegral.integral_of_le (by norm_num)]
  exact integral_Icc_eq_integral_Ioc.symm

private def spouseVectors {n : ℕ} (d : DiagonalScorePairs n) :
    (Fin n → ℝ) × (Fin n → ℝ) :=
  (fun i ↦ (diagonalPairAt d i).1, fun i ↦ (diagonalPairAt d i).2)

noncomputable def spouseStabilityKernel {n : ℕ}
    (x y : Fin n → ℝ) : ℝ≥0∞ :=
  ∏ i : Fin n, ENNReal.ofReal (scoreRowKernel (Finset.univ.erase i) y (x i))

private theorem measurable_spouseStabilityKernel (n : ℕ) :
    Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) ↦ spouseStabilityKernel z.1 z.2) := by
  unfold spouseStabilityKernel scoreRowKernel
  refine Finset.measurable_prod _ fun i _ ↦ Measurable.ennreal_ofReal ?_
  refine Finset.measurable_prod _ fun j _ ↦ measurable_const.sub ?_
  exact ((measurable_pi_apply i).comp measurable_fst).mul
    ((measurable_pi_apply j).comp measurable_snd)

private theorem ae_spouseVectorLaw_mem_Icc (n : ℕ) :
    ∀ᵐ y ∂spouseVectorLaw n, ∀ j, y j ∈ Icc (0 : ℝ) 1 :=
  ae_all_iff.2 fun j ↦
    let h := measurePreserving_eval (fun _ : Fin n ↦ unitScoreLaw) j
    h.quasiMeasurePreserving.ae (ae_restrict_mem measurableSet_Icc)

private def offDiagonalSigmaEquiv (n : ℕ) :
    {q : ScorePairIndex n // q.1 ≠ q.2} ≃ (i : Fin n) × {j : Fin n // i ≠ j} where
  toFun q := ⟨q.val.1, ⟨q.val.2, q.property⟩⟩
  invFun q := ⟨(q.1,q.2.val),q.2.property⟩
  left_inv q := by cases q; rfl
  right_inv q := by cases q; rfl

private theorem spouseStabilityKernel_eq {n : ℕ} {x y : Fin n → ℝ}
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) :
    spouseStabilityKernel x y = ∏ q : {q : ScorePairIndex n // q.1 ≠ q.2},
      ENNReal.ofReal (1 - x q.val.1 * y q.val.2) := by
  classical
  unfold spouseStabilityKernel scoreRowKernel
  trans ∏ i : Fin n, ∏ j : {j : Fin n // i ≠ j}, ENNReal.ofReal (1 - x i * y j.val)
  · refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [ENNReal.ofReal_prod_of_nonneg]
    · exact Finset.prod_subtype _ (by simp [ne_comm])
        (fun j ↦ ENNReal.ofReal (1 - x i * y j))
    · intro j _
      exact sub_nonneg.mpr
        ((mul_le_mul_of_nonneg_right (hx i).2 (hy j).1).trans (by simpa using (hy j).2))
  · rw [← Fintype.prod_sigma']
    exact Fintype.prod_equiv (offDiagonalSigmaEquiv n).symm _ _ fun _ ↦ rfl

theorem lintegral_scoreRowKernel_unitScoreLaw {n : ℕ} (J : Finset (Fin n))
    (y : Fin n → ℝ) (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) :
    (∫⁻ x, ENNReal.ofReal (scoreRowKernel J y x) ∂unitScoreLaw) =
      ENNReal.ofReal (scoreRowMass J y 0 1) := by
  have hint : Integrable (scoreRowKernel J y) unitScoreLaw :=
    (continuous_scoreRowKernel J y).integrableOn_Icc
  have hnn : 0 ≤ᵐ[unitScoreLaw] scoreRowKernel J y := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Icc :
      MeasurableSet (Icc (0 : ℝ) 1))] with x hx
    unfold scoreRowKernel
    exact Finset.prod_nonneg fun j _ ↦ sub_nonneg.mpr
      ((mul_le_mul_of_nonneg_right hx.2 (hy j).1).trans (by simpa using (hy j).2))
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [unitScoreLaw, scoreRowMass, intervalIntegral.integral_of_le (by norm_num)]
  exact integral_Icc_eq_integral_Ioc

private theorem lintegral_spouseStabilityKernel {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) :
    (∫⁻ x, spouseStabilityKernel x y ∂spouseVectorLaw n) = femaleSpouseStabilityDensity y := by
  let f (i : Fin n) (x : ℝ) := ENNReal.ofReal (scoreRowKernel (Finset.univ.erase i) y x)
  have hf (i : Fin n) : Measurable (f i) :=
    (continuous_scoreRowKernel _ _).measurable.ennreal_ofReal
  have hi := iIndepFun_pi (μ := fun _ : Fin n ↦ unitScoreLaw)
    (X := f) (fun i ↦ (hf i).aemeasurable)
  calc
    _ = ∏ i : Fin n, ∫⁻ x, f i (x i) ∂spouseVectorLaw n :=
      lintegral_prod_eq_prod_lintegral_of_indepFun _ _ hi
        (fun i ↦ (hf i).comp (measurable_pi_apply i))
    _ = _ := by
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      exact ((measurePreserving_eval (fun _ : Fin n ↦ unitScoreLaw) i).lintegral_comp
        (hf i)).trans (lintegral_scoreRowKernel_unitScoreLaw _ y hy)

theorem femaleSpouseStabilityDensity_le_one {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) :
    femaleSpouseStabilityDensity y ≤ 1 := by
  rw [← lintegral_spouseStabilityKernel y hy]
  have hone : (∫⁻ _x, 1 ∂spouseVectorLaw n) = 1 := by simp
  rw [← hone]
  apply lintegral_mono_ae
  filter_upwards [ae_spouseVectorLaw_mem_Icc n] with x hx
  rw [spouseStabilityKernel_eq hx hy]
  calc
    _ ≤ ∏ _q : {q : ScorePairIndex n // q.1 ≠ q.2}, (1 : ℝ≥0∞) := by
      refine Finset.prod_le_prod' fun q _ ↦ ?_
      rw [ENNReal.ofReal_le_one]
      exact sub_le_self _ (mul_nonneg (hx q.val.1).1 (hy q.val.2).1)
    _ = _ := Finset.prod_const_one

theorem continuousScoreLaw_stable_and_spouseVectors {n : ℕ} (μ : Matching n)
    {B : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hB : MeasurableSet B) :
    continuousScoreLaw n
        {x | IsScoreStable x μ ∧
          ((fun i ↦ maleSpouseScore x μ i), femaleSpouseByHusband μ x) ∈ B} =
      ∫⁻ z, B.indicator (fun z ↦ spouseStabilityKernel z.1 z.2) z
        ∂((spouseVectorLaw n).prod (spouseVectorLaw n)) := by
  have hv : MeasurePreserving (@spouseVectors n) (diagonalScoreLaw n)
      ((spouseVectorLaw n).prod (spouseVectorLaw n)) :=
    measurePreserving_diagonalScoreVectors n
  have hvec (x : ScoreProfile n) : spouseVectors (splitScorePairs μ x).1 =
      ((fun i ↦ maleSpouseScore x μ i), femaleSpouseByHusband μ x) := by
    apply Prod.ext <;> funext i
    · simp only [spouseVectors, diagonalPairAt_splitScorePairs, maleSpouseScore]
    · simp only [spouseVectors, diagonalPairAt_splitScorePairs, femaleSpouseByHusband,
        femaleSpouseScore, Equiv.symm_apply_apply]
  have hcut : MeasurableSet (spouseVectors ⁻¹' B) := hB.preimage hv.measurable
  have he : {x | IsScoreStable x μ ∧
      ((fun i ↦ maleSpouseScore x μ i), femaleSpouseByHusband μ x) ∈ B} =
      {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ spouseVectors ⁻¹' B} := by
    ext x
    simp [hvec]
  rw [he, continuousScoreLaw_stable_and_diagonal_prod μ hcut,
    ← hv.lintegral_comp ((measurable_spouseStabilityKernel n).indicator hB)]
  apply lintegral_congr_ae
  filter_upwards [ae_diagonalPairAt_mem_Icc n] with d hd
  by_cases h : spouseVectors d ∈ B
  · rw [indicator_of_mem (show d ∈ spouseVectors ⁻¹' B from h), indicator_of_mem h]
    exact (spouseStabilityKernel_eq (fun i ↦ (hd i).1) (fun i ↦ (hd i).2)).symm
  · rw [indicator_of_notMem (show d ∉ spouseVectors ⁻¹' B from h), indicator_of_notMem h]

theorem continuousScoreLaw_stable_and_femaleSpouse {n : ℕ} (μ : Matching n)
    {B : Set (Fin n → ℝ)} (hB : MeasurableSet B) :
    continuousScoreLaw n {x | IsScoreStable x μ ∧ femaleSpouseByHusband μ x ∈ B} =
      ∫⁻ y in B, femaleSpouseStabilityDensity y ∂spouseVectorLaw n := by
  rw [show {x | IsScoreStable x μ ∧ femaleSpouseByHusband μ x ∈ B} =
    {x | IsScoreStable x μ ∧
      ((fun i ↦ maleSpouseScore x μ i), femaleSpouseByHusband μ x) ∈ Prod.snd ⁻¹' B} from rfl,
    continuousScoreLaw_stable_and_spouseVectors μ (hB.preimage measurable_snd),
    lintegral_prod_symm' _ ((measurable_spouseStabilityKernel n).indicator
      (hB.preimage measurable_snd)), ← lintegral_indicator hB]
  apply lintegral_congr_ae
  filter_upwards [ae_spouseVectorLaw_mem_Icc n] with y hy
  by_cases h : y ∈ B
  · rw [indicator_of_mem h, ← lintegral_spouseStabilityKernel y hy]
    exact lintegral_congr fun x ↦ indicator_of_mem h _
  · rw [indicator_of_notMem h, ← lintegral_zero]
    exact lintegral_congr fun x ↦ indicator_of_notMem h _

theorem sum_measure_scoreStable_eq_expected (n : ℕ) :
    (∑ μ : Matching n, continuousScoreLaw n {x | IsScoreStable x μ}) =
      ENNReal.ofReal (expectedNumStableMatchings n) := by
  have hf (μ : Matching n) :
      Measurable ({x | IsScoreStable x μ}.indicator (1 : ScoreProfile n → ℝ≥0∞)) :=
    measurable_const.indicator (measurableSet_isScoreStable μ)
  calc
    _ = ∑ μ : Matching n, ∫⁻ x, {x | IsScoreStable x μ}.indicator 1 x ∂continuousScoreLaw n := by
      refine Finset.sum_congr rfl fun μ _ ↦ ?_
      rw [lintegral_indicator_one (measurableSet_isScoreStable μ)]
    _ = ∫⁻ x, ∑ μ : Matching n, {x | IsScoreStable x μ}.indicator 1 x ∂continuousScoreLaw n :=
      (lintegral_finsetSum _ fun μ _ ↦ hf μ).symm
    _ = ∫⁻ x, ∑ μ : Matching n, (scoreMarkEvent n).indicator 1 (x, μ)
        ∂continuousScoreLaw n := by
      refine lintegral_congr fun x ↦ Finset.sum_congr rfl fun μ _ ↦ ?_
      by_cases h : IsScoreStable x μ <;> simp [scoreMarkEvent, h]
    _ = _ := by
      have hm : Measurable (1 : ScoreProfile n × Matching n → ℝ≥0∞) :=
        measurable_const
      simpa using (continuous_mark_counting_identity n hm).symm

end LennonPittelFormalization

end

section

open Filter MeasureTheory Set StableMarriage

open scoped ENNReal BigOperators Topology

namespace LennonPittelFormalization

def spouseVectorTotal {n : ℕ} (y : Fin n → ℝ) : ℝ :=
  ∑ i, y i

private theorem measurable_spouseVectorTotal (n : ℕ) :
    Measurable (@spouseVectorTotal n) :=
  Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i

def smallSpouseScoreSet (n : ℕ) : Set (Fin n → ℝ) :=
  {y | (∀ i, 0 ≤ y i) ∧ spouseVectorTotal y < 2}

private theorem measurableSet_nonnegativeSpouseScores (n : ℕ) :
    MeasurableSet {y : Fin n → ℝ | ∀ i, 0 ≤ y i} := by
  rw [ofPred_forall]
  exact MeasurableSet.iInter fun i ↦ measurableSet_le measurable_const (measurable_pi_apply i)

theorem measurableSet_smallSpouseScoreSet (n : ℕ) :
    MeasurableSet (smallSpouseScoreSet n) := by
  unfold smallSpouseScoreSet
  rw [ofPred_and]
  exact (measurableSet_nonnegativeSpouseScores n).inter
    (measurableSet_lt (measurable_spouseVectorTotal n) measurable_const)

private theorem exists_shell_index {s b : ℝ} {n : ℕ} (hn : 0 < n) {N : ℕ}
    (hbs : b ≤ s) (hs : (s - b) * (n : ℝ) ≤ (N : ℝ)) :
    ∃ j : Fin (N + 1), b + (j.val : ℝ) / n ≤ s ∧ s ≤ b + (j.val + 1 : ℝ) / n := by
  let j := ⌊(s - b) * (n : ℝ)⌋₊
  have hj : j ≤ N := Nat.floor_le_of_le hs
  have hfloor : (j : ℝ) ≤ (s - b) * (n : ℝ) :=
    Nat.floor_le (mul_nonneg (sub_nonneg.mpr hbs) (Nat.cast_nonneg n))
  have hceil : (s - b) * (n : ℝ) ≤ (j : ℝ) + 1 :=
    (Nat.lt_floor_add_one _).le
  refine ⟨⟨j, Nat.lt_succ_of_le hj⟩, ?_, ?_⟩
  · have h := (div_le_iff₀ (Nat.cast_pos.mpr hn)).2 hfloor
    linarith
  · have h := (le_div_iff₀ (Nat.cast_pos.mpr hn)).2 hceil
    linarith

private theorem lintegral_le_const_mul_volume {n : ℕ} {S : Set (Fin n → ℝ)}
    (hS : MeasurableSet S) {f : (Fin n → ℝ) → ℝ≥0∞} {c : ℝ≥0∞}
    (hf : ∀ y ∈ S, f y ≤ c) :
    (∫⁻ y in S, f y) ≤ c * volume S := by
  calc
    _ ≤ ∫⁻ _ in S, c := setLIntegral_mono' hS hf
    _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]

private theorem lintegral_spouseShell_le {n : ℕ} {S : Set (Fin n → ℝ)}
    (hS : MeasurableSet S) {f : (Fin n → ℝ) → ℝ≥0∞} {l R c : ℝ}
    (hl : 0 < l) (hc : 0 ≤ c) (hL : ∀ y ∈ S, l ≤ spouseVectorTotal y)
    (hV : volume S ≤ ENNReal.ofReal (R ^ n / (n.factorial : ℝ)))
    (hf : ∀ y ∈ S, f y ≤ ENNReal.ofReal (c / spouseVectorTotal y ^ n)) :
    (∫⁻ y in S, f y) ≤ ENNReal.ofReal (c * (R / l) ^ n / (n.factorial : ℝ)) := by
  have hc' : 0 ≤ c / l ^ n := div_nonneg hc (pow_nonneg hl.le _)
  calc
    _ ≤ ENNReal.ofReal (c / l ^ n) * volume S :=
      lintegral_le_const_mul_volume hS fun y hy ↦ (hf y hy).trans
        (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left hc (pow_pos hl _)
          (pow_le_pow_left₀ hl.le (hL y hy) _)))
    _ ≤ ENNReal.ofReal (c / l ^ n) * ENNReal.ofReal (R ^ n / (n.factorial : ℝ)) :=
      by gcongr
    _ = _ := by rw [← ENNReal.ofReal_mul hc', div_pow]; congr 1; ring

private theorem thinShell_ratio_pow_le {n : ℕ} (hn : 0 < n)
    {b l a : ℝ} (hb : 0 < b) (hbl : b ≤ l) (ha : a ≤ 1) :
    ((l + 1 / (n : ℝ) - a * l) / l) ^ n ≤ Real.exp (1 / b - a * n) := by
  have hl := hb.trans_le hbl
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hR : 0 ≤ l + 1 / (n : ℝ) - a * l := by
    linarith [mul_le_of_le_one_left hl.le ha, one_div_nonneg.mpr hn'.le]
  have hdiv : (1 / (n : ℝ)) / l ≤ 1 / (n : ℝ) / b :=
    div_le_div_of_nonneg_left (by positivity) hb hbl
  have hratio : (l + 1 / (n : ℝ) - a * l) / l = 1 + ((1 / (n : ℝ)) / l - a) := by
    field_simp [hl.ne']; ring
  calc
    _ ≤ (Real.exp (1 / (n : ℝ) / b - a)) ^ n := by
      refine pow_le_pow_left₀ (div_nonneg hR hl.le) ?_ n
      rw [hratio]
      linarith [Real.add_one_le_exp (1 / (n : ℝ) / b - a)]
    _ = _ := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp [hn'.ne']

theorem factorial_mul_lintegral_smallSpouseScore_le {n : ℕ} (hn : 0 < n)
    {f : (Fin n → ℝ) → ℝ≥0∞}
    (hf₀ : ∀ y ∈ smallSpouseScoreSet n, spouseVectorTotal y ≤ 1 / 2 → f y ≤ 1)
    (hf₁ : ∀ y ∈ smallSpouseScoreSet n, 1 / 2 ≤ spouseVectorTotal y →
      f y ≤ ENNReal.ofReal (Real.exp (spouseVectorTotal y) *
        ((1 - Real.exp (-spouseVectorTotal y)) / spouseVectorTotal y) ^ n)) :
    (n.factorial : ℝ≥0∞) * (∫⁻ y in smallSpouseScoreSet n, f y) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ n) +
        ENNReal.ofReal ((2 * (n : ℝ) + 1) * Real.exp 4 * (1 - Real.exp (-2)) ^ n) := by
  let A := smallSpouseScoreSet n ∩ scoreSimplex n (1 / 2)
  have hsmall := measurableSet_smallSpouseScoreSet n
  have hA : MeasurableSet A := hsmall.inter (measurableSet_scoreSimplex _ _)
  have hnear : (n.factorial : ℝ≥0∞) * (∫⁻ y in A, f y) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
    have hbound := lintegral_le_const_mul_volume hA (fun y hy ↦ hf₀ y hy.1 hy.2.2)
    have hvol : volume A ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ n / (n.factorial : ℝ)) := by
      rw [← volume_scoreSimplex n (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      exact measure_mono inter_subset_right
    calc
      _ ≤ (n.factorial : ℝ≥0∞) * ENNReal.ofReal ((1 / 2 : ℝ) ^ n / (n.factorial : ℝ)) := by
        have h := (by simpa only [one_mul] using hbound :
          (∫⁻ y in A, f y) ≤ volume A)
        exact mul_le_mul_right (h.trans hvol) _
      _ = _ := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp [show (n.factorial : ℝ) ≠ 0 by positivity]
  let l (j : Fin (2 * n + 1)) : ℝ := 1 / 2 + j.val / (n : ℝ)
  let S (j : Fin (2 * n + 1)) : Set (Fin n → ℝ) :=
    smallSpouseScoreSet n ∩ {y | y ∈ scoreSimplex n (l j + 1 / (n : ℝ)) ∧
      l j ≤ spouseVectorTotal y}
  have hS (j : Fin (2 * n + 1)) : MeasurableSet (S j) := by
    refine hsmall.inter ?_
    rw [ofPred_and]
    exact (measurableSet_scoreSimplex _ _).inter
      (measurableSet_le measurable_const (measurable_spouseVectorTotal n))
  have hcover : smallSpouseScoreSet n ⊆ A ∪ ⋃ j, S j := by
    intro y hy
    by_cases ht : spouseVectorTotal y ≤ 1 / 2
    · exact Or.inl ⟨hy, hy.1, ht⟩
    · have hs : (spouseVectorTotal y - 1 / 2) * (n : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by
        push_cast
        exact mul_le_mul_of_nonneg_right (by linarith [hy.2]) (Nat.cast_nonneg n)
      obtain ⟨j, hj₁, hj₂⟩ := exists_shell_index hn (le_of_not_ge ht) hs
      exact Or.inr (mem_iUnion.mpr ⟨j, hy, ⟨hy.1, hj₂.trans_eq (by
        dsimp only [l]
        ring)⟩, hj₁⟩)
  let q : ℝ := 1 - Real.exp (-2)
  have hq₀ : 0 ≤ q := by
    dsimp [q]
    linarith [Real.exp_le_one_iff.mpr (by norm_num : (-2 : ℝ) ≤ 0)]
  let c := Real.exp 4 * q ^ n
  have hlocal (j : Fin (2 * n + 1)) :
      (∫⁻ y in S j, f y) ≤ ENNReal.ofReal (c / (n.factorial : ℝ)) := by
    have hlhalf : 1 / 2 ≤ l j := le_add_of_nonneg_right (by positivity)
    have hl : 0 < l j := by linarith
    have hR : 0 ≤ l j + 1 / (n : ℝ) := by positivity
    have hV : volume (S j) ≤
        ENNReal.ofReal ((l j + 1 / (n : ℝ)) ^ n / (n.factorial : ℝ)) := by
      rw [← volume_scoreSimplex n hR]
      exact measure_mono fun _ hy ↦ hy.2.1
    have hdens (y : Fin n → ℝ) (hy : y ∈ S j) :
        f y ≤ ENNReal.ofReal (Real.exp 2 * q ^ n / spouseVectorTotal y ^ n) := by
      have hs : 1 / 2 ≤ spouseVectorTotal y := hlhalf.trans hy.2.2
      refine (hf₁ y hy.1 hs).trans (ENNReal.ofReal_le_ofReal ?_)
      have hs₀ : 0 ≤ 1 - Real.exp (-spouseVectorTotal y) := by
        linarith [Real.exp_le_one_iff.mpr (by linarith : -spouseVectorTotal y ≤ 0)]
      have hsq : 1 - Real.exp (-spouseVectorTotal y) ≤ q :=
        sub_le_sub_left (Real.exp_le_exp.mpr (by linarith [hy.1.2])) 1
      rw [div_pow, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right
        (mul_le_mul (Real.exp_le_exp.mpr hy.1.2.le)
          (pow_le_pow_left₀ hs₀ hsq _) (pow_nonneg hs₀ _) (Real.exp_pos _).le)
        (pow_nonneg (by linarith) _)
    refine (lintegral_spouseShell_le (hS j) hl (by positivity) (fun _ hy ↦ hy.2.2)
      hV hdens).trans (ENNReal.ofReal_le_ofReal ?_)
    have hratio := thinShell_ratio_pow_le hn (by norm_num : (0 : ℝ) < 1 / 2) hlhalf
      (by norm_num : (0 : ℝ) ≤ 1)
    norm_num at hratio
    have hcoef : Real.exp 2 * q ^ n * Real.exp 2 = c := by
      dsimp only [c]
      rw [show Real.exp 4 = Real.exp 2 * Real.exp 2 by rw [← Real.exp_add]; norm_num]
      ring
    rw [← hcoef]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (by simpa only [one_div] using hratio) (by positivity)) (Nat.cast_nonneg _)
  have hshells : (n.factorial : ℝ≥0∞) * (∫⁻ y in ⋃ j, S j, f y) ≤
      ENNReal.ofReal ((2 * (n : ℝ) + 1) * Real.exp 4 * q ^ n) := by
    calc
      _ ≤ (n.factorial : ℝ≥0∞) * ∑ j : Fin (2 * n + 1), ∫⁻ y in S j, f y := by
        exact mul_le_mul_right (by simpa [tsum_fintype] using
          (lintegral_iUnion_le S f : (∫⁻ y in ⋃ j, S j, f y) ≤
            ∑' j, ∫⁻ y in S j, f y)) _
      _ ≤ (n.factorial : ℝ≥0∞) * ∑ _ : Fin (2 * n + 1),
          ENNReal.ofReal (c / (n.factorial : ℝ)) := by
        gcongr with j _
        exact hlocal j
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        simp only [← ENNReal.ofReal_natCast]
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        push_cast
        dsimp only [c]
        field_simp [show (n.factorial : ℝ) ≠ 0 by positivity]
  have hUnion := (lintegral_mono_set hcover).trans
    (lintegral_union_le (μ := volume) f A (⋃ j, S j))
  exact (mul_le_mul_right hUnion _).trans (by rw [mul_add]; exact add_le_add hnear hshells)

theorem tendsto_factorial_mul_lintegral_smallSpouseScore_zero
    (f : ∀ n : ℕ, (Fin n → ℝ) → ℝ≥0∞)
    (hf₀ : ∀ᶠ n in atTop, ∀ y ∈ smallSpouseScoreSet n,
      spouseVectorTotal y ≤ 1 / 2 → f n y ≤ 1)
    (hf₁ : ∀ᶠ n in atTop, ∀ y ∈ smallSpouseScoreSet n, 1 / 2 ≤ spouseVectorTotal y →
      f n y ≤ ENNReal.ofReal (Real.exp (spouseVectorTotal y) *
        ((1 - Real.exp (-spouseVectorTotal y)) / spouseVectorTotal y) ^ n)) :
    Tendsto (fun n ↦ (n.factorial : ℝ≥0∞) *
      (∫⁻ y in smallSpouseScoreSet n, f n y)) atTop (𝓝 0) := by
  let q : ℝ := 1 - Real.exp (-2)
  have hq₀ : 0 ≤ q :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num))
  have hq₁ : q < 1 := sub_lt_self _ (Real.exp_pos _)
  have hhalf : Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hgeom := tendsto_pow_atTop_nhds_zero_of_lt_one hq₀ hq₁
  have hngeom := tendsto_self_mul_const_pow_of_lt_one hq₀ hq₁
  have hterm : Tendsto (fun n : ℕ ↦ (2 * (n : ℝ) + 1) * Real.exp 4 * q ^ n)
      atTop (𝓝 0) := by
    have h := ((hngeom.const_mul (2 : ℝ)).add hgeom).const_mul (Real.exp 4)
    rw [mul_zero, zero_add, mul_zero] at h
    refine h.congr fun n ↦ ?_
    ring
  have ht : Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((1 / 2 : ℝ) ^ n) +
      ENNReal.ofReal ((2 * (n : ℝ) + 1) * Real.exp 4 * q ^ n)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, zero_add] using
      (ENNReal.tendsto_ofReal hhalf).add (ENNReal.tendsto_ofReal hterm)
  refine tendsto_const_nhds.squeeze' ht (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ), hf₀, hf₁] with n hn h₀ h₁
  exact factorial_mul_lintegral_smallSpouseScore_le (zero_lt_one.trans_le hn) h₀ h₁

private def spouseScoreCube (n : ℕ) : Set (Fin n → ℝ) :=
  univ.pi fun _ ↦ Icc (0 : ℝ) 1

private theorem measurableSet_spouseScoreCube (n : ℕ) : MeasurableSet (spouseScoreCube n) :=
  (measurableSet_pi countable_univ).2 (Or.inl fun _ _ ↦ measurableSet_Icc)

private noncomputable def maskedFemaleStabilityDensity (n : ℕ) (y : Fin n → ℝ) :
    ℝ≥0∞ :=
  (spouseScoreCube n).indicator femaleSpouseStabilityDensity y

private theorem femaleSpouseStabilityDensity_eq_ofReal_prod {n : ℕ} {y : Fin n → ℝ}
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) :
    femaleSpouseStabilityDensity y =
      ENNReal.ofReal (∏ i, scoreRowMass (Finset.univ.erase i) y 0 1) := by
  unfold femaleSpouseStabilityDensity
  symm
  apply ENNReal.ofReal_prod_of_nonneg
  intro i _
  unfold scoreRowMass
  refine intervalIntegral.integral_nonneg (by norm_num) fun x hx ↦ ?_
  unfold scoreRowKernel
  exact Finset.prod_nonneg fun j _ ↦ sub_nonneg.mpr (calc
    x * y j ≤ 1 * y j := mul_le_mul_of_nonneg_right hx.2 (hy j).1
    _ ≤ 1 := by simpa only [one_mul] using (hy j).2)

private theorem sum_stable_femaleSpouse_eq_factorial_mul {n : ℕ}
    {B : Set (Fin n → ℝ)} (hB : MeasurableSet B) :
    (∑ μ : Matching n, continuousScoreLaw n
      {x | IsScoreStable x μ ∧ femaleSpouseByHusband μ x ∈ B}) =
      (n.factorial : ℝ≥0∞) * (∫⁻ y in B, maskedFemaleStabilityDensity n y) := by
  simp_rw [continuousScoreLaw_stable_and_femaleSpouse _ hB]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  rw [spouseVectorLaw_eq_restrict_volume, Measure.restrict_restrict hB]
  change (n.factorial : ℝ≥0∞) *
    (∫⁻ y in B ∩ spouseScoreCube n, femaleSpouseStabilityDensity y) = _
  unfold maskedFemaleStabilityDensity
  rw [setLIntegral_indicator (measurableSet_spouseScoreCube n),
    inter_comm B (spouseScoreCube n)]

theorem tendsto_sum_stable_smallSpouseScore_zero :
    Tendsto (fun n : ℕ ↦ ∑ μ : Matching n, continuousScoreLaw n
      {x | IsScoreStable x μ ∧ femaleSpouseByHusband μ x ∈ smallSpouseScoreSet n})
      atTop (𝓝 0) := by
  simp_rw [sum_stable_femaleSpouse_eq_factorial_mul (measurableSet_smallSpouseScoreSet _)]
  apply tendsto_factorial_mul_lintegral_smallSpouseScore_zero
  · exact Eventually.of_forall fun n y _ _ ↦ by
      by_cases hy : y ∈ spouseScoreCube n
      · rw [maskedFemaleStabilityDensity, indicator_of_mem hy]
        exact femaleSpouseStabilityDensity_le_one y (fun j ↦ hy j (mem_univ j))
      · simp [maskedFemaleStabilityDensity, indicator_of_notMem hy]
  · exact Eventually.of_forall fun n y _ hs ↦ by
      by_cases hy : y ∈ spouseScoreCube n
      · have hcube (j : Fin n) : y j ∈ Icc (0 : ℝ) 1 := hy j (mem_univ j)
        change 1 / 2 ≤ ∑ j, y j at hs
        rw [maskedFemaleStabilityDensity, indicator_of_mem hy,
          femaleSpouseStabilityDensity_eq_ofReal_prod hcube]
        apply ENNReal.ofReal_le_ofReal
        simpa only [spouseVectorTotal, Fintype.card_fin] using
          scoreRowMass_prod_le_finite_exp y hcube (by linarith [hs])
      · simp [maskedFemaleStabilityDensity, indicator_of_notMem hy]

end LennonPittelFormalization

end

section

open Filter MeasureTheory Set StableMarriage

open scoped BigOperators ENNReal Topology

namespace LennonPittelFormalization

def pittelScoreCube (n : ℕ) : Set (Fin n → ℝ) :=
  univ.pi fun _ ↦ Icc (0 : ℝ) 1

theorem measurableSet_pittelScoreCube (n : ℕ) : MeasurableSet (pittelScoreCube n) :=
  (measurableSet_pi countable_univ).2 (Or.inl fun _ _ ↦ measurableSet_Icc)

noncomputable def pittelDensity (n : ℕ) : (Fin n → ℝ) → ℝ≥0∞ :=
  (pittelScoreCube n).indicator femaleSpouseStabilityDensity

theorem measurable_pittelDensity (n : ℕ) : Measurable (pittelDensity n) :=
  (measurable_femaleSpouseStabilityDensity n).indicator (measurableSet_pittelScoreCube n)

theorem pittelDensity_eq_ofReal_prod {n : ℕ} {y : Fin n → ℝ}
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) :
    pittelDensity n y =
      ENNReal.ofReal (∏ i, scoreRowMass (Finset.univ.erase i) y 0 1) := by
  rw [pittelDensity, indicator_of_mem (show y ∈ pittelScoreCube n from fun j _ ↦ hy j)]
  unfold femaleSpouseStabilityDensity
  symm
  apply ENNReal.ofReal_prod_of_nonneg
  intro i _
  unfold scoreRowMass
  refine intervalIntegral.integral_nonneg (by norm_num) fun x hx ↦ ?_
  unfold scoreRowKernel
  exact Finset.prod_nonneg fun j _ ↦ sub_nonneg.mpr (calc
    x * y j ≤ 1 * y j := mul_le_mul_of_nonneg_right hx.2 (hy j).1
    _ ≤ 1 := by simpa only [one_mul] using (hy j).2)

theorem pittelDensity_le_inv_pow {n : ℕ} {y : Fin n → ℝ} (hs : 2 ≤ spouseVectorTotal y) :
    pittelDensity n y ≤ ENNReal.ofReal (Real.exp 2 / spouseVectorTotal y ^ n) := by
  by_cases hy : y ∈ pittelScoreCube n
  · have hcube (i : Fin n) : y i ∈ Icc (0 : ℝ) 1 := hy i (mem_univ i)
    rw [pittelDensity_eq_ofReal_prod hcube]
    apply ENNReal.ofReal_le_ofReal
    simpa only [spouseVectorTotal, Fintype.card_fin] using
      scoreRowMass_prod_le_inv_pow y hcube hs
  · simp [pittelDensity, indicator_of_notMem hy]

theorem sum_measure_scoreStable_and_femaleSpouse_eq_pittelDensity {n : ℕ}
    {B : Set (Fin n → ℝ)} (hB : MeasurableSet B) :
    (∑ μ : Matching n, continuousScoreLaw n
      {x | IsScoreStable x μ ∧ femaleSpouseByHusband μ x ∈ B}) =
      (n.factorial : ℝ≥0∞) * (∫⁻ y in B, pittelDensity n y) := by
  simp_rw [continuousScoreLaw_stable_and_femaleSpouse _ hB]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  rw [spouseVectorLaw_eq_restrict_volume, Measure.restrict_restrict hB]
  change (n.factorial : ℝ≥0∞) *
    (∫⁻ y in B ∩ pittelScoreCube n, femaleSpouseStabilityDensity y) = _
  unfold pittelDensity
  rw [setLIntegral_indicator (measurableSet_pittelScoreCube n),
    inter_comm B (pittelScoreCube n)]

theorem ofReal_expectedNumStableMatchings_eq_pittelDensity (n : ℕ) :
    ENNReal.ofReal (expectedNumStableMatchings n) =
      (n.factorial : ℝ≥0∞) * (∫⁻ y, pittelDensity n y) := by
  rw [← sum_measure_scoreStable_eq_expected]
  simpa only [mem_univ, and_true, Measure.restrict_univ] using
    (sum_measure_scoreStable_and_femaleSpouse_eq_pittelDensity
      (n := n) MeasurableSet.univ)

noncomputable def pittelRadiusLower (n : ℕ) : ℝ := 6 * Real.log n

noncomputable def pittelRadiusUpper (n : ℕ) : ℝ := n / (Real.log n) ^ 2

private theorem tendsto_log_nat_atTop : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem eventually_two_le_pittelRadiusLower : ∀ᶠ n in atTop, 2 ≤ pittelRadiusLower n := by
  filter_upwards [tendsto_log_nat_atTop.eventually_ge_atTop 1] with n hn
  unfold pittelRadiusLower
  linarith

theorem eventually_pittelRadiusLower_le_upper :
    ∀ᶠ n in atTop, pittelRadiusLower n ≤ pittelRadiusUpper n := by
  have h : Tendsto (fun n : ℕ ↦ 6 * (Real.log n)^3 / (n : ℝ)) atTop (𝓝 0) := by
    have h' := ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 3 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)).const_mul 6
    simpa [Function.comp_def, mul_div_assoc] using h'
  filter_upwards [(tendsto_order.mp h).2 1 zero_lt_one, eventually_gt_atTop (1 : ℕ)]
    with n hn hn'
  have hpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn')
  have hb : 6 * (Real.log n) ^ 3 < (n : ℝ) := by
    simpa only [one_mul] using (div_lt_iff₀ hpos).mp hn
  unfold pittelRadiusLower pittelRadiusUpper
  apply (le_div_iff₀ (sq_pos_of_pos hlog)).mpr
  calc
    6 * Real.log n * Real.log n ^ 2 = 6 * Real.log n ^ 3 := by ring
    _ ≤ (n : ℝ) := hb.le

theorem eventually_pittelRadiusUpper_le_size :
    ∀ᶠ n in atTop, pittelRadiusUpper n ≤ (n : ℝ) := by
  filter_upwards [tendsto_log_nat_atTop.eventually_ge_atTop 1] with n hn
  unfold pittelRadiusUpper
  apply div_le_self (Nat.cast_nonneg _)
  nlinarith

private theorem tendsto_log_log_nat_ratio_zero :
    Tendsto (fun n : ℕ ↦ Real.log (Real.log n) / Real.log n) atTop (𝓝 0) := by
  simpa [Function.comp_def] using
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_log_nat_atTop

theorem tendsto_log_pittelRadiusLower_ratio_zero :
    Tendsto (fun n : ℕ ↦ Real.log (pittelRadiusLower n) / Real.log n) atTop (𝓝 0) := by
  have hconst : Tendsto (fun n : ℕ ↦ Real.log 6 / Real.log n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_log_nat_atTop
  have h := hconst.add tendsto_log_log_nat_ratio_zero
  simp only [add_zero] at h
  refine h.congr' ?_
  filter_upwards [tendsto_log_nat_atTop.eventually_gt_atTop 0] with n hn
  rw [pittelRadiusLower, Real.log_mul (by norm_num) hn.ne', add_div]

theorem tendsto_log_pittelWindowUpper_ratio_one :
    Tendsto (fun n : ℕ ↦ Real.log ((n : ℝ) / pittelRadiusLower n) / Real.log n)
      atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_log_pittelRadiusLower_ratio_zero
  simp only [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [tendsto_log_nat_atTop.eventually_gt_atTop 0, eventually_gt_atTop (0 : ℕ)]
    with n hlog hn
  have hL : 0 < pittelRadiusLower n := mul_pos (by norm_num) hlog
  rw [Real.log_div (by exact_mod_cast hn.ne') hL.ne', sub_div, div_self hlog.ne']

theorem tendsto_log_pittelWindowLower_ratio_one :
    Tendsto (fun n : ℕ ↦ Real.log (pittelRadiusUpper n / pittelRadiusLower n) / Real.log n)
      atTop (𝓝 1) := by
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub
    (tendsto_log_log_nat_ratio_zero.const_mul 2)).sub tendsto_log_pittelRadiusLower_ratio_zero
  simp only [mul_zero, sub_zero] at h
  refine h.congr' ?_
  filter_upwards [tendsto_log_nat_atTop.eventually_gt_atTop 0, eventually_gt_atTop (0 : ℕ)]
    with n hlog hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < pittelRadiusLower n := mul_pos (by norm_num) hlog
  have hU : 0 < pittelRadiusUpper n := div_pos hn' (sq_pos_of_pos hlog)
  rw [Real.log_div hU.ne' hL.ne', pittelRadiusUpper,
    Real.log_div hn'.ne' (pow_ne_zero _ hlog.ne'), Real.log_pow, sub_div, sub_div,
    div_self hlog.ne', mul_div_assoc]
  norm_num

theorem lintegral_Ioc_inv_of_pos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫⁻ s in Ioc a b, ENNReal.ofReal s⁻¹) = ENNReal.ofReal (Real.log (b / a)) := by
  have hi : IntervalIntegrable (fun s : ℝ ↦ s⁻¹) volume a b :=
    (continuousOn_id.inv₀ fun _ hs ↦
      (ha.trans_le ((uIcc_of_le hab ▸ hs).1)).ne').intervalIntegrable
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hi),
    ← intervalIntegral.integral_of_le hab, integral_inv_of_pos ha (ha.trans_le hab)]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs using
    inv_nonneg.mpr (ha.trans hs.1).le

private theorem measurable_pittelTotal (n : ℕ) : Measurable (@spouseVectorTotal n) :=
  Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i

private theorem pittelDensity_eq_zero_of_exists_neg {n : ℕ} {y : Fin n → ℝ}
    (hy : ¬∀ i, 0 ≤ y i) : pittelDensity n y = 0 := by
  exact indicator_of_notMem (fun h ↦ hy fun i ↦ (h i (mem_univ i)).1) _

private theorem pittelDensity_mass_single_shell_le {n : ℕ} {l r : ℝ}
    (hl : 2 ≤ l) (hr : 0 ≤ r) :
    (∫⁻ y in scoreSimplex n r ∩ {y | l ≤ spouseVectorTotal y}, pittelDensity n y) ≤
      ENNReal.ofReal (Real.exp 2 * (r / l) ^ n / (n.factorial : ℝ)) := by
  let S := scoreSimplex n r ∩ {y | l ≤ spouseVectorTotal y}
  have hS : MeasurableSet S :=
    (measurableSet_scoreSimplex _ _).inter (measurableSet_le measurable_const
      (measurable_pittelTotal n))
  have hl' : 0 < l := by linarith
  have hc' : 0 ≤ Real.exp 2 / l ^ n := by positivity
  calc
    _ ≤ ∫⁻ _ in S, ENNReal.ofReal (Real.exp 2 / l ^ n) := by
      apply setLIntegral_mono' hS
      intro y hy
      exact (pittelDensity_le_inv_pow (hl.trans hy.2)).trans
        (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left (Real.exp_pos _).le
          (pow_pos hl' _) (pow_le_pow_left₀ hl'.le hy.2 _)))
    _ = ENNReal.ofReal (Real.exp 2 / l ^ n) * volume S := by
      rw [lintegral_const, Measure.restrict_apply_univ]
    _ ≤ ENNReal.ofReal (Real.exp 2 / l ^ n) * ENNReal.ofReal (r ^ n / (n.factorial : ℝ)) := by
      rw [← volume_scoreSimplex n hr]
      exact mul_le_mul_right (measure_mono inter_subset_left) _
    _ = _ := by
      rw [← ENNReal.ofReal_mul hc', div_pow]
      congr 1
      ring

private theorem pittelDensity_mass_ge_two_le {n : ℕ} (hn : 0 < n) {R : ℝ} (hR : 2 ≤ R) :
    (n.factorial : ℝ≥0∞) * (∫⁻ y in scoreSimplex n R ∩ {y | 2 ≤ spouseVectorTotal y},
      pittelDensity n y) ≤
      ENNReal.ofReal (Real.exp 3 * ((n : ℝ) * Real.log (R / 2) + 2)) := by
  let N : ℕ := ⌈(n : ℝ) * Real.log (R / 2)⌉₊
  let r (j : ℕ) : ℝ := 2 * Real.exp ((j : ℝ) / n)
  let S (j : Fin (N + 1)) := scoreSimplex n (r (j + 1)) ∩ {y | r j ≤ spouseVectorTotal y}
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hr₂ (j : ℕ) : 2 ≤ r j := by
    dsimp [r]
    have he := Real.one_le_exp_iff.mpr (div_nonneg (Nat.cast_nonneg j) hn'.le)
    linarith
  have hRlog : 0 ≤ (n : ℝ) * Real.log (R / 2) :=
    mul_nonneg hn'.le (Real.log_nonneg (by linarith))
  have hcover : scoreSimplex n R ∩ {y | 2 ≤ spouseVectorTotal y} ⊆ ⋃ j, S j := by
    intro y hy
    let s := spouseVectorTotal y
    have hs₂ : 2 ≤ s := hy.2
    have hsR : s ≤ R := hy.1.2
    have hs₀ : 0 < s / 2 := by linarith
    let j : ℕ := ⌊(n : ℝ) * Real.log (s / 2)⌋₊
    have hlog : 0 ≤ Real.log (s / 2) := Real.log_nonneg (by linarith)
    have hle : (j : ℝ) ≤ (n : ℝ) * Real.log (s / 2) :=
      Nat.floor_le (mul_nonneg hn'.le hlog)
    have hlt : (n : ℝ) * Real.log (s / 2) < (j : ℝ) + 1 := Nat.lt_floor_add_one _
    have hj : j ≤ N := by
      apply Nat.floor_le_of_le
      refine (mul_le_mul_of_nonneg_left ?_ hn'.le).trans (Nat.le_ceil _)
      apply Real.log_le_log hs₀
      linarith
    have h₁ : (j : ℝ) / n ≤ Real.log (s / 2) :=
      (div_le_iff₀ hn').mpr (by rwa [mul_comm])
    have h₂ : Real.log (s / 2) ≤ ((j + 1 : ℕ) : ℝ) / n := by
      apply (le_div_iff₀ hn').mpr
      push_cast
      linarith
    have hl : r j ≤ s := by
      have he := Real.exp_le_exp.mpr h₁
      rw [Real.exp_log hs₀] at he
      dsimp [r]
      linarith
    have hu : s ≤ r (j + 1) := by
      have he := Real.exp_le_exp.mpr h₂
      rw [Real.exp_log hs₀] at he
      dsimp [r]
      linarith
    exact mem_iUnion.mpr ⟨⟨j, Nat.lt_succ_of_le hj⟩, ⟨hy.1.1, hu⟩, hl⟩
  have hlocal (j : Fin (N + 1)) : (∫⁻ y in S j, pittelDensity n y) ≤
      ENNReal.ofReal (Real.exp 3 / (n.factorial : ℝ)) := by
    refine (pittelDensity_mass_single_shell_le (hr₂ (j : ℕ)) (by positivity)).trans_eq ?_
    have hratio : r ((j : ℕ) + 1) / r j = Real.exp (1 / (n : ℝ)) := by
      dsimp only [r]
      rw [mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0), ← Real.exp_sub]
      push_cast
      congr 1
      ring
    rw [hratio, ← Real.exp_nat_mul, show (n : ℝ) * (1 / (n : ℝ)) = 1 by
      field_simp, ← Real.exp_add]
    norm_num
  calc
    _ ≤ (n.factorial : ℝ≥0∞) * ∑ j : Fin (N + 1), ∫⁻ y in S j, pittelDensity n y := by
      have h := (lintegral_mono_set hcover).trans (by simpa [tsum_fintype] using
        (lintegral_iUnion_le (μ := volume) S (pittelDensity n)))
      exact mul_le_mul_right h _
    _ ≤ (n.factorial : ℝ≥0∞) * ∑ _ : Fin (N + 1),
          ENNReal.ofReal (Real.exp 3 / (n.factorial : ℝ)) := by
      gcongr with j _
      exact hlocal j
    _ = ENNReal.ofReal (Real.exp 3 * ((N : ℝ) + 1)) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      simp only [← ENNReal.ofReal_natCast]
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      push_cast
      field_simp [show (n.factorial : ℝ) ≠ 0 by positivity]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left (by linarith [Nat.ceil_lt_add_one hRlog])
        (Real.exp_pos _).le

private noncomputable def pittelTinyMass (n : ℕ) : ℝ≥0∞ :=
  (n.factorial : ℝ≥0∞) * (∫⁻ y in smallSpouseScoreSet n, pittelDensity n y)

private theorem tendsto_pittelTinyMass_zero : Tendsto pittelTinyMass atTop (𝓝 0) := by
  refine tendsto_sum_stable_smallSpouseScore_zero.congr fun n ↦ ?_
  exact sum_measure_scoreStable_and_femaleSpouse_eq_pittelDensity
    (measurableSet_smallSpouseScoreSet n)

private theorem pittelSmallMass_le {n : ℕ} (hn : 0 < n) {R : ℝ} (hR : 2 ≤ R) :
    (n.factorial : ℝ≥0∞) *
      (∫⁻ y in {y | spouseVectorTotal y ≤ R}, pittelDensity n y) ≤
      pittelTinyMass n + ENNReal.ofReal (Real.exp 3 * ((n : ℝ) * Real.log (R / 2) + 2)) := by
  have hEq :
      (∫⁻ y in {y | spouseVectorTotal y ≤ R}, pittelDensity n y) =
        ∫⁻ y in scoreSimplex n R, pittelDensity n y := by
    rw [← lintegral_indicator (measurableSet_le (measurable_pittelTotal n) measurable_const),
      ← lintegral_indicator (measurableSet_scoreSimplex n R)]
    refine lintegral_congr fun y ↦ ?_
    by_cases hy : ∀ i, 0 ≤ y i
    · by_cases hsum : spouseVectorTotal y ≤ R
      · rw [indicator_of_mem (show y ∈ {z | spouseVectorTotal z ≤ R} from hsum),
          indicator_of_mem (show y ∈ scoreSimplex n R from ⟨hy, hsum⟩)]
      · rw [indicator_of_notMem (show y ∉ {z | spouseVectorTotal z ≤ R} from hsum),
          indicator_of_notMem (show y ∉ scoreSimplex n R from fun h ↦ hsum h.2)]
    · by_cases hsum : spouseVectorTotal y ≤ R
      · rw [indicator_of_mem (show y ∈ {z | spouseVectorTotal z ≤ R} from hsum),
          pittelDensity_eq_zero_of_exists_neg hy,
          indicator_of_notMem (show y ∉ scoreSimplex n R from fun h ↦ hy h.1)]
      · rw [indicator_of_notMem (show y ∉ {z | spouseVectorTotal z ≤ R} from hsum),
          indicator_of_notMem (show y ∉ scoreSimplex n R from fun h ↦ hsum h.2)]
  have hsub : scoreSimplex n R ⊆
      smallSpouseScoreSet n ∪ (scoreSimplex n R ∩ {y | 2 ≤ spouseVectorTotal y}) := by
    intro y hy
    by_cases hs : 2 ≤ spouseVectorTotal y
    · exact Or.inr ⟨hy, hs⟩
    · exact Or.inl ⟨hy.1, lt_of_not_ge hs⟩
  rw [hEq]
  calc
    _ ≤ (n.factorial : ℝ≥0∞) *
        ((∫⁻ y in smallSpouseScoreSet n, pittelDensity n y) +
          ∫⁻ y in scoreSimplex n R ∩ {y | 2 ≤ spouseVectorTotal y}, pittelDensity n y) :=
      mul_le_mul_right ((lintegral_mono_set hsub).trans (lintegral_union_le _ _ _)) _
    _ ≤ _ := by
      rw [mul_add]
      exact add_le_add le_rfl (pittelDensity_mass_ge_two_le hn hR)

private theorem tendsto_log_pittelRadiusLower_half_ratio_zero :
    Tendsto (fun n : ℕ ↦ Real.log (pittelRadiusLower n / 2) / Real.log n) atTop (𝓝 0) := by
  have hconst : Tendsto (fun n : ℕ ↦ Real.log 2 / Real.log n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_log_nat_atTop
  have h := tendsto_log_pittelRadiusLower_ratio_zero.sub hconst
  simp only [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_two_le_pittelRadiusLower] with n hn
  rw [Real.log_div (by linarith : pittelRadiusLower n ≠ 0) (by norm_num), sub_div]

private theorem tendsto_pittelNormalizer_atTop :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * Real.log n) atTop atTop :=
  tendsto_natCast_atTop_atTop.atTop_mul_atTop₀ tendsto_log_nat_atTop

private theorem tendsto_pittelSmallMass_bound_ratio_zero :
    Tendsto (fun n : ℕ ↦ ENNReal.ofReal
      (Real.exp 3 * ((n : ℝ) * Real.log (pittelRadiusLower n / 2) + 2)) /
        ENNReal.ofReal ((n : ℝ) * Real.log n)) atTop (𝓝 0) := by
  have hconst : Tendsto (fun n : ℕ ↦ (2 : ℝ) / ((n : ℝ) * Real.log n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_pittelNormalizer_atTop
  have h := (tendsto_log_pittelRadiusLower_half_ratio_zero.add hconst).const_mul (Real.exp 3)
  simp only [add_zero, mul_zero] at h
  have h' := ENNReal.tendsto_ofReal h
  simp only [ENNReal.ofReal_zero] at h'
  refine h'.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  rw [← ENNReal.ofReal_div_of_pos (mul_pos hn' hlog)]
  congr 1
  field_simp

theorem tendsto_pittelSmallMass_ratio_zero :
    Tendsto (fun n : ℕ ↦ (n.factorial : ℝ≥0∞) *
      (∫⁻ y in {y | spouseVectorTotal y ≤ pittelRadiusLower n}, pittelDensity n y) /
        ENNReal.ofReal ((n : ℝ) * Real.log n)) atTop (𝓝 0) := by
  have h := tendsto_pittelTinyMass_zero.add tendsto_pittelSmallMass_bound_ratio_zero
  simp only [zero_add] at h
  refine tendsto_const_nhds.squeeze' h (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ), eventually_two_le_pittelRadiusLower,
    tendsto_pittelNormalizer_atTop.eventually_ge_atTop 1] with n hn hL hnorm
  have hd : 1 ≤ ENNReal.ofReal ((n : ℝ) * Real.log n) := by
    simpa using ENNReal.ofReal_le_ofReal hnorm
  refine (ENNReal.div_le_div_right (pittelSmallMass_le hn hL) _).trans ?_
  rw [ENNReal.add_div]
  gcongr
  calc
    _ ≤ pittelTinyMass n / 1 := ENNReal.div_le_div_left hd _
    _ = _ := div_one _

end LennonPittelFormalization

end

section

open MeasureTheory Set

open scoped BigOperators

namespace LennonPittelFormalization

noncomputable def pittelRowIntegral {ι : Type*} (I : Finset ι) (w : ι → ℝ) (s : ℝ) : ℝ :=
  ∫ t in 0..s, ∏ j ∈ I, (1 - t * w j)

private theorem one_sub_le_exp_quadratic (u : ℝ) (hu : 0 ≤ u) :
    1 - u ≤ Real.exp (-u - u ^ 2 / 2) := by
  let f (x : ℝ) := (1 - x) * Real.exp (x + x ^ 2 / 2)
  have hd (x : ℝ) : HasDerivAt f (-(x ^ 2) * Real.exp (x + x ^ 2 / 2)) x := by
    have h₁ := (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
    have h₂ := ((hasDerivAt_id x).add ((hasDerivAt_pow 2 x).div_const 2)).exp
    convert h₁.mul h₂ using 1 <;> first | rfl | (norm_num [f, id] <;> ring)
  have hanti : Antitone f := antitone_of_hasDerivAt_nonpos hd (fun x ↦
    show -(x ^ 2) * Real.exp (x + x ^ 2 / 2) ≤ 0 from
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (Real.exp_nonneg _))
  have hh : f u ≤ f 0 := hanti hu
  rw [show -u - u ^ 2 / 2 = -(u + u ^ 2 / 2) by ring, Real.exp_neg, ← one_div]
  exact (le_div_iff₀ (Real.exp_pos (u + u ^ 2 / 2))).2 (by simpa [f] using hh)

private theorem exp_cubic_le_one_sub (u : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1 / 2) :
    Real.exp (-u - u ^ 2 / 2 - u ^ 3) ≤ 1 - u := by
  let f (x : ℝ) := (1 - x) * Real.exp (x + x ^ 2 / 2 + x ^ 3)
  have hd (x : ℝ) :
      HasDerivAt f (x ^ 2 * (2 - 3 * x) * Real.exp (x + x ^ 2 / 2 + x ^ 3)) x := by
    have h₁ := (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
    have h₂ := (((hasDerivAt_id x).add ((hasDerivAt_pow 2 x).div_const 2)).add
      (hasDerivAt_pow 3 x)).exp
    convert h₁.mul h₂ using 1 <;> first | rfl | (norm_num [f, id] <;> ring)
  have hm : MonotoneOn f (Icc 0 (1 / 2)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc ..)
      (show ContinuousOn f (Icc 0 (1 / 2)) by dsimp [f]; fun_prop)
      (fun x _ ↦ (hd x).hasDerivWithinAt)
    intro x hx
    have hx' : x ≤ 1 / 2 := (interior_subset hx).2
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (Real.exp_nonneg _)
  have hh : f 0 ≤ f u := hm ⟨le_rfl, by norm_num⟩ ⟨hu, hu'⟩ hu
  have hh' := (div_le_iff₀ (Real.exp_pos (u + u ^ 2 / 2 + u ^ 3))).2
    (show 1 ≤ (1 - u) * Real.exp (u + u ^ 2 / 2 + u ^ 3) by simpa [f] using hh)
  simpa only [one_div, ← Real.exp_neg, neg_add, sub_eq_add_neg] using hh'

private theorem exp_neg_le_quadratic (u : ℝ) (hu : 0 ≤ u) :
    Real.exp (-u) ≤ 1 - u + u ^ 2 / 2 := by
  let f (x : ℝ) := 1 - x + x ^ 2 / 2 - Real.exp (-x)
  have hd (x : ℝ) : HasDerivAt f (-1 + x + Real.exp (-x)) x := by
    have h₁ := (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
    have h₂ := (hasDerivAt_pow 2 x).div_const 2
    have h₃ := (hasDerivAt_id x).neg.exp
    convert (h₁.add h₂).sub h₃ using 1 <;> first | rfl | (norm_num [f, id] <;> ring)
  have hm := monotone_of_hasDerivAt_nonneg hd (fun x ↦
    show 0 ≤ -1 + x + Real.exp (-x) by linarith [Real.one_sub_le_exp_neg x])
  have h : f 0 ≤ f u := hm hu
  simpa [f, sub_nonneg] using h

private theorem pittel_exp_moment {a : ℝ} (ha : 0 < a) (k : ℕ) :
    (∫ t : ℝ in Ioi 0, t ^ k * Real.exp (-(a * t))) = (k.factorial : ℝ) / a ^ (k + 1) := by
  calc
    _ = ∫ t : ℝ in Ioi 0, t ^ (((k : ℝ) + 1) - 1) * Real.exp (-(a * t)) := by
      simp only [add_sub_cancel_right, Real.rpow_natCast]
    _ = _ := by
      rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity) ha,
        Real.Gamma_nat_eq_factorial, ← Nat.cast_succ, Real.rpow_natCast, one_div,
        inv_pow, div_eq_mul_inv, mul_comm]

private theorem pittel_integrable_exp_moment {a : ℝ} (ha : 0 < a) (k : ℕ) :
    IntegrableOn (fun t : ℝ ↦ t ^ k * Real.exp (-(a * t))) (Ioi 0) := by
  have hbase : IntegrableOn (fun t : ℝ ↦ t ^ k * Real.exp (-t)) (Ioi 0) := by
    simpa only [add_sub_cancel_right, Real.rpow_natCast, mul_comm] using
      (Real.GammaIntegral_convergent (s := (k : ℝ) + 1) (by positivity))
  have hscaled : IntegrableOn (fun t : ℝ ↦ (a * t) ^ k * Real.exp (-(a * t))) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff _ 0 ha).mpr (by simpa only [mul_zero] using hbase)
  simpa only [IntegrableOn, mul_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ ha.ne'),
    one_mul] using
    hscaled.const_mul ((a ^ k)⁻¹)

private noncomputable def expMonomial (a : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  t ^ k * Real.exp (-(a * t))

private noncomputable def rowUpper (a b t : ℝ) : ℝ :=
  expMonomial a 0 t - (b / 2) * expMonomial a 2 t + (b ^ 2 / 8) * expMonomial a 4 t

private noncomputable def rowLower (a b m t : ℝ) : ℝ :=
  expMonomial a 0 t - (b / 2) * expMonomial a 2 t - (m * b) * expMonomial a 3 t

private theorem rowUpper_eq (a b t : ℝ) :
    rowUpper a b t =
      Real.exp (-(a * t)) * (1 - b * t ^ 2 / 2 + (b * t ^ 2 / 2) ^ 2 / 2) := by
  simp only [rowUpper, expMonomial, pow_zero, one_mul]
  ring

private theorem rowLower_eq (a b m t : ℝ) :
    rowLower a b m t = Real.exp (-(a * t)) * (1 - b * t ^ 2 / 2 - m * b * t ^ 3) := by
  simp only [rowLower, expMonomial, pow_zero, one_mul]
  ring

private theorem prod_le_rowUpper {ι : Type*} (I : Finset ι) (w : ι → ℝ) (t : ℝ)
    (ht : 0 ≤ t) (hw : ∀ j ∈ I, 0 ≤ w j) (hcap : ∀ j ∈ I, t * w j ≤ 1) :
    (∏ j ∈ I, (1 - t * w j)) ≤ rowUpper (∑ j ∈ I, w j) (∑ j ∈ I, (w j) ^ 2) t := by
  let a := ∑ j ∈ I, w j
  let b := ∑ j ∈ I, (w j) ^ 2
  have hb : 0 ≤ b := Finset.sum_nonneg fun j _ ↦ sq_nonneg (w j)
  change _ ≤ rowUpper a b t
  calc
    _ ≤ ∏ j ∈ I, Real.exp (-(t * w j) - (t * w j) ^ 2 / 2) :=
      Finset.prod_le_prod (fun j hj ↦ sub_nonneg.mpr (hcap j hj))
        (fun j hj ↦ one_sub_le_exp_quadratic _ (mul_nonneg ht (hw j hj)))
    _ = Real.exp (-(a * t)) * Real.exp (-(b * t ^ 2 / 2)) := by
      rw [← Real.exp_sum, ← Real.exp_add]
      congr 1
      simp [a, b, mul_pow, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div,
        Finset.sum_neg_distrib]
      ring
    _ ≤ rowUpper a b t := by
      rw [rowUpper_eq]
      exact mul_le_mul_of_nonneg_left (exp_neg_le_quadratic _ (by positivity))
        (Real.exp_nonneg _)

private theorem rowLower_le_prod {ι : Type*} (I : Finset ι) (w : ι → ℝ) (t m : ℝ)
    (ht : 0 ≤ t) (hw : ∀ j ∈ I, 0 ≤ w j) (hm : ∀ j ∈ I, w j ≤ m)
    (hsmall : ∀ j ∈ I, t * w j ≤ 1 / 2) :
    rowLower (∑ j ∈ I, w j) (∑ j ∈ I, (w j) ^ 2) m t ≤
      ∏ j ∈ I, (1 - t * w j) := by
  let a := ∑ j ∈ I, w j
  let b := ∑ j ∈ I, (w j) ^ 2
  let c := ∑ j ∈ I, (w j) ^ 3
  have hc : c ≤ m * b := by
    dsimp [c, b]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    simpa only [pow_succ' (w j) 2] using
      mul_le_mul_of_nonneg_right (hm j hj) (sq_nonneg (w j))
  change rowLower a b m t ≤ _
  calc
    _ ≤ Real.exp (-(a * t)) * Real.exp (-(b * t ^ 2 / 2 + c * t ^ 3)) := by
      rw [rowLower_eq]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      have hc' := mul_le_mul_of_nonneg_right hc (pow_nonneg ht 3)
      linarith [Real.one_sub_le_exp_neg (b * t ^ 2 / 2 + c * t ^ 3)]
    _ = ∏ j ∈ I, Real.exp (-(t * w j) - (t * w j) ^ 2 / 2 - (t * w j) ^ 3) := by
      rw [← Real.exp_sum, ← Real.exp_add]
      congr 1
      simp [a, b, c, mul_pow, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div,
        Finset.sum_neg_distrib]
      ring
    _ ≤ _ := Finset.prod_le_prod (fun j _ ↦ Real.exp_nonneg _)
      (fun j hj ↦ exp_cubic_le_one_sub _ (mul_nonneg ht (hw j hj)) (hsmall j hj))

private theorem integrableOn_rowUpper {a : ℝ} (ha : 0 < a) (b : ℝ) :
    IntegrableOn (rowUpper a b) (Ioi 0) := by
  exact ((pittel_integrable_exp_moment ha 0).sub
    ((pittel_integrable_exp_moment ha 2).const_mul (b / 2))).add
      ((pittel_integrable_exp_moment ha 4).const_mul (b ^ 2 / 8))

private theorem integrableOn_rowLower {a : ℝ} (ha : 0 < a) (b m : ℝ) :
    IntegrableOn (rowLower a b m) (Ioi 0) := by
  exact ((pittel_integrable_exp_moment ha 0).sub
    ((pittel_integrable_exp_moment ha 2).const_mul (b / 2))).sub
      ((pittel_integrable_exp_moment ha 3).const_mul (m * b))

private theorem integral_rowUpper {a : ℝ} (ha : 0 < a) (b : ℝ) :
    (∫ t : ℝ in Ioi 0, rowUpper a b t) = 1 / a - b / a ^ 3 + 3 * b ^ 2 / a ^ 5 := by
  have h0 := pittel_integrable_exp_moment ha 0
  have h2 := (pittel_integrable_exp_moment ha 2).const_mul (b / 2)
  have h4 := (pittel_integrable_exp_moment ha 4).const_mul (b ^ 2 / 8)
  have h := integral_add (h0.sub h2) h4
  simp only [Pi.sub_apply] at h
  rw [integral_sub h0 h2, integral_const_mul, integral_const_mul] at h
  simp only [pittel_exp_moment ha] at h
  calc
    _ = _ := by simpa only [rowUpper, expMonomial] using h
    _ = _ := by norm_num [Nat.factorial]; ring

private theorem integral_rowLower {a : ℝ} (ha : 0 < a) (b m : ℝ) :
    (∫ t : ℝ in Ioi 0, rowLower a b m t) = 1 / a - b / a ^ 3 - 6 * m * b / a ^ 4 := by
  have h0 := pittel_integrable_exp_moment ha 0
  have h2 := (pittel_integrable_exp_moment ha 2).const_mul (b / 2)
  have h3 := (pittel_integrable_exp_moment ha 3).const_mul (m * b)
  have h := integral_sub (h0.sub h2) h3
  simp only [Pi.sub_apply] at h
  rw [integral_sub h0 h2, integral_const_mul, integral_const_mul] at h
  simp only [pittel_exp_moment ha] at h
  calc
    _ = _ := by simpa only [rowLower, expMonomial] using h
    _ = _ := by norm_num [Nat.factorial]; ring

theorem pittelRowIntegral_le {ι : Type*} (I : Finset ι) (w : ι → ℝ) {s : ℝ}
    (hs : 0 ≤ s) (hw : ∀ j ∈ I, 0 ≤ w j) (hcap : ∀ j ∈ I, s * w j ≤ 1)
    (ha : 0 < ∑ j ∈ I, w j) :
    let a := ∑ j ∈ I, w j
    let b := ∑ j ∈ I, (w j) ^ 2
    pittelRowIntegral I w s ≤ 1 / a - b / a ^ 3 + 3 * b ^ 2 / a ^ 5 := by
  dsimp only
  let a := ∑ j ∈ I, w j
  let b := ∑ j ∈ I, (w j) ^ 2
  have hfi : Continuous fun t : ℝ ↦ ∏ j ∈ I, (1 - t * w j) := by fun_prop
  have hUi := integrableOn_rowUpper ha b
  have hUi' : IntegrableOn (rowUpper a b) (Ioc 0 s) := hUi.mono_set Ioc_subset_Ioi_self
  have hUn : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Ioi 0)] rowUpper a b := by
    apply ae_of_all
    intro t
    rw [rowUpper_eq]
    apply mul_nonneg (Real.exp_nonneg _)
    nlinarith [sq_nonneg (b * t ^ 2 / 2 - 1)]
  calc
    pittelRowIntegral I w s ≤ ∫ t : ℝ in Ioc 0 s, rowUpper a b t := by
      rw [pittelRowIntegral, intervalIntegral.integral_of_le hs]
      apply setIntegral_mono_on (hfi.intervalIntegrable 0 s).1 hUi' measurableSet_Ioc
      intro t ht
      exact prod_le_rowUpper I w t ht.1.le hw fun j hj ↦
        mul_le_mul_of_nonneg_right ht.2 (hw j hj) |>.trans (hcap j hj)
    _ ≤ ∫ t : ℝ in Ioi 0, rowUpper a b t :=
      setIntegral_mono_set hUi hUn Ioc_subset_Ioi_self.eventuallyLE
    _ = _ := integral_rowUpper ha b

theorem le_pittelRowIntegral {ι : Type*} (I : Finset ι) (w : ι → ℝ) {s L m : ℝ}
    (hL : 0 ≤ L) (hLs : L ≤ s) (hw : ∀ j ∈ I, 0 ≤ w j) (hcap : ∀ j ∈ I, s * w j ≤ 1)
    (hm : ∀ j ∈ I, w j ≤ m) (hsmall : ∀ j ∈ I, L * w j ≤ 1 / 2)
    (ha : 0 < ∑ j ∈ I, w j) :
    let a := ∑ j ∈ I, w j
    let b := ∑ j ∈ I, (w j) ^ 2
    1 / a - b / a ^ 3 - 6 * m * b / a ^ 4 - Real.exp (-(a * L)) / a ≤ pittelRowIntegral I w s :=
  by
    dsimp only
    let a := ∑ j ∈ I, w j
    let b := ∑ j ∈ I, (w j) ^ 2
    have hb : 0 ≤ b := Finset.sum_nonneg fun j _ ↦ sq_nonneg (w j)
    have hm' : 0 ≤ m := by
      obtain ⟨j, hj⟩ : I.Nonempty := by
        by_contra he
        rw [Finset.not_nonempty_iff_eq_empty.mp he, Finset.sum_empty] at ha
        exact lt_irrefl 0 ha
      exact (hw j hj).trans (hm j hj)
    have hs := hL.trans hLs
    have hfi : Continuous fun t : ℝ ↦ ∏ j ∈ I, (1 - t * w j) := by fun_prop
    have hRi := integrableOn_rowLower ha b m
    have hRi₁ : IntegrableOn (rowLower a b m) (Ioc 0 L) :=
      hRi.mono_set Ioc_subset_Ioi_self
    have hRi₂ : IntegrableOn (rowLower a b m) (Ioi L) := hRi.mono_set (Ioi_subset_Ioi hL)
    have hdiff : (∫ t : ℝ in Ioi 0, rowLower a b m t) =
        (∫ t : ℝ in Ioc 0 L, rowLower a b m t) +
          ∫ t : ℝ in Ioi L, rowLower a b m t := by
      rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hRi₁ hRi₂,
        Ioc_union_Ioi_eq_Ioi hL]
    have htail : (∫ t : ℝ in Ioi L, rowLower a b m t) ≤ Real.exp (-(a * L)) / a := by
      have hneg : -a < 0 := neg_lt_zero.mpr ha
      calc
        _ ≤ ∫ t : ℝ in Ioi L, Real.exp (-a * t) := by
          apply setIntegral_mono_on hRi₂ (integrableOn_exp_mul_Ioi hneg L) measurableSet_Ioi
          intro t ht
          rw [rowLower_eq, neg_mul]
          nth_rw 2 [← mul_one (Real.exp _)]
          apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
          have ht' : 0 ≤ t := hL.trans ht.le
          have h₂ : 0 ≤ b * t ^ 2 / 2 := by positivity
          have h₃ : 0 ≤ m * b * t ^ 3 := by positivity
          linarith
        _ = _ := by rw [integral_exp_mul_Ioi hneg, neg_div_neg_eq, neg_mul]
    calc
      _ ≤ ∫ t : ℝ in Ioc 0 L, rowLower a b m t := by
        rw [integral_rowLower ha b m] at hdiff
        linarith
      _ ≤ ∫ t : ℝ in Ioc 0 L, ∏ j ∈ I, (1 - t * w j) := by
        apply setIntegral_mono_on hRi₁ (hfi.intervalIntegrable 0 L).1 measurableSet_Ioc
        intro t ht
        exact rowLower_le_prod I w t m ht.1.le hw hm fun j hj ↦
          mul_le_mul_of_nonneg_right ht.2 (hw j hj) |>.trans (hsmall j hj)
      _ ≤ pittelRowIntegral I w s := by
        rw [pittelRowIntegral, intervalIntegral.integral_of_le hs]
        apply setIntegral_mono_set (hfi.intervalIntegrable 0 s).1 _
          (Ioc_subset_Ioc le_rfl hLs).eventuallyLE
        filter_upwards [self_mem_ae_restrict (μ := volume) (measurableSet_Ioc (a := 0) (b := s))]
          with t ht
        exact Finset.prod_nonneg fun j hj ↦ sub_nonneg.mpr
          (mul_le_mul_of_nonneg_right ht.2 (hw j hj) |>.trans (hcap j hj))

end LennonPittelFormalization

end

section

open Filter Finset

open scoped BigOperators Topology

namespace LennonPittelFormalization

private theorem abs_log_sub_sub_one_le {q : ℝ} (h : |q - 1| ≤ 1 / 2) :
    |Real.log q - (q - 1)| ≤ 2 * |q - 1| ^ 2 := by
  have hx : |1 - q| = |q - 1| := abs_sub_comm _ _
  have hx' : |1 - q| < 1 := by rw [hx]; linarith
  have hTaylor := Real.abs_log_sub_add_sum_range_le hx' 1
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, pow_one, div_one,
    show (1 : ℝ) - (1 - q) = q by ring, hx] at hTaylor
  calc
    |Real.log q - (q - 1)| = |1 - q + Real.log q| := by congr 1; ring
    _ ≤ |q - 1| ^ 2 / (1 - |q - 1|) := hTaylor
    _ ≤ 2 * |q - 1| ^ 2 := by
      apply (div_le_iff₀ (by linarith : 0 < 1 - |q - 1|)).2
      nlinarith [mul_nonneg (sq_nonneg |q - 1|) (show 0 ≤ 1 - 2 * |q - 1| by linarith)]

private theorem pittel_model_error {w T m : ℝ} (hw : 0 ≤ w) (hwm : w ≤ m)
    (hm : m ≤ 1 / 2) (hT : 0 ≤ T) (hTm : T ≤ m) :
    |1 / (1 - w) - (T - w ^ 2) / (1 - w) ^ 3 - (1 + w - T)| ≤
      34 * m * w := by
  have ha : 0 < 1 - w := by linarith
  have ha2 : 1 / 2 ≤ 1 - w := by linarith
  have ha3 : 1 / 8 ≤ (1 - w) ^ 3 := by
    calc
      _ = (1 / 2 : ℝ) ^ 3 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) ha2 _
  have hb3 : (1 - w) ^ 3 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ ha.le (show 1 - w ≤ 1 by linarith) 3
  have hnum : 1 - (1 - w) ^ 3 ≤ 3 * w := by
    nlinarith [mul_nonneg (sq_nonneg w) (show 0 ≤ 3 - w by linarith)]
  have hA : w ^ 2 / (1 - w) ≤ 2 * w ^ 2 := by
    apply (div_le_iff₀ ha).2
    nlinarith [mul_nonneg (sq_nonneg w) (show 0 ≤ 1 - 2 * w by linarith)]
  have hB : w ^ 2 / (1 - w) ^ 3 ≤ 8 * w ^ 2 := by
    apply (div_le_iff₀ (pow_pos ha _)).2
    nlinarith [mul_nonneg (sq_nonneg w) (show 0 ≤ 8 * (1 - w) ^ 3 - 1 by linarith)]
  have hC : T * (1 - (1 - w) ^ 3) / (1 - w) ^ 3 ≤ 24 * T * w := by
    apply (div_le_iff₀ (pow_pos ha _)).2
    calc
      T * (1 - (1 - w) ^ 3) ≤ T * (3 * w) := mul_le_mul_of_nonneg_left hnum hT
      _ = 24 * T * w * (1 / 8) := by ring
      _ ≤ 24 * T * w * (1 - w) ^ 3 := mul_le_mul_of_nonneg_left ha3 (by positivity)
  have heq :
      1 / (1 - w) - (T - w ^ 2) / (1 - w) ^ 3 - (1 + w - T) =
        w ^ 2 / (1 - w) + w ^ 2 / (1 - w) ^ 3 -
          T * (1 - (1 - w) ^ 3) / (1 - w) ^ 3 := by
    field_simp
    ring
  rw [heq]
  apply abs_le.2
  have hD : T * (1 - (1 - w) ^ 3) / (1 - w) ^ 3 ≥ 0 := by
    exact div_nonneg (mul_nonneg hT (sub_nonneg.mpr hb3)) (pow_nonneg ha.le _)
  have hE := mul_le_mul_of_nonneg_right hwm hw
  have hF := mul_le_mul_of_nonneg_right hTm hw
  constructor <;> linarith [div_nonneg (sq_nonneg w) ha.le,
    div_nonneg (sq_nonneg w) (pow_nonneg ha.le 3)]

theorem abs_log_prod_pittelRows_le {n : ℕ} {w q : Fin n → ℝ} {m e : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hwm : ∀ i, w i ≤ m)
    (hm : 0 ≤ m) (hm' : m ≤ 1 / 2) (he : 0 ≤ e) :
    let T := ∑ i, w i ^ 2
    let d := 2 * m + 34 * m ^ 2 + e
    let E := 34 * m + (n : ℝ) * e
    d ≤ 1 / 2 →
    (∀ i, |q i - (1 / (1 - w i) - (T - w i ^ 2) / (1 - w i) ^ 3)| ≤ e) →
    (∀ i, 0 < q i) ∧
      |Real.log (∏ i, q i) - (1 - (n : ℝ) * T)| ≤ E + 2 * d * (1 + n * T + E) := by
  classical
  dsimp only
  let T := ∑ i, w i ^ 2
  let d := 2 * m + 34 * m ^ 2 + e
  let E := 34 * m + (n : ℝ) * e
  change d ≤ 1 / 2 → _ → (∀ i, 0 < q i) ∧
    |Real.log (∏ i, q i) - (1 - (n : ℝ) * T)| ≤ E + 2 * d * (1 + n * T + E)
  intro hd hrow
  have hT : 0 ≤ T := Finset.sum_nonneg fun i _ ↦ sq_nonneg (w i)
  have hTm : T ≤ m := calc
    T ≤ ∑ i, m * w i := Finset.sum_le_sum fun i _ ↦ by
      simpa only [pow_two] using mul_le_mul_of_nonneg_right (hwm i) (hw i)
    _ = m := by rw [← Finset.mul_sum, hsum, mul_one]
  have hclose (i) : |q i - (1 + w i - T)| ≤ 34 * m * w i + e := calc
    _ ≤ |q i - (1 / (1 - w i) - (T - w i ^ 2) / (1 - w i) ^ 3)| +
        |1 / (1 - w i) - (T - w i ^ 2) / (1 - w i) ^ 3 - (1 + w i - T)| :=
      abs_sub_le _ _ _
    _ ≤ _ := by
      linarith [hrow i, pittel_model_error (hw i) (hwm i) hm' hT hTm]
  have hu (i) : |q i - 1| ≤ w i + T + (34 * m * w i + e) := calc
    _ ≤ |q i - (1 + w i - T)| + |(1 + w i - T) - 1| := abs_sub_le _ _ _
    _ ≤ _ := by
      have ha : |(1 + w i - T) - 1| ≤ w i + T := by
        apply abs_le.2
        constructor <;> linarith [hw i]
      linarith [hclose i]
  have hud (i) : |q i - 1| ≤ d := by
    have hmul := mul_le_mul_of_nonneg_left (hwm i) (show 0 ≤ 34 * m by positivity)
    dsimp [d]
    nlinarith [hu i, hTm, hwm i]
  have hq (i) : 0 < q i := by
    linarith [(abs_le.1 ((hud i).trans hd)).1]
  refine ⟨hq, ?_⟩
  have hsum_close : ∑ i, |q i - (1 + w i - T)| ≤ E := calc
    _ ≤ ∑ i, (34 * m * w i + e) := Finset.sum_le_sum fun i _ ↦ hclose i
    _ = E := by simp [E, Finset.sum_add_distrib, ← Finset.mul_sum, hsum, nsmul_eq_mul]
  have hsum_u : ∑ i, |q i - 1| ≤ 1 + n * T + E := calc
    _ ≤ ∑ i, (w i + T + (34 * m * w i + e)) := Finset.sum_le_sum fun i _ ↦ hu i
    _ = _ := by simp [E, Finset.sum_add_distrib, ← Finset.mul_sum, hsum, nsmul_eq_mul]
  have hsum_log : ∑ i, |Real.log (q i) - (q i - 1)| ≤ 2 * d * (1 + n * T + E) := calc
    _ ≤ ∑ i, (2 * d) * |q i - 1| := by
      apply Finset.sum_le_sum
      intro i _
      refine (abs_log_sub_sub_one_le ((hud i).trans hd)).trans ?_
      have hh := mul_le_mul_of_nonneg_right (hud i) (abs_nonneg (q i - 1))
      nlinarith
    _ = 2 * d * ∑ i, |q i - 1| := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum_u (by dsimp [d]; positivity)
  rw [Real.log_prod (fun i _ ↦ (hq i).ne')]
  have hsum_target : ∑ i, (w i - T) = 1 - (n : ℝ) * T := by
    simp [Finset.sum_sub_distrib, hsum, nsmul_eq_mul]
  rw [← hsum_target, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |Real.log (q i) - (w i - T)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (|Real.log (q i) - (q i - 1)| + |q i - (1 + w i - T)|) := by
      apply Finset.sum_le_sum
      intro i _
      have h : q i - 1 - (w i - T) = q i - (1 + w i - T) := by ring
      simpa only [h] using abs_sub_le (Real.log (q i)) (q i - 1) (w i - T)
    _ ≤ _ := by
      rw [Finset.sum_add_distrib]
      linarith

theorem eventually_pittelRowsProduct_close_of_error {m e : ℕ → ℝ}
    (hm0 : Tendsto m atTop (𝓝 0)) (he0 : Tendsto e atTop (𝓝 0))
    (hne0 : Tendsto (fun n : ℕ ↦ (n : ℝ) * e n) atTop (𝓝 0))
    (hmn : ∀ᶠ n in atTop, 0 ≤ m n) (hen : ∀ᶠ n in atTop, 0 ≤ e n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ᶠ n in atTop, ∀ w q : Fin n → ℝ,
      (∀ i, 0 ≤ w i) → (∑ i, w i) = 1 → (∀ i, w i ≤ m n) →
      |(n : ℝ) * (∑ i, w i ^ 2) - 2| ≤ η →
      (∀ i, |q i - (1 / (1 - w i) - ((∑ j, w j ^ 2) - w i ^ 2) / (1 - w i) ^ 3)|
        ≤ e n) →
      |(∏ i, q i) - (Real.exp 1)⁻¹| ≤ ε := by
  let d (n : ℕ) := 2 * m n + 34 * m n ^ 2 + e n
  let E (n : ℕ) := 34 * m n + (n : ℝ) * e n
  have hd0 : Tendsto d atTop (𝓝 0) := by
    simpa [d] using ((hm0.const_mul 2).add ((hm0.pow 2).const_mul 34)).add he0
  have hE0 : Tendsto E atTop (𝓝 0) := by
    simpa [E] using (hm0.const_mul 34).add hne0
  obtain ⟨δ, hδ, hδexp⟩ := Metric.continuousAt_iff.mp
    (Real.continuous_exp.continuousAt (x := (-1 : ℝ))) ε hε
  refine ⟨δ / 2, by positivity, ?_⟩
  have hB0 : Tendsto (fun n ↦ E n + 2 * d n * (1 + (2 + δ / 2) + E n))
      atTop (𝓝 0) := by
    simpa using hE0.add ((hd0.const_mul 2).mul (hE0.const_add (1 + (2 + δ / 2))))
  filter_upwards [hmn, hen, (tendsto_order.mp hm0).2 (1 / 2) (by norm_num),
    (tendsto_order.mp hd0).2 (1 / 2) (by norm_num),
    (tendsto_order.mp hB0).2 (δ / 2) (by positivity)] with n hm he hml hdl hBl
  intro w q hw hsum hwm hnorm hrow
  let T := ∑ i, w i ^ 2
  change |(n : ℝ) * T - 2| ≤ δ / 2 at hnorm
  obtain ⟨hq, hlog⟩ := abs_log_prod_pittelRows_le hw hsum hwm hm hml.le he hdl.le hrow
  have hd : 0 ≤ d n := by dsimp [d]; positivity
  have hupper : (n : ℝ) * T ≤ 2 + δ / 2 := by linarith [(abs_le.1 hnorm).2]
  have hl : |Real.log (∏ i, q i) - (1 - (n : ℝ) * T)| < δ / 2 := calc
    _ ≤ E n + 2 * d n * (1 + (n : ℝ) * T + E n) := hlog
    _ ≤ E n + 2 * d n * (1 + (2 + δ / 2) + E n) := by gcongr
    _ < δ / 2 := hBl
  have htotal : |Real.log (∏ i, q i) - (-1)| < δ := calc
    _ ≤ |Real.log (∏ i, q i) - (1 - (n : ℝ) * T)| +
        |(1 - (n : ℝ) * T) - (-1)| := abs_sub_le _ _ _
    _ < δ := by
      rw [show (1 - (n : ℝ) * T) - (-1) = -((n : ℝ) * T - 2) by ring, abs_neg]
      linarith
  have hfinal := hδexp (x := Real.log (∏ i, q i)) (by simpa only [Real.dist_eq] using htotal)
  simpa only [Real.dist_eq, Real.exp_log (Finset.prod_pos fun i _ ↦ hq i), Real.exp_neg]
    using hfinal.le

private theorem pittel_row_error_rates :
    let m (n : ℕ) := 12 * Real.log n / n
    let L (n : ℕ) := 6 * Real.log n
    let e (n : ℕ) := 96 * (m n) ^ 2 + 2 * Real.exp (-(L n / 2))
    Tendsto m atTop (𝓝 0) ∧
      Tendsto (fun n ↦ L n * m n) atTop (𝓝 0) ∧
      Tendsto e atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ ↦ (n : ℝ) * e n) atTop (𝓝 0) := by
  let m (n : ℕ) := 12 * Real.log n / n
  let L (n : ℕ) := 6 * Real.log n
  let e (n : ℕ) := 96 * (m n) ^ 2 + 2 * Real.exp (-(L n / 2))
  change Tendsto m atTop (𝓝 0) ∧ Tendsto (fun n ↦ L n * m n) atTop (𝓝 0) ∧
    Tendsto e atTop (𝓝 0) ∧ Tendsto (fun n : ℕ ↦ (n : ℝ) * e n) atTop (𝓝 0)
  have hc : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n / n) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hc
  have hlog2 : Tendsto (fun n : ℕ ↦ Real.log n ^ 2 / n) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_one, Real.rpow_ofNat] using
      (isLittleO_log_rpow_rpow_atTop (s := 1) 2 (by norm_num)).tendsto_div_nhds_zero.comp hc
  have hm : Tendsto m atTop (𝓝 0) := by
    simpa only [m, mul_div_assoc, mul_zero] using hlog.const_mul 12
  have hLm : Tendsto (fun n ↦ L n * m n) atTop (𝓝 0) := by
    refine (show Tendsto (fun n : ℕ ↦ 72 * (Real.log n ^ 2 / n)) atTop (𝓝 0) by
      simpa only [mul_zero] using hlog2.const_mul 72).congr fun n ↦ ?_
    dsimp [L, m]
    ring
  have hnm2 : Tendsto (fun n : ℕ ↦ (n : ℝ) * (m n) ^ 2) atTop (𝓝 0) := by
    refine (show Tendsto (fun n : ℕ ↦ 144 * (Real.log n ^ 2 / n)) atTop (𝓝 0) by
      simpa only [mul_zero] using hlog2.const_mul 144).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    dsimp [m]
    field_simp [Nat.cast_ne_zero.mpr hn.ne']
    ring
  have htail_eq {n : ℕ} (hn : 0 < n) :
      Real.exp (-(L n / 2)) = ((n : ℝ) ^ 3)⁻¹ := by
    rw [show -(L n / 2) = -((3 : ℕ) : ℝ) * Real.log n by dsimp [L]; norm_num; ring,
      neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (Nat.cast_pos.mpr hn)]
  have htail : Tendsto (fun n ↦ Real.exp (-(L n / 2))) atTop (𝓝 0) := by
    refine ((tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by norm_num : 3 ≠ 0))).comp
      hc).congr' ?_
    exact (eventually_gt_atTop 0).mono fun n hn ↦ (htail_eq hn).symm
  have hntail : Tendsto (fun n : ℕ ↦ (n : ℝ) * Real.exp (-(L n / 2))) atTop (𝓝 0) := by
    refine ((tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by norm_num : 2 ≠ 0))).comp
      hc).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    change ((n : ℝ) ^ 2)⁻¹ = (n : ℝ) * Real.exp (-(L n / 2))
    rw [htail_eq hn]
    field_simp [hn'.ne']
  refine ⟨hm, hLm, ?_, ?_⟩
  · simpa only [e, mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0)] using
      ((hm.pow 2).const_mul 96).add (htail.const_mul 2)
  · refine (show Tendsto
      (fun n : ℕ ↦ 96 * ((n : ℝ) * (m n) ^ 2) + 2 * ((n : ℝ) * Real.exp (-(L n / 2))))
      atTop (𝓝 0) by simpa only [mul_zero, add_zero] using
        (hnm2.const_mul 96).add (hntail.const_mul 2)).congr fun n ↦ ?_
    dsimp [e]
    ring

private theorem pittel_row_abs_of_bounds {q a b m L : ℝ} (ha : 1 / 2 ≤ a)
    (hb : 0 ≤ b) (hbm : b ≤ m) (hL : 0 ≤ L)
    (hu : q ≤ 1 / a - b / a ^ 3 + 3 * b ^ 2 / a ^ 5)
    (hl : 1 / a - b / a ^ 3 - 6 * m * b / a ^ 4 - Real.exp (-(a * L)) / a ≤ q) :
    |q - (1 / a - b / a ^ 3)| ≤ 96 * m ^ 2 + 2 * Real.exp (-(L / 2)) := by
  have ha' : 0 < a := by linarith
  have hm : 0 ≤ m := hb.trans hbm
  have ha4 : 1 / 16 ≤ a ^ 4 := by
    calc
      _ = (1 / 2 : ℝ) ^ 4 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) ha _
  have ha5 : 1 / 32 ≤ a ^ 5 := by
    calc
      _ = (1 / 2 : ℝ) ^ 5 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) ha _
  have hu' : 3 * b ^ 2 / a ^ 5 ≤ 96 * m ^ 2 := calc
    _ ≤ 3 * m ^ 2 / a ^ 5 := by gcongr
    _ ≤ _ := by
      apply (div_le_iff₀ (pow_pos ha' _)).2
      nlinarith [mul_nonneg (sq_nonneg m) (show 0 ≤ 32 * a ^ 5 - 1 by linarith)]
  have hl' : 6 * m * b / a ^ 4 ≤ 96 * m ^ 2 := calc
    _ ≤ 6 * m * m / a ^ 4 := by gcongr
    _ ≤ _ := by
      apply (div_le_iff₀ (pow_pos ha' _)).2
      nlinarith [mul_nonneg (sq_nonneg m) (show 0 ≤ 16 * a ^ 4 - 1 by linarith)]
  have htail : Real.exp (-(a * L)) / a ≤ 2 * Real.exp (-(L / 2)) := by
    apply (div_le_iff₀ ha').2
    calc
      _ ≤ Real.exp (-(L / 2)) := Real.exp_le_exp.mpr (by
        nlinarith [mul_le_mul_of_nonneg_right ha hL])
      _ = 2 * Real.exp (-(L / 2)) * (1 / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ha (by positivity)
  exact abs_le.2 ⟨by linarith, by linarith [Real.exp_pos (-(L / 2))]⟩

theorem eventually_pittelRowsProduct_close {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ᶠ n : ℕ in atTop, ∀ (w : Fin n → ℝ) (s : ℝ),
      6 * Real.log n ≤ s →
      (∀ i, 0 ≤ w i) → (∑ i, w i) = 1 → (∀ i, w i ≤ 12 * Real.log n / n) →
      |(n : ℝ) * (∑ i, w i ^ 2) - 2| ≤ η →
      (∀ i, s * w i ≤ 1) →
      |(∏ i, pittelRowIntegral (univ.erase i) w s) - (Real.exp 1)⁻¹| ≤ ε := by
  let m (n : ℕ) := 12 * Real.log n / n
  let L (n : ℕ) := 6 * Real.log n
  let e (n : ℕ) := 96 * (m n) ^ 2 + 2 * Real.exp (-(L n / 2))
  obtain ⟨hm0, hLm0, he0, hne0⟩ := pittel_row_error_rates
  have hLn : ∀ᶠ n : ℕ in atTop, 0 ≤ L n := (eventually_ge_atTop 1).mono fun n hn ↦ by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact mul_nonneg (by norm_num) (Real.log_nonneg hn')
  have hmn : ∀ᶠ n : ℕ in atTop, 0 ≤ m n := (eventually_ge_atTop 1).mono fun n hn ↦ by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    dsimp [m]
    positivity [Real.log_nonneg hn']
  have hen : ∀ᶠ n : ℕ in atTop, 0 ≤ e n := .of_forall fun n ↦ by dsimp [e]; positivity
  obtain ⟨η, hη, hgood⟩ := eventually_pittelRowsProduct_close_of_error
    (m := m) (e := e) hm0 he0 hne0 hmn hen hε
  refine ⟨η, hη, ?_⟩
  filter_upwards [hgood, hLn, hmn, (tendsto_order.mp hm0).2 (1 / 2) (by norm_num),
    (tendsto_order.mp hLm0).2 (1 / 2) (by norm_num)] with n hg hL hm hm' hLm
  intro w s hLs hw hsum hwm hnorm hcap
  apply hg w _ hw hsum hwm hnorm
  intro i
  let I : Finset (Fin n) := univ.erase i
  let a := ∑ j ∈ I, w j
  let b := ∑ j ∈ I, w j ^ 2
  have ha : a = 1 - w i := by
    dsimp only [a, I]
    rw [Finset.sum_erase_eq_sub (f := w) (mem_univ i), hsum]
  have hb : b = (∑ j, w j ^ 2) - w i ^ 2 :=
    Finset.sum_erase_eq_sub (f := fun j ↦ w j ^ 2) (mem_univ i)
  have hal : 1 / 2 ≤ a := by linarith [hwm i]
  have hap : 0 < a := by linarith
  have hbn : 0 ≤ b := Finset.sum_nonneg fun j _ ↦ sq_nonneg (w j)
  have hbm : b ≤ m n := calc
    b ≤ ∑ j ∈ I, m n * w j := Finset.sum_le_sum fun j _ ↦ by
      simpa only [pow_two] using mul_le_mul_of_nonneg_right (hwm j) (hw j)
    _ = m n * a := by rw [Finset.mul_sum]
    _ ≤ m n := by rw [ha]; nlinarith [mul_nonneg hm (hw i)]
  have hsmall (j : Fin n) : L n * w j ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left (hwm j) hL).trans hLm.le
  have hu := pittelRowIntegral_le I w (hL.trans hLs) (fun j _ ↦ hw j)
    (fun j _ ↦ hcap j) hap
  have hl := le_pittelRowIntegral I w hL hLs (fun j _ ↦ hw j)
    (fun j _ ↦ hcap j) (fun j _ ↦ hwm j) (fun j _ ↦ hsmall j) hap
  rw [← ha, ← hb]
  exact pittel_row_abs_of_bounds hal hbn hbm hL hu hl

end LennonPittelFormalization

end

section

open MeasureTheory Set

open scoped ENNReal BigOperators

namespace LennonPittelFormalization

noncomputable def spouseAngle {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  x i / (∑ j, x j)

theorem measurable_spouseAngle (n : ℕ) : Measurable (@spouseAngle n) :=
  measurable_pi_iff.2 fun i ↦ (measurable_pi_apply i).div
    (Finset.measurable_sum _ fun j _ ↦ measurable_pi_apply j)

noncomputable def spouseAngularLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  (n.factorial : ℝ≥0∞) • Measure.map spouseAngle (volume.restrict (scoreSimplex n 1))

theorem isProbabilityMeasure_spouseAngularLaw (n : ℕ) :
    IsProbabilityMeasure (spouseAngularLaw n) := by
  refine ⟨?_⟩
  rw [spouseAngularLaw, Measure.smul_apply, Measure.map_apply (measurable_spouseAngle n)
    MeasurableSet.univ, preimage_univ, Measure.restrict_apply_univ,
    volume_scoreSimplex n zero_le_one]
  have hf : (n.factorial : ℝ≥0∞) ≠ 0 := by positivity
  rw [one_pow, one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_natCast,
    smul_eq_mul, ENNReal.mul_inv_cancel hf (by simp)]

instance (n : ℕ) : IsProbabilityMeasure (spouseAngularLaw n) :=
  isProbabilityMeasure_spouseAngularLaw n

noncomputable def spouseRadialLaw (n : ℕ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity
    (fun s ↦ ENNReal.ofReal (s ^ (n - 1) / ((n - 1).factorial : ℝ)))

instance (n : ℕ) : SigmaFinite (spouseRadialLaw n) := by
  unfold spouseRadialLaw
  infer_instance

private theorem measurable_spouseTotal (n : ℕ) :
    Measurable (fun x : Fin n → ℝ ↦ ∑ i, x i) :=
  Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i

private theorem measurableSet_spouseOrthant (n : ℕ) :
    MeasurableSet {x : Fin n → ℝ | ∀ i, 0 ≤ x i} := by
  rw [ofPred_forall]
  exact MeasurableSet.iInter fun i ↦ measurableSet_le measurable_const (measurable_pi_apply i)

theorem ae_spouseAngularLaw {n : ℕ} (hn : 0 < n) :
    ∀ᵐ w ∂(spouseAngularLaw n), (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 := by
  have hs0 : volume (scoreSimplex n 0) = 0 := by
    rw [volume_scoreSimplex n le_rfl, zero_pow hn.ne', zero_div, ENNReal.ofReal_zero]
  have hu := ae_restrict_mem (μ := (volume : Measure (Fin n → ℝ)))
    (measurableSet_scoreSimplex n 1)
  have hz : ∀ᵐ x ∂((volume : Measure (Fin n → ℝ)).restrict (scoreSimplex n 1)),
      x ∉ scoreSimplex n 0 := by
    rw [ae_iff]
    change (volume.restrict (scoreSimplex n 1)) {x | ¬ x ∉ scoreSimplex n 0} = 0
    simp only [not_not, ofPred_mem_eq]
    rw [Measure.restrict_apply (measurableSet_scoreSimplex n 0)]
    exact le_antisymm ((measure_mono inter_subset_left).trans_eq hs0) zero_le
  rw [spouseAngularLaw]
  apply Measure.ae_smul_measure
  rw [ae_map_iff (measurable_spouseAngle n).aemeasurable
    (show MeasurableSet {w : Fin n → ℝ | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1} from
      (measurableSet_spouseOrthant n).inter
        (measurableSet_eq_fun (measurable_spouseTotal n) measurable_const))]
  · filter_upwards [hu, hz] with x hx hx0
    have hsum : 0 < ∑ i, x i := lt_of_not_ge fun h ↦ hx0 ⟨hx.1, h⟩
    exact ⟨fun i ↦ div_nonneg (hx.1 i) hsum.le, by
      simp only [spouseAngle, ← Finset.sum_div, div_self hsum.ne']⟩

theorem volume_preimage_spouseScale (n : ℕ) {c : ℝ} (hc : 0 < c)
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s) :
    volume ((fun (x : Fin n → ℝ) i ↦ c⁻¹ * x i) ⁻¹' s) =
      ENNReal.ofReal (c ^ n) * volume s := by
  let M := Matrix.diagonal (fun _ : Fin n ↦ c⁻¹)
  have hdet : Matrix.det M = (c⁻¹) ^ n := by simp [M]
  have hm : Matrix.det M ≠ 0 := by rw [hdet]; positivity
  have h := Real.map_matrix_volume_pi_eq_smul_volume_pi hm
  have heq : ⇑(Matrix.toLin' M) = fun x i ↦ c⁻¹ * x i := by
    funext x i
    simp [M, Matrix.diagonal_toLin', LinearMap.smul_apply]
  rw [heq, hdet, ← inv_pow, inv_inv, abs_of_nonneg (by positivity)] at h
  rw [← smul_eq_mul, ← Measure.smul_apply, ← h, Measure.map_apply (by fun_prop) hs]

theorem spouseRadialLaw_Iic {n : ℕ} (hn : 0 < n) (u : ℝ) :
    spouseRadialLaw n (Iic u) = ENNReal.ofReal ((max u 0) ^ n / (n.factorial : ℝ)) := by
  rw [spouseRadialLaw, withDensity_apply _ measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic]
  have heq : Iic u ∩ Ioi (0 : ℝ) = Ioc 0 u := by ext; simp [and_comm]
  rw [heq]
  by_cases hu : 0 < u
  · rw [max_eq_left hu.le]
    let f : ℝ → ℝ := fun s ↦ s ^ (n - 1) / ((n - 1).factorial : ℝ)
    have hf : Continuous f := by fun_prop
    change (∫⁻ s in Ioc 0 u, ENNReal.ofReal (f s)) = _
    rw [← ofReal_integral_eq_lintegral_ofReal (hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self)]
    · rw [← intervalIntegral.integral_of_le hu.le]
      congr 1
      unfold f
      have hpred : n - 1 + 1 = n := Nat.sub_add_cancel hn
      rw [intervalIntegral.integral_div, integral_pow, hpred, zero_pow hn.ne', sub_zero]
      have hfac : n.factorial = n * (n - 1).factorial := by
        nth_rw 1 [← hpred]
        rw [Nat.factorial_succ, hpred]
      rw [hfac, Nat.cast_mul, div_div]
      have hcast : ((n - 1 : ℕ) : ℝ) + 1 = n := by exact_mod_cast hpred
      rw [hcast]
    · exact (ae_restrict_mem measurableSet_Ioc).mono fun s hs ↦ by
        exact div_nonneg (pow_nonneg hs.1.le _) (Nat.cast_nonneg _)
  · have hu' : u ≤ 0 := le_of_not_gt hu
    simp [Ioc_eq_empty_of_le hu', max_eq_right hu', zero_pow hn.ne']

private def angularSector (n : ℕ) (u : ℝ) (t : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  scoreSimplex n u ∩ spouseAngle ⁻¹' t

private theorem measurableSet_angularSector {n : ℕ} (u : ℝ) {t : Set (Fin n → ℝ)}
    (ht : MeasurableSet t) : MeasurableSet (angularSector n u t) :=
  (measurableSet_scoreSimplex n u).inter (ht.preimage (measurable_spouseAngle n))

private theorem spouseAngle_scale {n : ℕ} (x : Fin n → ℝ) {c : ℝ} (hc : c ≠ 0) :
    spouseAngle (fun i ↦ c * x i) = spouseAngle x := by
  funext i
  simp only [spouseAngle, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ hc

private theorem volume_angularSector {n : ℕ} (u : ℝ) (hu : 0 < u)
    {t : Set (Fin n → ℝ)} (ht : MeasurableSet t) :
    volume (angularSector n u t) =
      ENNReal.ofReal (u ^ n) * volume (angularSector n 1 t) := by
  rw [← volume_preimage_spouseScale n hu (measurableSet_angularSector 1 ht)]
  congr 1
  ext x
  simp only [angularSector, mem_inter_iff, mem_preimage,
    spouseAngle_scale x (inv_ne_zero hu.ne')]
  have hmul : ∀ z : ℝ, u⁻¹ * z ≤ 1 ↔ z ≤ u := fun z ↦ by
    rw [inv_mul_eq_div, div_le_iff₀ hu, one_mul]
  simp only [scoreSimplex, mem_ofPred_eq, ← Finset.mul_sum, hmul]
  have hsign : ∀ z : ℝ, 0 ≤ u⁻¹ * z ↔ 0 ≤ z := fun z ↦
    (mul_nonneg_iff_of_pos_left (inv_pos.mpr hu))
  simp only [hsign]

private theorem spouseAngularLaw_apply {n : ℕ} {t : Set (Fin n → ℝ)} (ht : MeasurableSet t) :
    spouseAngularLaw n t = (n.factorial : ℝ≥0∞) * volume (angularSector n 1 t) := by
  rw [spouseAngularLaw, Measure.smul_apply, Measure.map_apply (measurable_spouseAngle n) ht,
    Measure.restrict_apply (ht.preimage (measurable_spouseAngle n))]
  simp only [smul_eq_mul, angularSector, inter_comm]

private theorem volume_angularSector_eq_mul {n : ℕ} (hn : 0 < n) (u : ℝ)
    {t : Set (Fin n → ℝ)} (ht : MeasurableSet t) :
    volume (angularSector n u t) = spouseRadialLaw n (Iic u) * spouseAngularLaw n t := by
  rw [spouseRadialLaw_Iic hn, spouseAngularLaw_apply ht]
  by_cases hu : 0 < u
  · rw [max_eq_left hu.le, volume_angularSector u hu ht, ← mul_assoc]
    congr 1
    have hnR' : (0 : ℝ) < n.factorial := by positivity
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
      div_mul_cancel₀ _ hnR'.ne']
  · have hu' : u ≤ 0 := le_of_not_gt hu
    have hsub : angularSector n u t ⊆ scoreSimplex n 0 :=
      fun _ hx ↦ ⟨hx.1.1, hx.1.2.trans hu'⟩
    have h0 : volume (scoreSimplex n 0) = 0 := by
      rw [volume_scoreSimplex n le_rfl, zero_pow hn.ne', zero_div, ENNReal.ofReal_zero]
    simp only [max_eq_right hu', zero_pow hn.ne', zero_div, ENNReal.ofReal_zero, zero_mul]
    exact le_antisymm ((measure_mono hsub).trans_eq h0) zero_le

private def angularRay {n : ℕ} (t : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {x | ∀ i, 0 ≤ x i} ∩ spouseAngle ⁻¹' t

private theorem measure_angularRay_radius {n : ℕ} (hn : 0 < n)
    {t : Set (Fin n → ℝ)} (ht : MeasurableSet t) :
    Measure.map (fun x : Fin n → ℝ ↦ ∑ i, x i) (volume.restrict (angularRay t)) =
      spouseAngularLaw n t • spouseRadialLaw n := by
  let μ := Measure.map (fun x : Fin n → ℝ ↦ ∑ i, x i) (volume.restrict (angularRay t))
  let ν := spouseAngularLaw n t • spouseRadialLaw n
  have hμ (u : ℝ) : μ (Iic u) = volume (angularSector n u t) := by
    change (Measure.map (fun x : Fin n → ℝ ↦ ∑ i, x i)
      (volume.restrict (angularRay t))) (Iic u) = _
    rw [Measure.map_apply (measurable_spouseTotal n) measurableSet_Iic,
      Measure.restrict_apply (measurableSet_Iic.preimage (measurable_spouseTotal n))]
    congr 1
    ext x
    simp only [angularRay, angularSector, scoreSimplex, mem_inter_iff, mem_preimage,
      mem_Iic, mem_ofPred_eq]
    tauto
  have hcdf (u : ℝ) : μ (Iic u) = ν (Iic u) := by
    change μ (Iic u) = (spouseAngularLaw n t • spouseRadialLaw n) (Iic u)
    rw [hμ, volume_angularSector_eq_mul hn u ht, Measure.smul_apply, smul_eq_mul, mul_comm]
  have hfin (u : ℝ) : μ (Iic u) ≠ ∞ := by
    rw [hμ]
    exact ne_top_of_le_ne_top (by rw [volume_scoreSimplex n (le_max_right u 0)]; simp)
      (measure_mono fun x hx ↦ ⟨hx.1.1, hx.1.2.trans (le_max_left u 0)⟩ :
        volume (angularSector n u t) ≤ volume (scoreSimplex n (max u 0)))
  apply Measure.ext_of_Ioc' μ ν
  · intro a b _
    exact ne_top_of_le_ne_top (hfin b) (measure_mono fun _ hx ↦ hx.2)
  · intro a b hab
    have hν (u : ℝ) : ν (Iic u) ≠ ∞ := hcdf u ▸ hfin u
    rw [← show Iic b \ Iic a = Ioc a b by ext x; simp [and_comm],
      measure_sdiff (Iic_subset_Iic.mpr hab.le)
      measurableSet_Iic.nullMeasurableSet (hfin a),
      measure_sdiff (Iic_subset_Iic.mpr hab.le) measurableSet_Iic.nullMeasurableSet (hν a),
      hcdf a, hcdf b]

private theorem measure_map_spouseRadialAngular {n : ℕ} (hn : 0 < n) :
    Measure.map (fun x : Fin n → ℝ ↦ (∑ i, x i, spouseAngle x))
      (volume.restrict {x : Fin n → ℝ | ∀ i, 0 ≤ x i}) =
      (spouseRadialLaw n).prod (spouseAngularLaw n) := by
  symm
  apply Measure.prod_eq
  intro s t hs ht
  have hmeas : Measurable (fun x : Fin n → ℝ ↦ (∑ i, x i, spouseAngle x)) :=
    (measurable_spouseTotal n).prodMk (measurable_spouseAngle n)
  rw [Measure.map_apply hmeas (hs.prod ht), Measure.restrict_apply ((hs.prod ht).preimage hmeas)]
  rw [← mul_comm, ← smul_eq_mul, ← Measure.smul_apply, ← measure_angularRay_radius hn ht,
    Measure.map_apply (measurable_spouseTotal n) hs,
    Measure.restrict_apply (hs.preimage (measurable_spouseTotal n))]
  congr 1
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_prod, mem_ofPred_eq, angularRay]
  tauto

theorem lintegral_spouseRadialAngular {n : ℕ} (hn : 0 < n)
    {f : (Fin n → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, f x ∂(volume.restrict {x | ∀ i, 0 ≤ x i})) =
      ∫⁻ s, ∫⁻ w, f (fun i ↦ s * w i) ∂(spouseAngularLaw n) ∂(spouseRadialLaw n) := by
  let decode : ℝ × (Fin n → ℝ) → (Fin n → ℝ) := fun p i ↦ p.1 * p.2 i
  have hdecode : Measurable decode := by unfold decode; fun_prop
  have hpair : Measurable (fun x : Fin n → ℝ ↦ (∑ i, x i, spouseAngle x)) :=
    (measurable_spouseTotal n).prodMk (measurable_spouseAngle n)
  rw [← lintegral_prod (fun p ↦ f (decode p)) (hf.comp hdecode).aemeasurable,
    ← measure_map_spouseRadialAngular hn]
  change _ = ∫⁻ z, (f ∘ decode) z ∂(Measure.map (fun x : Fin n → ℝ ↦
    (∑ i, x i, spouseAngle x)) (volume.restrict {x | ∀ i, 0 ≤ x i}))
  rw [lintegral_map (hf.comp hdecode) hpair]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (μ := (volume : Measure (Fin n → ℝ)))
    (measurableSet_spouseOrthant n)] with x hx
  congr 1
  funext i
  change x i = (∑ j, x j) * (x i / ∑ j, x j)
  by_cases h : (∑ j, x j) = 0
  · have hle : x i ≤ ∑ j, x j :=
      Finset.single_le_sum (fun j _ ↦ hx j) (Finset.mem_univ i)
    rw [h, zero_mul]
    exact le_antisymm (h ▸ hle) (hx i)
  · field_simp

end LennonPittelFormalization

end

section

open Filter MeasureTheory Set

open scoped ENNReal BigOperators Topology

namespace LennonPittelFormalization

private theorem integrableOn_exp_neg_mul_pow (a : ℕ) :
    IntegrableOn (fun x : ℝ ↦ Real.exp (-x) * x ^ a) (Ioi 0) := by
  refine (Real.GammaIntegral_convergent (show 0 < (a : ℝ) + 1 by positivity)).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x _
  rw [add_sub_cancel_right, Real.rpow_natCast]

private theorem integral_exp_neg_mul_pow (a : ℕ) :
    (∫ x : ℝ in Ioi 0, Real.exp (-x) * x ^ a) = (a.factorial : ℝ) := by
  rw [← Real.Gamma_nat_eq_factorial]
  rw [Real.Gamma_eq_integral (by positivity)]
  simp only [add_sub_cancel_right, Real.rpow_natCast]

private theorem restrict_nonneg_eq_pi (n : ℕ) :
    (volume : Measure (Fin n → ℝ)).restrict {x | ∀ i, 0 ≤ x i} =
      Measure.pi (fun _ : Fin n ↦ (volume : Measure ℝ).restrict (Ioi 0)) := by
  have heq : {x : Fin n → ℝ | ∀ i, 0 ≤ x i} = univ.pi (fun _ ↦ Ici 0) := by
    ext x
    simp [Pi.le_def]
  rw [heq, volume_pi, Measure.restrict_pi_pi]
  simp only [Measure.restrict_congr_set (Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ)))]

private theorem lintegral_exp_monomial {n : ℕ} (a : Fin n → ℕ) :
    (∫⁻ x : Fin n → ℝ, ENNReal.ofReal (Real.exp (-(∑ i, x i)) * ∏ i, x i ^ a i)
      ∂(volume.restrict {x | ∀ i, 0 ≤ x i})) =
      ENNReal.ofReal (∏ i, ((a i).factorial : ℝ)) := by
  simp only [← Finset.sum_neg_distrib, Real.exp_sum, ← Finset.prod_mul_distrib]
  rw [restrict_nonneg_eq_pi, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_fin_nat_prod_eq_prod (fun (i : Fin n) (t : ℝ) ↦ Real.exp (-t) * t ^ a i)]
    simp_rw [integral_exp_neg_mul_pow]
  · exact Integrable.fintype_prod_dep fun i ↦ integrableOn_exp_neg_mul_pow (a i)
  · have hs : MeasurableSet {x : Fin n → ℝ | ∀ i, 0 ≤ x i} := by
      rw [ofPred_forall]
      exact MeasurableSet.iInter fun i ↦ measurableSet_le measurable_const (measurable_pi_apply i)
    rw [← restrict_nonneg_eq_pi]
    filter_upwards [ae_restrict_mem hs] with x hx
    exact Finset.prod_nonneg fun i _ ↦ mul_nonneg (Real.exp_pos _).le (pow_nonneg (hx i) _)

private theorem measurable_exp_monomial (n : ℕ) (a : Fin n → ℕ) :
    Measurable (fun x : Fin n → ℝ ↦
      ENNReal.ofReal (Real.exp (-(∑ i, x i)) * ∏ i, x i ^ a i)) := by
  fun_prop

private theorem lintegral_exp_monomial_radius {n : ℕ} (a : Fin n → ℕ)
    (μ : Measure (Fin n → ℝ))
    (hμ : ∀ᵐ w ∂μ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1) (s : ℝ) (hs : 0 < s) :
    (∫⁻ w, ENNReal.ofReal
      (Real.exp (-(∑ i, s * w i)) * ∏ i, (s * w i) ^ a i) ∂μ) =
      ENNReal.ofReal (Real.exp (-s) * s ^ (∑ i, a i)) *
        (∫⁻ w, ENNReal.ofReal (∏ i, w i ^ a i) ∂μ) := by
  rw [← lintegral_const_mul _ (by fun_prop)]
  apply lintegral_congr_ae
  filter_upwards [hμ] with w hw
  rw [← Finset.mul_sum, hw.2, mul_one, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, mul_assoc]

private theorem lintegral_radial_factor (n k : ℕ) :
    (∫⁻ s in Ioi (0 : ℝ),
      ENNReal.ofReal (s ^ (n - 1) / ((n - 1).factorial : ℝ)) *
        ENNReal.ofReal (Real.exp (-s) * s ^ k)) =
      ENNReal.ofReal (((n - 1 + k).factorial : ℝ) / ((n - 1).factorial : ℝ)) := by
  calc
    _ = ∫⁻ s in Ioi (0 : ℝ),
        ENNReal.ofReal ((Real.exp (-s) * s ^ (n - 1 + k)) /
          ((n - 1).factorial : ℝ)) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      rw [← ENNReal.ofReal_mul (div_nonneg (pow_nonneg hs.le _) (by positivity)), pow_add]
      congr 1
      ring
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal
        ((integrableOn_exp_neg_mul_pow (n - 1 + k)).div_const _)]
      · rw [integral_div, integral_exp_neg_mul_pow]
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        exact div_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg hs.le _)) (by positivity)

private theorem lintegral_angle_monomial_of_radial {n : ℕ} (a : Fin n → ℕ)
    (μ : Measure (Fin n → ℝ)) [SFinite μ]
    (hμ : ∀ᵐ w ∂μ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1)
    (hrad : ∀ {f : (Fin n → ℝ) → ℝ≥0∞}, Measurable f →
      (∫⁻ x, f x ∂(volume.restrict {x | ∀ i, 0 ≤ x i})) =
        ∫⁻ s, ∫⁻ w, f (fun i ↦ s * w i) ∂μ
          ∂((volume.restrict (Ioi (0 : ℝ))).withDensity
            (fun s ↦ ENNReal.ofReal (s ^ (n - 1) / ((n - 1).factorial : ℝ))))) :
    (∫⁻ w, ENNReal.ofReal (∏ i, w i ^ a i) ∂μ) =
      ENNReal.ofReal ((∏ i, ((a i).factorial : ℝ)) * ((n - 1).factorial : ℝ) /
        ((n - 1 + ∑ i, a i).factorial : ℝ)) := by
  let k := ∑ i, a i
  let c := ∫⁻ w, ENNReal.ofReal (∏ i, w i ^ a i) ∂μ
  let f (x : Fin n → ℝ) :=
    ENNReal.ofReal (Real.exp (-(∑ i, x i)) * ∏ i, x i ^ a i)
  let g (s : ℝ) := ENNReal.ofReal (s ^ (n - 1) / ((n - 1).factorial : ℝ))
  let h (s : ℝ) := ENNReal.ofReal (Real.exp (-s) * s ^ k)
  have hF : Measurable (fun (z : ℝ × (Fin n → ℝ)) ↦ f (fun i ↦ z.1 * z.2 i)) := by
    fun_prop
  have hEq := hrad (f := f) (measurable_exp_monomial n a)
  rw [lintegral_exp_monomial a, lintegral_withDensity_eq_lintegral_mul _
    (show Measurable g by fun_prop) (Measurable.lintegral_prod_right hF)] at hEq
  have hInner : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      (∫⁻ w, f (fun i ↦ s * w i) ∂μ) = h s * c := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact lintegral_exp_monomial_radius a μ hμ s hs
  have hMul :
      ENNReal.ofReal (∏ i, ((a i).factorial : ℝ)) =
        ENNReal.ofReal (((n - 1 + k).factorial : ℝ) / ((n - 1).factorial : ℝ)) * c := by
    rw [hEq]
    calc
      _ = ∫⁻ s in Ioi (0 : ℝ), (g s * h s) * c := by
        apply lintegral_congr_ae
        filter_upwards [hInner] with s hs
        rw [Pi.mul_apply, hs, mul_assoc]
      _ = _ := by
        rw [lintegral_mul_const _ (show Measurable (fun s ↦ g s * h s) by fun_prop),
          lintegral_radial_factor]
  have hpos : 0 < (((n - 1 + k).factorial : ℝ) / ((n - 1).factorial : ℝ)) := by
    positivity
  change c = _
  rw [show (∏ i, ((a i).factorial : ℝ)) * ((n - 1).factorial : ℝ) /
      ((n - 1 + ∑ i, a i).factorial : ℝ) =
      (∏ i, ((a i).factorial : ℝ)) /
        (((n - 1 + k).factorial : ℝ) / ((n - 1).factorial : ℝ)) by
      rw [div_div_eq_mul_div],
    ENNReal.ofReal_div_of_pos hpos, ENNReal.eq_div_iff (by positivity) ENNReal.ofReal_ne_top]
  exact hMul.symm

private theorem integral_angle_monomial_of_lintegral {n : ℕ} (μ : Measure (Fin n → ℝ))
    (hμ : ∀ᵐ w ∂μ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1)
    (a : Fin n → ℕ) {r : ℝ} (hr : 0 ≤ r)
    (hm : (∫⁻ w, ENNReal.ofReal (∏ i, w i ^ a i) ∂μ) = ENNReal.ofReal r) :
    (∫ w, ∏ i, w i ^ a i ∂μ) = r := by
  have hn : 0 ≤ᵐ[μ] fun w ↦ ∏ i, w i ^ a i :=
    hμ.mono fun w hw ↦ Finset.prod_nonneg fun i _ ↦ pow_nonneg (hw.1 i) _
  have hi : Integrable (fun w ↦ ∏ i, w i ^ a i) μ :=
    ⟨(show Measurable (fun w : Fin n → ℝ ↦ ∏ i, w i ^ a i) by
      fun_prop).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hn).mpr (hm ▸ ENNReal.ofReal_lt_top)⟩
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg_of_ae hn) hr).mp
    ((ofReal_integral_eq_lintegral_ofReal hi hn).trans hm)

private theorem lintegral_angle_power_of_monomial {n : ℕ} (μ : Measure (Fin n → ℝ))
    (hm : ∀ a : Fin n → ℕ, (∫⁻ w, ENNReal.ofReal (∏ i, w i ^ a i) ∂μ) =
      ENNReal.ofReal ((∏ i, ((a i).factorial : ℝ)) * ((n - 1).factorial : ℝ) /
        ((n - 1 + ∑ i, a i).factorial : ℝ)))
    (i : Fin n) (k : ℕ) :
    (∫⁻ w, ENNReal.ofReal (w i ^ k) ∂μ) =
      ENNReal.ofReal ((k.factorial : ℝ) * ((n - 1).factorial : ℝ) /
        ((n - 1 + k).factorial : ℝ)) := by
  have hPow (w : Fin n → ℝ) : (∏ j, w j ^ (Pi.single i k) j) = w i ^ k := by
    rw [Fintype.prod_eq_single i]
    · simp
    · intro j hj
      simp [Pi.single_eq_of_ne hj]
  have hFact : (∏ j, (((Pi.single i k : Fin n → ℕ) j).factorial : ℝ)) =
      (k.factorial : ℝ) := by
    rw [Fintype.prod_eq_single i]
    · simp
    · intro j hj
      simp [Pi.single_eq_of_ne hj]
  simpa only [hPow, hFact, Finset.sum_pi_single', Finset.mem_univ, ite_true] using
    hm (Pi.single i k)

private theorem factorial_power_quotient_le {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (k.factorial : ℝ) * ((n - 1).factorial : ℝ) / ((n - 1 + k).factorial : ℝ)
      ≤ ((k : ℝ) / n) ^ k := by
  have hn1 : n - 1 + 1 = n := by omega
  have hden : (((n - 1).factorial : ℝ) * (n : ℝ) ^ k) ≤ ((n - 1 + k).factorial : ℝ) := by
    exact_mod_cast (hn1 ▸ Nat.factorial_mul_pow_le_factorial (m := n - 1) (n := k))
  have hfac : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast Nat.factorial_le_pow k
  rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  calc
    _ ≤ (k : ℝ) ^ k * (((n - 1).factorial : ℝ) * (n : ℝ) ^ k) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right hfac (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left hden (by positivity)

private theorem measure_angle_large_coordinate_of_power {n : ℕ} {μ : Measure (Fin n → ℝ)}
    (hn : 0 < n) (i : Fin n) (k : ℕ) {t : ℝ} (ht : 0 < t)
    (hm : (∫⁻ w, ENNReal.ofReal (w i ^ k) ∂μ) =
      ENNReal.ofReal ((k.factorial : ℝ) * ((n - 1).factorial : ℝ) /
        ((n - 1 + k).factorial : ℝ))) :
    μ {w | t < w i} ≤ ENNReal.ofReal (((k : ℝ) / n / t) ^ k) := by
  have hmeas : Measurable (fun w : Fin n → ℝ ↦ ENNReal.ofReal (w i ^ k)) := by fun_prop
  calc
    _ ≤ μ {w | ENNReal.ofReal (t ^ k) ≤ ENNReal.ofReal (w i ^ k)} := by
      apply measure_mono
      intro w hw
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ ht.le hw.le _)
    _ ≤ (∫⁻ w, ENNReal.ofReal (w i ^ k) ∂μ) / ENNReal.ofReal (t ^ k) :=
      meas_ge_le_lintegral_div hmeas.aemeasurable (by positivity) ENNReal.ofReal_ne_top
    _ ≤ _ := by
      rw [hm, div_pow, ENNReal.ofReal_div_of_pos (pow_pos ht _)]
      exact ENNReal.div_le_div_right (ENNReal.ofReal_le_ofReal (factorial_power_quotient_le hn k)) _

private theorem tendsto_measure_angle_max_of_power
    (μ : ∀ n : ℕ, Measure (Fin n → ℝ))
    (hm : ∀ {n}, 0 < n → ∀ (i : Fin n) (k : ℕ),
      (∫⁻ w, ENNReal.ofReal (w i ^ k) ∂(μ n)) =
        ENNReal.ofReal ((k.factorial : ℝ) * ((n - 1).factorial : ℝ) /
          ((n - 1 + k).factorial : ℝ))) :
    Tendsto (fun n ↦ μ n {w | ∃ i, 12 * Real.log n / n < w i}) atTop (𝓝 0) := by
  have hcast : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog := Real.tendsto_log_atTop.comp hcast
  have hbound : ∀ᶠ n : ℕ in atTop,
      μ n {w | ∃ i, 12 * Real.log n / n < w i} ≤ ENNReal.ofReal ((n : ℝ)⁻¹) := by
    filter_upwards [eventually_gt_atTop 0, hlog.eventually_ge_atTop 1] with n hn hl
    change 1 ≤ Real.log (n : ℝ) at hl
    let k : ℕ := ⌈2 * Real.log (n : ℝ)⌉₊
    let t : ℝ := 12 * Real.log (n : ℝ) / n
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hlogpos : 0 < Real.log (n : ℝ) := zero_lt_one.trans_le hl
    have ht : 0 < t := by dsimp [t]; positivity
    have hklo : 2 * Real.log (n : ℝ) ≤ (k : ℝ) := Nat.le_ceil _
    have hkhi : (k : ℝ) ≤ 3 * Real.log (n : ℝ) := by
      have h := Nat.ceil_lt_add_one (show 0 ≤ 2 * Real.log (n : ℝ) by positivity)
      change (k : ℝ) < 2 * Real.log (n : ℝ) + 1 at h
      linarith
    have hratio : (k : ℝ) / n / t ≤ 4⁻¹ := by
      dsimp only [t]
      rw [div_div_eq_mul_div, div_le_iff₀ (by positivity : 0 < 12 * Real.log (n : ℝ))]
      rw [div_mul_cancel₀ _ hnR.ne']
      linarith
    have hpow : ((k : ℝ) / n / t) ^ k ≤ ((n : ℝ) ^ 2)⁻¹ := by
      calc
        _ ≤ (4⁻¹ : ℝ) ^ k := pow_le_pow_left₀ (by positivity) hratio _
        _ ≤ Real.exp (-1) ^ k := by
          apply pow_le_pow_left₀ (by norm_num)
          rw [Real.exp_neg]
          exact inv_anti₀ (Real.exp_pos _) (Real.exp_one_lt_three.le.trans (by norm_num))
        _ = Real.exp (-(k : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
        _ ≤ Real.exp (-(2 * Real.log (n : ℝ))) := Real.exp_le_exp.mpr (neg_le_neg hklo)
        _ = _ := by
          rw [Real.exp_neg, ← Nat.cast_two (R := ℝ), Real.exp_nat_mul, Real.exp_log hnR]
    calc
      _ ≤ ∑ i : Fin n, μ n {w | t < w i} := by
        rw [ofPred_exists]
        exact measure_iUnion_fintype_le _ _
      _ ≤ ∑ _ : Fin n, ENNReal.ofReal (((n : ℝ) ^ 2)⁻¹) :=
        Finset.sum_le_sum fun i _ ↦ (measure_angle_large_coordinate_of_power hn i k ht
          (hm hn i k)).trans (ENNReal.ofReal_le_ofReal hpow)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
  have hzero : Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((n : ℝ)⁻¹)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal
      (tendsto_inv_atTop_zero.comp hcast)
  exact tendsto_const_nhds.squeeze' hzero (Eventually.of_forall fun _ ↦ zero_le) hbound

def pittelTypicalAngles (n : ℕ) (η : ℝ) : Set (Fin n → ℝ) :=
  {w | (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧ (∀ i, w i ≤ 12 * Real.log n / n) ∧
    |(n : ℝ) * (∑ i, w i ^ 2) - 2| ≤ η}

theorem measurableSet_pittelTypicalAngles (n : ℕ) (η : ℝ) :
    MeasurableSet (pittelTypicalAngles n η) := by
  unfold pittelTypicalAngles
  simp only [ofPred_and, ofPred_forall]
  refine (MeasurableSet.iInter fun i ↦ measurableSet_le measurable_const
    (measurable_pi_apply i)).inter ((measurableSet_eq_fun (by fun_prop) measurable_const).inter
    ((MeasurableSet.iInter fun i ↦ measurableSet_le (measurable_pi_apply i)
      measurable_const).inter (measurableSet_le (by fun_prop) measurable_const)))

private theorem pittel_integrable_coord_pow {n : ℕ} {μ : Measure (Fin n → ℝ)}
    [IsFiniteMeasure μ] (hμ : ∀ᵐ w ∂μ, ∀ i, w i ∈ Icc (0 : ℝ) 1)
    (i : Fin n) (k : ℕ) : Integrable (fun w ↦ w i ^ k) μ := by
  refine Integrable.of_bound ((continuous_apply i).pow k).aestronglyMeasurable
    1 (hμ.mono fun w hw ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hw i).1 k)]
  exact pow_le_one₀ (hw i).1 (hw i).2

private theorem pittel_integrable_coord_sq_mul_sq {n : ℕ} {μ : Measure (Fin n → ℝ)}
    [IsFiniteMeasure μ] (hμ : ∀ᵐ w ∂μ, ∀ i, w i ∈ Icc (0 : ℝ) 1)
    (i j : Fin n) : Integrable (fun w ↦ w i ^ 2 * w j ^ 2) μ := by
  refine Integrable.of_bound (by fun_prop) 1 (hμ.mono fun w hw ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simpa only [one_mul] using mul_le_mul (pow_le_one₀ (hw i).1 (hw i).2)
    (pow_le_one₀ (hw j).1 (hw j).2) (sq_nonneg (w j)) (zero_le_one : (0 : ℝ) ≤ 1)

private theorem pittel_prod_coord_pow_single {n : ℕ} (w : Fin n → ℝ) (i : Fin n) (k : ℕ) :
    (∏ j, w j ^ Pi.single i k j) = w i ^ k := by
  rw [Finset.prod_eq_single i (fun j _ hj ↦ by simp [Pi.single_eq_of_ne hj])
    (fun hi ↦ (hi (Finset.mem_univ i)).elim), Pi.single_eq_same]

private theorem pittel_prod_factorial_single {n : ℕ} (i : Fin n) (k : ℕ) :
    (∏ j, (Nat.factorial ((Pi.single i k : Fin n → ℕ) j) : ℝ)) = (k.factorial : ℝ) := by
  rw [Finset.prod_eq_single i (fun j _ hj ↦ by simp [Pi.single_eq_of_ne hj])
    (fun hi ↦ (hi (Finset.mem_univ i)).elim), Pi.single_eq_same]

private theorem pittel_prod_factorial_two {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    (∏ l, (Nat.factorial ((Pi.single i 2 + Pi.single j 2 : Fin n → ℕ) l) : ℝ)) = 4 := by
  have hpoint (l : Fin n) :
      Nat.factorial ((Pi.single i 2 + Pi.single j 2 : Fin n → ℕ) l) =
        Nat.factorial ((Pi.single i 2 : Fin n → ℕ) l) *
          Nat.factorial ((Pi.single j 2 : Fin n → ℕ) l) := by
    by_cases hi : l = i
    · subst l
      simp [Pi.single_eq_of_ne hij]
    · simp [Pi.single_eq_of_ne hi]
  simp_rw [hpoint, Nat.cast_mul, Finset.prod_mul_distrib, pittel_prod_factorial_single]
  norm_num [Nat.factorial]

private theorem pittel_factorial_add_two {n : ℕ} (hn : 0 < n) :
    ((n - 1 + 2).factorial : ℝ) = (n - 1).factorial * n * ((n : ℝ) + 1) := by
  have hsplit : n - 1 + 2 = (n - 1 + 1) + 1 := by omega
  rw [hsplit, Nat.factorial_succ, Nat.factorial_succ, show n - 1 + 1 = n by omega]
  push_cast
  ring

private theorem pittel_factorial_add_four {n : ℕ} (hn : 0 < n) :
    ((n - 1 + 4).factorial : ℝ) =
      (n - 1).factorial * n * ((n : ℝ) + 1) * (n + 2) * (n + 3) := by
  have hsplit : n - 1 + 4 = (n - 1 + 2 + 1) + 1 := by omega
  rw [hsplit, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  rw [pittel_factorial_add_two hn, Nat.cast_sub (show 1 ≤ n by omega)]
  push_cast
  ring

noncomputable def pittelAngularSquareScore {n : ℕ} (w : Fin n → ℝ) : ℝ :=
  (n : ℝ) * ∑ i, w i ^ 2

section Moments

variable {n : ℕ} {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ]

variable (hμ : ∀ᵐ w ∂μ, ∀ i, w i ∈ Icc (0 : ℝ) 1)

variable (hmoment : ∀ a : Fin n → ℕ, (∫ w, ∏ i, w i ^ a i ∂μ) =
  (∏ i, ((a i).factorial : ℝ)) * ((n - 1).factorial : ℝ) /
    ((n - 1 + ∑ i, a i).factorial : ℝ))

include hmoment in
omit [IsProbabilityMeasure μ] in

private theorem pittel_integral_coord_pow (i : Fin n) (k : ℕ) :
    (∫ w, w i ^ k ∂μ) =
      (k.factorial : ℝ) * ((n - 1).factorial : ℝ) / ((n - 1 + k).factorial : ℝ) := by
  simpa [pittel_prod_coord_pow_single, pittel_prod_factorial_single, Finset.sum_pi_single'] using
    hmoment (Pi.single i k)

include hmoment in
omit [IsProbabilityMeasure μ] in

private theorem pittel_integral_coord_sq_mul_sq (i j : Fin n) (hij : i ≠ j) :
    (∫ w, w i ^ 2 * w j ^ 2 ∂μ) =
      (4 : ℝ) * ((n - 1).factorial : ℝ) / ((n - 1 + 4).factorial : ℝ) := by
  have h := hmoment (Pi.single i 2 + Pi.single j 2)
  rw [pittel_prod_factorial_two i j hij] at h
  simpa [Pi.add_apply, pow_add, Finset.prod_mul_distrib, pittel_prod_coord_pow_single,
    Finset.sum_add_distrib, Finset.sum_pi_single'] using h

include hμ hmoment in

private theorem pittel_integral_squareScore (hn : 0 < n) :
    (∫ w, pittelAngularSquareScore w ∂μ) = 2 * (n : ℝ) / ((n : ℝ) + 1) := by
  have hf : (0 : ℝ) < (n - 1).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  simp only [pittelAngularSquareScore]
  rw [integral_const_mul,
    integral_finsetSum _ (fun i _ ↦ pittel_integrable_coord_pow hμ i 2)]
  simp_rw [pittel_integral_coord_pow hmoment, pittel_factorial_add_two hn]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num [Nat.factorial]
  field_simp

include hμ hmoment in

private theorem pittel_integral_squareScore_sq (hn : 0 < n) :
    (∫ w, pittelAngularSquareScore w ^ 2 ∂μ) =
      4 * (n : ℝ) ^ 2 * ((n : ℝ) + 5) /
        (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
  classical
  have hf : (0 : ℝ) < (n - 1).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hprod (i : Fin n) :
      (∑ j, ∫ w, w i ^ 2 * w j ^ 2 ∂μ) =
        ((n - 1 : ℕ) : ℝ) * (4 * ((n - 1).factorial : ℝ) / ((n - 1 + 4).factorial : ℝ)) +
          24 * ((n - 1).factorial : ℝ) / ((n - 1 + 4).factorial : ℝ) := by
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i)]
    congr 1
    · have hcard : (Finset.univ.erase i).card = n - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      calc
        _ = ∑ _ ∈ Finset.univ.erase i,
            (4 : ℝ) * ((n - 1).factorial : ℝ) / ((n - 1 + 4).factorial : ℝ) :=
          Finset.sum_congr rfl fun j hj ↦ pittel_integral_coord_sq_mul_sq hmoment i j
            (Finset.ne_of_mem_erase hj).symm
        _ = _ := by rw [Finset.sum_const, hcard, nsmul_eq_mul]
    · simp_rw [← pow_add]
      norm_num [pittel_integral_coord_pow hmoment i 4, Nat.factorial]
  simp_rw [pittelAngularSquareScore, mul_pow, sq (∑ i : Fin n, _), Finset.sum_mul_sum]
  rw [integral_const_mul, integral_finsetSum _ (fun i _ ↦
      integrable_finsetSum _ fun j _ ↦ pittel_integrable_coord_sq_mul_sq hμ i j)]
  simp_rw [integral_finsetSum _ (fun j _ ↦ pittel_integrable_coord_sq_mul_sq hμ _ j), hprod,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    pittel_factorial_add_four hn, Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
  field_simp
  ring

include hμ in

private theorem pittel_integrable_squareScore :
    Integrable (fun w ↦ pittelAngularSquareScore w) μ := by
  unfold pittelAngularSquareScore
  exact (integrable_finsetSum _ fun i _ ↦ pittel_integrable_coord_pow hμ i 2).const_mul _

include hμ in

private theorem pittel_integrable_squareScore_sq :
    Integrable (fun w ↦ pittelAngularSquareScore w ^ 2) μ := by
  simp_rw [pittelAngularSquareScore, mul_pow, sq (∑ i : Fin n, _), Finset.sum_mul_sum]
  exact (integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
    pittel_integrable_coord_sq_mul_sq hμ i j).const_mul _

include hμ in

private theorem pittel_integrable_squareScore_deviation :
    Integrable (fun w ↦ (pittelAngularSquareScore w - 2) ^ 2) μ := by
  have heq : (fun w : Fin n → ℝ ↦ (pittelAngularSquareScore w - 2) ^ 2) =
      fun w ↦ pittelAngularSquareScore w ^ 2 - 4 * pittelAngularSquareScore w + 4 := by
    funext w
    ring
  rw [heq]
  exact ((pittel_integrable_squareScore_sq hμ).sub
    ((pittel_integrable_squareScore hμ).const_mul _)).add (integrable_const _)

include hμ hmoment in

private theorem pittel_integral_squareScore_deviation (hn : 0 < n) :
    (∫ w, (pittelAngularSquareScore w - 2) ^ 2 ∂μ) =
      4 * ((n : ℝ) ^ 2 - (n : ℝ) + 6) /
        (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
  have heq (w : Fin n → ℝ) : (pittelAngularSquareScore w - 2) ^ 2 =
      pittelAngularSquareScore w ^ 2 - 4 * pittelAngularSquareScore w + 4 := by ring
  have hlin : Integrable (fun w : Fin n → ℝ ↦ 4 * pittelAngularSquareScore w) μ :=
    (pittel_integrable_squareScore hμ).const_mul _
  have hsub : Integrable (fun w : Fin n → ℝ ↦
      pittelAngularSquareScore w ^ 2 - 4 * pittelAngularSquareScore w) μ :=
    (pittel_integrable_squareScore_sq hμ).sub hlin
  simp_rw [heq]
  rw [integral_add hsub (integrable_const (4 : ℝ)),
    integral_sub (pittel_integrable_squareScore_sq hμ) hlin,
    integral_const_mul, integral_const, probReal_univ, one_smul,
    pittel_integral_squareScore_sq hμ hmoment hn, pittel_integral_squareScore hμ hmoment hn]
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  field_simp
  ring

include hμ hmoment in

private theorem pittel_angular_measure_deviation_le (hn : 0 < n) {η : ℝ} (hη : 0 < η) :
    μ {w | η < |pittelAngularSquareScore w - 2|} ≤ ENNReal.ofReal (28 / (η ^ 2 * n)) := by
  let f (w : Fin n → ℝ) : ℝ := (pittelAngularSquareScore w - 2) ^ 2
  have hf : Measurable (fun w ↦ ENNReal.ofReal (f w)) := by
    dsimp [f, pittelAngularSquareScore]
    fun_prop
  have hηsq : 0 < η ^ 2 := by positivity
  have hmark := meas_ge_le_lintegral_div (μ := μ) hf.aemeasurable
    (ε := ENNReal.ofReal (η ^ 2)) (by positivity) ENNReal.ofReal_ne_top
  have hinc : {w | η < |pittelAngularSquareScore w - 2|} ⊆
      {w | ENNReal.ofReal (η ^ 2) ≤ ENNReal.ofReal (f w)} := by
    intro w hw
    apply ENNReal.ofReal_le_ofReal
    dsimp [f]
    rw [← sq_abs (pittelAngularSquareScore w - 2)]
    exact (sq_le_sq₀ hη.le (abs_nonneg _)).mpr (le_of_lt hw)
  refine (measure_mono hinc).trans (hmark.trans ?_)
  rw [← ofReal_integral_eq_lintegral_ofReal (pittel_integrable_squareScore_deviation hμ)
      (Eventually.of_forall fun w ↦ sq_nonneg (pittelAngularSquareScore w - 2)),
    ← ENNReal.ofReal_div_of_pos hηsq, pittel_integral_squareScore_deviation hμ hmoment hn]
  apply ENNReal.ofReal_le_ofReal
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnum : 4 * ((n : ℝ) ^ 2 - (n : ℝ) + 6) ≤ 28 * (n : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
  have hden : (n : ℝ) ^ 3 ≤ ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) := by
    nlinarith [sq_nonneg (n : ℝ)]
  calc
    _ ≤ (28 * (n : ℝ) ^ 2 / (n : ℝ) ^ 3) / η ^ 2 := by
      exact div_le_div_of_nonneg_right (div_le_div₀ (by positivity) hnum (by positivity) hden)
        hηsq.le
    _ = _ := by field_simp

end Moments

theorem tendsto_pittel_angular_measure_deviation_zero
    (μ : ∀ n : ℕ, Measure (Fin n → ℝ))
    (hprob : ∀ n > 0, IsProbabilityMeasure (μ n))
    (hsupp : ∀ n > 0, ∀ᵐ w ∂(μ n), ∀ i, w i ∈ Icc (0 : ℝ) 1)
    (hmom : ∀ n > 0, ∀ a : Fin n → ℕ, (∫ w, ∏ i, w i ^ a i ∂(μ n)) =
      (∏ i, ((a i).factorial : ℝ)) * ((n - 1).factorial : ℝ) /
        ((n - 1 + ∑ i, a i).factorial : ℝ))
    {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n ↦ μ n {w | η < |pittelAngularSquareScore w - 2|}) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((28 / η ^ 2) / (n : ℝ)))
      atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (tendsto_const_div_atTop_nhds_zero_nat (28 / η ^ 2))
  refine tendsto_const_nhds.squeeze' ht (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  let := hprob n hn
  rw [div_div]
  exact pittel_angular_measure_deviation_le (hsupp n hn) (hmom n hn) hn hη

theorem lintegral_spouseAngularLaw_monomial {n : ℕ} (hn : 0 < n) (a : Fin n → ℕ) :
    (∫⁻ w, ENNReal.ofReal (∏ i, w i ^ a i) ∂(spouseAngularLaw n)) =
      ENNReal.ofReal ((∏ i, ((a i).factorial : ℝ)) * ((n - 1).factorial : ℝ) /
        ((n - 1 + ∑ i, a i).factorial : ℝ)) :=
  lintegral_angle_monomial_of_radial a (spouseAngularLaw n) (ae_spouseAngularLaw hn)
    (lintegral_spouseRadialAngular hn)

theorem integral_spouseAngularLaw_monomial {n : ℕ} (hn : 0 < n) (a : Fin n → ℕ) :
    (∫ w, ∏ i, w i ^ a i ∂(spouseAngularLaw n)) =
      (∏ i, ((a i).factorial : ℝ)) * ((n - 1).factorial : ℝ) /
        ((n - 1 + ∑ i, a i).factorial : ℝ) :=
  integral_angle_monomial_of_lintegral _ (ae_spouseAngularLaw hn) a (by positivity)
    (lintegral_spouseAngularLaw_monomial hn a)

theorem tendsto_measure_compl_pittelTypicalAngles_zero {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n : ℕ ↦ spouseAngularLaw n (pittelTypicalAngles n η)ᶜ) atTop (𝓝 0) := by
  have hmax := tendsto_measure_angle_max_of_power spouseAngularLaw fun hn i k ↦
    lintegral_angle_power_of_monomial _ (lintegral_spouseAngularLaw_monomial hn) i k
  have hsupp (n : ℕ) (hn : 0 < n) :
      ∀ᵐ w ∂(spouseAngularLaw n), ∀ i, w i ∈ Icc (0 : ℝ) 1 :=
    (ae_spouseAngularLaw hn).mono fun w hw i ↦
      ⟨hw.1 i, hw.2 ▸ Finset.single_le_sum (f := w) (fun j _ ↦ hw.1 j) (Finset.mem_univ i)⟩
  have hsq := tendsto_pittel_angular_measure_deviation_zero spouseAngularLaw
    (fun _ _ ↦ inferInstance) hsupp (fun _ hn a ↦ integral_spouseAngularLaw_monomial hn a) hη
  have hsum := hmax.add hsq
  simp only [add_zero] at hsum
  refine tendsto_const_nhds.squeeze' hsum (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  let B : Set (Fin n → ℝ) := {w | ∃ i, 12 * Real.log n / n < w i}
  let C : Set (Fin n → ℝ) := {w | η < |pittelAngularSquareScore w - 2|}
  let D : Set (Fin n → ℝ) := B ∪ C
  have hsub : (pittelTypicalAngles n η)ᶜ ≤ᵐ[spouseAngularLaw n] D := by
    filter_upwards [ae_spouseAngularLaw hn] with w hw
    intro hbad
    by_cases hB : w ∈ B
    · exact Or.inl hB
    · apply Or.inr
      change η < |pittelAngularSquareScore w - 2|
      apply lt_of_not_ge
      intro hC
      apply hbad
      refine ⟨hw.1, hw.2, fun i ↦ le_of_not_gt (fun hi ↦ hB ⟨i, hi⟩), hC⟩
  exact (measure_mono_ae hsub).trans (measure_union_le B C)

theorem tendsto_probReal_compl_pittelTypicalAngles_zero {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n : ℕ ↦ (spouseAngularLaw n).real (pittelTypicalAngles n η)ᶜ)
      atTop (𝓝 0) := by
  simpa only [measureReal_def, ENNReal.toReal_zero, Function.comp_def] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (tendsto_measure_compl_pittelTypicalAngles_zero hη)

theorem tendsto_probReal_pittelTypicalAngles_one {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n : ℕ ↦ (spouseAngularLaw n).real (pittelTypicalAngles n η))
      atTop (𝓝 1) := by
  have ht := tendsto_const_nhds.sub (tendsto_probReal_compl_pittelTypicalAngles_zero hη)
      (a := (1 : ℝ))
  simp only [sub_zero] at ht
  refine ht.congr fun n ↦ ?_
  rw [probReal_compl_eq_one_sub (measurableSet_pittelTypicalAngles n η)]
  ring

end LennonPittelFormalization

end

section

open Filter MeasureTheory Set StableMarriage

open scoped BigOperators ENNReal Topology

namespace LennonPittelFormalization

private theorem pittelRowMass_scale {ι : Type*} (I : Finset ι) (w : ι → ℝ) {s : ℝ}
    (hs : 0 < s) :
    scoreRowMass I (fun j ↦ s * w j) 0 1 = s⁻¹ * scoreRowMass I w 0 s := by
  unfold scoreRowMass
  convert intervalIntegral.integral_comp_mul_right (a := (0 : ℝ)) (b := 1)
    (scoreRowKernel I w) hs.ne' using 1
  · congr 1
    funext t
    unfold scoreRowKernel
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    ring
  · simp

private theorem pittel_eventual_log_ge (C : ℝ) :
    ∀ᶠ n : ℕ in atTop, C ≤ Real.log n :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop C

private theorem pittel_bulk_bounds {n : ℕ} (hn : 1 < n) (hlog : 12 ≤ Real.log n)
    {s : ℝ} (hs : 0 ≤ s) (hu : s ≤ (n : ℝ) / (Real.log n) ^ 2)
    {w : Fin n → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hmax : ∀ i, w i ≤ 12 * Real.log n / n) :
    ∀ i, s * w i ∈ Icc (0 : ℝ) 1 := by
  intro i
  refine ⟨mul_nonneg hs (hw i), ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hl : 0 < Real.log n := by linarith
  calc
    s * w i ≤ ((n : ℝ) / (Real.log n) ^ 2) * (12 * Real.log n / n) :=
      mul_le_mul hu (hmax i) (hw i) (by positivity)
    _ = 12 / Real.log n := by field_simp
    _ ≤ 1 := (div_le_one hl).2 hlog

private theorem pittel_eventual_bulk_bounds :
    ∀ᶠ n : ℕ in atTop, ∀ {s : ℝ}, 0 ≤ s → s ≤ (n : ℝ) / (Real.log n)^2 →
      ∀ {w : Fin n → ℝ}, (∀ i, 0 ≤ w i) →
        (∀ i, w i ≤ 12 * Real.log n / n) → ∀ i, s * w i ∈ Icc (0 : ℝ) 1 := by
  filter_upwards [eventually_gt_atTop (1 : ℕ), pittel_eventual_log_ge 12] with n hn hlog
  exact pittel_bulk_bounds hn hlog

private theorem pittel_lintegral_radial_weight {n : ℕ} (hn : 0 < n)
    {l u C : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hC : 0 ≤ C) :
    (n.factorial : ℝ≥0∞) *
        (∫⁻ s in Ioc l u, ENNReal.ofReal (C / s ^ n)
          ∂spouseRadialLaw n) =
      ENNReal.ofReal ((n : ℝ) * C * Real.log (u / l)) := by
  have hd : Measurable (fun s : ℝ ↦
      ENNReal.ofReal (s ^ (n - 1) / ((n - 1).factorial : ℝ))) := by fun_prop
  have hg : Measurable (fun s : ℝ ↦ ENNReal.ofReal (C / s ^ n)) := by fun_prop
  rw [spouseRadialLaw, setLIntegral_withDensity_eq_setLIntegral_mul _ hd hg measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr (show Ioc l u ⊆ Ioi 0 from fun s hs ↦ hl.trans hs.1),
    ← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top n.factorial)]
  calc
    _ = ∫⁻ s in Ioc l u, ENNReal.ofReal ((n : ℝ) * C) * ENNReal.ofReal s⁻¹ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc : MeasurableSet (Ioc l u))]
        with s hs
      have hs' : 0 < s := hl.trans hs.1
      have hf : ((n - 1).factorial : ℝ) ≠ 0 := by positivity
      have hnat := Nat.factorial_succ (n - 1)
      rw [show n - 1 + 1 = n by omega] at hnat
      have hnfac : (n.factorial : ℝ) = (n : ℝ) * ((n - 1).factorial : ℝ) := by
        exact_mod_cast hnat
      change (n.factorial : ℝ≥0∞) *
          (ENNReal.ofReal (s ^ (n - 1) / ((n - 1).factorial : ℝ)) *
            ENNReal.ofReal (C / s ^ n)) =
        ENNReal.ofReal ((n : ℝ) * C) * ENNReal.ofReal s⁻¹
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), hnfac]
      congr 1
      rw [← show n - 1 + 1 = n by omega, pow_succ s (n - 1)]
      field_simp
      simp [mul_comm]
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_Ioc_inv_of_pos hl hlu,
        ← ENNReal.ofReal_mul (by positivity)]

private noncomputable def pittelWindowMass (n : ℕ) (A : Set ℝ) : ℝ≥0∞ :=
  (n.factorial : ℝ≥0∞) * ∫⁻ y in {y | spouseVectorTotal y ∈ A}, pittelDensity n y


private theorem pittelTotal_scale {n : ℕ} {w : Fin n → ℝ} (hw : ∑ i, w i = 1) (s : ℝ) :
    spouseVectorTotal (fun i ↦ s * w i) = s := by
  simp only [spouseVectorTotal, ← Finset.mul_sum, hw, mul_one]

private theorem pittelWindowMass_le_mean (n : ℕ) (A : Set ℝ) :
    pittelWindowMass n A ≤ ENNReal.ofReal (expectedNumStableMatchings n) := by
  rw [ofReal_expectedNumStableMatchings_eq_pittelDensity, pittelWindowMass]
  exact mul_le_mul_right (lintegral_mono' Measure.restrict_le_self le_rfl) _

private theorem pittelMean_eq_small_add_bulk (n : ℕ) (L : ℝ) :
    ENNReal.ofReal (expectedNumStableMatchings n) =
      pittelWindowMass n (Iic L) + pittelWindowMass n (Ioc L (n : ℝ)) := by
  have ha : MeasurableSet {y : Fin n → ℝ | spouseVectorTotal y ∈ Iic L} :=
    measurableSet_Iic.preimage (measurable_pittelTotal n)
  have hb : MeasurableSet {y : Fin n → ℝ | spouseVectorTotal y ∈ Ioc L (n : ℝ)} :=
    measurableSet_Ioc.preimage (measurable_pittelTotal n)
  rw [ofReal_expectedNumStableMatchings_eq_pittelDensity, ← lintegral_add_compl _ ha,
    mul_add, pittelWindowMass, pittelWindowMass]
  congr 2
  rw [← lintegral_indicator ha.compl, ← lintegral_indicator hb]
  apply lintegral_congr
  intro y
  by_cases hy : y ∈ pittelScoreCube n
  · have hle : spouseVectorTotal y ≤ (n : ℝ) := by
      calc
        spouseVectorTotal y ≤ ∑ _i : Fin n, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ ↦ (hy i (mem_univ i)).2
        _ = _ := by simp
    have heq : y ∈ {y : Fin n → ℝ | spouseVectorTotal y ∈ Iic L}ᶜ ↔
        y ∈ {y : Fin n → ℝ | spouseVectorTotal y ∈ Ioc L (n : ℝ)} := by
      simp [not_le, hle]
    by_cases h : y ∈ {y : Fin n → ℝ | spouseVectorTotal y ∈ Iic L}ᶜ
    · rw [indicator_of_mem h, indicator_of_mem (heq.mp h)]
    · rw [indicator_of_notMem h, indicator_of_notMem (heq.not.mp h)]
  · have hz : pittelDensity n y = 0 := indicator_of_notMem hy _
    simp only [Set.indicator_apply, hz, ite_self]

private theorem pittelDensity_scale {n : ℕ} {s : ℝ} (hs : 0 < s) {w : Fin n → ℝ}
    (hy : ∀ j, s * w j ∈ Icc (0 : ℝ) 1) :
    pittelDensity n (fun j ↦ s * w j) =
      ENNReal.ofReal ((∏ i : Fin n, scoreRowMass (Finset.univ.erase i) w 0 s) / s ^ n) := by
  rw [pittelDensity_eq_ofReal_prod hy]
  simp_rw [pittelRowMass_scale _ _ hs]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    inv_pow, div_eq_inv_mul]

private theorem pittel_angular_integral_le {n : ℕ} (ν : Measure (Fin n → ℝ))
    [IsProbabilityMeasure ν] {B : Set (Fin n → ℝ)} (hB : MeasurableSet B) {s C : ℝ}
    (hs : 2 ≤ s) (hC : 0 ≤ C)
    (hν : ∀ᵐ w ∂ν, ∑ i, w i = 1)
    (hrow : ∀ w ∈ B, (∀ j, s * w j ∈ Icc (0 : ℝ) 1) →
      (∏ i : Fin n, scoreRowMass (Finset.univ.erase i) w 0 s) ≤ C) :
    (∫⁻ w, pittelDensity n (fun j ↦ s * w j) ∂ν) ≤
      ENNReal.ofReal ((C + Real.exp 2 * (ν Bᶜ).toReal) / s ^ n) := by
  have hp : 0 < s := by linarith
  have hpow : 0 < s ^ n := pow_pos hp _
  rw [← lintegral_add_compl _ hB]
  have h₁ : (∫⁻ w in B, pittelDensity n (fun j ↦ s * w j) ∂ν) ≤
      ENNReal.ofReal (C / s ^ n) := by
    calc
      _ ≤ ∫⁻ _w in B, ENNReal.ofReal (C / s ^ n) ∂ν := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (μ := ν) hB] with w hw
        by_cases hy : (fun j ↦ s * w j) ∈ pittelScoreCube n
        · have hc (j : Fin n) : s * w j ∈ Icc (0 : ℝ) 1 := hy j (mem_univ _)
          rw [pittelDensity_scale hp hc]
          exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hrow w hw hc) hpow.le)
        · simp [pittelDensity, indicator_of_notMem hy]
      _ = ENNReal.ofReal (C / s ^ n) * ν B := setLIntegral_const _ _
      _ ≤ _ := mul_le_of_le_one_right' (prob_le_one (μ := ν))
  have h₂ : (∫⁻ w in Bᶜ, pittelDensity n (fun j ↦ s * w j) ∂ν) ≤
      ENNReal.ofReal (Real.exp 2 / s ^ n) * ν Bᶜ := by
    rw [← setLIntegral_const]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_of_ae hν] with w hw
    have ht := pittelTotal_scale hw s
    have htotal : 2 ≤ spouseVectorTotal (fun j ↦ s * w j) := by rwa [ht]
    simpa only [ht] using pittelDensity_le_inv_pow htotal
  calc
    _ ≤ ENNReal.ofReal (C / s ^ n) + ENNReal.ofReal (Real.exp 2 / s ^ n) * ν Bᶜ :=
      add_le_add h₁ h₂
    _ = _ := by
      conv_lhs =>
        rw [← ENNReal.ofReal_toReal (measure_ne_top ν Bᶜ),
          ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

private theorem pittel_angular_integral_ge {n : ℕ} (ν : Measure (Fin n → ℝ))
    [IsProbabilityMeasure ν] {B : Set (Fin n → ℝ)} (hB : MeasurableSet B) {s C : ℝ}
    (hs : 0 < s) (hC : 0 ≤ C)
    (hrow : ∀ w ∈ B, (∀ j, s * w j ∈ Icc (0 : ℝ) 1) ∧
      C ≤ (∏ i : Fin n, scoreRowMass (Finset.univ.erase i) w 0 s)) :
    ENNReal.ofReal ((C * (ν B).toReal) / s ^ n) ≤
      ∫⁻ w, pittelDensity n (fun j ↦ s * w j) ∂ν := by
  calc
    _ = ENNReal.ofReal (C / s ^ n) * ν B := by
      conv_rhs => rw [← ENNReal.ofReal_toReal (measure_ne_top ν B),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    _ = ∫⁻ _w in B, ENNReal.ofReal (C / s ^ n) ∂ν := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ w in B, pittelDensity n (fun j ↦ s * w j) ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (μ := ν) hB] with w hw
      obtain ⟨hc, hq⟩ := hrow w hw
      rw [pittelDensity_scale hs hc]
      exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hq (by positivity))
    _ ≤ _ := lintegral_mono' Measure.restrict_le_self le_rfl

private theorem pittelWindowMass_eq_radial {n : ℕ} (hn : 0 < n) {A : Set ℝ}
    (hA : MeasurableSet A) :
    pittelWindowMass n A =
      (n.factorial : ℝ≥0∞) *
        ∫⁻ s in A, ∫⁻ w, pittelDensity n (fun i ↦ s * w i) ∂spouseAngularLaw n
          ∂spouseRadialLaw n := by
  let B : Set (Fin n → ℝ) := {y | spouseVectorTotal y ∈ A}
  let Q : Set (Fin n → ℝ) := {y | ∀ i, 0 ≤ y i}
  have hB : MeasurableSet B := hA.preimage (measurable_pittelTotal n)
  have hQ : MeasurableSet Q := by
    change MeasurableSet {y : Fin n → ℝ | ∀ i, 0 ≤ y i}
    rw [ofPred_forall]
    exact MeasurableSet.iInter fun i ↦
      measurableSet_le measurable_const (measurable_pi_apply i)
  let f := B.indicator (pittelDensity n)
  have hf : Measurable f := (measurable_pittelDensity n).indicator hB
  rw [pittelWindowMass, ← lintegral_indicator hB]
  congr 1
  change (∫⁻ y, f y) = _
  calc
    _ = ∫⁻ y, f y ∂(volume.restrict Q) := by
      rw [← lintegral_indicator hQ]
      apply lintegral_congr
      intro y
      by_cases h : y ∈ Q
      · rw [indicator_of_mem h]
      · have hc : y ∉ pittelScoreCube n := fun hc ↦ h (fun i ↦ (hc i (mem_univ i)).1)
        rw [indicator_of_notMem h]
        have hz : pittelDensity n y = 0 := indicator_of_notMem hc _
        change B.indicator (pittelDensity n) y = 0
        by_cases hy : y ∈ B
        · rw [indicator_of_mem hy, hz]
        · exact indicator_of_notMem hy _
    _ = ∫⁻ s, ∫⁻ w, f (fun i ↦ s * w i) ∂spouseAngularLaw n ∂spouseRadialLaw n :=
      lintegral_spouseRadialAngular hn hf
    _ = _ := by
      rw [← lintegral_indicator hA]
      apply lintegral_congr
      intro s
      by_cases hs : s ∈ A
      · rw [indicator_of_mem hs]
        apply lintegral_congr_ae
        filter_upwards [ae_spouseAngularLaw hn] with w hw
        exact indicator_of_mem (show (fun i ↦ s * w i) ∈ B by
          change spouseVectorTotal (fun i ↦ s * w i) ∈ A
          rwa [pittelTotal_scale hw.2]) _
      · rw [indicator_of_notMem hs, ← lintegral_zero]
        apply lintegral_congr_ae
        filter_upwards [ae_spouseAngularLaw hn] with w hw
        exact indicator_of_notMem (show (fun i ↦ s * w i) ∉ B by
          change spouseVectorTotal (fun i ↦ s * w i) ∉ A
          rwa [pittelTotal_scale hw.2]) _

private theorem pittelWindowMass_le_log {n : ℕ} (hn : 0 < n)
    {l u C : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hC : 0 ≤ C)
    (h : ∀ s ∈ Ioc l u,
      (∫⁻ w, pittelDensity n (fun i ↦ s * w i) ∂spouseAngularLaw n) ≤
        ENNReal.ofReal (C / s ^ n)) :
    pittelWindowMass n (Ioc l u) ≤ ENNReal.ofReal ((n : ℝ) * C * Real.log (u / l)) := by
  rw [pittelWindowMass_eq_radial hn measurableSet_Ioc,
    ← pittel_lintegral_radial_weight hn hl hlu hC]
  apply mul_le_mul_right
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (μ := spouseRadialLaw n) measurableSet_Ioc] with s hs
  exact h s hs

private theorem pittelWindowMass_ge_log {n : ℕ} (hn : 0 < n)
    {l u C : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hC : 0 ≤ C)
    (h : ∀ s ∈ Ioc l u, ENNReal.ofReal (C / s ^ n) ≤
      ∫⁻ w, pittelDensity n (fun i ↦ s * w i) ∂spouseAngularLaw n) :
    ENNReal.ofReal ((n : ℝ) * C * Real.log (u / l)) ≤ pittelWindowMass n (Ioc l u) := by
  rw [pittelWindowMass_eq_radial hn measurableSet_Ioc,
    ← pittel_lintegral_radial_weight hn hl hlu hC]
  apply mul_le_mul_right
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (μ := spouseRadialLaw n) measurableSet_Ioc] with s hs
  exact h s hs

private theorem pittel_ofReal_windowRatio {n : ℕ} (hn : 0 < n) (hl : 0 < Real.log n)
    (C W : ℝ) :
    ENNReal.ofReal ((n : ℝ) * C * W) / ENNReal.ofReal ((n : ℝ) * Real.log n) =
      ENNReal.ofReal (C * (W / Real.log n)) := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← ENNReal.ofReal_div_of_pos (mul_pos hpos hl)]
  congr 1
  field_simp

private noncomputable def pittelNormalizer (n : ℕ) : ℝ := (n : ℝ) * Real.log n

private noncomputable def pittelSmallRatio (n : ℕ) : ℝ≥0∞ :=
  pittelWindowMass n (Iic (pittelRadiusLower n)) / ENNReal.ofReal (pittelNormalizer n)

private theorem pittelSmallRatio_ne_top {n : ℕ} (hn : 1 < n) : pittelSmallRatio n ≠ ⊤ := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have hp : 0 < pittelNormalizer n := mul_pos (by positivity) (Real.log_pos hn')
  unfold pittelSmallRatio
  apply ENNReal.div_ne_top
  · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (pittelWindowMass_le_mean _ _)
  · exact (ENNReal.ofReal_pos.mpr hp).ne'

private theorem tendsto_pittelSmallRatio_toReal :
    Tendsto (fun n ↦ (pittelSmallRatio n).toReal) atTop (𝓝 0) := by
  have h : Tendsto pittelSmallRatio atTop (𝓝 0) := tendsto_pittelSmallMass_ratio_zero
  simpa only [Function.comp_def, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h

private theorem pittelMean_sandwich {ε : ℝ} (hε : 0 < ε) (hε' : ε < (Real.exp 1)⁻¹) :
    ∃ lower upper : ℕ → ℝ,
      Tendsto lower atTop (𝓝 ((Real.exp 1)⁻¹ - ε)) ∧
      Tendsto upper atTop (𝓝 ((Real.exp 1)⁻¹ + ε)) ∧
      ∀ᶠ n in atTop, lower n ≤ expectedNumStableMatchings n / pittelNormalizer n ∧
        expectedNumStableMatchings n / pittelNormalizer n ≤ upper n := by
  obtain ⟨η, hη, hrows⟩ := eventually_pittelRowsProduct_close hε
  let c : ℝ := (Real.exp 1)⁻¹
  let B (n : ℕ) := pittelTypicalAngles n η
  let Clo (n : ℕ) := (c - ε) * (spouseAngularLaw n (B n)).toReal
  let Chi (n : ℕ) := c + ε + Real.exp 2 * (spouseAngularLaw n (B n)ᶜ).toReal
  let Wlo (n : ℕ) := Real.log (pittelRadiusUpper n / pittelRadiusLower n)
  let Whi (n : ℕ) := Real.log ((n : ℝ) / pittelRadiusLower n)
  refine ⟨fun n ↦ Clo n * (Wlo n / Real.log n),
    fun n ↦ (pittelSmallRatio n).toReal + Chi n * (Whi n / Real.log n), ?_, ?_, ?_⟩
  · have hC : Tendsto Clo atTop (𝓝 (c - ε)) := by
      simpa only [Clo, B, measureReal_def, mul_one] using
        (tendsto_probReal_pittelTypicalAngles_one hη).const_mul (c - ε)
    simpa only [Wlo, mul_one] using hC.mul tendsto_log_pittelWindowLower_ratio_one
  · have hC : Tendsto Chi atTop (𝓝 (c + ε)) := by
      simpa only [Chi, B, measureReal_def, mul_zero, add_zero] using
        ((tendsto_probReal_compl_pittelTypicalAngles_zero hη).const_mul
          (Real.exp 2)).const_add (c + ε)
    simpa only [Whi, mul_one, zero_add] using
      tendsto_pittelSmallRatio_toReal.add (hC.mul tendsto_log_pittelWindowUpper_ratio_one)
  filter_upwards [hrows, eventually_gt_atTop (1 : ℕ), eventually_two_le_pittelRadiusLower,
    eventually_pittelRadiusLower_le_upper, eventually_pittelRadiusUpper_le_size,
    pittel_eventual_bulk_bounds] with n hrow hn h2 hLU hUn hbulk
  have hn0 : 0 < n := by omega
  have hl : 0 < pittelRadiusLower n := by linarith
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have hlog := Real.log_pos hn'
  have hnorm : 0 < pittelNormalizer n := mul_pos (by positivity) hlog
  have hB : MeasurableSet (B n) := measurableSet_pittelTypicalAngles n η
  have hClo : 0 ≤ Clo n := mul_nonneg (sub_nonneg.mpr hε'.le) ENNReal.toReal_nonneg
  have hc : 0 < c := inv_pos.mpr (Real.exp_pos _)
  have hChi : 0 ≤ Chi n := by dsimp [Chi]; positivity
  have htotal : ∀ᵐ w ∂spouseAngularLaw n, ∑ i, w i = 1 :=
    (ae_spouseAngularLaw hn0).mono fun _ h ↦ h.2
  have hq (w : Fin n → ℝ) (hw : w ∈ B n) (s : ℝ) (hs : pittelRadiusLower n ≤ s)
      (hy : ∀ j, s * w j ∈ Icc (0 : ℝ) 1) :
      |(∏ i : Fin n, scoreRowMass (Finset.univ.erase i) w 0 s) - c| ≤ ε := by
    exact hrow w s hs hw.1 hw.2.1 hw.2.2.1 hw.2.2.2 (fun j ↦ (hy j).2)
  have hupper :
      pittelWindowMass n (Ioc (pittelRadiusLower n) (n : ℝ)) ≤
        ENNReal.ofReal ((n : ℝ) * Chi n * Whi n) := by
    apply pittelWindowMass_le_log hn0 hl (hLU.trans hUn) hChi
    intro s hs
    apply pittel_angular_integral_le _ hB (h2.trans hs.1.le) (add_nonneg hc.le hε.le) htotal
    intro w hw hy
    have h := (abs_le.mp (hq w hw s hs.1.le hy)).2
    linarith only [h]
  have hlower :
      ENNReal.ofReal ((n : ℝ) * Clo n * Wlo n) ≤
        pittelWindowMass n (Ioc (pittelRadiusLower n) (pittelRadiusUpper n)) := by
    apply pittelWindowMass_ge_log hn0 hl hLU hClo
    intro s hs
    have hs' := hl.trans hs.1
    apply pittel_angular_integral_ge _ hB hs' (sub_nonneg.mpr hε'.le)
    intro w hw
    have hy := hbulk hs'.le hs.2 hw.1 hw.2.2.1
    refine ⟨hy, ?_⟩
    have h := (abs_le.mp (hq w hw s hs.1.le hy)).1
    linarith only [h]
  have hmean : 0 ≤ expectedNumStableMatchings n := integral_nonneg fun _ ↦ Nat.cast_nonneg _
  have hqmean := div_nonneg hmean hnorm.le
  have hhi : 0 ≤ Whi n / Real.log n := by
    apply div_nonneg _ hlog.le
    exact Real.log_nonneg ((one_le_div hl).2 (hLU.trans hUn))
  constructor
  · have hE := ENNReal.div_le_div_right
      (hlower.trans (pittelWindowMass_le_mean _ _)) (ENNReal.ofReal (pittelNormalizer n))
    rw [pittelNormalizer, pittel_ofReal_windowRatio hn0 hlog] at hE
    change _ ≤ ENNReal.ofReal (expectedNumStableMatchings n) /
      ENNReal.ofReal (pittelNormalizer n) at hE
    rw [← ENNReal.ofReal_div_of_pos hnorm] at hE
    exact (ENNReal.ofReal_le_ofReal_iff hqmean).mp hE
  · have hE : ENNReal.ofReal (expectedNumStableMatchings n / pittelNormalizer n) ≤
        pittelSmallRatio n + ENNReal.ofReal (Chi n * (Whi n / Real.log n)) := by
      rw [ENNReal.ofReal_div_of_pos hnorm,
        pittelMean_eq_small_add_bulk n (pittelRadiusLower n), ENNReal.add_div]
      apply add_le_add le_rfl
      exact (ENNReal.div_le_div_right hupper _).trans_eq
        (pittel_ofReal_windowRatio hn0 hlog _ _)
    have ht := pittelSmallRatio_ne_top hn
    have hR := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ht, ENNReal.ofReal_ne_top⟩) hE
    simpa only [ENNReal.toReal_add ht ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hqmean,
      ENNReal.toReal_ofReal (mul_nonneg hChi hhi)] using hR

theorem tendsto_expectedNumStableMatchings_div_size_log :
    Tendsto (fun n : ℕ ↦ expectedNumStableMatchings n / ((n : ℝ) * Real.log n))
      atTop (𝓝 ((Real.exp 1)⁻¹)) := by
  let c : ℝ := (Real.exp 1)⁻¹
  have hc : 0 < c := inv_pos.mpr (Real.exp_pos _)
  change Tendsto (fun n : ℕ ↦ expectedNumStableMatchings n / pittelNormalizer n) atTop (𝓝 c)
  refine tendsto_order.2 ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · let ε := min (c / 2) ((c - x) / 2)
    have hε : 0 < ε := lt_min (by positivity) (by linarith)
    have hε' : ε < c := (min_le_left _ _).trans_lt (by linarith)
    have hstrict : x < c - ε := by linarith [min_le_right (c / 2) ((c - x) / 2)]
    obtain ⟨lower, upper, hL, hU, hbounds⟩ := pittelMean_sandwich hε hε'
    filter_upwards [(tendsto_order.mp hL).1 x hstrict, hbounds] with n hn hb
    exact hn.trans_le hb.1
  · let ε := min (c / 2) ((x - c) / 2)
    have hε : 0 < ε := lt_min (by positivity) (by linarith)
    have hε' : ε < c := (min_le_left _ _).trans_lt (by linarith)
    have hstrict : c + ε < x := by linarith [min_le_right (c / 2) ((x - c) / 2)]
    obtain ⟨lower, upper, hL, hU, hbounds⟩ := pittelMean_sandwich hε hε'
    filter_upwards [(tendsto_order.mp hU).2 x hstrict, hbounds] with n hn hb
    exact hb.2.trans_lt hn

end LennonPittelFormalization

end

open Filter MeasureTheory StableMarriage

open scoped Topology LennonPittelFormalization

open LennonPittelFormalization

private theorem mean_pos (n : ℕ) : 0 < expectedNumStableMatchings n := by
  by_contra! hn
  have h := uniform_profile_stable_mark_ne_zero n
  rw [uniform_mark_event_mass _ (measurableSet_stableMarkEvent n),
    markedNormalizer_stableMarkEvent, ENNReal.ofReal_of_nonpos hn, mul_zero] at h
  exact h rfl

theorem OMA.solution : OMA.R_LennonPittel_lennon_pittel_conjecture_R2_H2_R1.H1 := by
  let S (n : ℕ) : ℝ := ((n : ℝ) + 2) * Real.log ((n : ℝ) + 2)
  have hS (n : ℕ) : 0 < S n := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    exact mul_pos (by positivity) (Real.log_pos (by linarith))
  let a : ℝ := (Real.exp 1)⁻¹ / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have ha' : a < (Real.exp 1)⁻¹ := by dsimp [a]; linarith [inv_pos.mpr (Real.exp_pos 1)]
  have ht := (tendsto_order.mp tendsto_expectedNumStableMatchings_div_size_log).1 a ha'
  have tail : ∀ᶠ n : ℕ in atTop, a / 4 ≤ expectedNumStableMatchings n / S n := by
    filter_upwards [ht, eventually_ge_atTop (2 : ℕ)] with n hn h2
    have h2R : (2 : ℝ) ≤ n := by exact_mod_cast h2
    have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
    have hsq : (n : ℝ) + 2 ≤ (n : ℝ) * n := by nlinarith [sq_nonneg ((n : ℝ) - 2)]
    have hlog : Real.log ((n : ℝ) + 2) ≤ 2 * Real.log n := by
      have h := Real.log_le_log (by positivity) hsq
      rw [Real.log_mul (by positivity) (by positivity)] at h
      linarith
    have hscale : S n ≤ (2 * n) * (2 * Real.log n) :=
      mul_le_mul (by linarith) hlog (Real.log_nonneg (by linarith)) (by positivity)
    have hmean : a * ((n : ℝ) * Real.log n) < expectedNumStableMatchings n :=
      (lt_div_iff₀ (mul_pos (by positivity) hl)).1 hn
    apply (le_div_iff₀ (hS n)).2
    calc
      _ ≤ (a / 4) * ((2 * n) * (2 * Real.log n)) := mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = a * ((n : ℝ) * Real.log n) := by ring
      _ ≤ _ := hmean.le
  obtain ⟨N, hN⟩ := eventually_atTop.1 tail
  have finite (K : ℕ) : ∃ d : ℝ, 0 < d ∧ d ≤ a / 4 ∧
      ∀ n < K, d ≤ expectedNumStableMatchings n / S n := by
    induction K with
    | zero => exact ⟨a / 4, by positivity, le_rfl, by omega⟩
    | succ k ih =>
      obtain ⟨d, hd, hda, hprev⟩ := ih
      let t := expectedNumStableMatchings k / S k
      have ht : 0 < t := div_pos (mean_pos k) (hS k)
      refine ⟨min d t, lt_min hd ht, (min_le_left _ _).trans hda, ?_⟩
      intro n hn
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hn) with hn | rfl
      · exact (min_le_left _ _).trans (hprev n hn)
      · exact min_le_right _ _
  obtain ⟨d, hd, hda, hf⟩ := finite N
  refine ⟨d, hd, fun n ↦ (le_div_iff₀ (hS n)).1 ?_⟩
  rcases lt_or_ge n N with hn | hn
  · exact hf n hn
  · exact hda.trans (hN n hn)
