import OMAStatements.S_mo_485060

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

private lemma part1 (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∃ (π : Measure (ℝ × ℝ)) (_ : IsProbabilityMeasure π), π.snd = μ ∧
      (∀ A : Set ℝ, MeasurableSet A →
        π.fst (OMA.S_mo_485060.certainty π A) = (μ A) ^ 2) ∧
      π.fst (OMA.S_mo_485060.diracPoints π) = (μ.prod μ) (diagonal ℝ) := by
  have hR : ¬ Countable ℝ := not_countable_iff.mpr inferInstance
  have hRR : ¬ Countable (ℝ × ℝ) := fun h =>
    hR (Function.Injective.countable (f := fun x : ℝ => (x, (0 : ℝ)))
      fun _ _ hxy => (Prod.mk.inj hxy).1)
  let e : ℝ × ℝ ≃ᵐ ℝ := PolishSpace.measurableEquivOfNotCountable hRR hR
  let κ : Kernel ℝ ℝ :=
    { toFun := fun y => ((2 : ℝ≥0∞)⁻¹ • Measure.dirac (e.symm y).1) +
        ((2 : ℝ≥0∞)⁻¹ • Measure.dirac (e.symm y).2)
      measurable' := by
        refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
        have h1 : Measurable (fun y : ℝ => (2 : ℝ≥0∞)⁻¹ * s.indicator 1 (e.symm y).1) :=
          measurable_const.mul
            ((measurable_const.indicator hs).comp (measurable_fst.comp e.symm.measurable))
        have h2 : Measurable (fun y : ℝ => (2 : ℝ≥0∞)⁻¹ * s.indicator 1 (e.symm y).2) :=
          measurable_const.mul
            ((measurable_const.indicator hs).comp (measurable_snd.comp e.symm.measurable))
        have h12 : Measurable (fun y : ℝ =>
            (2 : ℝ≥0∞)⁻¹ * s.indicator 1 (e.symm y).1 +
            (2 : ℝ≥0∞)⁻¹ * s.indicator 1 (e.symm y).2) := h1.add h2
        simpa only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
          Measure.dirac_apply' _ hs] using h12 }
  have hκ_apply : ∀ y s, MeasurableSet s →
      κ y s = (2 : ℝ≥0∞)⁻¹ * s.indicator 1 (e.symm y).1 +
        (2 : ℝ≥0∞)⁻¹ * s.indicator 1 (e.symm y).2 := by
    intro y s hs
    simp [κ, Measure.add_apply, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs]
  have hκ_markov : IsMarkovKernel κ := by
    refine ⟨fun y => ⟨?_⟩⟩
    rw [hκ_apply y univ MeasurableSet.univ]
    simp [ENNReal.inv_two_add_inv_two]
  let ν : Measure ℝ := (μ.prod μ).map e
  have hν : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map e.measurable.aemeasurable
  let π : Measure (ℝ × ℝ) := ν ⊗ₘ κ
  have hπ : IsProbabilityMeasure π := inferInstance
  have hfst : π.fst = ν := Measure.fst_compProd ν κ
  have hcond : ∀ᵐ y ∂π.fst, π.condKernel y = κ y := by
    rw [hfst]
    exact ProbabilityTheory.condKernel_compProd ν κ
  refine ⟨π, hπ, ?_, ?_, ?_⟩
  · ext A hA
    rw [Measure.snd_apply hA, Measure.compProd_apply (measurable_snd hA)]
    have hpre : ∀ y : ℝ, Prod.mk y ⁻¹' (Prod.snd ⁻¹' A) = A := fun _ => rfl
    simp_rw [hpre, hκ_apply _ A hA]
    have hmeas1 : Measurable (fun y : ℝ => (2 : ℝ≥0∞)⁻¹ * A.indicator (1 : ℝ → ℝ≥0∞) (e.symm y).1) :=
      measurable_const.mul
        ((measurable_const.indicator hA).comp (measurable_fst.comp e.symm.measurable))
    have hmeas2 : Measurable (fun y : ℝ => (2 : ℝ≥0∞)⁻¹ * A.indicator (1 : ℝ → ℝ≥0∞) (e.symm y).2) :=
      measurable_const.mul
        ((measurable_const.indicator hA).comp (measurable_snd.comp e.symm.measurable))
    have hmeas : Measurable (fun y : ℝ =>
        (2 : ℝ≥0∞)⁻¹ * A.indicator (1 : ℝ → ℝ≥0∞) (e.symm y).1 +
        (2 : ℝ≥0∞)⁻¹ * A.indicator (1 : ℝ → ℝ≥0∞) (e.symm y).2) := hmeas1.add hmeas2
    dsimp only [ν]
    rw [lintegral_map hmeas e.measurable]
    simp_rw [e.symm_apply_apply]
    have hm1 : Measurable (fun p : ℝ × ℝ => (2 : ℝ≥0∞)⁻¹ * A.indicator (1 : ℝ → ℝ≥0∞) p.1) :=
      measurable_const.mul ((measurable_const.indicator hA).comp measurable_fst)
    have hm1' : Measurable (fun p : ℝ × ℝ => A.indicator (1 : ℝ → ℝ≥0∞) p.1) :=
      (measurable_const.indicator hA).comp measurable_fst
    have hm2' : Measurable (fun p : ℝ × ℝ => A.indicator (1 : ℝ → ℝ≥0∞) p.2) :=
      (measurable_const.indicator hA).comp measurable_snd
    rw [lintegral_add_left hm1, lintegral_const_mul _ hm1', lintegral_const_mul _ hm2']
    have hint1 : ∫⁻ p : ℝ × ℝ, A.indicator (1 : ℝ → ℝ≥0∞) p.1 ∂(μ.prod μ) = μ A := by
      have heq : (fun p : ℝ × ℝ => A.indicator (1 : ℝ → ℝ≥0∞) p.1) =
          (A ×ˢ (univ : Set ℝ)).indicator 1 := by
        ext ⟨x, y⟩
        by_cases hx : x ∈ A <;> simp [hx]
      rw [heq, lintegral_indicator_one (hA.prod MeasurableSet.univ), Measure.prod_prod,
        measure_univ, mul_one]
    have hint2 : ∫⁻ p : ℝ × ℝ, A.indicator (1 : ℝ → ℝ≥0∞) p.2 ∂(μ.prod μ) = μ A := by
      have heq : (fun p : ℝ × ℝ => A.indicator (1 : ℝ → ℝ≥0∞) p.2) =
          ((univ : Set ℝ) ×ˢ A).indicator 1 := by
        ext ⟨x, y⟩
        by_cases hy : y ∈ A <;> simp [hy]
      rw [heq, lintegral_indicator_one (MeasurableSet.univ.prod hA), Measure.prod_prod,
        measure_univ, one_mul]
    rw [hint1, hint2, ← add_mul, ENNReal.inv_two_add_inv_two, one_mul]
  · intro A hA
    have hae : OMA.S_mo_485060.certainty π A =ᵐ[π.fst] e.symm ⁻¹' (A ×ˢ A) := by
      filter_upwards [hcond] with y hy
      change (π.condKernel y A = 1) = ((e.symm y).1 ∈ A ∧ (e.symm y).2 ∈ A)
      rw [hy, hκ_apply y A hA]
      apply propext
      by_cases h1 : (e.symm y).1 ∈ A <;> by_cases h2 : (e.symm y).2 ∈ A
      · simp [h1, h2, ENNReal.inv_two_add_inv_two]
      · simp [h1, h2]
      · simp [h1, h2]
      · simp [h1, h2]
    rw [measure_congr hae, hfst,
      Measure.map_apply e.measurable ((hA.prod hA).preimage e.symm.measurable)]
    have hpre : e ⁻¹' (e.symm ⁻¹' (A ×ˢ A)) = A ×ˢ A := by
      ext p; simp
    rw [hpre, Measure.prod_prod, sq]
  · have hae : OMA.S_mo_485060.diracPoints π =ᵐ[π.fst] e.symm ⁻¹' (diagonal ℝ) := by
      filter_upwards [hcond] with y hy
      change (∃ x : ℝ, π.condKernel y = Measure.dirac x) = ((e.symm y).1 = (e.symm y).2)
      rw [hy]
      apply propext
      constructor
      · rintro ⟨x, hx⟩
        by_contra hneq
        have heval := congrArg (fun m : Measure ℝ => m {(e.symm y).1}) hx
        rw [hκ_apply y {(e.symm y).1} (MeasurableSet.singleton _)] at heval
        have hnotmem : (e.symm y).2 ∉ ({(e.symm y).1} : Set ℝ) := by
          simp [Ne.symm hneq]
        simp only [indicator_of_mem (mem_singleton _), Pi.one_apply, mul_one,
          indicator_of_notMem hnotmem, mul_zero, add_zero] at heval
        rw [Measure.dirac_apply' _ (MeasurableSet.singleton _)] at heval
        by_cases hxeq : x = (e.symm y).1
        · subst hxeq
          simp at heval
        · have hnot : x ∉ ({(e.symm y).1} : Set ℝ) := by simp [hxeq]
          simp [hnot] at heval
      · intro heq
        refine ⟨(e.symm y).1, ?_⟩
        ext s hs
        rw [hκ_apply y s hs, ← heq, ← add_mul, ENNReal.inv_two_add_inv_two, one_mul,
          Measure.dirac_apply' _ hs]
    rw [measure_congr hae, hfst,
      Measure.map_apply e.measurable (isClosed_diagonal.measurableSet.preimage e.symm.measurable)]
    have hpre : e ⁻¹' (e.symm ⁻¹' diagonal ℝ) = diagonal ℝ := by
      ext p; simp
    rw [hpre]

theorem OMA.solution : type_of% @OMA.S_mo_485060.main := by
  refine ⟨part1, ?_, ?_⟩
  · let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
    have hμ : IsProbabilityMeasure μ := by
      refine ⟨?_⟩
      simp [μ, Real.volume_Icc]
    obtain ⟨π, hπ, hsnd, hcert, hdirac⟩ := part1 μ
    refine ⟨π, hπ, ?_, ?_⟩
    · intro A hA hpos
      rw [hcert A hA, sq]
      rw [hsnd] at hpos
      exact ENNReal.mul_pos hpos.ne' hpos.ne'
    · rw [hdirac, Measure.prod_apply isClosed_diagonal.measurableSet]
      have hzero : ∀ x : ℝ, μ (Prod.mk x ⁻¹' diagonal ℝ) = 0 := by
        intro x
        have hpre : Prod.mk x ⁻¹' diagonal ℝ = {x} := by
          ext y
          simp [diagonal, eq_comm]
        rw [hpre]
        exact measure_singleton x
      simp [hzero]
  · intro π hπ hcert ⟨z, hz⟩
    have hpos : 0 < π.fst (OMA.S_mo_485060.certainty π {z}) :=
      hcert {z} (MeasurableSet.singleton z) hz
    have hsub : OMA.S_mo_485060.certainty π {z} ⊆ OMA.S_mo_485060.diracPoints π := by
      intro y hy
      refine ⟨z, ?_⟩
      ext s hs
      by_cases hzs : z ∈ s
      · rw [Measure.dirac_apply' _ hs, indicator_of_mem hzs, Pi.one_apply]
        apply le_antisymm
        · calc π.condKernel y s ≤ π.condKernel y univ := measure_mono (subset_univ s)
            _ = 1 := measure_univ
        · calc (1 : ℝ≥0∞) = π.condKernel y {z} := hy.symm
            _ ≤ π.condKernel y s := measure_mono (singleton_subset_iff.mpr hzs)
      · rw [Measure.dirac_apply' _ hs, indicator_of_notMem hzs]
        have hcompl : π.condKernel y ({z}ᶜ) = 0 := by
          rwa [prob_compl_eq_zero_iff (MeasurableSet.singleton z)]
        exact measure_mono_null (subset_compl_singleton_iff.mpr hzs) hcompl
    exact lt_of_lt_of_le hpos (measure_mono hsub)
