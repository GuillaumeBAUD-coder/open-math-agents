import OMAStatements.S_mo_389688

open MeasureTheory Set
open scoped ENNReal

namespace Claude389688

lemma cs389 {α : Type*} [MeasurableSpace α] (μ : Measure α) (f g : α → ℝ≥0∞)
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ a, f a * g a ∂μ) ^ 2 ≤ (∫⁻ a, f a ^ 2 ∂μ) * (∫⁻ a, g a ^ 2 ∂μ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf hg
  simp only [Pi.mul_apply] at h
  have e : ∀ u : α → ℝ≥0∞, ((∫⁻ a, u a ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)) ^ 2 = ∫⁻ a, u a ^ 2 ∂μ := by
    intro u
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  calc (∫⁻ a, f a * g a ∂μ) ^ 2
      ≤ ((∫⁻ a, f a ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ a, g a ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := by
        gcongr
    _ = _ := by rw [mul_pow, e, e]

theorem main389 : ∀ V : Set (ℝ × ℝ × ℝ), MeasurableSet V →
    volume V ^ 2 ≤ volume ((fun p : ℝ × ℝ × ℝ => (p.1, p.2.1)) '' V) *
      volume ((fun p : ℝ × ℝ × ℝ => (p.1, p.2.2)) '' V) *
      volume ((fun p : ℝ × ℝ × ℝ => p.2) '' V) := by
  intro V _
  set A := toMeasurable volume ((fun p : ℝ × ℝ × ℝ => (p.1, p.2.1)) '' V) with hA
  set B := toMeasurable volume ((fun p : ℝ × ℝ × ℝ => (p.1, p.2.2)) '' V) with hB
  set C := toMeasurable volume ((fun p : ℝ × ℝ × ℝ => p.2) '' V) with hC
  have hAm : MeasurableSet A := measurableSet_toMeasurable _ _
  have hBm : MeasurableSet B := measurableSet_toMeasurable _ _
  have hCm : MeasurableSet C := measurableSet_toMeasurable _ _
  rw [← measure_toMeasurable ((fun p : ℝ × ℝ × ℝ => (p.1, p.2.1)) '' V),
    ← measure_toMeasurable ((fun p : ℝ × ℝ × ℝ => (p.1, p.2.2)) '' V),
    ← measure_toMeasurable ((fun p : ℝ × ℝ × ℝ => p.2) '' V)]
  set a : ℝ × ℝ → ℝ≥0∞ := A.indicator 1 with ha
  set b : ℝ × ℝ → ℝ≥0∞ := B.indicator 1 with hb
  set c : ℝ × ℝ → ℝ≥0∞ := C.indicator 1 with hc
  have ham : Measurable a := measurable_one.indicator hAm
  have hbm : Measurable b := measurable_one.indicator hBm
  have hcm : Measurable c := measurable_one.indicator hCm
  have sq : ∀ (S : Set (ℝ × ℝ)) (q : ℝ × ℝ),
      (S.indicator (1 : ℝ × ℝ → ℝ≥0∞) q) ^ 2 = S.indicator (1 : ℝ × ℝ → ℝ≥0∞) q := by
    intro S q
    by_cases h : q ∈ S <;> simp [h]
  set W : Set (ℝ × ℝ × ℝ) := {p | (p.1, p.2.1) ∈ A ∧ (p.1, p.2.2) ∈ B ∧ p.2 ∈ C} with hW
  have hVW : V ⊆ W := fun p hp =>
    ⟨subset_toMeasurable _ _ ⟨p, hp, rfl⟩, subset_toMeasurable _ _ ⟨p, hp, rfl⟩,
      subset_toMeasurable _ _ ⟨p, hp, rfl⟩⟩
  set F : ℝ × ℝ × ℝ → ℝ≥0∞ := fun p => a (p.1, p.2.1) * (b (p.1, p.2.2) * c p.2) with hF
  have hFm : Measurable F := by
    have h1 : Measurable fun p : ℝ × ℝ × ℝ => a (p.1, p.2.1) := ham.comp (by fun_prop)
    have h2 : Measurable fun p : ℝ × ℝ × ℝ => b (p.1, p.2.2) := hbm.comp (by fun_prop)
    have h3 : Measurable fun p : ℝ × ℝ × ℝ => c p.2 := hcm.comp (by fun_prop)
    exact h1.mul (h2.mul h3)
  have hV : volume V ≤ ∫⁻ p, F p := by
    calc volume V ≤ volume W := measure_mono hVW
      _ ≤ ∫⁻ p, F p := by
        rw [← lintegral_indicator_one₀ (by
          apply MeasurableSet.nullMeasurableSet
          exact (hAm.preimage (by fun_prop : Measurable fun p : ℝ × ℝ × ℝ => (p.1, p.2.1))).inter
            ((hBm.preimage (by fun_prop : Measurable fun p : ℝ × ℝ × ℝ => (p.1, p.2.2))).inter
              (hCm.preimage (by fun_prop : Measurable fun p : ℝ × ℝ × ℝ => p.2))))]
        apply lintegral_mono
        intro p
        by_cases hp : p ∈ W
        · obtain ⟨h1, h2, h3⟩ := hp
          simp [hF, ha, hb, hc, hW, h1, h2, h3]
        · simp [hp]
  set h : ℝ × ℝ → ℝ≥0∞ := fun q => ∫⁻ z, b (q.1, z) * c (q.2, z) with hh
  have hhm : Measurable h := by
    have : Measurable fun r : (ℝ × ℝ) × ℝ => b (r.1.1, r.2) * c (r.1.2, r.2) :=
      (hbm.comp (by fun_prop)).mul (hcm.comp (by fun_prop))
    exact this.lintegral_prod_right'
  have hI : ∫⁻ p, F p = ∫⁻ q, a q * h q := by
    have e1 : ∫⁻ p, F p = ∫⁻ x, ∫⁻ q : ℝ × ℝ, F (x, q) :=
      lintegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure (ℝ × ℝ))) F hFm.aemeasurable
    have e2 : ∫⁻ q, a q * h q = ∫⁻ x, ∫⁻ y, a (x, y) * h (x, y) :=
      lintegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (fun q => a q * h q) (ham.mul hhm).aemeasurable
    rw [e1, e2]
    refine lintegral_congr fun x => ?_
    have e3 : ∫⁻ q : ℝ × ℝ, F (x, q) = ∫⁻ y, ∫⁻ z, F (x, y, z) :=
      lintegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (fun q : ℝ × ℝ => F (x, q))
        (hFm.comp (by fun_prop : Measurable fun q : ℝ × ℝ => (x, q))).aemeasurable
    rw [e3]
    refine lintegral_congr fun y => ?_
    simp only [hF, hh]
    rw [lintegral_const_mul]
    exact (hbm.comp (by fun_prop)).mul (hcm.comp (by fun_prop))
  have hβ : ∀ (S : Set (ℝ × ℝ)), MeasurableSet S →
      ∫⁻ x, ∫⁻ z, S.indicator (1 : ℝ × ℝ → ℝ≥0∞) (x, z) = volume S := by
    intro S hS
    rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod (volume : Measure ℝ) from rfl,
      ← lintegral_indicator_one hS, lintegral_prod _ (measurable_one.indicator hS).aemeasurable]
  have hh2 : ∫⁻ q, h q ^ 2 ≤ volume B * volume C := by
    have hpt : ∀ q : ℝ × ℝ, h q ^ 2 ≤ (∫⁻ z, b (q.1, z)) * (∫⁻ z, c (q.2, z)) := by
      intro q
      have := cs389 volume (fun z => b (q.1, z)) (fun z => c (q.2, z))
        (hbm.comp (by fun_prop)).aemeasurable (hcm.comp (by fun_prop)).aemeasurable
      simpa [hb, hc, sq] using this
    have hm1 : Measurable fun x : ℝ => ∫⁻ z, b (x, z) := hbm.lintegral_prod_right'
    have hm2 : Measurable fun y : ℝ => ∫⁻ z, c (y, z) := hcm.lintegral_prod_right'
    calc ∫⁻ q, h q ^ 2 ≤ ∫⁻ q : ℝ × ℝ, (∫⁻ z, b (q.1, z)) * (∫⁻ z, c (q.2, z)) := lintegral_mono hpt
      _ = (∫⁻ x, ∫⁻ z, b (x, z)) * (∫⁻ y, ∫⁻ z, c (y, z)) := by
        rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod (volume : Measure ℝ) from rfl,
          lintegral_prod_mul hm1.aemeasurable hm2.aemeasurable]
      _ = volume B * volume C := by rw [hβ B hBm, hβ C hCm]
  calc volume V ^ 2 ≤ (∫⁻ q, a q * h q) ^ 2 := by rw [← hI]; gcongr
    _ ≤ (∫⁻ q, a q ^ 2) * (∫⁻ q, h q ^ 2) := cs389 volume a h ham.aemeasurable hhm.aemeasurable
    _ ≤ volume A * (volume B * volume C) := by
        gcongr
        · simp only [ha, sq]; rw [lintegral_indicator_one hAm]
    _ = volume A * volume B * volume C := (mul_assoc _ _ _).symm

end Claude389688

theorem OMA.solution : type_of% @OMA.S_mo_389688.main := Claude389688.main389
