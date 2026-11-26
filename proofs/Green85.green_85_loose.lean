import FormalConjectures.GreensOpenProblems.«85»

/-!
# Green's Open Problem 85 (Cauchy--Schwarz Bound)

Proof that any nonempty open subset `A ⊆ [0, 1]^2` of sufficiently small measure `α` contains the
four vertices of an axis-parallel rectangle of area at least `(1 / 20) * α^2 / log (1 / α)`,
via Fubini's theorem, Jensen's inequality (Cauchy--Schwarz), and integration of `δ / max δ |t|`.
-/

-- Problem: Green's Open Problem 85 — green 85 loose
-- Upstream: formal-conjectures FormalConjectures/GreensOpenProblems/85.lean:61 (declaration Green85.green_85_loose)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter MeasureTheory MeasureTheory.Measure Set Topology

private lemma integrable_of_mem_unit {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f : α → ℝ} (hm : Measurable f)
    (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1) :
    Integrable f μ :=
  Integrable.of_bound hm.aestronglyMeasurable 1 (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]
    exact h1 x)

private lemma integral_psi_Icc_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {y₁ : ℝ}
    (hy₁ : y₁ ∈ Icc (0 : ℝ) 1) :
    ∫ y₂ in Icc (0 : ℝ) 1, (δ / max δ |y₁ - y₂|) ≤ 2 * δ * (1 + Real.log (1 / δ)) := by
  let ψ : ℝ → ℝ := fun t => δ / max δ |t|
  have hψ_cont : Continuous ψ := by
    have hne : ∀ t : ℝ, max δ |t| ≠ 0 := fun t => ne_of_gt (lt_of_lt_of_le hδ0 (le_max_left _ _))
    fun_prop (disch := assumption)
  have hψ_nonneg : ∀ t : ℝ, 0 ≤ ψ t := fun t =>
    div_nonneg hδ0.le (le_trans hδ0.le (le_max_left _ _))
  have hψ_even : ∀ t : ℝ, ψ (-t) = ψ t := fun t => by simp [ψ]
  have h1 : ∫ y₂ in Icc (0 : ℝ) 1, ψ (y₁ - y₂) = ∫ t in Ioc (y₁ - 1) y₁, ψ t := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_comp_sub_left ψ y₁, sub_zero,
      intervalIntegral.integral_of_le (by linarith)]
  have h2 : ∫ t in Ioc (y₁ - 1) y₁, ψ t ≤ ∫ t in Ioc (-1 : ℝ) 1, ψ t := by
    refine setIntegral_mono_set (hψ_cont.integrableOn_Ioc (μ := volume))
      (Eventually.of_forall hψ_nonneg) ?_
    refine Eventually.of_forall fun t ht => ?_
    rcases hy₁ with ⟨hy0, hy1⟩
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h3 : ∫ t in Ioc (-1 : ℝ) 1, ψ t = 2 * ∫ t in (0 : ℝ)..1, ψ t := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      ← intervalIntegral.integral_add_adjacent_intervals
        (hψ_cont.intervalIntegrable (-1) 0) (hψ_cont.intervalIntegrable 0 1)]
    have hneg : ∫ t in (-1 : ℝ)..0, ψ t = ∫ t in (0 : ℝ)..1, ψ t := by
      have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1) (f := ψ)
      simp only [neg_zero, hψ_even] at h
      exact h.symm
    rw [hneg]
    ring
  have h4 : ∫ t in (0 : ℝ)..1, ψ t = δ * (1 + Real.log (1 / δ)) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hψ_cont.intervalIntegrable 0 δ) (hψ_cont.intervalIntegrable δ 1)]
    have hleft : ∫ t in (0 : ℝ)..δ, ψ t = δ := by
      have hcongr : ∫ t in (0 : ℝ)..δ, ψ t = ∫ _t in (0 : ℝ)..δ, (1 : ℝ) := by
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [Set.uIcc_of_le hδ0.le] at ht
        have habs : |t| ≤ δ := by rw [abs_of_nonneg ht.1]; exact ht.2
        simp [ψ, max_eq_left habs, hδ0.ne']
      rw [hcongr]
      simp
    have hright : ∫ t in δ..1, ψ t = δ * Real.log (1 / δ) := by
      have hcongr : ∫ t in δ..1, ψ t = ∫ t in δ..1, δ * t⁻¹ := by
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [Set.uIcc_of_le hδ1.le] at ht
        have ht0 : 0 ≤ t := le_trans hδ0.le ht.1
        simp [ψ, abs_of_nonneg ht0, max_eq_right ht.1, div_eq_mul_inv]
      rw [hcongr, intervalIntegral.integral_const_mul, integral_inv_of_pos hδ0 zero_lt_one]
    rw [hleft, hright]
    ring
  calc ∫ y₂ in Icc (0 : ℝ) 1, ψ (y₁ - y₂)
      = ∫ t in Ioc (y₁ - 1) y₁, ψ t := h1
    _ ≤ ∫ t in Ioc (-1 : ℝ) 1, ψ t := h2
    _ = 2 * ∫ t in (0 : ℝ)..1, ψ t := h3
    _ = 2 * δ * (1 + Real.log (1 / δ)) := by rw [h4]; ring

private lemma slice_measure_le {A : Set (ℝ × ℝ)} {M : ℝ} (hM : 0 < M)
    (hAsub : A ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
    (hno : ∀ x₁ x₂ y₁ y₂,
      {(x₁, y₁), (x₂, y₁), (x₂, y₂), (x₁, y₂)} ⊆ A →
      |x₁ - x₂| * |y₁ - y₂| < M)
    (y₁ y₂ : ℝ) :
    (volume {x : ℝ | (x, y₁) ∈ A ∧ (x, y₂) ∈ A}).toReal ≤
      (2 * M) / max (2 * M) |y₁ - y₂| := by
  let S : Set ℝ := {x : ℝ | (x, y₁) ∈ A ∧ (x, y₂) ∈ A}
  have hSsub : S ⊆ Icc (0 : ℝ) 1 := fun x hx => (hAsub hx.1).1
  have hle1 : (volume S).toReal ≤ 1 := by
    have h1 : volume S ≤ volume (Icc (0 : ℝ) 1) := measure_mono hSsub
    have hfin : volume (Icc (0 : ℝ) 1) ≠ ⊤ := by simp [Real.volume_Icc]
    have h2 := ENNReal.toReal_mono hfin h1
    simpa [Real.volume_Icc] using h2
  by_cases hdist : |y₁ - y₂| ≤ 2 * M
  · rw [max_eq_left hdist, div_self (by positivity)]
    exact hle1
  · have hdist' : 2 * M < |y₁ - y₂| := lt_of_not_ge hdist
    rw [max_eq_right hdist'.le]
    have hypos : 0 < |y₁ - y₂| := lt_trans (by positivity) hdist'
    rcases S.eq_empty_or_nonempty with hSempty | ⟨x₀, hx₀⟩
    · simp [S, hSempty]
      positivity
    · let r : ℝ := M / |y₁ - y₂|
      have hr : 0 < r := div_pos hM hypos
      have hsub : S ⊆ Icc (x₀ - r) (x₀ + r) := by
        intro x hx
        have hrect : {(x, y₁), (x₀, y₁), (x₀, y₂), (x, y₂)} ⊆ A := by
          intro p hp
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
          rcases hp with rfl | rfl | rfl | rfl
          · exact hx.1
          · exact hx₀.1
          · exact hx₀.2
          · exact hx.2
        have hlt : |x - x₀| * |y₁ - y₂| < M := hno x x₀ y₁ y₂ hrect
        have hxr : |x - x₀| < r := (lt_div_iff₀ hypos).mpr hlt
        rw [abs_lt] at hxr
        exact ⟨by linarith, by linarith⟩
      have hmeas : volume S ≤ volume (Icc (x₀ - r) (x₀ + r)) := measure_mono hsub
      have hfin : volume (Icc (x₀ - r) (x₀ + r)) ≠ ⊤ := by simp [Real.volume_Icc]
      have htoReal := ENNReal.toReal_mono hfin hmeas
      rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)] at htoReal
      calc (volume S).toReal ≤ (x₀ + r) - (x₀ - r) := htoReal
        _ = 2 * M / |y₁ - y₂| := by dsimp only [r]; ring

theorem OMA.solution : type_of% @Green85.green_85_loose := by
  refine ⟨1 / 20, by norm_num, ?_⟩
  refine eventually_of_mem (Ioo_mem_nhdsGT (Real.exp_pos (-10))) ?_
  intro α hα A hAopen hAsub _ hαeq
  by_contra hno
  push Not at hno
  have hα_pos : 0 < α := hα.1
  have hα_lt : α < Real.exp (-10) := hα.2
  have hα_lt_one : α < 1 := lt_trans hα_lt (Real.exp_lt_one_iff.mpr (by norm_num))
  have hinv_gt : Real.exp 10 < 1 / α := by
    rw [lt_div_iff₀ hα_pos]
    have hmul := mul_lt_mul_of_pos_left hα_lt (Real.exp_pos 10)
    have hexp : Real.exp 10 * Real.exp (-10) = 1 := by
      rw [← Real.exp_add]
      norm_num
    linarith
  set L : ℝ := Real.log (1 / α)
  have hL_gt : 10 < L := by
    have h := Real.log_lt_log (Real.exp_pos 10) hinv_gt
    rw [Real.log_exp] at h
    exact h
  have hL_pos : 0 < L := by linarith
  set M : ℝ := (1 / 20) * α ^ 2 * L⁻¹
  have hM_pos : 0 < M := by positivity
  set δ : ℝ := 2 * M
  have hδ_pos : 0 < δ := by positivity
  have hδ_eq : δ = α ^ 2 / (10 * L) := by
    dsimp only [δ, M]
    ring
  have hδ_lt_one : δ < 1 := by
    rw [hδ_eq, div_lt_one (by positivity)]
    have hsq : α ^ 2 < 1 := by nlinarith
    linarith
  let I : Set ℝ := Icc (0 : ℝ) 1
  let μ : Measure ℝ := (volume : Measure ℝ).restrict I
  have : IsProbabilityMeasure μ := ⟨by simp [μ, I, Real.volume_Icc]⟩
  let χ : ℝ × ℝ → ℝ := A.indicator 1
  have hχ_meas : Measurable χ := measurable_const.indicator hAopen.measurableSet
  have hχ_nonneg : ∀ p, 0 ≤ χ p := fun p => Set.indicator_nonneg (fun _ _ => zero_le_one) p
  have hχ_le_one : ∀ p, χ p ≤ 1 := fun p => by
    by_cases hp : p ∈ A <;> simp [χ, hp]
  have hχ_int : Integrable χ (μ.prod μ) := integrable_of_mem_unit hχ_meas hχ_nonneg hχ_le_one
  have hα_int : ∫ p : ℝ × ℝ, χ p ∂(μ.prod μ) = α := by
    dsimp only [χ]
    rw [integral_indicator_one hAopen.measurableSet, measureReal_def,
      Measure.prod_restrict, Measure.restrict_apply hAopen.measurableSet,
      Set.inter_eq_left.mpr hAsub]
    exact hαeq.symm
  let f : ℝ → ℝ := fun x => ∫ y : ℝ, χ (x, y) ∂μ
  have hf_int_eq : ∫ x : ℝ, f x ∂μ = α := by
    rw [← hα_int]
    exact (MeasureTheory.integral_prod χ hχ_int).symm
  have hf_meas : Measurable f := hχ_meas.stronglyMeasurable.integral_prod_right'.measurable
  have hf_nonneg : ∀ x, 0 ≤ f x := fun x => integral_nonneg fun y => hχ_nonneg (x, y)
  have hf_le_one : ∀ x, f x ≤ 1 := fun x => by
    have hxi : Integrable (fun y => χ (x, y)) μ :=
      integrable_of_mem_unit (hχ_meas.comp (measurable_const.prodMk measurable_id))
        (fun y => hχ_nonneg (x, y)) (fun y => hχ_le_one (x, y))
    calc f x ≤ ∫ _y : ℝ, (1 : ℝ) ∂μ := integral_mono hxi (integrable_const 1) (fun y => hχ_le_one (x, y))
      _ = 1 := by simp
  have hjensen : α ^ 2 ≤ ∫ x : ℝ, (f x) ^ 2 ∂μ := by
    rw [← hf_int_eq]
    exact (convexOn_pow 2).map_integral_le (continuous_pow 2).continuousOn isClosed_Ici
      (Eventually.of_forall hf_nonneg)
      (integrable_of_mem_unit hf_meas hf_nonneg hf_le_one)
      (integrable_of_mem_unit (hf_meas.pow_const 2) (fun x => sq_nonneg (f x))
        (fun x => pow_le_one₀ (hf_nonneg x) (hf_le_one x)))
  let Φ : ℝ → ℝ × ℝ → ℝ := fun x p => χ (x, p.1) * χ (x, p.2)
  have hΦ_meas : Measurable (Function.uncurry Φ) := by
    refine (hχ_meas.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
      (hχ_meas.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have hΦ_nonneg : ∀ q : ℝ × (ℝ × ℝ), 0 ≤ Function.uncurry Φ q :=
    fun q => mul_nonneg (hχ_nonneg _) (hχ_nonneg _)
  have hΦ_le_one : ∀ q : ℝ × (ℝ × ℝ), Function.uncurry Φ q ≤ 1 :=
    fun q => mul_le_one₀ (hχ_le_one _) (hχ_nonneg _) (hχ_le_one _)
  have hΦ_int : Integrable (Function.uncurry Φ) (μ.prod (μ.prod μ)) :=
    integrable_of_mem_unit hΦ_meas hΦ_nonneg hΦ_le_one
  let g : ℝ × ℝ → ℝ := fun p => ∫ x : ℝ, Φ x p ∂μ
  have hsq_eq : ∫ x : ℝ, (f x) ^ 2 ∂μ = ∫ p : ℝ × ℝ, g p ∂(μ.prod μ) := by
    calc ∫ x : ℝ, (f x) ^ 2 ∂μ
        = ∫ x : ℝ, (∫ p : ℝ × ℝ, Φ x p ∂(μ.prod μ)) ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          dsimp only [f, Φ]
          rw [sq, ← MeasureTheory.integral_prod_mul]
      _ = ∫ p : ℝ × ℝ, g p ∂(μ.prod μ) := MeasureTheory.integral_integral_swap hΦ_int
  have hg_eq_vol : ∀ p : ℝ × ℝ,
      g p = (volume {x : ℝ | (x, p.1) ∈ A ∧ (x, p.2) ∈ A}).toReal := by
    intro p
    let S : Set ℝ := {x : ℝ | (x, p.1) ∈ A ∧ (x, p.2) ∈ A}
    have hSopen : IsOpen S :=
      (hAopen.preimage (continuous_id.prodMk continuous_const)).inter
        (hAopen.preimage (continuous_id.prodMk continuous_const))
    have hSsub : S ⊆ I := fun x hx => (hAsub hx.1).1
    have hind : ∀ x : ℝ, Φ x p = S.indicator (1 : ℝ → ℝ) x := by
      intro x
      by_cases hx1 : (x, p.1) ∈ A <;> by_cases hx2 : (x, p.2) ∈ A <;>
        simp [Φ, χ, S, hx1, hx2]
    dsimp only [g]
    simp_rw [hind]
    rw [integral_indicator_one hSopen.measurableSet, measureReal_def,
      Measure.restrict_apply hSopen.measurableSet, Set.inter_eq_left.mpr hSsub]
  let ψ2 : ℝ × ℝ → ℝ := fun p => δ / max δ |p.1 - p.2|
  have hψ2_cont : Continuous ψ2 := by
    have hne : ∀ p : ℝ × ℝ, max δ |p.1 - p.2| ≠ 0 :=
      fun p => ne_of_gt (lt_of_lt_of_le hδ_pos (le_max_left _ _))
    fun_prop (disch := assumption)
  have hψ2_int : Integrable ψ2 (μ.prod μ) :=
    integrable_of_mem_unit hψ2_cont.measurable
      (fun p => div_nonneg hδ_pos.le (le_trans hδ_pos.le (le_max_left _ _)))
      (fun p => (div_le_one (lt_of_lt_of_le hδ_pos (le_max_left _ _))).mpr (le_max_left _ _))
  have hg_int : Integrable g (μ.prod μ) := hΦ_int.integral_prod_right
  have hupper : ∫ p : ℝ × ℝ, g p ∂(μ.prod μ) ≤ 2 * δ * (1 + Real.log (1 / δ)) := by
    calc ∫ p : ℝ × ℝ, g p ∂(μ.prod μ)
        ≤ ∫ p : ℝ × ℝ, ψ2 p ∂(μ.prod μ) := by
          refine integral_mono hg_int hψ2_int fun p => ?_
          rw [hg_eq_vol p]
          exact slice_measure_le hM_pos hAsub hno p.1 p.2
      _ = ∫ y₁ : ℝ, (∫ y₂ : ℝ, ψ2 (y₁, y₂) ∂μ) ∂μ := MeasureTheory.integral_prod ψ2 hψ2_int
      _ ≤ ∫ _y₁ : ℝ, (2 * δ * (1 + Real.log (1 / δ))) ∂μ := by
          refine integral_mono_ae hψ2_int.integral_prod_left (integrable_const _) ?_
          filter_upwards [ae_restrict_mem measurableSet_Icc] with y₁ hy₁
          exact integral_psi_Icc_le hδ_pos hδ_lt_one hy₁
      _ = 2 * δ * (1 + Real.log (1 / δ)) := by simp
  have hchain : α ^ 2 ≤ 2 * δ * (1 + Real.log (1 / δ)) := by
    linarith [hjensen, hsq_eq, hupper]
  have hlog_bound : 1 + Real.log (1 / δ) < 5 * L := by
    have h1δ : 1 / δ = 10 * L * (1 / α) ^ 2 := by
      rw [hδ_eq]
      field_simp
    have hlog1δ : Real.log (1 / δ) = Real.log 10 + Real.log L + 2 * L := by
      rw [h1δ, Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by norm_num) hL_pos.ne', Real.log_pow]
      push_cast
      ring
    have hlog10 : Real.log 10 ≤ 9 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10)
      linarith
    have hlogL : Real.log L ≤ L - 1 := Real.log_le_sub_one_of_pos hL_pos
    linarith
  have hstrict : 2 * δ * (1 + Real.log (1 / δ)) < α ^ 2 := by
    have h1 : 2 * δ * (1 + Real.log (1 / δ)) < 2 * δ * (5 * L) :=
      mul_lt_mul_of_pos_left hlog_bound (by positivity)
    have h2 : 2 * δ * (5 * L) = α ^ 2 := by
      rw [hδ_eq]
      field_simp
      ring
    linarith
  linarith
