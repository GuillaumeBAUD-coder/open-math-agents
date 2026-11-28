import OMAStatements.S_mo_182409

namespace OMA.S_mo_182409.Proof

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

private def a (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ (k + 1)

private lemma a_pos (k : ℕ) : 0 < a k := by
  unfold a
  positivity

private lemma hasSum_a : HasSum a 1 := by
  have h0 : HasSum (fun k : ℕ => (1 / 2 : ℝ) ^ k) (1 - 1 / 2 : ℝ)⁻¹ :=
    hasSum_geometric_of_lt_one (by norm_num) (by norm_num)
  have h1 : HasSum (fun k : ℕ => (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ k) ((1 / 2 : ℝ) * (1 - 1 / 2 : ℝ)⁻¹) :=
    h0.mul_left (1 / 2 : ℝ)
  have h2 : (1 / 2 : ℝ) * (1 - 1 / 2 : ℝ)⁻¹ = 1 := by norm_num
  rw [h2] at h1
  convert h1 using 1
  ext k
  unfold a
  rw [pow_succ']

private lemma summable_a : Summable a := hasSum_a.summable

private lemma tsum_a : ∑' k, a k = 1 := hasSum_a.tsum_eq

private def boolToReal (b : Bool) : ℝ := if b then 1 else 0

private lemma boolToReal_nonneg (b : Bool) : 0 ≤ boolToReal b := by
  cases b <;> simp [boolToReal]

private lemma boolToReal_le_one (b : Bool) : boolToReal b ≤ 1 := by
  cases b <;> simp [boolToReal]

private def partialSum (N : ℕ) (ω : ℕ → Bool) : ℝ :=
  ∑ k ∈ Finset.range N, a k * boolToReal (ω k)

private def totalSum (ω : ℕ → Bool) : ℝ :=
  ∑' k, a k * boolToReal (ω k)

private lemma summable_term (ω : ℕ → Bool) : Summable (fun k => a k * boolToReal (ω k)) := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (a_pos k).le (boolToReal_nonneg _)) ?_ summable_a
  intro k
  calc a k * boolToReal (ω k) ≤ a k * 1 := mul_le_mul_of_nonneg_left (boolToReal_le_one _) (a_pos k).le
    _ = a k := mul_one _

private lemma tendsto_partialSum (ω : ℕ → Bool) :
    Tendsto (fun N => partialSum N ω) atTop (𝓝 (totalSum ω)) :=
  (summable_term ω).hasSum.tendsto_sum_nat

private lemma partialSum_mem_Icc (N : ℕ) (ω : ℕ → Bool) :
    partialSum N ω ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨Finset.sum_nonneg fun k _ => mul_nonneg (a_pos k).le (boolToReal_nonneg _), ?_⟩
  calc partialSum N ω
      ≤ ∑ k ∈ Finset.range N, a k := by
        refine Finset.sum_le_sum fun k _ => ?_
        calc a k * boolToReal (ω k) ≤ a k * 1 := mul_le_mul_of_nonneg_left (boolToReal_le_one _) (a_pos k).le
          _ = a k := mul_one _
    _ ≤ ∑' k, a k := summable_a.sum_le_tsum (Finset.range N) (fun k _ => (a_pos k).le)
    _ = 1 := tsum_a

private lemma totalSum_mem_Icc (ω : ℕ → Bool) : totalSum ω ∈ Set.Icc (0 : ℝ) 1 :=
  isClosed_Icc.mem_of_tendsto (tendsto_partialSum ω) (Eventually.of_forall fun N => partialSum_mem_Icc N ω)

private lemma measurable_partialSum (N : ℕ) : Measurable (partialSum N) := by
  unfold partialSum
  refine Finset.measurable_sum (Finset.range N) fun k _ => ?_
  exact measurable_const.mul ((measurable_of_countable boolToReal).comp (measurable_pi_apply k))

private lemma measurable_totalSum : Measurable totalSum :=
  measurable_of_tendsto_metrizable measurable_partialSum (tendsto_pi_nhds.mpr tendsto_partialSum)

private def ratEnum : ℕ → ℚ :=
  Classical.choose (exists_surjective_nat ℚ)

private lemma ratEnum_surjective : Function.Surjective ratEnum :=
  Classical.choose_spec (exists_surjective_nat ℚ)

private def pProb (k : ℕ) : ℝ :=
  1 / (1 + Real.exp (a k * (ratEnum k : ℝ)))

private lemma pProb_pos (k : ℕ) : 0 < pProb k := by
  unfold pProb
  positivity

private lemma pProb_lt_one (k : ℕ) : pProb k < 1 := by
  unfold pProb
  rw [div_lt_one (by positivity)]
  linarith [Real.exp_pos (a k * (ratEnum k : ℝ))]

private lemma one_sub_pProb_eq (k : ℕ) :
    1 - pProb k = pProb k * Real.exp (a k * (ratEnum k : ℝ)) := by
  unfold pProb
  have hpos : 0 < 1 + Real.exp (a k * (ratEnum k : ℝ)) := by positivity
  field_simp [hpos.ne']
  ring

private def bernMeasure (k : ℕ) : Measure Bool :=
  ENNReal.ofReal (1 - pProb k) • Measure.dirac false +
    ENNReal.ofReal (pProb k) • Measure.dirac true

private instance instIsProbBern (k : ℕ) : IsProbabilityMeasure (bernMeasure k) := by
  refine ⟨?_⟩
  have h1 : 0 ≤ 1 - pProb k := sub_nonneg.mpr (pProb_lt_one k).le
  have h2 : 0 ≤ pProb k := (pProb_pos k).le
  simp [bernMeasure, ← ENNReal.ofReal_add h1 h2]

private def prodMeasure : Measure (ℕ → Bool) :=
  Measure.infinitePi bernMeasure

private instance instIsProbProd : IsProbabilityMeasure prodMeasure := by
  unfold prodMeasure
  infer_instance

private def counterMeasure : Measure ℝ :=
  prodMeasure.map totalSum

private instance instIsProbCounter : IsProbabilityMeasure counterMeasure :=
  Measure.isProbabilityMeasure_map measurable_totalSum.aemeasurable

private lemma counterMeasure_ae_Icc : ∀ᵐ x ∂counterMeasure, x ∈ Set.Icc (0 : ℝ) 1 := by
  exact (ae_map_iff measurable_totalSum.aemeasurable measurableSet_Icc).2
    (Eventually.of_forall totalSum_mem_Icc)

private lemma norm_exp_mul_le_of_abs_le_one (z : ℂ) {x : ℝ} (hx : |x| ≤ 1) :
    ‖Complex.exp (z * (x : ℂ))‖ ≤ Real.exp |z.re| := by
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  have hre : (z * (x : ℂ)).re = z.re * x := by simp [Complex.mul_re]
  rw [hre]
  calc z.re * x ≤ |z.re * x| := le_abs_self _
    _ = |z.re| * |x| := abs_mul _ _
    _ ≤ |z.re| * 1 := mul_le_mul_of_nonneg_left hx (abs_nonneg _)
    _ = |z.re| := mul_one _

private lemma integrable_exp_of_abs_le_one (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : ∀ᵐ x ∂μ, |x| ≤ 1) (z : ℂ) :
    Integrable (fun x : ℝ => Complex.exp (z * (x : ℂ))) μ := by
  refine (integrable_const (Real.exp |z.re|)).mono' ?_ ?_
  · exact (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable
  · exact hsupp.mono fun x hx => norm_exp_mul_le_of_abs_le_one z hx

private lemma counterMeasure_ae_abs_le_one : ∀ᵐ x ∂counterMeasure, |x| ≤ 1 := by
  refine counterMeasure_ae_Icc.mono fun x hx => ?_
  rw [abs_le]
  exact ⟨by linarith [hx.1], hx.2⟩

private lemma counterMeasure_integrable (z : ℂ) :
    Integrable (fun x : ℝ => Complex.exp (z * (x : ℂ))) counterMeasure :=
  integrable_exp_of_abs_le_one counterMeasure counterMeasure_ae_abs_le_one z

private lemma counterMeasure_norm_le (z : ℂ) :
    ‖transform counterMeasure z‖ ≤ Real.exp |z.re| := by
  unfold transform
  calc ‖∫ x, Complex.exp (z * (x : ℂ)) ∂counterMeasure‖
      ≤ ∫ x, ‖Complex.exp (z * (x : ℂ))‖ ∂counterMeasure := norm_integral_le_integral_norm _
    _ ≤ ∫ _x, Real.exp |z.re| ∂counterMeasure := by
        refine integral_mono_ae (counterMeasure_integrable z).norm (integrable_const _) ?_
        exact counterMeasure_ae_abs_le_one.mono fun x hx => norm_exp_mul_le_of_abs_le_one z hx
    _ = Real.exp |z.re| := by simp

private lemma counterMeasure_differentiable : Differentiable ℂ (transform counterMeasure) := by
  intro z₀
  have hbound_int : Integrable (fun _ : ℝ => Real.exp (‖z₀‖ + 1)) counterMeasure :=
    integrable_const _
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := counterMeasure) (x₀ := z₀) (s := Metric.ball z₀ 1)
    (F := fun z x => Complex.exp (z * (x : ℂ)))
    (F' := fun z x => (x : ℂ) * Complex.exp (z * (x : ℂ)))
    (bound := fun _ => Real.exp (‖z₀‖ + 1))
    (Metric.ball_mem_nhds z₀ zero_lt_one)
    (Eventually.of_forall fun z =>
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable)
    (counterMeasure_integrable z₀)
    ((Complex.continuous_ofReal.mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))).aestronglyMeasurable)
    (counterMeasure_ae_abs_le_one.mono fun x hx z hz => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hzn : |z.re| ≤ ‖z₀‖ + 1 := by
        have h1 : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
        have h2 : ‖z - z₀‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
        have h3 : ‖z‖ - ‖z₀‖ ≤ ‖z - z₀‖ := norm_sub_norm_le z z₀
        linarith
      calc |x| * ‖Complex.exp (z * (x : ℂ))‖
          ≤ 1 * Real.exp |z.re| :=
            mul_le_mul hx (norm_exp_mul_le_of_abs_le_one z hx) (norm_nonneg _) zero_le_one
        _ = Real.exp |z.re| := one_mul _
        _ ≤ Real.exp (‖z₀‖ + 1) := Real.exp_le_exp.mpr hzn)
    hbound_int
    (Eventually.of_forall fun x z _ => by
      have h1 : HasDerivAt (fun w : ℂ => w * (x : ℂ)) (x : ℂ) z := by
        simpa using (hasDerivAt_id z).mul_const (x : ℂ)
      have h2 : HasDerivAt (fun w : ℂ => Complex.exp (w * (x : ℂ)))
          (Complex.exp (z * (x : ℂ)) * (x : ℂ)) z := h1.cexp
      rw [mul_comm (Complex.exp (z * (x : ℂ))) (x : ℂ)] at h2
      exact h2)
  exact h.2.differentiableAt

private lemma integral_bernMeasure (k : ℕ) (g : Bool → ℂ) :
    ∫ b, g b ∂(bernMeasure k) =
      ((1 - pProb k : ℝ) : ℂ) * g false + ((pProb k : ℝ) : ℂ) * g true := by
  have h1 : 0 ≤ 1 - pProb k := sub_nonneg.mpr (pProb_lt_one k).le
  have h2 : 0 ≤ pProb k := (pProb_pos k).le
  have hint_dirac : ∀ (c : ℝ≥0∞) (b₀ : Bool), c ≠ ⊤ → Integrable g (c • Measure.dirac b₀) := by
    intro c b₀ hc
    have : IsFiniteMeasure (c • Measure.dirac b₀) := by
      refine ⟨?_⟩
      simpa using hc.lt_top
    refine (integrable_const (‖g false‖ + ‖g true‖)).mono' ?_ ?_
    · exact (measurable_of_countable g).aestronglyMeasurable
    · refine Eventually.of_forall fun b => ?_
      cases b
      · linarith [norm_nonneg (g true)]
      · linarith [norm_nonneg (g false)]
  unfold bernMeasure
  rw [integral_add_measure (hint_dirac _ false ENNReal.ofReal_ne_top) (hint_dirac _ true ENNReal.ofReal_ne_top)]
  rw [integral_smul_measure, integral_smul_measure]
  rw [integral_dirac, integral_dirac]
  rw [ENNReal.toReal_ofReal h1, ENNReal.toReal_ofReal h2]
  simp [Complex.real_smul]

private lemma bern_factor_zero (n : ℕ) :
    let z : ℂ := ((ratEnum n : ℝ) : ℂ) + ((Real.pi / a n : ℝ) : ℂ) * Complex.I
    ∫ b : Bool, Complex.exp (z * ((a n * boolToReal b : ℝ) : ℂ)) ∂(bernMeasure n) = 0 := by
  intro z
  rw [integral_bernMeasure]
  simp only [boolToReal, Bool.false_eq_true, ↓reduceIte, mul_zero, Complex.ofReal_zero,
    Complex.exp_zero, mul_one]
  have han : a n ≠ 0 := (a_pos n).ne'
  have hza : z * (a n : ℂ) = ((a n * (ratEnum n : ℝ) : ℝ) : ℂ) + (Real.pi : ℂ) * Complex.I := by
    simp only [z]
    push_cast
    have hdiv : ((Real.pi : ℂ) / (a n : ℂ)) * (a n : ℂ) = (Real.pi : ℂ) :=
      div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr han)
    calc (((ratEnum n : ℝ) : ℂ) + (Real.pi : ℂ) / (a n : ℂ) * Complex.I) * (a n : ℂ)
        = (a n : ℂ) * ((ratEnum n : ℝ) : ℂ) + ((Real.pi : ℂ) / (a n : ℂ) * (a n : ℂ)) * Complex.I := by ring
      _ = (a n : ℂ) * ((ratEnum n : ℝ) : ℂ) + (Real.pi : ℂ) * Complex.I := by rw [hdiv]
  rw [hza, Complex.exp_add, Complex.exp_pi_mul_I, ← Complex.ofReal_exp]
  have hsub := one_sub_pProb_eq n
  have hsubC : ((1 - pProb n : ℝ) : ℂ) = ((pProb n : ℝ) : ℂ) * ((Real.exp (a n * (ratEnum n : ℝ)) : ℝ) : ℂ) := by
    exact_mod_cast hsub
  rw [hsubC]
  ring

private lemma partialSum_integral_zero (n N : ℕ) (hN : n < N) :
    let z : ℂ := ((ratEnum n : ℝ) : ℂ) + ((Real.pi / a n : ℝ) : ℂ) * Complex.I
    ∫ ω, Complex.exp (z * (partialSum N ω : ℂ)) ∂prodMeasure = 0 := by
  intro z
  let s : Finset ℕ := Finset.range N
  let f : (k : s) → Bool → ℂ := fun k b => Complex.exp (z * ((a k.1 * boolToReal b : ℝ) : ℂ))
  have hrewrite : ∀ ω : ℕ → Bool,
      Complex.exp (z * (partialSum N ω : ℂ)) = ∏ k : s, f k (s.restrict ω k) := by
    intro ω
    unfold partialSum
    push_cast
    rw [Finset.mul_sum, Complex.exp_sum]
    rw [← Finset.prod_coe_sort s (fun k => Complex.exp (z * ((a k : ℂ) * (boolToReal (ω k) : ℂ))))]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [f, Complex.ofReal_mul]
    rfl
  simp_rw [hrewrite]
  have hmeas : AEStronglyMeasurable (fun y : (k : s) → Bool => ∏ k : s, f k (y k))
      (Measure.pi fun k : s => bernMeasure k.1) :=
    (measurable_of_countable _).aestronglyMeasurable
  rw [prodMeasure, integral_restrict_infinitePi (μ := bernMeasure) (s := s) hmeas]
  rw [integral_fintype_prod_eq_prod f]
  have hn_mem : n ∈ s := Finset.mem_range.mpr hN
  refine Finset.prod_eq_zero (i := ⟨n, hn_mem⟩) (Finset.mem_univ _) ?_
  exact bern_factor_zero n

private lemma counterMeasure_zero_at_rat (q : ℚ) :
    ∃ z : ℂ, z.re = q ∧ transform counterMeasure z = 0 := by
  obtain ⟨n, hn⟩ := ratEnum_surjective q
  let z : ℂ := ((ratEnum n : ℝ) : ℂ) + ((Real.pi / a n : ℝ) : ℂ) * Complex.I
  refine ⟨z, ?_, ?_⟩
  · simp [z, hn]
  · unfold transform
    have hmeas_exp : AEStronglyMeasurable (fun x : ℝ => Complex.exp (z * (x : ℂ))) counterMeasure :=
      (by fun_prop : Continuous fun x : ℝ => Complex.exp (z * (x : ℂ))).aestronglyMeasurable
    rw [counterMeasure, integral_map measurable_totalSum.aemeasurable hmeas_exp]
    have htendsto : Tendsto (fun N => ∫ ω, Complex.exp (z * (partialSum N ω : ℂ)) ∂prodMeasure)
        atTop (𝓝 (∫ ω, Complex.exp (z * (totalSum ω : ℂ)) ∂prodMeasure)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => Real.exp |z.re|) ?_ (integrable_const _) ?_ ?_
      · intro N
        exact (Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal)).measurable.comp
          (measurable_partialSum N) |>.aestronglyMeasurable
      · intro N
        refine Eventually.of_forall fun ω => ?_
        have hmem := partialSum_mem_Icc N ω
        have habs : |partialSum N ω| ≤ 1 := by
          rw [abs_le]
          exact ⟨by linarith [hmem.1], hmem.2⟩
        exact norm_exp_mul_le_of_abs_le_one z habs
      · refine Eventually.of_forall fun ω => ?_
        exact (Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal)).continuousAt.tendsto.comp
          (tendsto_partialSum ω)
    have hzero : Tendsto (fun N => ∫ ω, Complex.exp (z * (partialSum N ω : ℂ)) ∂prodMeasure)
        atTop (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop n] with N hN
      exact (partialSum_integral_zero n N hN).symm
    exact tendsto_nhds_unique htendsto hzero

private lemma positive_criterion (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsupp : ∀ᵐ x ∂μ, |x| ≤ 1) (R : ℝ) (_hR : 0 ≤ R)
    (hatom : Real.exp R * (1 - μ.real {0}) < μ.real {0})
    (z : ℂ) (hz : |z.re| ≤ R) :
    transform μ z ≠ 0 := by
  intro h0
  have hint := integrable_exp_of_abs_le_one μ hsupp z
  have hsplit : transform μ z =
      (∫ x in ({0} : Set ℝ), Complex.exp (z * (x : ℂ)) ∂μ) +
      (∫ x in ({0} : Set ℝ)ᶜ, Complex.exp (z * (x : ℂ)) ∂μ) := by
    unfold transform
    exact (integral_add_compl (measurableSet_singleton 0) hint).symm
  have hsing : ∫ x in ({0} : Set ℝ), Complex.exp (z * (x : ℂ)) ∂μ = ((μ.real {0} : ℝ) : ℂ) := by
    have hcongr : ∫ x in ({0} : Set ℝ), Complex.exp (z * (x : ℂ)) ∂μ =
        ∫ _x in ({0} : Set ℝ), (1 : ℂ) ∂μ := by
      refine setIntegral_congr_fun (measurableSet_singleton 0) fun x hx => ?_
      simp [Set.mem_singleton_iff.mp hx]
    rw [hcongr, setIntegral_const, Complex.real_smul, mul_one]
  have hcompl_norm : ‖∫ x in ({0} : Set ℝ)ᶜ, Complex.exp (z * (x : ℂ)) ∂μ‖ ≤
      Real.exp R * (1 - μ.real {0}) := by
    calc ‖∫ x in ({0} : Set ℝ)ᶜ, Complex.exp (z * (x : ℂ)) ∂μ‖
        ≤ ∫ x in ({0} : Set ℝ)ᶜ, ‖Complex.exp (z * (x : ℂ))‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ _x in ({0} : Set ℝ)ᶜ, Real.exp R ∂μ := by
          refine integral_mono_ae hint.integrableOn.norm (integrable_const _) ?_
          refine (ae_restrict_of_ae hsupp).mono fun x hx => ?_
          exact (norm_exp_mul_le_of_abs_le_one z hx).trans (Real.exp_le_exp.mpr hz)
      _ = μ.real ({0} : Set ℝ)ᶜ * Real.exp R := by
          rw [setIntegral_const, smul_eq_mul]
      _ = Real.exp R * (1 - μ.real {0}) := by
          rw [mul_comm, probReal_compl_eq_one_sub (measurableSet_singleton 0)]
  rw [h0, hsing] at hsplit
  have heq : ((μ.real {0} : ℝ) : ℂ) = - ∫ x in ({0} : Set ℝ)ᶜ, Complex.exp (z * (x : ℂ)) ∂μ :=
    eq_neg_of_add_eq_zero_left hsplit.symm
  have hnorm_eq : μ.real {0} = ‖∫ x in ({0} : Set ℝ)ᶜ, Complex.exp (z * (x : ℂ)) ∂μ‖ := by
    have := congrArg norm heq
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg] at this
    exact this
  linarith

end

end OMA.S_mo_182409.Proof

theorem OMA.solution : type_of% @OMA.S_mo_182409.main := by
  refine ⟨?_, ?_⟩
  · refine ⟨OMA.S_mo_182409.Proof.counterMeasure, inferInstance,
      OMA.S_mo_182409.Proof.counterMeasure_ae_Icc,
      OMA.S_mo_182409.Proof.counterMeasure_integrable,
      OMA.S_mo_182409.Proof.counterMeasure_differentiable,
      OMA.S_mo_182409.Proof.counterMeasure_norm_le,
      OMA.S_mo_182409.Proof.counterMeasure_zero_at_rat, ?_⟩
    intro a b hab
    obtain ⟨q, hqa, hqb⟩ := exists_rat_btwn hab
    obtain ⟨z, hzr, hz0⟩ := OMA.S_mo_182409.Proof.counterMeasure_zero_at_rat q
    exact ⟨z, hzr ▸ hqa, hzr ▸ hqb, hz0⟩
  · intro μ _ hsupp R hR hatom z hz
    exact OMA.S_mo_182409.Proof.positive_criterion μ hsupp R hR hatom z hz
