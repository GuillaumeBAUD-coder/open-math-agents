import OMAReductions.R_Erdos704_erdos_704_variants_davies_lower_R1_H1_R1

/-!
Proof of `Erdos704.erdos_704.variants.davies_lower.R1.H1.R1.H2` (Davies's averaged arcsine
measure and logarithmic potential).

We construct `μ` as the pushforward `(μA.prod μΘ).map Φ` where:
- `μA` is `(1 / (4 a^{3/2})) da` on `[1/4, 1]` (total mass `1/2`),
- `μΘ` is `(1 / π) dθ` on `[0, π]` (probability measure),
- `Φ (a, θ) = (a / 2) * (1 - cos θ)`.

Each required property follows cleanly:
1. Total mass `1/2` and support in `[0, 1]` from `∫_{1/4}^1 (1 / (4 a^{3/2})) da = 1/2`.
2. CDF on `[0, 1/4]` equals `∫_{1/4}^1 (arccos(1 - 2t/a) / π) * w(a) da`, which is continuous,
   vanishes at `0`, and has slope `≥ 1/π ≥ 1/(2π)` by 1-Lipschitzness of `cos`.
3. On `[1/4, 1]`, Tonelli on `K(t, a) = 1 / (4π a^{3/2} √(t (a - t)))` over `x ≤ t < a ≤ 1`
   gives `μ([x, 1]) = ∫_x^1 √(1 - t)/(2π t^{3/2}) dt`, hence equality of measures on `[1/4, 1]`.
4. For `y ∈ [0, 1/4]`, Euler's integral `∫_0^{π/2} log(sin u) du = -(π/2) log 2` yields
   `∫_0^π log |y - Φ(a, θ)| dθ = π log(a/4)`, and FTC gives `∫_{1/4}^1 log(a/4) w(a) da = 1 - 3 log 2`,
   from which dominated convergence bounds the truncated logarithmic potential.
-/

namespace Erdos704DaviesR1H1R1H2

open Filter MeasureTheory Real Set Topology
open scoped BigOperators Classical ENNReal

private noncomputable def w (a : ℝ) : ℝ :=
  1 / (4 * a ^ ((3 : ℝ) / 2))

private noncomputable def ρRight (t : ℝ) : ℝ :=
  Real.sqrt (1 - t) / (2 * Real.pi * t ^ ((3 : ℝ) / 2))

private noncomputable def μA : Measure ℝ :=
  (volume.restrict (Set.Icc (1 / 4 : ℝ) 1)).withDensity (fun a => ENNReal.ofReal (w a))

private noncomputable def μΘ : Measure ℝ :=
  (volume.restrict (Set.Icc (0 : ℝ) Real.pi)).withDensity (fun _ => ENNReal.ofReal (1 / Real.pi))

private noncomputable def Φ (p : ℝ × ℝ) : ℝ :=
  (p.1 / 2) * (1 - Real.cos p.2)

private noncomputable def μ : Measure ℝ :=
  (μA.prod μΘ).map Φ

/- ### Section 1: Basic calculus identities for `w` and `Φ` -/

private lemma w_nonneg {a : ℝ} (ha : 0 ≤ a) : 0 ≤ w a := by
  dsimp [w]; positivity

private lemma measurable_w : Measurable w := by
  unfold w
  exact measurable_const.div (measurable_const.mul (measurable_id.pow_const _))

private lemma continuousOn_w : ContinuousOn w (Set.Icc (1 / 4 : ℝ) 1) := by
  unfold w
  refine continuousOn_const.div (continuousOn_const.mul ?_) fun a ha => ?_
  · exact ContinuousOn.rpow_const continuousOn_id fun a ha => Or.inl (by linarith [ha.1])
  · have ha' : 0 < a := by linarith [ha.1]
    positivity

private lemma quarter_rpow_neg_half : (1 / 4 : ℝ) ^ (-(1 / 2 : ℝ)) = 2 := by
  rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
  have hsq : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
    norm_num
  rw [hsq]
  norm_num

private lemma integral_w : ∫ a in (1 / 4 : ℝ)..1, w a = 1 / 2 := by
  let F : ℝ → ℝ := fun a => -(1 / 2) * a ^ (-(1 / 2 : ℝ))
  have hderiv : ∀ a ∈ Set.uIcc (1 / 4 : ℝ) 1, HasDerivAt F (w a) a := by
    intro a ha
    rw [Set.uIcc_of_le (by norm_num : (1 / 4 : ℝ) ≤ 1)] at ha
    have ha_pos : 0 < a := by linarith [ha.1]
    have h1 : HasDerivAt (fun x : ℝ => x ^ (-(1 / 2 : ℝ)))
        ((-(1 / 2 : ℝ)) * a ^ (-(1 / 2 : ℝ) - 1)) a :=
      Real.hasDerivAt_rpow_const (Or.inl ha_pos.ne')
    have h2 : HasDerivAt F (-(1 / 2) * ((-(1 / 2 : ℝ)) * a ^ (-(1 / 2 : ℝ) - 1))) a :=
      h1.const_mul (-(1 / 2))
    convert h2 using 1
    dsimp [w]
    rw [show (-(1 / 2 : ℝ) - 1 : ℝ) = -((3 : ℝ) / 2) by norm_num, Real.rpow_neg ha_pos.le]
    ring
  have hint : IntervalIntegrable w volume (1 / 4 : ℝ) 1 :=
    continuousOn_w.intervalIntegrable_of_Icc (by norm_num)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  dsimp [F]
  rw [Real.one_rpow, quarter_rpow_neg_half]
  norm_num

private lemma integral_log_div_four_mul_w :
    ∫ a in (1 / 4 : ℝ)..1, Real.log (a / 4) * w a = 1 - 3 * Real.log 2 := by
  let F : ℝ → ℝ := fun a => -(1 / 2) * a ^ (-(1 / 2 : ℝ)) * (Real.log (a / 4) + 2)
  have hderiv : ∀ a ∈ Set.uIcc (1 / 4 : ℝ) 1,
      HasDerivAt F (Real.log (a / 4) * w a) a := by
    intro a ha
    rw [Set.uIcc_of_le (by norm_num : (1 / 4 : ℝ) ≤ 1)] at ha
    have ha_pos : 0 < a := by linarith [ha.1]
    have h1 : HasDerivAt (fun x : ℝ => -(1 / 2) * x ^ (-(1 / 2 : ℝ))) (w a) a := by
      have hr : HasDerivAt (fun x : ℝ => -(1 / 2) * x ^ (-(1 / 2 : ℝ)))
          (-(1 / 2) * ((-(1 / 2 : ℝ)) * a ^ (-(1 / 2 : ℝ) - 1))) a :=
        (Real.hasDerivAt_rpow_const (p := -(1 / 2 : ℝ)) (Or.inl ha_pos.ne')).const_mul (-(1 / 2))
      have heq : -(1 / 2) * ((-(1 / 2 : ℝ)) * a ^ (-(1 / 2 : ℝ) - 1)) = w a := by
        dsimp [w]
        rw [show (-(1 / 2 : ℝ) - 1 : ℝ) = -((3 : ℝ) / 2) by norm_num, Real.rpow_neg ha_pos.le]
        ring
      rwa [heq] at hr
    have h2 : HasDerivAt (fun x : ℝ => Real.log (x / 4) + 2) (a⁻¹) a := by
      have hdiv : HasDerivAt (fun x : ℝ => x / 4) (1 / 4) a := by
        simpa using (hasDerivAt_id a).div_const 4
      have hlog : HasDerivAt (fun x : ℝ => Real.log (x / 4) + 2) ((1 / 4) / (a / 4)) a :=
        (hdiv.log (by positivity)).add_const (2 : ℝ)
      have heq : (1 / 4 : ℝ) / (a / 4) = a⁻¹ := by field_simp [ha_pos.ne']
      rwa [heq] at hlog
    have hprod := h1.mul h2
    have hpow : a ^ (-(1 / 2 : ℝ)) * a⁻¹ = (a ^ ((3 : ℝ) / 2))⁻¹ := by
      rw [← Real.rpow_neg_one a, ← Real.rpow_add ha_pos, ← Real.rpow_neg ha_pos.le]
      congr 1; norm_num
    have heq : w a * (Real.log (a / 4) + 2) + -(1 / 2) * a ^ (-(1 / 2 : ℝ)) * a⁻¹ =
        Real.log (a / 4) * w a := by
      dsimp [w]
      rw [mul_assoc (-(1 / 2 : ℝ)), hpow]
      ring
    rwa [heq] at hprod
  have hcont : ContinuousOn (fun a => Real.log (a / 4) * w a) (Set.Icc (1 / 4 : ℝ) 1) := by
    refine ContinuousOn.mul ?_ continuousOn_w
    exact ContinuousOn.log (continuousOn_id.div_const 4) fun a ha => by linarith [ha.1]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable_of_Icc (by norm_num))]
  dsimp [F]
  rw [Real.one_rpow, quarter_rpow_neg_half]
  have hlog1 : Real.log ((1 : ℝ) / 4) = -(2 * Real.log 2) := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub,
      show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]
    push_cast; ring
  have hlog2 : Real.log ((1 / 4 : ℝ) / 4) = -(4 * Real.log 2) := by
    rw [show ((1 / 4 : ℝ) / 4) = 1 / (2 : ℝ) ^ (4 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by positivity), Real.log_one, zero_sub, Real.log_pow]
    push_cast; ring
  rw [hlog1, hlog2]
  ring

private lemma continuous_Φ : Continuous Φ := by
  unfold Φ
  exact (continuous_fst.div_const 2).mul (continuous_const.sub (Real.continuous_cos.comp continuous_snd))

/- ### Section 2: Measure properties of `μA`, `μΘ`, and `μ` -/

private lemma μA_univ : μA Set.univ = ENNReal.ofReal (1 / 2) := by
  rw [μA, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Icc (1 / 4 : ℝ) 1)] w := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
    exact w_nonneg (by linarith [ha.1])
  have hint : IntegrableOn w (Set.Icc (1 / 4 : ℝ) 1) volume :=
    continuousOn_w.integrableOn_compact isCompact_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg,
    MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num),
    integral_w]

private lemma μΘ_univ : μΘ Set.univ = 1 := by
  rw [μΘ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    setLIntegral_const, Real.volume_Icc, sub_zero, ← ENNReal.ofReal_mul (by positivity)]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [show (1 / Real.pi) * Real.pi = 1 by field_simp [hpi], ENNReal.ofReal_one]

private instance instIsFiniteMeasure_μA : IsFiniteMeasure μA :=
  ⟨by rw [μA_univ]; exact ENNReal.ofReal_lt_top⟩

private instance instIsProbabilityMeasure_μΘ : IsProbabilityMeasure μΘ :=
  ⟨μΘ_univ⟩

private instance instIsFiniteMeasure_μ : IsFiniteMeasure μ := by
  refine ⟨?_⟩
  rw [μ, Measure.map_apply continuous_Φ.measurable MeasurableSet.univ, Set.preimage_univ,
    ← Set.univ_prod_univ, Measure.prod_prod, μA_univ, μΘ_univ, mul_one]
  exact ENNReal.ofReal_lt_top

private lemma μA_compl_Icc : μA (Set.Icc (1 / 4 : ℝ) 1)ᶜ = 0 := by
  rw [μA, withDensity_apply _ measurableSet_Icc.compl,
    Measure.restrict_restrict measurableSet_Icc.compl, Set.compl_inter_self,
    Measure.restrict_empty, lintegral_zero_measure]

private lemma μΘ_compl_Icc : μΘ (Set.Icc (0 : ℝ) Real.pi)ᶜ = 0 := by
  rw [μΘ, withDensity_apply _ measurableSet_Icc.compl,
    Measure.restrict_restrict measurableSet_Icc.compl, Set.compl_inter_self,
    Measure.restrict_empty, lintegral_zero_measure]

private lemma μ_compl_Icc : μ (Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
  rw [μ, Measure.map_apply continuous_Φ.measurable measurableSet_Icc.compl]
  have hsub : Φ ⁻¹' (Set.Icc (0 : ℝ) 1)ᶜ ⊆
      ((Set.Icc (1 / 4 : ℝ) 1)ᶜ ×ˢ Set.univ) ∪ (Set.univ ×ˢ (Set.Icc (0 : ℝ) Real.pi)ᶜ) := by
    rintro ⟨a, θ⟩ hmem
    by_contra hnot
    simp only [Set.mem_union, Set.mem_prod, Set.mem_compl_iff, Set.mem_univ, and_true, true_and,
      not_or, not_not] at hnot
    rcases hnot with ⟨ha, _hθ⟩
    have hcos1 : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
    have hcos2 : Real.cos θ ≤ 1 := Real.cos_le_one θ
    have hΦ0 : 0 ≤ Φ (a, θ) := by dsimp [Φ]; nlinarith [ha.1]
    have hΦ1 : Φ (a, θ) ≤ 1 := by dsimp [Φ]; nlinarith [ha.1, ha.2]
    exact hmem ⟨hΦ0, hΦ1⟩
  have h1 : (μA.prod μΘ) ((Set.Icc (1 / 4 : ℝ) 1)ᶜ ×ˢ Set.univ) = 0 := by
    rw [Measure.prod_prod, μA_compl_Icc, zero_mul]
  have h2 : (μA.prod μΘ) (Set.univ ×ˢ (Set.Icc (0 : ℝ) Real.pi)ᶜ) = 0 := by
    rw [Measure.prod_prod, μΘ_compl_Icc, mul_zero]
  exact measure_mono_null hsub (measure_union_null h1 h2)

private lemma μ_Icc_zero_one : μ (Set.Icc (0 : ℝ) 1) = ENNReal.ofReal (1 / 2) := by
  have huniv : μ Set.univ = ENNReal.ofReal (1 / 2) := by
    rw [μ, Measure.map_apply continuous_Φ.measurable MeasurableSet.univ, Set.preimage_univ,
      ← Set.univ_prod_univ, Measure.prod_prod, μA_univ, μΘ_univ, mul_one]
  have hadd := measure_add_measure_compl (μ := μ) (s := Set.Icc (0 : ℝ) 1) measurableSet_Icc
  rw [μ_compl_Icc, add_zero, huniv] at hadd
  exact hadd

private lemma integral_μA_eq (g : ℝ → ℝ) :
    ∫ a, g a ∂μA = ∫ a in (1 / 4 : ℝ)..1, g a * w a := by
  rw [μA, integral_withDensity_eq_integral_toReal_smul
    (measurable_w.ennreal_ofReal) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards with a ha
  rw [Set.uIoc_of_le (by norm_num : (1 / 4 : ℝ) ≤ 1)] at ha
  rw [ENNReal.toReal_ofReal (w_nonneg (by linarith [ha.1])), smul_eq_mul, mul_comm]

private lemma integral_μΘ_eq (h : ℝ → ℝ) :
    ∫ θ, h θ ∂μΘ = (1 / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi, h θ := by
  rw [μΘ, integral_withDensity_eq_integral_toReal_smul
    measurable_const (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le Real.pi_pos.le,
    ENNReal.toReal_ofReal (by positivity)]
  simp only [smul_eq_mul, intervalIntegral.integral_const_mul]

private lemma μΘ_Icc_eq {u v : ℝ} (h0 : 0 ≤ u) (hpi : v ≤ Real.pi) :
    μΘ (Set.Icc u v) = ENNReal.ofReal ((v - u) / Real.pi) := by
  rw [μΘ, withDensity_apply _ measurableSet_Icc,
    Measure.restrict_restrict measurableSet_Icc,
    Set.inter_eq_left.mpr (Set.Icc_subset_Icc h0 hpi),
    setLIntegral_const, Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/- ### Section 3: CDF of `μ` on `[0, 1/4]` -/

private lemma cos_ge_iff_le_arccos {u θ : ℝ} (hu : u ∈ Set.Icc (-1 : ℝ) 1)
    (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
    u ≤ Real.cos θ ↔ θ ≤ Real.arccos u := by
  constructor
  · intro h
    have h1 := Real.arccos_le_arccos h
    rwa [Real.arccos_cos hθ.1 hθ.2] at h1
  · intro h
    have h1 := Real.strictAntiOn_cos.antitoneOn
      hθ ⟨Real.arccos_nonneg u, Real.arccos_le_pi u⟩ h
    rwa [Real.cos_arccos hu.1 hu.2] at h1

private lemma cos_le_iff_arccos_le {u θ : ℝ} (hu : u ∈ Set.Icc (-1 : ℝ) 1)
    (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
    Real.cos θ ≤ u ↔ Real.arccos u ≤ θ := by
  constructor
  · intro h
    have h1 := Real.arccos_le_arccos h
    rwa [Real.arccos_cos hθ.1 hθ.2] at h1
  · intro h
    have h1 := Real.strictAntiOn_cos.antitoneOn
      ⟨Real.arccos_nonneg u, Real.arccos_le_pi u⟩ hθ h
    rwa [Real.cos_arccos hu.1 hu.2] at h1

private lemma μ_Icc_zero_t {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (1 / 4)) :
    (μ (Set.Icc (0 : ℝ) t)).toReal =
      ∫ a in (1 / 4 : ℝ)..1, (Real.arccos (1 - 2 * t / a) / Real.pi) * w a := by
  have hmap : μ (Set.Icc (0 : ℝ) t) =
      ∫⁻ a, μΘ (Prod.mk a ⁻¹' (Φ ⁻¹' Set.Icc (0 : ℝ) t)) ∂μA := by
    rw [μ, Measure.map_apply continuous_Φ.measurable measurableSet_Icc,
      Measure.prod_apply (measurableSet_Icc.preimage continuous_Φ.measurable)]
  have hslice : ∀ᵐ a ∂μA,
      μΘ (Prod.mk a ⁻¹' (Φ ⁻¹' Set.Icc (0 : ℝ) t)) =
        ENNReal.ofReal (Real.arccos (1 - 2 * t / a) / Real.pi) := by
    have hae : ∀ᵐ a ∂μA, a ∈ Set.Icc (1 / 4 : ℝ) 1 := by
      rw [ae_iff]; exact μA_compl_Icc
    filter_upwards [hae] with a ha
    have ha_pos : 0 < a := by linarith [ha.1]
    have hu : 1 - 2 * t / a ∈ Set.Icc (-1 : ℝ) 1 := by
      have hdiv_nonneg : 0 ≤ 2 * t / a := div_nonneg (by linarith [ht.1]) ha_pos.le
      have hdiv_le : 2 * t / a ≤ 2 := by
        rw [div_le_iff₀ ha_pos]; linarith [ht.2, ha.1]
      exact ⟨by linarith, by linarith⟩
    have hae_set : (Prod.mk a ⁻¹' (Φ ⁻¹' Set.Icc (0 : ℝ) t)) =ᵐ[μΘ]
        Set.Icc (0 : ℝ) (Real.arccos (1 - 2 * t / a)) := by
      have hθae : ∀ᵐ θ ∂μΘ, θ ∈ Set.Icc (0 : ℝ) Real.pi := by
        rw [ae_iff]; exact μΘ_compl_Icc
      filter_upwards [hθae] with θ hθ
      apply propext
      change (0 ≤ (a / 2) * (1 - Real.cos θ) ∧ (a / 2) * (1 - Real.cos θ) ≤ t) ↔
        (0 ≤ θ ∧ θ ≤ Real.arccos (1 - 2 * t / a))
      have h0 : 0 ≤ (a / 2) * (1 - Real.cos θ) := by
        nlinarith [Real.cos_le_one θ, ha_pos]
      have hle : (a / 2) * (1 - Real.cos θ) ≤ t ↔ 1 - 2 * t / a ≤ Real.cos θ := by
        have : (a / 2) * (1 - Real.cos θ) ≤ t ↔ 1 - Real.cos θ ≤ 2 * t / a := by
          rw [le_div_iff₀ ha_pos]; constructor <;> intro h <;> linarith
        rw [this]; constructor <;> intro h <;> linarith
      rw [hle, cos_ge_iff_le_arccos hu hθ]
      exact ⟨fun h => ⟨hθ.1, h.2⟩, fun h => ⟨h0, h.2⟩⟩
    rw [measure_congr hae_set, μΘ_Icc_eq le_rfl (Real.arccos_le_pi _),
      sub_zero]
  have hcont : ContinuousOn (fun a => (Real.arccos (1 - 2 * t / a) / Real.pi) * w a)
      (Set.Icc (1 / 4 : ℝ) 1) := by
    refine ContinuousOn.mul ?_ continuousOn_w
    refine ContinuousOn.div_const ?_ Real.pi
    exact Real.continuous_arccos.comp_continuousOn
      (continuousOn_const.sub (continuousOn_const.div continuousOn_id fun a ha => by linarith [ha.1]))
  have hint : Integrable (fun a => Real.arccos (1 - 2 * t / a) / Real.pi) μA := by
    rw [μA, integrable_withDensity_iff_integrable_smul₀' (measurable_w.ennreal_ofReal.aemeasurable)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    have heq : (fun a => (ENNReal.ofReal (w a)).toReal • (Real.arccos (1 - 2 * t / a) / Real.pi)) =ᵐ[volume.restrict (Set.Icc (1 / 4 : ℝ) 1)]
        (fun a => (Real.arccos (1 - 2 * t / a) / Real.pi) * w a) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
      rw [ENNReal.toReal_ofReal (w_nonneg (by linarith [ha.1])), smul_eq_mul, mul_comm]
    exact (hcont.integrableOn_compact isCompact_Icc).congr heq.symm
  have hnonneg : 0 ≤ᵐ[μA] fun a => Real.arccos (1 - 2 * t / a) / Real.pi :=
    ae_of_all _ fun a => div_nonneg (Real.arccos_nonneg _) Real.pi_pos.le
  rw [hmap, lintegral_congr_ae hslice,
    ← ofReal_integral_eq_lintegral_ofReal hint hnonneg,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hnonneg), integral_μA_eq]

private lemma μ_Icc_zero_zero : (μ (Set.Icc (0 : ℝ) 0)).toReal = 0 := by
  rw [μ_Icc_zero_t ⟨le_rfl, by norm_num⟩]
  simp [Real.arccos_one]

private lemma μ_cdf_slope {t₁ t₂ : ℝ} (h0 : 0 ≤ t₁) (h12 : t₁ ≤ t₂) (h2 : t₂ ≤ 1 / 4) :
    (t₂ - t₁) / (2 * Real.pi) ≤ (μ (Set.Icc (0 : ℝ) t₂)).toReal - (μ (Set.Icc (0 : ℝ) t₁)).toReal := by
  rw [μ_Icc_zero_t ⟨le_trans h0 h12, h2⟩, μ_Icc_zero_t ⟨h0, le_trans h12 h2⟩]
  have hcont (t : ℝ) : ContinuousOn (fun a => (Real.arccos (1 - 2 * t / a) / Real.pi) * w a)
      (Set.Icc (1 / 4 : ℝ) 1) := by
    refine ContinuousOn.mul ?_ continuousOn_w
    refine ContinuousOn.div_const ?_ Real.pi
    exact Real.continuous_arccos.comp_continuousOn
      (continuousOn_const.sub (continuousOn_const.div continuousOn_id fun a ha => by linarith [ha.1]))
  rw [← intervalIntegral.integral_sub
    ((hcont t₂).intervalIntegrable_of_Icc (by norm_num))
    ((hcont t₁).intervalIntegrable_of_Icc (by norm_num))]
  have hpt : ∀ a ∈ Set.Icc (1 / 4 : ℝ) 1,
      ((2 * (t₂ - t₁)) / Real.pi) * w a ≤
        (Real.arccos (1 - 2 * t₂ / a) / Real.pi) * w a -
          (Real.arccos (1 - 2 * t₁ / a) / Real.pi) * w a := by
    intro a ha
    have ha_pos : 0 < a := by linarith [ha.1]
    set u₁ := 1 - 2 * t₁ / a
    set u₂ := 1 - 2 * t₂ / a
    have hu₁ : u₁ ∈ Set.Icc (-1 : ℝ) 1 := by
      have : 0 ≤ 2 * t₁ / a := div_nonneg (by linarith) ha_pos.le
      have : 2 * t₁ / a ≤ 2 := by rw [div_le_iff₀ ha_pos]; linarith [ha.1]
      exact ⟨by dsimp [u₁]; linarith, by dsimp [u₁]; linarith⟩
    have hu₂ : u₂ ∈ Set.Icc (-1 : ℝ) 1 := by
      have : 0 ≤ 2 * t₂ / a := div_nonneg (by linarith) ha_pos.le
      have : 2 * t₂ / a ≤ 2 := by rw [div_le_iff₀ ha_pos]; linarith [ha.1]
      exact ⟨by dsimp [u₂]; linarith, by dsimp [u₂]; linarith⟩
    have hu_le : u₂ ≤ u₁ := by
      dsimp [u₁, u₂]
      have : 2 * t₁ / a ≤ 2 * t₂ / a := div_le_div_of_nonneg_right (by linarith) ha_pos.le
      linarith
    have harc_le : Real.arccos u₁ ≤ Real.arccos u₂ := Real.arccos_le_arccos hu_le
    have hlip : u₁ - u₂ ≤ Real.arccos u₂ - Real.arccos u₁ := by
      have hcos : |Real.cos (Real.arccos u₁) - Real.cos (Real.arccos u₂)| ≤
          |Real.arccos u₁ - Real.arccos u₂| := by
        simpa [Real.dist_eq] using Real.lipschitzWith_cos.dist_le_mul (Real.arccos u₁) (Real.arccos u₂)
      rw [Real.cos_arccos hu₁.1 hu₁.2, Real.cos_arccos hu₂.1 hu₂.2,
        abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)] at hcos
      linarith
    have hdiff : 2 * (t₂ - t₁) ≤ u₁ - u₂ := by
      have heq : u₁ - u₂ = (2 * (t₂ - t₁)) / a := by dsimp [u₁, u₂]; ring
      rw [heq, le_div_iff₀ ha_pos]
      nlinarith [ha.2]
    have hstep : 2 * (t₂ - t₁) / Real.pi ≤
        Real.arccos u₂ / Real.pi - Real.arccos u₁ / Real.pi := by
      rw [← sub_div]
      exact div_le_div_of_nonneg_right (le_trans hdiff hlip) Real.pi_pos.le
    have hw_nn : 0 ≤ w a := w_nonneg ha_pos.le
    have := mul_le_mul_of_nonneg_right hstep hw_nn
    linarith
  have hmono := intervalIntegral.integral_mono_on (by norm_num : (1 / 4 : ℝ) ≤ 1)
    ((continuousOn_const.mul continuousOn_w).intervalIntegrable_of_Icc (μ := volume) (by norm_num))
    (((hcont t₂).sub (hcont t₁)).intervalIntegrable_of_Icc (μ := volume) (by norm_num))
    hpt
  simp only [Pi.mul_apply, Pi.sub_apply] at hmono
  rw [intervalIntegral.integral_const_mul, integral_w] at hmono
  have hbound : (t₂ - t₁) / (2 * Real.pi) ≤ (2 * (t₂ - t₁) / Real.pi) * (1 / 2) := by
    have hnn : 0 ≤ t₂ - t₁ := by linarith
    have hpi : 0 < Real.pi := Real.pi_pos
    rw [show (2 * (t₂ - t₁) / Real.pi) * (1 / 2) = (t₂ - t₁) / Real.pi by ring]
    rw [div_le_div_iff₀ (by positivity) hpi]
    nlinarith
  exact le_trans hbound hmono

private lemma μ_Icc_zero_quarter_pos : 0 < (μ (Set.Icc (0 : ℝ) (1 / 4))).toReal := by
  have h := μ_cdf_slope (t₁ := 0) (t₂ := 1 / 4) le_rfl (by norm_num) le_rfl
  rw [μ_Icc_zero_zero, sub_zero, sub_zero] at h
  have hpos : (0 : ℝ) < (1 / 4 : ℝ) / (2 * Real.pi) := by positivity
  linarith

private lemma μ_cdf_continuousOn :
    ContinuousOn (fun t : ℝ => (μ (Set.Icc (0 : ℝ) t)).toReal) (Set.Icc (0 : ℝ) (1 / 4)) := by
  have hcont_int : ContinuousOn
      (fun t : ℝ => ∫ a in (1 / 4 : ℝ)..1, (Real.arccos (1 - 2 * t / a) / Real.pi) * w a)
      (Set.Icc (0 : ℝ) (1 / 4)) := by
    intro t₀ ht₀
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    have hcont2 : ContinuousOn
        (fun p : ℝ × ℝ => (Real.arccos (1 - 2 * p.1 / p.2) / Real.pi) * w p.2)
        (Set.Icc (0 : ℝ) (1 / 4) ×ˢ Set.Icc (1 / 4 : ℝ) 1) := by
      refine ContinuousOn.mul ?_ (continuousOn_w.comp continuousOn_snd fun _ hp => hp.2)
      refine ContinuousOn.div_const ?_ Real.pi
      exact Real.continuous_arccos.comp_continuousOn
        (continuousOn_const.sub ((continuousOn_const.mul continuousOn_fst).div continuousOn_snd
          fun p hp => by linarith [hp.2.1]))
    have huc := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hcont2
    rw [Metric.uniformContinuousOn_iff] at huc
    obtain ⟨δ, hδ_pos, hδ⟩ := huc (ε / 2) (by linarith)
    refine ⟨δ, hδ_pos, fun t ht hdist => ?_⟩
    have hcont_t (s : ℝ) : ContinuousOn (fun a => (Real.arccos (1 - 2 * s / a) / Real.pi) * w a)
        (Set.Icc (1 / 4 : ℝ) 1) := by
      refine ContinuousOn.mul ?_ continuousOn_w
      refine ContinuousOn.div_const ?_ Real.pi
      exact Real.continuous_arccos.comp_continuousOn
        (continuousOn_const.sub (continuousOn_const.div continuousOn_id fun a ha => by linarith [ha.1]))
    rw [Real.dist_eq, ← intervalIntegral.integral_sub
      ((hcont_t t).intervalIntegrable_of_Icc (by norm_num))
      ((hcont_t t₀).intervalIntegrable_of_Icc (by norm_num))]
    calc |∫ a in (1 / 4 : ℝ)..1, ((Real.arccos (1 - 2 * t / a) / Real.pi) * w a -
            (Real.arccos (1 - 2 * t₀ / a) / Real.pi) * w a)|
        ≤ ∫ a in (1 / 4 : ℝ)..1, |(Real.arccos (1 - 2 * t / a) / Real.pi) * w a -
            (Real.arccos (1 - 2 * t₀ / a) / Real.pi) * w a| :=
          intervalIntegral.abs_integral_le_integral_abs (by norm_num)
      _ ≤ ∫ _a in (1 / 4 : ℝ)..1, (ε / 2) := by
          refine intervalIntegral.integral_mono_on (by norm_num)
            (((hcont_t t).sub (hcont_t t₀)).abs.intervalIntegrable_of_Icc (by norm_num))
            (continuousOn_const.intervalIntegrable_of_Icc (by norm_num)) fun a ha => ?_
          have hpair : dist (t, a) (t₀, a) < δ := by
            rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
            exact hdist
          have hlt := hδ (t, a) ⟨ht, ha⟩ (t₀, a) ⟨ht₀, ha⟩ hpair
          rw [Real.dist_eq] at hlt
          exact hlt.le
      _ = (3 / 4) * (ε / 2) := by rw [intervalIntegral.integral_const]; norm_num
      _ < ε := by linarith
  exact hcont_int.congr fun t ht => μ_Icc_zero_t ht

/- ### Section 4: Density of `μ` on `[1/4, 1]` via Tonelli -/

private lemma tendsto_setLIntegral_iUnion {s : ℕ → Set ℝ} (hmono : Monotone s)
    (hs : ∀ n, MeasurableSet (s n)) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    Tendsto (fun n => ∫⁻ x in s n, f x ∂volume) atTop (𝓝 (∫⁻ x in ⋃ n, s n, f x ∂volume)) := by
  have h1 : (∫⁻ x in ⋃ n, s n, f x ∂volume) = ⨆ n, ∫⁻ x in s n, f x ∂volume := by
    rw [← lintegral_indicator (MeasurableSet.iUnion hs)]
    have heq : (⋃ n, s n).indicator f = fun x => ⨆ n, (s n).indicator f x := by
      ext x
      by_cases hx : x ∈ ⋃ n, s n
      · rw [Set.indicator_of_mem hx]
        obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
        apply le_antisymm
        · exact le_iSup_of_le k (by rw [Set.indicator_of_mem hk])
        · exact iSup_le fun n => Set.indicator_le_self (s n) f x
      · rw [Set.indicator_of_notMem hx]
        symm
        exact iSup_eq_bot.mpr fun n => by
          rw [Set.indicator_of_notMem (fun hn => hx (Set.mem_iUnion.mpr ⟨n, hn⟩))]
          rfl
    rw [heq, lintegral_iSup (fun n => hf.indicator (hs n))
      (fun m n hmn x => Set.indicator_le_indicator_of_subset (hmono hmn) (fun _ => zero_le) x)]
    congr 1; ext n
    exact lintegral_indicator (hs n) f
  rw [h1]
  exact tendsto_atTop_iSup fun m n hmn => lintegral_mono_set (hmono hmn)

private lemma lintegral_inv_sqrt_prod {x a : ℝ} (hx : 0 < x) (hxa : x < a) :
    ∫⁻ t in Set.Ioo x a, ENNReal.ofReal (1 / Real.sqrt (t * (a - t))) =
      ENNReal.ofReal (Real.pi - Real.arccos (1 - 2 * x / a)) := by
  have ha_pos : 0 < a := lt_trans hx hxa
  let b : ℕ → ℝ := fun n => a - (a - x) / ((n : ℝ) + 2)
  have hb_mono : Monotone b := by
    intro m n hmn
    dsimp [b]
    have hle : (a - x) / ((n : ℝ) + 2) ≤ (a - x) / ((m : ℝ) + 2) :=
      div_le_div_of_nonneg_left (by linarith) (by positivity) (by exact_mod_cast (by omega : m + 2 ≤ n + 2))
    linarith
  have hb_gt : ∀ n, x < b n := by
    intro n; dsimp [b]
    have hlt : (a - x) / ((n : ℝ) + 2) < a - x := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith
    linarith
  have hb_lt : ∀ n, b n < a := by
    intro n; dsimp [b]; have : 0 < (a - x) / ((n : ℝ) + 2) := div_pos (by linarith) (by positivity)
    linarith
  have hb_tendsto : Tendsto b atTop (𝓝 a) := by
    have h0 : Tendsto (fun n : ℕ => (a - x) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa [b] using tendsto_const_nhds.sub h0
  have hunion : (⋃ n : ℕ, Set.Ioc x (b n)) = Set.Ioo x a := by
    ext t; simp only [Set.mem_iUnion, Set.mem_Ioc, Set.mem_Ioo]
    constructor
    · rintro ⟨n, h1, h2⟩; exact ⟨h1, lt_of_le_of_lt h2 (hb_lt n)⟩
    · rintro ⟨h1, h2⟩
      have hev := hb_tendsto.eventually (Ioi_mem_nhds h2)
      obtain ⟨n, hn⟩ := hev.exists
      exact ⟨n, h1, hn.le⟩
  have hstep : ∀ n : ℕ,
      ∫⁻ t in Set.Ioc x (b n), ENNReal.ofReal (1 / Real.sqrt (t * (a - t))) =
        ENNReal.ofReal (Real.arccos (1 - 2 * b n / a) - Real.arccos (1 - 2 * x / a)) := by
    intro n
    have hderiv : ∀ t ∈ Set.uIcc x (b n),
        HasDerivAt (fun s => Real.arccos (1 - 2 * s / a)) (1 / Real.sqrt (t * (a - t))) t := by
      intro t ht
      rw [Set.uIcc_of_le (hb_gt n).le] at ht
      have ht_pos : 0 < t := lt_of_lt_of_le hx ht.1
      have hta_pos : 0 < a - t := by linarith [ht.2, hb_lt n]
      have harg_ne1 : 1 - 2 * t / a ≠ 1 := by
        intro h; have : 2 * t / a = 0 := by linarith
        have : 2 * t = 0 := (div_eq_zero_iff.mp this).resolve_right ha_pos.ne'
        linarith
      have harg_nem1 : 1 - 2 * t / a ≠ -1 := by
        intro h; have : 2 * t / a = 2 := by linarith
        have : 2 * t = 2 * a := (div_eq_iff ha_pos.ne').mp this
        linarith
      have hlin : HasDerivAt (fun s => 1 - 2 * s / a) (-(2 / a)) t := by
        have h1 : HasDerivAt (fun s => 2 * s / a) (2 * 1 / a) t :=
          ((hasDerivAt_id t).const_mul 2).div_const a
        have h2 := h1.const_sub 1
        have heq : -(2 * 1 / a) = -(2 / a) := by ring
        rwa [heq] at h2
      have harc : HasDerivAt (Real.arccos ∘ fun s => 1 - 2 * s / a)
          (-(1 / Real.sqrt (1 - (1 - 2 * t / a) ^ 2)) * -(2 / a)) t :=
        (Real.hasDerivAt_arccos harg_nem1 harg_ne1).comp t hlin
      have hval : -(1 / Real.sqrt (1 - (1 - 2 * t / a) ^ 2)) * -(2 / a) =
          1 / Real.sqrt (t * (a - t)) := by
        have hsq : 1 - (1 - 2 * t / a) ^ 2 = (2 / a) ^ 2 * (t * (a - t)) := by
          field_simp [ha_pos.ne']; ring
        rw [hsq, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
        have hrt_ne : Real.sqrt (t * (a - t)) ≠ 0 := (Real.sqrt_pos.mpr (mul_pos ht_pos hta_pos)).ne'
        field_simp [ha_pos.ne', hrt_ne]
      rw [hval] at harc
      exact harc
    have hcont : ContinuousOn (fun t => 1 / Real.sqrt (t * (a - t))) (Set.Icc x (b n)) := by
      refine continuousOn_const.div ?_ fun t ht => ?_
      · exact Real.continuous_sqrt.comp_continuousOn
          (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
      · have ht_pos : 0 < t := lt_of_lt_of_le hx ht.1
        have hta_pos : 0 < a - t := by linarith [ht.2, hb_lt n]
        exact (Real.sqrt_pos.mpr (mul_pos ht_pos hta_pos)).ne'
    have hint : IntegrableOn (fun t => 1 / Real.sqrt (t * (a - t))) (Set.Ioc x (b n)) volume :=
      (hcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
    have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc x (b n))] (fun t => 1 / Real.sqrt (t * (a - t))) :=
      ae_of_all _ fun _ => by positivity
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg,
      ← intervalIntegral.integral_of_le (hb_gt n).le,
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
        (hcont.intervalIntegrable_of_Icc (hb_gt n).le)]
  have hlim_lhs : Tendsto
      (fun n : ℕ => ∫⁻ t in Set.Ioc x (b n), ENNReal.ofReal (1 / Real.sqrt (t * (a - t))))
      atTop (𝓝 (∫⁻ t in Set.Ioo x a, ENNReal.ofReal (1 / Real.sqrt (t * (a - t))))) := by
    have hmono_set : Monotone (fun n : ℕ => Set.Ioc x (b n)) :=
      fun m n hmn => Set.Ioc_subset_Ioc_right (hb_mono hmn)
    rw [← hunion]
    have hmeas_f : Measurable (fun t => ENNReal.ofReal (1 / Real.sqrt (t * (a - t)))) :=
      ENNReal.measurable_ofReal.comp
        (measurable_const.div (Real.continuous_sqrt.measurable.comp
          (measurable_id.mul (measurable_const.sub measurable_id))))
    exact tendsto_setLIntegral_iUnion hmono_set (fun _ => measurableSet_Ioc) hmeas_f
  have hlim_rhs : Tendsto
      (fun n : ℕ => ENNReal.ofReal (Real.arccos (1 - 2 * b n / a) - Real.arccos (1 - 2 * x / a)))
      atTop (𝓝 (ENNReal.ofReal (Real.pi - Real.arccos (1 - 2 * x / a)))) := by
    refine ENNReal.continuous_ofReal.continuousAt.tendsto.comp ?_
    have h1 : Tendsto (fun n : ℕ => 1 - 2 * b n / a) atTop (𝓝 (-1 : ℝ)) := by
      have h := (hb_tendsto.const_mul 2).div_const a
      have h' := tendsto_const_nhds (x := (1 : ℝ)).sub h
      convert h' using 1
      field_simp [ha_pos.ne']; ring
    have h2 := (Real.continuous_arccos.continuousAt.tendsto.comp h1).sub_const
      (Real.arccos (1 - 2 * x / a))
    rwa [Real.arccos_neg_one] at h2
  simp_rw [hstep] at hlim_lhs
  exact tendsto_nhds_unique hlim_lhs hlim_rhs

private lemma lintegral_inv_a_rpow_sqrt {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∫⁻ a in Set.Ioc t 1, ENNReal.ofReal (1 / (a ^ ((3 : ℝ) / 2) * Real.sqrt (a - t))) =
      ENNReal.ofReal (2 * Real.sqrt (1 - t) / t) := by
  let c : ℕ → ℝ := fun n => t + (1 - t) / ((n : ℝ) + 2)
  have hc_anti : Antitone c := by
    intro m n hmn
    dsimp [c]
    have hle : (1 - t) / ((n : ℝ) + 2) ≤ (1 - t) / ((m : ℝ) + 2) :=
      div_le_div_of_nonneg_left (by linarith) (by positivity)
        (by exact_mod_cast (by omega : m + 2 ≤ n + 2))
    linarith
  have hc_gt : ∀ n, t < c n := by
    intro n; dsimp [c]; have : 0 < (1 - t) / ((n : ℝ) + 2) := div_pos (by linarith) (by positivity)
    linarith
  have hc_lt : ∀ n, c n < 1 := by
    intro n; dsimp [c]
    have hlt : (1 - t) / ((n : ℝ) + 2) < 1 - t := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith
    linarith
  have hc_tendsto : Tendsto c atTop (𝓝 t) := by
    have h0 : Tendsto (fun n : ℕ => (1 - t) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa [c] using tendsto_const_nhds.add h0
  have hunion : (⋃ n : ℕ, Set.Ioc (c n) 1) = Set.Ioc t 1 := by
    ext a; simp only [Set.mem_iUnion, Set.mem_Ioc]
    constructor
    · rintro ⟨n, h1, h2⟩; exact ⟨lt_trans (hc_gt n) h1, h2⟩
    · rintro ⟨h1, h2⟩
      have hev := hc_tendsto.eventually (Iio_mem_nhds h1)
      obtain ⟨n, hn⟩ := hev.exists
      exact ⟨n, hn, h2⟩
  have hstep : ∀ n : ℕ,
      ∫⁻ a in Set.Ioc (c n) 1, ENNReal.ofReal (1 / (a ^ ((3 : ℝ) / 2) * Real.sqrt (a - t))) =
        ENNReal.ofReal (2 * Real.sqrt (1 - t) / t - 2 * Real.sqrt (1 - t / c n) / t) := by
    intro n
    have hderiv : ∀ a ∈ Set.uIcc (c n) 1,
        HasDerivAt (fun s => 2 * Real.sqrt (1 - t / s) / t)
          (1 / (a ^ ((3 : ℝ) / 2) * Real.sqrt (a - t))) a := by
      intro a ha
      rw [Set.uIcc_of_le (hc_lt n).le] at ha
      have ha_pos : 0 < a := lt_of_lt_of_le (lt_trans ht0 (hc_gt n)) ha.1
      have hat_pos : 0 < a - t := by linarith [hc_gt n, ha.1]
      have hsub_pos : 0 < 1 - t / a := by
        rw [sub_pos, div_lt_one ha_pos]; linarith
      have hdiv : HasDerivAt (fun s => 1 - t / s) (t / a ^ 2) a := by
        have hinv : HasDerivAt (fun s => s⁻¹) (-(a ^ 2)⁻¹) a := hasDerivAt_inv ha_pos.ne'
        have hsub : HasDerivAt (fun s => 1 - t * s⁻¹) (-(t * -(a ^ 2)⁻¹)) a :=
          (hinv.const_mul t).const_sub 1
        have hfun : (fun s => 1 - t * s⁻¹) = (fun s => 1 - t / s) := by
          ext s; rw [div_eq_mul_inv]
        have hval : -(t * -(a ^ 2)⁻¹) = t / a ^ 2 := by ring
        rwa [hfun, hval] at hsub
      have hsqrt := hdiv.sqrt hsub_pos.ne'
      have hfull := (hsqrt.const_mul 2).div_const t
      have hval : 2 * (t / a ^ 2 / (2 * Real.sqrt (1 - t / a))) / t =
          1 / (a ^ ((3 : ℝ) / 2) * Real.sqrt (a - t)) := by
        have hsq : 1 - t / a = (a - t) / a := by field_simp [ha_pos.ne']
        rw [hsq, Real.sqrt_div hat_pos.le]
        have hpow : a ^ ((3 : ℝ) / 2) = a * Real.sqrt a := by
          rw [show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num, Real.rpow_add ha_pos, Real.rpow_one,
            Real.sqrt_eq_rpow]
        rw [hpow]
        have hra : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha_pos).ne'
        have hrat : Real.sqrt (a - t) ≠ 0 := (Real.sqrt_pos.mpr hat_pos).ne'
        have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha_pos.le
        field_simp [ht0.ne', ha_pos.ne', hra, hrat]
        nlinarith [hsa]
      rwa [hval] at hfull
    have hcont : ContinuousOn (fun a => 1 / (a ^ ((3 : ℝ) / 2) * Real.sqrt (a - t)))
        (Set.Icc (c n) 1) := by
      refine continuousOn_const.div (ContinuousOn.mul ?_ ?_) fun a ha => ?_
      · exact ContinuousOn.rpow_const continuousOn_id fun a ha =>
          Or.inl (lt_of_lt_of_le (lt_trans ht0 (hc_gt n)) ha.1).ne'
      · exact Real.continuous_sqrt.comp_continuousOn (continuousOn_id.sub continuousOn_const)
      · have ha_pos : 0 < a := lt_of_lt_of_le (lt_trans ht0 (hc_gt n)) ha.1
        have hat_pos : 0 < a - t := by linarith [hc_gt n, ha.1]
        positivity
    have hint : IntegrableOn (fun a => 1 / (a ^ ((3 : ℝ) / 2) * Real.sqrt (a - t)))
        (Set.Ioc (c n) 1) volume :=
      (hcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
    have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc (c n) 1)]
        (fun a => 1 / (a ^ ((3 : ℝ) / 2) * Real.sqrt (a - t))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
      have ha_pos : 0 < a := lt_trans (lt_trans ht0 (hc_gt n)) ha.1
      positivity
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg,
      ← intervalIntegral.integral_of_le (hc_lt n).le,
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
        (hcont.intervalIntegrable_of_Icc (hc_lt n).le)]
    simp
  have hlim_lhs : Tendsto
      (fun n : ℕ => ∫⁻ a in Set.Ioc (c n) 1,
        ENNReal.ofReal (1 / (a ^ ((3 : ℝ) / 2) * Real.sqrt (a - t))))
      atTop (𝓝 (∫⁻ a in Set.Ioc t 1,
        ENNReal.ofReal (1 / (a ^ ((3 : ℝ) / 2) * Real.sqrt (a - t))))) := by
    have hmono_set : Monotone (fun n : ℕ => Set.Ioc (c n) 1) :=
      fun m n hmn => Set.Ioc_subset_Ioc_left (hc_anti hmn)
    rw [← hunion]
    have hmeas_f : Measurable (fun a => ENNReal.ofReal (1 / (a ^ ((3 : ℝ) / 2) * Real.sqrt (a - t)))) :=
      ENNReal.measurable_ofReal.comp
        (measurable_const.div ((measurable_id.pow_const _).mul
          (Real.continuous_sqrt.measurable.comp (measurable_id.sub measurable_const))))
    exact tendsto_setLIntegral_iUnion hmono_set (fun _ => measurableSet_Ioc) hmeas_f
  have hlim_rhs : Tendsto
      (fun n : ℕ => ENNReal.ofReal (2 * Real.sqrt (1 - t) / t - 2 * Real.sqrt (1 - t / c n) / t))
      atTop (𝓝 (ENNReal.ofReal (2 * Real.sqrt (1 - t) / t))) := by
    refine ENNReal.continuous_ofReal.continuousAt.tendsto.comp ?_
    have h1 : Tendsto (fun n : ℕ => 1 - t / c n) atTop (𝓝 (0 : ℝ)) := by
      have hdiv : Tendsto (fun n : ℕ => t / c n) atTop (𝓝 (t / t)) :=
        tendsto_const_nhds.div hc_tendsto ht0.ne'
      rw [div_self ht0.ne'] at hdiv
      simpa using tendsto_const_nhds (x := (1 : ℝ)).sub hdiv
    have h2 : Tendsto (fun n : ℕ => 2 * Real.sqrt (1 - t / c n) / t) atTop (𝓝 0) := by
      have hsq := Real.continuous_sqrt.continuousAt.tendsto.comp h1
      rw [Real.sqrt_zero] at hsq
      simpa using (hsq.const_mul 2).div_const t
    simpa using tendsto_const_nhds.sub h2
  simp_rw [hstep] at hlim_lhs
  exact tendsto_nhds_unique hlim_lhs hlim_rhs

private noncomputable def νRight : Measure ℝ :=
  (volume.restrict (Set.Icc (1 / 4 : ℝ) 1)).withDensity (fun t => ENNReal.ofReal (ρRight t))

private lemma measurable_ρRight : Measurable ρRight := by
  unfold ρRight
  exact (Real.continuous_sqrt.measurable.comp (measurable_const.sub measurable_id)).div
    (measurable_const.mul (measurable_id.pow_const _))

private lemma continuousOn_ρRight : ContinuousOn ρRight (Set.Icc (1 / 4 : ℝ) 1) := by
  unfold ρRight
  refine ContinuousOn.div ?_ (continuousOn_const.mul ?_) fun t ht => ?_
  · exact Real.continuous_sqrt.comp_continuousOn (continuousOn_const.sub continuousOn_id)
  · exact ContinuousOn.rpow_const continuousOn_id fun t ht => Or.inl (by linarith [ht.1])
  · have ht_pos : 0 < t := by linarith [ht.1]
    positivity

private lemma μ_Icc_x_one {x : ℝ} (hx : x ∈ Set.Icc (1 / 4 : ℝ) 1) :
    μ (Set.Icc x 1) = νRight (Set.Icc x 1) := by
  have hx_pos : 0 < x := by linarith [hx.1]
  have hLHS : μ (Set.Icc x 1) =
      ∫⁻ a in Set.Ioo x 1,
        ENNReal.ofReal (((Real.pi - Real.arccos (1 - 2 * x / a)) / Real.pi) * w a) := by
    rw [μ, Measure.map_apply continuous_Φ.measurable measurableSet_Icc,
      Measure.prod_apply (measurableSet_Icc.preimage continuous_Φ.measurable)]
    have hslice : ∀ᵐ a ∂μA,
        μΘ (Prod.mk a ⁻¹' (Φ ⁻¹' Set.Icc x 1)) =
          (Set.Ioo x 1).indicator
            (fun a => ENNReal.ofReal ((Real.pi - Real.arccos (1 - 2 * x / a)) / Real.pi)) a := by
      have hae1 : ∀ᵐ a ∂μA, a ∈ Set.Icc (1 / 4 : ℝ) 1 := by rw [ae_iff]; exact μA_compl_Icc
      have hsing_x : μA {x} = 0 := by
        rw [μA, withDensity_apply _ (measurableSet_singleton x),
          Measure.restrict_restrict (measurableSet_singleton x)]
        exact setLIntegral_measure_zero _ _ (measure_mono_null Set.inter_subset_left Real.volume_singleton)
      have hsing_1 : μA {1} = 0 := by
        rw [μA, withDensity_apply _ (measurableSet_singleton 1),
          Measure.restrict_restrict (measurableSet_singleton 1)]
        exact setLIntegral_measure_zero _ _ (measure_mono_null Set.inter_subset_left Real.volume_singleton)
      have hae_ne : ∀ᵐ a ∂μA, a ≠ x ∧ a ≠ 1 := by
        rw [ae_iff]
        have hsub : {a : ℝ | ¬ (a ≠ x ∧ a ≠ 1)} ⊆ {x} ∪ {1} := by
          intro a ha; simp only [Set.mem_ofPred_eq, not_and_or, not_not] at ha; exact ha
        exact measure_mono_null hsub (measure_union_null hsing_x hsing_1)
      filter_upwards [hae1, hae_ne] with a ha ⟨hax, ha1⟩
      by_cases hxa : x < a
      · have ha_oo : a ∈ Set.Ioo x 1 := ⟨hxa, lt_of_le_of_ne ha.2 ha1⟩
        rw [Set.indicator_of_mem ha_oo]
        have ha_pos : 0 < a := lt_trans hx_pos hxa
        have hu : 1 - 2 * x / a ∈ Set.Icc (-1 : ℝ) 1 := by
          have h1 : 0 ≤ 2 * x / a := by positivity
          have h2 : 2 * x / a ≤ 2 := by rw [div_le_iff₀ ha_pos]; linarith
          exact ⟨by linarith, by linarith⟩
        have hae_set : (Prod.mk a ⁻¹' (Φ ⁻¹' Set.Icc x 1)) =ᵐ[μΘ]
            Set.Icc (Real.arccos (1 - 2 * x / a)) Real.pi := by
          have hθae : ∀ᵐ θ ∂μΘ, θ ∈ Set.Icc (0 : ℝ) Real.pi := by rw [ae_iff]; exact μΘ_compl_Icc
          filter_upwards [hθae] with θ hθ
          apply propext
          change (x ≤ (a / 2) * (1 - Real.cos θ) ∧ (a / 2) * (1 - Real.cos θ) ≤ 1) ↔
            (Real.arccos (1 - 2 * x / a) ≤ θ ∧ θ ≤ Real.pi)
          have hle1 : (a / 2) * (1 - Real.cos θ) ≤ 1 := by
            nlinarith [Real.neg_one_le_cos θ, Real.cos_le_one θ, ha.1, ha.2]
          have hge : x ≤ (a / 2) * (1 - Real.cos θ) ↔ Real.cos θ ≤ 1 - 2 * x / a := by
            have : x ≤ (a / 2) * (1 - Real.cos θ) ↔ 2 * x / a ≤ 1 - Real.cos θ := by
              rw [div_le_iff₀ ha_pos]; constructor <;> intro h <;> linarith
            rw [this]; constructor <;> intro h <;> linarith
          rw [hge, cos_le_iff_arccos_le hu hθ]
          exact ⟨fun h => ⟨h.1, hθ.2⟩, fun h => ⟨h.1, hle1⟩⟩
        rw [measure_congr hae_set, μΘ_Icc_eq (Real.arccos_nonneg _) le_rfl]
      · have hnot : a ∉ Set.Ioo x 1 := fun h => hxa h.1
        rw [Set.indicator_of_notMem hnot]
        have hlt : a < x := lt_of_le_of_ne (not_lt.mp hxa) hax
        have hempty : (Prod.mk a ⁻¹' (Φ ⁻¹' Set.Icc x 1)) = ∅ := by
          ext θ; simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_empty_iff_false, iff_false]
          rintro ⟨h1, _⟩
          have hle : Φ (a, θ) ≤ a := by
            dsimp [Φ]; nlinarith [Real.neg_one_le_cos θ, Real.cos_le_one θ, ha.1]
          linarith
        rw [hempty, measure_empty]
    have hmeas_ind : Measurable ((Set.Ioo x 1).indicator
        (fun a => ENNReal.ofReal ((Real.pi - Real.arccos (1 - 2 * x / a)) / Real.pi))) :=
      (ENNReal.measurable_ofReal.comp
        ((measurable_const.sub (Real.continuous_arccos.measurable.comp
          (measurable_const.sub (measurable_const.div measurable_id)))).div_const _)).indicator
        measurableSet_Ioo
    rw [lintegral_congr_ae hslice, μA,
      lintegral_withDensity_eq_lintegral_mul _ measurable_w.ennreal_ofReal hmeas_ind]
    have hmul_ind :
        ((fun a => ENNReal.ofReal (w a)) *
          (Set.Ioo x 1).indicator (fun a => ENNReal.ofReal ((Real.pi - Real.arccos (1 - 2 * x / a)) / Real.pi))) =
        (Set.Ioo x 1).indicator (fun a =>
          ENNReal.ofReal (((Real.pi - Real.arccos (1 - 2 * x / a)) / Real.pi) * w a)) := by
      ext a
      by_cases ha : a ∈ Set.Ioo x 1
      · simp only [Pi.mul_apply, Set.indicator_of_mem ha]
        rw [← ENNReal.ofReal_mul (w_nonneg (lt_trans hx_pos ha.1).le), mul_comm]
      · simp only [Pi.mul_apply, Set.indicator_of_notMem ha, mul_zero]
    rw [hmul_ind, lintegral_indicator measurableSet_Ioo,
      Measure.restrict_restrict measurableSet_Ioo,
      Set.inter_eq_left.mpr (Set.Ioo_subset_Icc_self.trans (Set.Icc_subset_Icc hx.1 le_rfl))]
  have hRHS : νRight (Set.Icc x 1) =
      ∫⁻ t in Set.Ioo x 1, ENNReal.ofReal (ρRight t) := by
    rw [νRight, withDensity_apply _ measurableSet_Icc,
      Measure.restrict_restrict measurableSet_Icc,
      Set.inter_eq_left.mpr (Set.Icc_subset_Icc hx.1 le_rfl)]
    exact setLIntegral_congr Ioo_ae_eq_Icc.symm
  rw [hLHS, hRHS]
  let K : ℝ × ℝ → ℝ≥0∞ := fun p =>
    if x < p.1 ∧ p.1 < p.2 ∧ p.2 < 1 then
      ENNReal.ofReal (1 / (4 * Real.pi * p.2 ^ ((3 : ℝ) / 2) * Real.sqrt (p.1 * (p.2 - p.1))))
    else 0
  have hK_meas : Measurable K := by
    let S : Set (ℝ × ℝ) :=
      {p | x < p.1} ∩ ({p | p.1 < p.2} ∩ {p | p.2 < 1})
    have hS : MeasurableSet S :=
      (measurableSet_lt measurable_const measurable_fst).inter
        ((measurableSet_lt measurable_fst measurable_snd).inter
          (measurableSet_lt measurable_snd measurable_const))
    have hf : Measurable fun p : ℝ × ℝ =>
        ENNReal.ofReal (1 / (4 * Real.pi * p.2 ^ ((3 : ℝ) / 2) * Real.sqrt (p.1 * (p.2 - p.1)))) := by
      refine ENNReal.measurable_ofReal.comp ?_
      refine measurable_const.div (Measurable.mul ?_ ?_)
      · exact measurable_const.mul (measurable_snd.pow_const _)
      · exact Real.continuous_sqrt.measurable.comp
          (measurable_fst.mul (measurable_snd.sub measurable_fst))
    have heq : K = S.indicator (fun p : ℝ × ℝ =>
        ENNReal.ofReal (1 / (4 * Real.pi * p.2 ^ ((3 : ℝ) / 2) * Real.sqrt (p.1 * (p.2 - p.1))))) := by
      ext ⟨t, a⟩; simp [K, S, Set.indicator]
    rw [heq]
    exact hf.indicator hS
  have htonelli : (∫⁻ a, ∫⁻ t, K (t, a) ∂volume ∂volume) = ∫⁻ t, ∫⁻ a, K (t, a) ∂volume ∂volume := by
    rw [← lintegral_prod_symm K hK_meas.aemeasurable, lintegral_prod K hK_meas.aemeasurable]
  have horder1 : (∫⁻ a, ∫⁻ t, K (t, a) ∂volume ∂volume) =
      ∫⁻ a in Set.Ioo x 1,
        ENNReal.ofReal (((Real.pi - Real.arccos (1 - 2 * x / a)) / Real.pi) * w a) := by
    rw [← lintegral_indicator measurableSet_Ioo]
    refine lintegral_congr fun a => ?_
    by_cases ha : a ∈ Set.Ioo x 1
    · rw [Set.indicator_of_mem ha]
      have ha_pos : 0 < a := lt_trans hx_pos ha.1
      have hinner : (fun t => K (t, a)) =
          (Set.Ioo x a).indicator (fun t =>
            ENNReal.ofReal (w a / Real.pi) * ENNReal.ofReal (1 / Real.sqrt (t * (a - t)))) := by
        ext t
        by_cases ht : t ∈ Set.Ioo x a
        · rw [Set.indicator_of_mem ht]
          simp only [K, ht.1, ht.2, ha.2, and_self, ↓reduceIte]
          rw [← ENNReal.ofReal_mul (by dsimp [w]; positivity)]
          congr 1; dsimp [w]; ring
        · rw [Set.indicator_of_notMem ht]
          simp only [K, Set.mem_Ioo, not_and_or] at ht ⊢
          split_ifs with h
          · rcases ht with h1 | h2
            · exact absurd h.1 h1
            · exact absurd h.2.1 h2
          · rfl
      have hmeas_t : Measurable (fun t => ENNReal.ofReal (1 / Real.sqrt (t * (a - t)))) :=
        ENNReal.measurable_ofReal.comp
          (measurable_const.div (Real.continuous_sqrt.measurable.comp
            (measurable_id.mul (measurable_const.sub measurable_id))))
      rw [hinner, lintegral_indicator measurableSet_Ioo, lintegral_const_mul _ hmeas_t,
        lintegral_inv_sqrt_prod hx_pos ha.1, ← ENNReal.ofReal_mul (by dsimp [w]; positivity)]
      congr 1; ring
    · rw [Set.indicator_of_notMem ha]
      have hzero : ∀ t, K (t, a) = 0 := by
        intro t; simp only [K, ite_eq_right_iff]
        rintro ⟨h1, h2, h3⟩
        exact absurd ⟨lt_trans h1 h2, h3⟩ ha
      simp [hzero]
  have horder2 : (∫⁻ t, ∫⁻ a, K (t, a) ∂volume ∂volume) =
      ∫⁻ t in Set.Ioo x 1, ENNReal.ofReal (ρRight t) := by
    rw [← lintegral_indicator measurableSet_Ioo]
    refine lintegral_congr fun t => ?_
    by_cases ht : t ∈ Set.Ioo x 1
    · rw [Set.indicator_of_mem ht]
      have ht_pos : 0 < t := lt_trans hx_pos ht.1
      have hinner : (fun a => K (t, a)) =
          (Set.Ioo t 1).indicator (fun a =>
            ENNReal.ofReal (1 / (4 * Real.pi * Real.sqrt t)) *
              ENNReal.ofReal (1 / (a ^ ((3 : ℝ) / 2) * Real.sqrt (a - t)))) := by
        ext a
        by_cases ha : a ∈ Set.Ioo t 1
        · rw [Set.indicator_of_mem ha]
          simp only [K, ht.1, ha.1, ha.2, and_self, ↓reduceIte]
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [Real.sqrt_mul ht_pos.le]
          ring
        · rw [Set.indicator_of_notMem ha]
          simp only [K, Set.mem_Ioo, not_and_or] at ha ⊢
          split_ifs with h
          · rcases ha with h1 | h2
            · exact absurd h.2.1 h1
            · exact absurd h.2.2 h2
          · rfl
      have hIoo_eq_Ioc :
          ∫⁻ a in Set.Ioo t 1, ENNReal.ofReal (1 / (a ^ ((3 : ℝ) / 2) * Real.sqrt (a - t))) =
          ∫⁻ a in Set.Ioc t 1, ENNReal.ofReal (1 / (a ^ ((3 : ℝ) / 2) * Real.sqrt (a - t))) :=
        setLIntegral_congr Ioo_ae_eq_Ioc
      have hmeas_a : Measurable (fun a => ENNReal.ofReal (1 / (a ^ ((3 : ℝ) / 2) * Real.sqrt (a - t)))) :=
        ENNReal.measurable_ofReal.comp
          (measurable_const.div ((measurable_id.pow_const _).mul
            (Real.continuous_sqrt.measurable.comp (measurable_id.sub measurable_const))))
      rw [hinner, lintegral_indicator measurableSet_Ioo, lintegral_const_mul _ hmeas_a,
        hIoo_eq_Ioc, lintegral_inv_a_rpow_sqrt ht_pos ht.2, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      dsimp [ρRight]
      have hpow : t ^ ((3 : ℝ) / 2) = t * Real.sqrt t := by
        rw [show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num, Real.rpow_add ht_pos, Real.rpow_one,
          Real.sqrt_eq_rpow]
      rw [hpow]
      have hrt : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht_pos).ne'
      field_simp [Real.pi_ne_zero, ht_pos.ne', hrt]
      ring
    · rw [Set.indicator_of_notMem ht]
      have hzero : ∀ a, K (t, a) = 0 := by
        intro a; simp only [K, ite_eq_right_iff]
        rintro ⟨h1, h2, h3⟩
        exact absurd ⟨h1, lt_trans h2 h3⟩ ht
      simp [hzero]
  rw [← horder1, htonelli, horder2]

private lemma μ_singleton_right {x : ℝ} (hx : x ∈ Set.Icc (1 / 4 : ℝ) 1) :
    μ {x} = 0 := by
  have hx_pos : 0 < x := by linarith [hx.1]
  rw [μ, Measure.map_apply continuous_Φ.measurable (measurableSet_singleton x),
    Measure.prod_apply ((measurableSet_singleton x).preimage continuous_Φ.measurable)]
  have hzero : ∀ᵐ a ∂μA, μΘ (Prod.mk a ⁻¹' (Φ ⁻¹' {x})) = 0 := by
    have hae : ∀ᵐ a ∂μA, a ∈ Set.Icc (1 / 4 : ℝ) 1 := by rw [ae_iff]; exact μA_compl_Icc
    filter_upwards [hae] with a ha
    have ha_pos : 0 < a := by linarith [ha.1]
    by_cases hxa : x ≤ a
    · have hu : 1 - 2 * x / a ∈ Set.Icc (-1 : ℝ) 1 := by
        have h1 : 0 ≤ 2 * x / a := by positivity
        have h2 : 2 * x / a ≤ 2 := by rw [div_le_iff₀ ha_pos]; linarith
        exact ⟨by linarith, by linarith⟩
      have hsub : (Prod.mk a ⁻¹' (Φ ⁻¹' {x})) ∩ Set.Icc (0 : ℝ) Real.pi ⊆
          {Real.arccos (1 - 2 * x / a)} := by
        rintro θ ⟨hΦ, hθ⟩
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Φ] at hΦ ⊢
        have hcos : Real.cos θ = 1 - 2 * x / a := by
          have : a * (1 - Real.cos θ) = 2 * x := by linarith
          field_simp [ha_pos.ne']; linarith
        rw [← hcos, Real.arccos_cos hθ.1 hθ.2]
      have hsing : μΘ {Real.arccos (1 - 2 * x / a)} = 0 := by
        rw [μΘ, withDensity_apply _ (measurableSet_singleton _),
          Measure.restrict_restrict (measurableSet_singleton _)]
        exact setLIntegral_measure_zero _ _ (measure_mono_null Set.inter_subset_left Real.volume_singleton)
      have hae_le : μΘ (Prod.mk a ⁻¹' (Φ ⁻¹' {x})) ≤ μΘ {Real.arccos (1 - 2 * x / a)} := by
        calc μΘ (Prod.mk a ⁻¹' (Φ ⁻¹' {x}))
            ≤ μΘ (((Prod.mk a ⁻¹' (Φ ⁻¹' {x})) ∩ Set.Icc (0 : ℝ) Real.pi) ∪
                (Set.Icc (0 : ℝ) Real.pi)ᶜ) :=
              measure_mono (fun θ hθ => by
                by_cases h : θ ∈ Set.Icc (0 : ℝ) Real.pi
                · exact Or.inl ⟨hθ, h⟩
                · exact Or.inr h)
          _ ≤ μΘ ((Prod.mk a ⁻¹' (Φ ⁻¹' {x})) ∩ Set.Icc (0 : ℝ) Real.pi) +
                μΘ (Set.Icc (0 : ℝ) Real.pi)ᶜ := measure_union_le _ _
          _ ≤ μΘ {Real.arccos (1 - 2 * x / a)} + 0 := by
              rw [μΘ_compl_Icc]; exact add_le_add (measure_mono hsub) le_rfl
          _ = μΘ {Real.arccos (1 - 2 * x / a)} := add_zero _
      exact le_antisymm (hae_le.trans hsing.le) zero_le
    · have hempty : Prod.mk a ⁻¹' (Φ ⁻¹' {x}) = ∅ := by
        ext θ; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        intro hΦ
        have hle : Φ (a, θ) ≤ a := by
          dsimp [Φ]; nlinarith [Real.neg_one_le_cos θ, Real.cos_le_one θ, ha.1]
        linarith
      rw [hempty, measure_empty]
  rw [lintegral_congr_ae hzero, lintegral_zero]

private lemma μ_restrict_right_eq : μ.restrict (Set.Icc (1 / 4 : ℝ) 1) = νRight := by
  have hfin_right : IsFiniteMeasure νRight := by
    refine ⟨?_⟩
    rw [νRight, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    have hint : IntegrableOn ρRight (Set.Icc (1 / 4 : ℝ) 1) volume :=
      continuousOn_ρRight.integrableOn_compact isCompact_Icc
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc (1 / 4 : ℝ) 1)] ρRight := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      dsimp [ρRight]
      have ht_pos : 0 < t := by linarith [ht.1]
      positivity
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
    exact ENNReal.ofReal_lt_top
  have hIoc_eq : ∀ u v : ℝ, u < v →
      (μ.restrict (Set.Icc (1 / 4 : ℝ) 1)) (Set.Ioc u v) = νRight (Set.Ioc u v) := by
    intro u v huv
    have hν_compl : νRight (Set.Icc (1 / 4 : ℝ) 1)ᶜ = 0 := by
      rw [νRight, withDensity_apply _ measurableSet_Icc.compl,
        Measure.restrict_restrict measurableSet_Icc.compl, Set.compl_inter_self,
        Measure.restrict_empty, lintegral_zero_measure]
    have hν_eq : νRight (Set.Ioc u v) = νRight (Set.Ioc u v ∩ Set.Icc (1 / 4 : ℝ) 1) := by
      have h1 := measure_inter_add_sdiff (μ := νRight) (Set.Ioc u v)
        (t := Set.Icc (1 / 4 : ℝ) 1) measurableSet_Icc
      have hdiff : νRight (Set.Ioc u v \ Set.Icc (1 / 4 : ℝ) 1) = 0 :=
        measure_mono_null (fun x hx => hx.2) hν_compl
      rw [hdiff, add_zero] at h1
      exact h1.symm
    rw [Measure.restrict_apply measurableSet_Ioc, hν_eq]
    by_cases hle : v ≤ 1 / 4 ∨ 1 ≤ u
    · rcases hle with hv | hu
      · have hsub : Set.Ioc u v ∩ Set.Icc (1 / 4 : ℝ) 1 ⊆ {(1 / 4 : ℝ)} := by
          rintro x ⟨⟨_, hxv⟩, ⟨hx1, _⟩⟩; simp only [Set.mem_singleton_iff]; linarith
        have h1 : μ (Set.Ioc u v ∩ Set.Icc (1 / 4 : ℝ) 1) = 0 :=
          measure_mono_null hsub (μ_singleton_right ⟨le_rfl, by norm_num⟩)
        have h2 : νRight (Set.Ioc u v ∩ Set.Icc (1 / 4 : ℝ) 1) = 0 := by
          refine measure_mono_null hsub ?_
          rw [νRight, withDensity_apply _ (measurableSet_singleton _),
            Measure.restrict_restrict (measurableSet_singleton _)]
          exact setLIntegral_measure_zero _ _ (measure_mono_null Set.inter_subset_left Real.volume_singleton)
        rw [h1, h2]
      · have hempty : Set.Ioc u v ∩ Set.Icc (1 / 4 : ℝ) 1 = ∅ := by
          ext x; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Icc, Set.mem_empty_iff_false,
            iff_false]; intro h; linarith
        rw [hempty, measure_empty, measure_empty]
    · push Not at hle
      rcases hle with ⟨hv_gt, hu_lt⟩
      let a := max u (1 / 4 : ℝ)
      let b := min v 1
      have ha_mem : a ∈ Set.Icc (1 / 4 : ℝ) 1 := ⟨le_max_right _ _, max_le hu_lt.le (by norm_num)⟩
      have hb_mem : b ∈ Set.Icc (1 / 4 : ℝ) 1 := ⟨le_min hv_gt.le (by norm_num), min_le_right _ _⟩
      have hab : a ≤ b := max_le (le_min huv.le hu_lt.le) (le_min hv_gt.le (by norm_num))
      have hset_eq : Set.Ioc u v ∩ Set.Icc (1 / 4 : ℝ) 1 =
          if u < 1 / 4 then Set.Icc a b else Set.Ioc a b := by
        split_ifs with hu14
        · ext x; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Icc, a, b, max_le_iff,
            le_min_iff]
          constructor
          · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩; exact ⟨⟨by linarith, h3⟩, ⟨h2, h4⟩⟩
          · rintro ⟨⟨_, h3⟩, ⟨h2, h4⟩⟩; exact ⟨⟨by linarith, h2⟩, ⟨h3, h4⟩⟩
        · ext x; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Icc, a, b, max_lt_iff,
            le_min_iff]
          constructor
          · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩; exact ⟨⟨h1, by linarith⟩, ⟨h2, h4⟩⟩
          · rintro ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩; exact ⟨⟨h1, h2⟩, ⟨h3.le, h4⟩⟩
      have hIco_eq : ∀ (M : Measure ℝ) [IsFiniteMeasure M],
          (∀ y ∈ Set.Icc (1 / 4 : ℝ) 1, M {y} = 0) →
          M (Set.Ico a b) + M (Set.Icc b 1) = M (Set.Icc a 1) := by
        intro M _ _
        have hdisj : Disjoint (Set.Ico a b) (Set.Icc b 1) :=
          Set.disjoint_left.mpr fun x h1 h2 => not_lt_of_ge h2.1 h1.2
        have hunion : Set.Ico a b ∪ Set.Icc b 1 = Set.Icc a 1 :=
          Set.Ico_union_Icc_eq_Icc hab hb_mem.2
        rw [← measure_union hdisj measurableSet_Icc, hunion]
      have hν_sing : ∀ y ∈ Set.Icc (1 / 4 : ℝ) 1, νRight {y} = 0 := by
        intro y _
        rw [νRight, withDensity_apply _ (measurableSet_singleton _),
          Measure.restrict_restrict (measurableSet_singleton _)]
        exact setLIntegral_measure_zero _ _ (measure_mono_null Set.inter_subset_left Real.volume_singleton)
      have hIco : μ (Set.Ico a b) = νRight (Set.Ico a b) := by
        have h1 := hIco_eq μ (fun y hy => μ_singleton_right hy)
        have h2 := hIco_eq νRight hν_sing
        rw [μ_Icc_x_one ha_mem, μ_Icc_x_one hb_mem] at h1
        exact (ENNReal.add_left_inj (measure_ne_top νRight _)).mp (h1.trans h2.symm)
      have hIcc_eq_Ico : ∀ (M : Measure ℝ), M {b} = 0 → M (Set.Icc a b) = M (Set.Ico a b) := by
        intro M hb0
        have hunion : Set.Ico a b ∪ {b} = Set.Icc a b := Set.Ico_union_right hab
        have hdisj : Disjoint (Set.Ico a b) {b} :=
          Set.disjoint_singleton_right.mpr fun h => lt_irrefl b h.2
        rw [← hunion, measure_union hdisj (measurableSet_singleton b), hb0, add_zero]
      have hIoc_eq_Ico : ∀ (M : Measure ℝ), M {a} = 0 → M {b} = 0 → M (Set.Ioc a b) = M (Set.Ico a b) := by
        intro M ha0 hb0
        have h1 : M (Set.Icc a b) = M (Set.Ico a b) := hIcc_eq_Ico M hb0
        have hunion : {a} ∪ Set.Ioc a b = Set.Icc a b := by
          ext z; simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_Ioc, Set.mem_Icc]
          constructor
          · rintro (rfl | ⟨h1, h2⟩)
            · exact ⟨le_rfl, hab⟩
            · exact ⟨h1.le, h2⟩
          · rintro ⟨h1, h2⟩
            rcases eq_or_lt_of_le h1 with rfl | hlt
            · exact Or.inl rfl
            · exact Or.inr ⟨hlt, h2⟩
        have hdisj : Disjoint ({a} : Set ℝ) (Set.Ioc a b) :=
          Set.disjoint_singleton_left.mpr fun h => lt_irrefl a h.1
        rw [← hunion, measure_union hdisj measurableSet_Ioc, ha0, zero_add] at h1
        exact h1
      rw [hset_eq]
      split_ifs
      · rw [hIcc_eq_Ico μ (μ_singleton_right hb_mem), hIcc_eq_Ico νRight (hν_sing b hb_mem), hIco]
      · rw [hIoc_eq_Ico μ (μ_singleton_right ha_mem) (μ_singleton_right hb_mem),
          hIoc_eq_Ico νRight (hν_sing a ha_mem) (hν_sing b hb_mem), hIco]
  exact Measure.ext_of_Ioc (μ.restrict (Set.Icc (1 / 4 : ℝ) 1)) νRight hIoc_eq

private lemma integral_μ_right (f : ℝ → ℝ) (_hf : Continuous f) :
    ∫ t in Set.Icc (1 / 4 : ℝ) 1, f t ∂μ =
      ∫ t in (1 / 4 : ℝ)..1, f t * (Real.sqrt (1 - t) / (2 * Real.pi * t ^ ((3 : ℝ) / 2))) := by
  rw [μ_restrict_right_eq, νRight,
    integral_withDensity_eq_integral_toReal_smul measurable_ρRight.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards with t ht
  rw [Set.uIoc_of_le (by norm_num : (1 / 4 : ℝ) ≤ 1)] at ht
  have ht_pos : 0 < t := by linarith [ht.1]
  have hnn : 0 ≤ ρRight t := by dsimp [ρRight]; positivity
  rw [ENNReal.toReal_ofReal hnn, smul_eq_mul, mul_comm]
  rfl

/- ### Section 5: Euler's `log sin` integral and logarithmic potential -/

private lemma integrable_log_sin_half_pi :
    IntervalIntegrable (fun u => Real.log (Real.sin u)) volume 0 (Real.pi / 2) := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by positivity)]
  have hdom : IntegrableOn (fun u : ℝ => |Real.log (2 / Real.pi)| + 2 * u ^ (-(1 / 2 : ℝ)))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) volume := by
    refine IntegrableOn.add (integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top.ne)) ?_
    have hr := intervalIntegral.intervalIntegrable_rpow' (r := -(1 / 2 : ℝ)) (a := 0) (b := Real.pi / 2)
      (by norm_num)
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by positivity)] at hr
    exact hr.const_mul 2
  refine hdom.mono' (Real.measurable_log.comp Real.continuous_sin.measurable).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  have hu_pos : 0 < u := hu.1
  have hsin_pos : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi hu_pos (by linarith [hu.2, Real.pi_pos])
  have hsin_le1 : Real.sin u ≤ 1 := Real.sin_le_one u
  have hsin_lb : 2 / Real.pi * u ≤ Real.sin u := Real.mul_le_sin hu_pos.le hu.2.le
  have hlog_neg : Real.log (Real.sin u) ≤ 0 := Real.log_nonpos hsin_pos.le hsin_le1
  have hlog_lb : Real.log (2 / Real.pi) + Real.log u ≤ Real.log (Real.sin u) := by
    rw [← Real.log_mul (by positivity) hu_pos.ne']
    exact Real.log_le_log (by positivity) hsin_lb
  have hneg_log_u : -Real.log u ≤ 2 * u ^ (-(1 / 2 : ℝ)) := by
    by_cases hu1 : u ≤ 1
    · have h1 : -Real.log u = 2 * Real.log (u ^ (-(1 / 2 : ℝ))) := by
        rw [Real.log_rpow hu_pos]; ring
      have h2 : Real.log (u ^ (-(1 / 2 : ℝ))) ≤ u ^ (-(1 / 2 : ℝ)) :=
        le_trans (Real.log_le_sub_one_of_pos (by positivity)) (by linarith)
      linarith
    · have hlog_pos : 0 ≤ Real.log u := Real.log_nonneg (le_of_not_ge hu1)
      have hnn : 0 ≤ 2 * u ^ (-(1 / 2 : ℝ)) := by positivity
      linarith
  rw [Real.norm_eq_abs, abs_of_nonpos hlog_neg]
  linarith [neg_abs_le (Real.log (2 / Real.pi))]

private lemma integral_log_sin_half_pi :
    ∫ u in (0 : ℝ)..(Real.pi / 2), Real.log (Real.sin u) = -(Real.pi / 2) * Real.log 2 := by
  set I := ∫ u in (0 : ℝ)..(Real.pi / 2), Real.log (Real.sin u)
  have hcos : ∫ u in (0 : ℝ)..(Real.pi / 2), Real.log (Real.cos u) = I := by
    have hsub := intervalIntegral.integral_comp_sub_left (fun u => Real.log (Real.sin u)) (Real.pi / 2)
      (a := 0) (b := Real.pi / 2)
    simp only [sub_zero, sub_self, Real.sin_pi_div_two_sub] at hsub
    exact hsub
  have hint_cos : IntervalIntegrable (fun u => Real.log (Real.cos u)) volume 0 (Real.pi / 2) := by
    have h := (integrable_log_sin_half_pi.comp_sub_left (Real.pi / 2)).symm
    simpa only [sub_zero, sub_self, Real.sin_pi_div_two_sub] using h
  have hadd : 2 * I = ∫ u in (0 : ℝ)..(Real.pi / 2), (Real.log (Real.sin u) + Real.log (Real.cos u)) := by
    rw [intervalIntegral.integral_add integrable_log_sin_half_pi hint_cos, hcos]
    ring
  have hdouble : ∫ u in (0 : ℝ)..(Real.pi / 2), (Real.log (Real.sin u) + Real.log (Real.cos u)) =
      (∫ u in (0 : ℝ)..(Real.pi / 2), Real.log (Real.sin (2 * u))) - (Real.pi / 2) * Real.log 2 := by
    have hae : ∀ᵐ u ∂volume, u ∈ Set.uIoc (0 : ℝ) (Real.pi / 2) →
        Real.log (Real.sin u) + Real.log (Real.cos u) = Real.log (Real.sin (2 * u)) - Real.log 2 := by
      have hne : ∀ᵐ u ∂volume, u ≠ Real.pi / 2 := by
        rw [ae_iff]; simp
      filter_upwards [hne] with u hune hu
      rw [Set.uIoc_of_le (by positivity)] at hu
      have hu_lt : u < Real.pi / 2 := lt_of_le_of_ne hu.2 hune
      have hs : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi hu.1 (by linarith [Real.pi_pos])
      have hc : 0 < Real.cos u := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hu.1], hu_lt⟩
      rw [← Real.log_mul hs.ne' hc.ne',
        show Real.sin u * Real.cos u = Real.sin (2 * u) / 2 by rw [Real.sin_two_mul]; ring,
        Real.log_div (by rw [Real.sin_two_mul]; positivity) (by norm_num)]
    rw [intervalIntegral.integral_congr_ae hae]
    have hint2 : IntervalIntegrable (fun u => Real.log (Real.sin (2 * u))) volume 0 (Real.pi / 2) := by
      have heq : (fun u => Real.log (Real.sin (2 * u))) =ᵐ[volume.restrict (Set.uIoc 0 (Real.pi / 2))]
          (fun u => (Real.log (Real.sin u) + Real.log (Real.cos u)) + Real.log 2) := by
        change ∀ᵐ u ∂volume.restrict (Set.uIoc 0 (Real.pi / 2)), _
        rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
        filter_upwards [hae] with u hu hmem
        linarith [hu hmem]
      exact ((integrable_log_sin_half_pi.add hint_cos).add intervalIntegrable_const).congr_ae heq.symm
    rw [intervalIntegral.integral_sub hint2 intervalIntegrable_const, intervalIntegral.integral_const,
      sub_zero, smul_eq_mul]
  have hpi : ∫ v in (0 : ℝ)..Real.pi, Real.log (Real.sin v) = 2 * I := by
    have hsym : ∫ v in (Real.pi / 2)..Real.pi, Real.log (Real.sin v) = I := by
      have hsub := intervalIntegral.integral_comp_sub_left (fun v => Real.log (Real.sin v)) Real.pi
        (a := Real.pi / 2) (b := Real.pi)
      simp only [sub_self, show Real.pi - Real.pi / 2 = Real.pi / 2 by ring, Real.sin_pi_sub] at hsub
      exact hsub
    have hint_right : IntervalIntegrable (fun v => Real.log (Real.sin v)) volume (Real.pi / 2) Real.pi := by
      have h := (integrable_log_sin_half_pi.comp_sub_left Real.pi).symm
      simpa only [sub_zero, show Real.pi - Real.pi / 2 = Real.pi / 2 by ring, Real.sin_pi_sub] using h
    rw [← intervalIntegral.integral_add_adjacent_intervals integrable_log_sin_half_pi hint_right, hsym]
    ring
  have hcomp : ∫ u in (0 : ℝ)..(Real.pi / 2), Real.log (Real.sin (2 * u)) = I := by
    have h := intervalIntegral.integral_comp_mul_left (fun v => Real.log (Real.sin v))
      (a := 0) (b := Real.pi / 2) (c := 2) (by norm_num)
    simp only [mul_zero, show 2 * (Real.pi / 2) = Real.pi by ring, smul_eq_mul] at h
    rw [h, hpi]
    ring
  linarith

private lemma integrable_log_abs_sin (a b : ℝ) :
    IntervalIntegrable (fun u => Real.log |Real.sin u|) volume a b := by
  have h0pi : IntervalIntegrable (fun u => Real.log |Real.sin u|) volume 0 Real.pi := by
    have h1 : IntervalIntegrable (fun u => Real.log |Real.sin u|) volume 0 (Real.pi / 2) := by
      refine integrable_log_sin_half_pi.congr_ae ?_
      change ∀ᵐ u ∂volume.restrict (Set.uIoc 0 (Real.pi / 2)), _
      rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
      filter_upwards with u hu
      rw [Set.uIoc_of_le (by positivity)] at hu
      rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hu.1.le (by linarith [hu.2, Real.pi_pos]))]
    have h2 : IntervalIntegrable (fun u => Real.log |Real.sin u|) volume (Real.pi / 2) Real.pi := by
      have h := (h1.comp_sub_left Real.pi).symm
      simpa only [sub_zero, show Real.pi - Real.pi / 2 = Real.pi / 2 by ring, Real.sin_pi_sub] using h
    exact h1.trans h2
  have hper : Function.Periodic (fun u => Real.log |Real.sin u|) Real.pi := by
    intro u; simp [Real.sin_add_pi]
  have hint_k : ∀ k : ℤ, IntervalIntegrable (fun u => Real.log |Real.sin u|) volume
      ((k : ℝ) * Real.pi) (((k + 1 : ℤ) : ℝ) * Real.pi) := by
    intro k
    have h := h0pi.comp_sub_right ((k : ℝ) * Real.pi)
    have hsub : (fun u => Real.log |Real.sin (u - (k : ℝ) * Real.pi)|) =
        (fun u => Real.log |Real.sin u|) := by
      ext u
      have hp := hper.int_mul (-k) u
      simpa [sub_eq_add_neg, add_comm] using hp
    rw [hsub] at h
    simpa [add_mul, one_mul, add_comm] using h
  have hbound : ∀ m n : ℤ, m ≤ n →
      IntervalIntegrable (fun u => Real.log |Real.sin u|) volume
        ((m : ℝ) * Real.pi) ((n : ℝ) * Real.pi) := by
    intro m n hmn
    obtain ⟨d, rfl⟩ := Int.exists_add_of_le hmn
    induction d with
    | zero => simp
    | succ k ih =>
      have hstep := hint_k (m + (k : ℤ))
      have heq1 : ((m + ((k + 1 : ℕ) : ℤ) : ℤ) : ℝ) * Real.pi =
          (((m + (k : ℤ)) + 1 : ℤ) : ℝ) * Real.pi := by push_cast; ring
      rw [heq1]
      exact (ih (by omega)).trans hstep
  let m : ℤ := ⌊min a b / Real.pi⌋
  let n : ℤ := ⌈max a b / Real.pi⌉
  have hmn : m ≤ n := by
    have hm : (m : ℝ) ≤ min a b / Real.pi := Int.floor_le _
    have hn : max a b / Real.pi ≤ (n : ℝ) := Int.le_ceil _
    have hle : min a b / Real.pi ≤ max a b / Real.pi :=
      div_le_div_of_nonneg_right (min_le_max) Real.pi_pos.le
    exact_mod_cast (hm.trans (hle.trans hn))
  have hm_le : (m : ℝ) * Real.pi ≤ min a b :=
    (le_div_iff₀ Real.pi_pos).mp (Int.floor_le _)
  have hn_ge : max a b ≤ (n : ℝ) * Real.pi :=
    (div_le_iff₀ Real.pi_pos).mp (Int.le_ceil _)
  have hmn_pi : (m : ℝ) * Real.pi ≤ (n : ℝ) * Real.pi :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hmn) Real.pi_pos.le
  refine (hbound m n hmn).mono_set (Set.uIcc_subset_uIcc ?_ ?_)
  · rw [Set.uIcc_of_le hmn_pi]
    exact ⟨le_trans hm_le (min_le_left _ _), le_trans (le_max_left _ _) hn_ge⟩
  · rw [Set.uIcc_of_le hmn_pi]
    exact ⟨le_trans hm_le (min_le_right _ _), le_trans (le_max_right _ _) hn_ge⟩

private lemma integral_log_abs_sin_pi :
    ∫ u in (0 : ℝ)..Real.pi, Real.log |Real.sin u| = -Real.pi * Real.log 2 := by
  have hae : ∀ᵐ u ∂volume, u ∈ Set.uIoc (0 : ℝ) Real.pi →
      Real.log |Real.sin u| = Real.log (Real.sin u) := by
    filter_upwards with u hu
    rw [Set.uIoc_of_le Real.pi_pos.le] at hu
    rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hu.1.le hu.2)]
  rw [intervalIntegral.integral_congr_ae hae]
  have hsym : ∫ v in (Real.pi / 2)..Real.pi, Real.log (Real.sin v) =
      ∫ u in (0 : ℝ)..(Real.pi / 2), Real.log (Real.sin u) := by
    have hsub := intervalIntegral.integral_comp_sub_left (fun v => Real.log (Real.sin v)) Real.pi
      (a := Real.pi / 2) (b := Real.pi)
    simp only [sub_self, show Real.pi - Real.pi / 2 = Real.pi / 2 by ring, Real.sin_pi_sub] at hsub
    exact hsub
  have hint_right : IntervalIntegrable (fun v => Real.log (Real.sin v)) volume (Real.pi / 2) Real.pi := by
    have h := (integrable_log_sin_half_pi.comp_sub_left Real.pi).symm
    simpa only [sub_zero, show Real.pi - Real.pi / 2 = Real.pi / 2 by ring, Real.sin_pi_sub] using h
  rw [← intervalIntegral.integral_add_adjacent_intervals integrable_log_sin_half_pi hint_right,
    hsym, integral_log_sin_half_pi]
  ring

private lemma integrable_log_abs_sin_shift_half (φ : ℝ) :
    IntervalIntegrable (fun θ => Real.log |Real.sin ((θ + φ) / 2)|) volume 0 Real.pi ∧
    IntervalIntegrable (fun θ => Real.log |Real.sin ((θ - φ) / 2)|) volume 0 Real.pi := by
  constructor
  · have h := IntervalIntegrable.comp_mul_left (integrable_log_abs_sin (φ / 2) ((Real.pi + φ) / 2))
      (c := (1 / 2 : ℝ))
    have h2 := IntervalIntegrable.comp_add_right h φ
    have heq : (fun θ => Real.log |Real.sin ((1 / 2 : ℝ) * (θ + φ))|) =
        (fun θ => Real.log |Real.sin ((θ + φ) / 2)|) := by ext θ; congr 2; ring
    have ha1 : (φ / 2) / (1 / 2 : ℝ) - φ = 0 := by ring
    have ha2 : ((Real.pi + φ) / 2) / (1 / 2 : ℝ) - φ = Real.pi := by ring
    rwa [heq, ha1, ha2] at h2
  · have h := IntervalIntegrable.comp_mul_left (integrable_log_abs_sin ((-φ) / 2) ((Real.pi - φ) / 2))
      (c := (1 / 2 : ℝ))
    have h2 := IntervalIntegrable.comp_sub_right h φ
    have heq : (fun θ => Real.log |Real.sin ((1 / 2 : ℝ) * (θ - φ))|) =
        (fun θ => Real.log |Real.sin ((θ - φ) / 2)|) := by ext θ; congr 2; ring
    have ha1 : ((-φ) / 2) / (1 / 2 : ℝ) + φ = 0 := by ring
    have ha2 : ((Real.pi - φ) / 2) / (1 / 2 : ℝ) + φ = Real.pi := by ring
    rwa [heq, ha1, ha2] at h2

private lemma integral_log_abs_cos_sub_cos (φ : ℝ) :
    ∫ θ in (0 : ℝ)..Real.pi, Real.log |Real.cos φ - Real.cos θ| = -Real.pi * Real.log 2 := by
  obtain ⟨h1, h2⟩ := integrable_log_abs_sin_shift_half φ
  have hae : ∀ᵐ θ ∂volume, θ ∈ Set.uIoc (0 : ℝ) Real.pi →
      Real.log |Real.cos φ - Real.cos θ| =
        Real.log 2 + Real.log |Real.sin ((θ + φ) / 2)| + Real.log |Real.sin ((θ - φ) / 2)| := by
    have hbad : (volume {θ : ℝ | Real.sin ((θ + φ) / 2) = 0 ∨ Real.sin ((θ - φ) / 2) = 0}) = 0 := by
      have hcnt1 : ({θ : ℝ | Real.sin ((θ + φ) / 2) = 0}).Countable := by
        have hsub : {θ : ℝ | Real.sin ((θ + φ) / 2) = 0} ⊆ Set.range (fun k : ℤ => 2 * (k : ℝ) * Real.pi - φ) := by
          intro θ hθ
          rw [Set.mem_ofPred_eq, Real.sin_eq_zero_iff] at hθ
          obtain ⟨k, hk⟩ := hθ
          exact ⟨k, by linarith⟩
        exact (Set.countable_range _).mono hsub
      have hcnt2 : ({θ : ℝ | Real.sin ((θ - φ) / 2) = 0}).Countable := by
        have hsub : {θ : ℝ | Real.sin ((θ - φ) / 2) = 0} ⊆ Set.range (fun k : ℤ => 2 * (k : ℝ) * Real.pi + φ) := by
          intro θ hθ
          rw [Set.mem_ofPred_eq, Real.sin_eq_zero_iff] at hθ
          obtain ⟨k, hk⟩ := hθ
          exact ⟨k, by linarith⟩
        exact (Set.countable_range _).mono hsub
      exact (hcnt1.union hcnt2).measure_zero volume
    have hne : ∀ᵐ θ ∂volume, Real.sin ((θ + φ) / 2) ≠ 0 ∧ Real.sin ((θ - φ) / 2) ≠ 0 := by
      rw [ae_iff]
      have hset : {θ : ℝ | ¬ (Real.sin ((θ + φ) / 2) ≠ 0 ∧ Real.sin ((θ - φ) / 2) ≠ 0)} =
          {θ : ℝ | Real.sin ((θ + φ) / 2) = 0 ∨ Real.sin ((θ - φ) / 2) = 0} := by
        ext θ; simp only [Set.mem_ofPred_eq, not_and_or, not_not]
      rw [hset]
      exact hbad
    filter_upwards [hne] with θ ⟨hs1, hs2⟩ _
    have htrig : Real.cos φ - Real.cos θ = 2 * Real.sin ((θ + φ) / 2) * Real.sin ((θ - φ) / 2) := by
      have h := Real.cos_sub_cos φ θ
      have hodd : Real.sin ((φ - θ) / 2) = -Real.sin ((θ - φ) / 2) := by
        rw [← Real.sin_neg]; congr 1; ring
      have hcomm : (φ + θ) / 2 = (θ + φ) / 2 := by ring
      rw [h, hcomm, hodd]; ring
    rw [htrig, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      Real.log_mul (by positivity) (abs_ne_zero.mpr hs2),
      Real.log_mul (by norm_num) (abs_ne_zero.mpr hs1)]
  rw [intervalIntegral.integral_congr_ae hae,
    intervalIntegral.integral_add (intervalIntegrable_const.add h1) h2,
    intervalIntegral.integral_add intervalIntegrable_const h1,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  have hint1 : ∫ θ in (0 : ℝ)..Real.pi, Real.log |Real.sin ((θ + φ) / 2)| =
      2 * ∫ u in (φ / 2)..((Real.pi + φ) / 2), Real.log |Real.sin u| := by
    have hcomp := intervalIntegral.integral_comp_mul_left (fun u => Real.log |Real.sin u|)
      (a := φ) (b := Real.pi + φ) (c := (1 / 2 : ℝ)) (by norm_num)
    have hshift := intervalIntegral.integral_comp_add_right
      (fun θ => Real.log |Real.sin ((1 / 2 : ℝ) * θ)|) φ (a := 0) (b := Real.pi)
    simp only [zero_add] at hshift
    have heq : (fun θ => Real.log |Real.sin ((θ + φ) / 2)|) =
        (fun θ => Real.log |Real.sin ((1 / 2 : ℝ) * (θ + φ))|) := by ext θ; congr 2; ring
    rw [heq, hshift, hcomp]
    simp only [one_div, inv_inv, smul_eq_mul, inv_mul_eq_div]
  have hint2 : ∫ θ in (0 : ℝ)..Real.pi, Real.log |Real.sin ((θ - φ) / 2)| =
      2 * ∫ u in ((φ - Real.pi) / 2)..(φ / 2), Real.log |Real.sin u| := by
    have hcomp := intervalIntegral.integral_comp_mul_left (fun u => Real.log |Real.sin u|)
      (a := -φ) (b := Real.pi - φ) (c := (1 / 2 : ℝ)) (by norm_num)
    have hshift := intervalIntegral.integral_comp_sub_right
      (fun θ => Real.log |Real.sin ((1 / 2 : ℝ) * θ)|) φ (a := 0) (b := Real.pi)
    simp only [zero_sub] at hshift
    have heq : (fun θ => Real.log |Real.sin ((θ - φ) / 2)|) =
        (fun θ => Real.log |Real.sin ((1 / 2 : ℝ) * (θ - φ))|) := by ext θ; congr 2; ring
    rw [heq, hshift, hcomp]
    simp only [one_div, inv_inv, smul_eq_mul, inv_mul_eq_div]
    congr 1
    have hneg := intervalIntegral.integral_comp_neg (fun u => Real.log |Real.sin u|)
      (a := (-φ) / 2) (b := (Real.pi - φ) / 2)
    have heven : (fun u => Real.log |Real.sin (-u)|) = (fun u => Real.log |Real.sin u|) := by
      ext u; simp [Real.sin_neg]
    rw [heven] at hneg
    rw [hneg]
    congr 1 <;> ring
  rw [hint1, hint2, add_assoc, ← mul_add, add_comm (∫ u in (φ / 2)..((Real.pi + φ) / 2), _),
    intervalIntegral.integral_add_adjacent_intervals
      (integrable_log_abs_sin _ _) (integrable_log_abs_sin _ _)]
  have hper : Function.Periodic (fun u => Real.log |Real.sin u|) Real.pi := by
    intro u; simp [Real.sin_add_pi]
  have hper_int := hper.intervalIntegral_add_eq ((φ - Real.pi) / 2) 0
  rw [zero_add, show (φ - Real.pi) / 2 + Real.pi = (Real.pi + φ) / 2 by ring] at hper_int
  rw [hper_int, integral_log_abs_sin_pi]
  ring

private lemma integral_μΘ_log_abs {y a : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) (1 / 4))
    (ha : a ∈ Set.Icc (1 / 4 : ℝ) 1) :
    ∫ θ, Real.log |y - Φ (a, θ)| ∂μΘ = Real.log (a / 4) := by
  have ha_pos : 0 < a := by linarith [ha.1]
  have hu : 1 - 2 * y / a ∈ Set.Icc (-1 : ℝ) 1 := by
    have h1 : 0 ≤ 2 * y / a := div_nonneg (by linarith [hy.1]) ha_pos.le
    have h2 : 2 * y / a ≤ 2 := by rw [div_le_iff₀ ha_pos]; linarith [hy.2, ha.1]
    exact ⟨by linarith, by linarith⟩
  set φ := Real.arccos (1 - 2 * y / a)
  have hy_eq : y = (a / 2) * (1 - Real.cos φ) := by
    rw [Real.cos_arccos hu.1 hu.2]; field_simp [ha_pos.ne']; ring
  have hsub_eq : ∀ θ, y - Φ (a, θ) = (a / 2) * (Real.cos θ - Real.cos φ) := by
    intro θ; dsimp [Φ]; rw [hy_eq]; ring
  rw [integral_μΘ_eq]
  have hae : ∀ᵐ θ ∂volume, θ ∈ Set.uIoc (0 : ℝ) Real.pi →
      Real.log |y - Φ (a, θ)| = Real.log (a / 2) + Real.log |Real.cos φ - Real.cos θ| := by
    have hbad : (volume {θ : ℝ | Real.cos φ - Real.cos θ = 0}) = 0 := by
      have hcnt : ({θ : ℝ | Real.cos φ - Real.cos θ = 0}).Countable := by
        have hsub : {θ : ℝ | Real.cos φ - Real.cos θ = 0} ⊆
            (Set.range (fun k : ℤ => φ + 2 * (k : ℝ) * Real.pi)) ∪
            (Set.range (fun k : ℤ => -φ + 2 * (k : ℝ) * Real.pi)) := by
          intro θ hθ
          rw [Set.mem_ofPred_eq, sub_eq_zero] at hθ
          have h := Real.cos_eq_cos_iff.mp hθ
          rcases h with ⟨k, hk | hk⟩
          · exact Or.inl ⟨k, by linarith⟩
          · exact Or.inr ⟨k, by linarith⟩
        exact ((Set.countable_range _).union (Set.countable_range _)).mono hsub
      exact hcnt.measure_zero volume
    have hne : ∀ᵐ θ ∂volume, Real.cos φ - Real.cos θ ≠ 0 := by
      rw [ae_iff]
      have hset : {θ : ℝ | ¬ Real.cos φ - Real.cos θ ≠ 0} = {θ : ℝ | Real.cos φ - Real.cos θ = 0} := by
        ext θ; simp
      rw [hset]
      exact hbad
    filter_upwards [hne] with θ hne _
    rw [hsub_eq θ, abs_mul, abs_of_pos (by positivity : 0 < a / 2), abs_sub_comm,
      Real.log_mul (by positivity) (abs_ne_zero.mpr hne)]
  have hint_cos : IntervalIntegrable (fun θ => Real.log |Real.cos φ - Real.cos θ|) volume 0 Real.pi := by
    obtain ⟨h1, h2⟩ := integrable_log_abs_sin_shift_half φ
    have hbad : (volume {θ : ℝ | Real.sin ((θ + φ) / 2) = 0 ∨ Real.sin ((θ - φ) / 2) = 0}) = 0 := by
      have hcnt1 : ({θ : ℝ | Real.sin ((θ + φ) / 2) = 0}).Countable := by
        have hsub : {θ : ℝ | Real.sin ((θ + φ) / 2) = 0} ⊆ Set.range (fun k : ℤ => 2 * (k : ℝ) * Real.pi - φ) := by
          intro θ hθ; rw [Set.mem_ofPred_eq, Real.sin_eq_zero_iff] at hθ
          obtain ⟨k, hk⟩ := hθ; exact ⟨k, by linarith⟩
        exact (Set.countable_range _).mono hsub
      have hcnt2 : ({θ : ℝ | Real.sin ((θ - φ) / 2) = 0}).Countable := by
        have hsub : {θ : ℝ | Real.sin ((θ - φ) / 2) = 0} ⊆ Set.range (fun k : ℤ => 2 * (k : ℝ) * Real.pi + φ) := by
          intro θ hθ; rw [Set.mem_ofPred_eq, Real.sin_eq_zero_iff] at hθ
          obtain ⟨k, hk⟩ := hθ; exact ⟨k, by linarith⟩
        exact (Set.countable_range _).mono hsub
      exact (hcnt1.union hcnt2).measure_zero volume
    have hne : ∀ᵐ θ ∂volume, Real.sin ((θ + φ) / 2) ≠ 0 ∧ Real.sin ((θ - φ) / 2) ≠ 0 := by
      rw [ae_iff]
      have hset : {θ : ℝ | ¬ (Real.sin ((θ + φ) / 2) ≠ 0 ∧ Real.sin ((θ - φ) / 2) ≠ 0)} =
          {θ : ℝ | Real.sin ((θ + φ) / 2) = 0 ∨ Real.sin ((θ - φ) / 2) = 0} := by
        ext θ; simp only [Set.mem_ofPred_eq, not_and_or, not_not]
      rw [hset]
      exact hbad
    refine (((intervalIntegrable_const (c := Real.log 2)).add h1).add h2).congr_ae ?_
    change ∀ᵐ θ ∂volume.restrict (Set.uIoc 0 Real.pi), _
    rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hne] with θ ⟨hs1, hs2⟩ _
    have htrig : Real.cos φ - Real.cos θ = 2 * Real.sin ((θ + φ) / 2) * Real.sin ((θ - φ) / 2) := by
      have h := Real.cos_sub_cos φ θ
      have hodd : Real.sin ((φ - θ) / 2) = -Real.sin ((θ - φ) / 2) := by
        rw [← Real.sin_neg]; congr 1; ring
      have hcomm : (φ + θ) / 2 = (θ + φ) / 2 := by ring
      rw [h, hcomm, hodd]; ring
    rw [htrig, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      Real.log_mul (by positivity) (abs_ne_zero.mpr hs2),
      Real.log_mul (by norm_num) (abs_ne_zero.mpr hs1)]
  rw [intervalIntegral.integral_congr_ae hae,
    intervalIntegral.integral_add intervalIntegrable_const hint_cos,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul, integral_log_abs_cos_sub_cos φ]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hlog : Real.log (a / 4) = Real.log (a / 2) - Real.log 2 := by
    rw [← Real.log_div (by positivity) (by norm_num)]; congr 1; ring
  rw [hlog]
  field_simp [hpi]
  ring

private lemma log_potential_bound {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) (1 / 4))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧
      ∫ t in Set.Icc (0 : ℝ) 1, Real.log (max |y - t| (Real.exp (-M))) ∂μ ≤
        1 - 3 * Real.log 2 + ε := by
  let g : ℕ → ℝ × ℝ → ℝ := fun n p => Real.log (max |y - Φ p| (Real.exp (-((n : ℝ) + 1))))
  let gLim : ℝ × ℝ → ℝ := fun p => Real.log |y - Φ p|
  have hbound_le1 : ∀ᵐ p ∂(μA.prod μΘ), |y - Φ p| ≤ 1 := by
    have hae : ∀ᵐ p ∂(μA.prod μΘ), p.1 ∈ Set.Icc (1 / 4 : ℝ) 1 ∧ p.2 ∈ Set.Icc (0 : ℝ) Real.pi := by
      have h1 : (μA.prod μΘ) ((Set.Icc (1 / 4 : ℝ) 1)ᶜ ×ˢ Set.univ) = 0 := by
        rw [Measure.prod_prod, μA_compl_Icc, zero_mul]
      have h2 : (μA.prod μΘ) (Set.univ ×ˢ (Set.Icc (0 : ℝ) Real.pi)ᶜ) = 0 := by
        rw [Measure.prod_prod, μΘ_compl_Icc, mul_zero]
      rw [ae_iff]
      have hsub : {p : ℝ × ℝ | ¬ (p.1 ∈ Set.Icc (1 / 4 : ℝ) 1 ∧ p.2 ∈ Set.Icc (0 : ℝ) Real.pi)} ⊆
          ((Set.Icc (1 / 4 : ℝ) 1)ᶜ ×ˢ Set.univ) ∪ (Set.univ ×ˢ (Set.Icc (0 : ℝ) Real.pi)ᶜ) := by
        rintro ⟨a, θ⟩ h; simp only [Set.mem_ofPred_eq, not_and_or] at h
        rcases h with ha | hθ
        · exact Or.inl ⟨ha, trivial⟩
        · exact Or.inr ⟨trivial, hθ⟩
      exact measure_mono_null hsub (measure_union_null h1 h2)
    filter_upwards [hae] with ⟨a, θ⟩ ⟨ha, _⟩
    have hΦ0 : 0 ≤ Φ (a, θ) := by dsimp [Φ]; nlinarith [Real.cos_le_one θ, ha.1]
    have hΦ1 : Φ (a, θ) ≤ 1 := by dsimp [Φ]; nlinarith [Real.neg_one_le_cos θ, ha.1, ha.2]
    rw [abs_le]
    constructor <;> linarith [hy.1, hy.2]
  have hne_ae : ∀ᵐ p ∂(μA.prod μΘ), y - Φ p ≠ 0 := by
    rw [ae_iff]
    have hsub : {p : ℝ × ℝ | ¬ (y - Φ p ≠ 0)} ⊆ Φ ⁻¹' {y} := by
      intro p hp; simp only [Set.mem_ofPred_eq, not_not, sub_eq_zero] at hp
      exact hp.symm
    have hmeas_zero : (μA.prod μΘ) (Φ ⁻¹' {y}) = 0 := by
      rw [Measure.prod_apply ((measurableSet_singleton y).preimage continuous_Φ.measurable)]
      have hslice : ∀ᵐ a ∂μA, μΘ (Prod.mk a ⁻¹' (Φ ⁻¹' {y})) = 0 := by
        have hae : ∀ᵐ a ∂μA, a ∈ Set.Icc (1 / 4 : ℝ) 1 := by rw [ae_iff]; exact μA_compl_Icc
        filter_upwards [hae] with a ha
        have ha_pos : 0 < a := by linarith [ha.1]
        have hsub' : (Prod.mk a ⁻¹' (Φ ⁻¹' {y})) ∩ Set.Icc (0 : ℝ) Real.pi ⊆
            {Real.arccos (1 - 2 * y / a)} := by
          rintro θ ⟨hΦ, hθ⟩
          simp only [Set.mem_preimage, Set.mem_singleton_iff, Φ] at hΦ ⊢
          have hcos : Real.cos θ = 1 - 2 * y / a := by
            have : a * (1 - Real.cos θ) = 2 * y := by linarith
            field_simp [ha_pos.ne']; linarith
          rw [← hcos, Real.arccos_cos hθ.1 hθ.2]
        have hsing : μΘ {Real.arccos (1 - 2 * y / a)} = 0 := by
          rw [μΘ, withDensity_apply _ (measurableSet_singleton _),
            Measure.restrict_restrict (measurableSet_singleton _)]
          exact setLIntegral_measure_zero _ _ (measure_mono_null Set.inter_subset_left Real.volume_singleton)
        have hae_le : μΘ (Prod.mk a ⁻¹' (Φ ⁻¹' {y})) ≤ μΘ {Real.arccos (1 - 2 * y / a)} := by
          calc μΘ (Prod.mk a ⁻¹' (Φ ⁻¹' {y}))
              ≤ μΘ (((Prod.mk a ⁻¹' (Φ ⁻¹' {y})) ∩ Set.Icc (0 : ℝ) Real.pi) ∪
                  (Set.Icc (0 : ℝ) Real.pi)ᶜ) :=
                measure_mono (fun θ hθ => by
                  by_cases h : θ ∈ Set.Icc (0 : ℝ) Real.pi
                  · exact Or.inl ⟨hθ, h⟩
                  · exact Or.inr h)
            _ ≤ μΘ ((Prod.mk a ⁻¹' (Φ ⁻¹' {y})) ∩ Set.Icc (0 : ℝ) Real.pi) +
                  μΘ (Set.Icc (0 : ℝ) Real.pi)ᶜ := measure_union_le _ _
            _ ≤ μΘ {Real.arccos (1 - 2 * y / a)} + 0 := by
                rw [μΘ_compl_Icc]; exact add_le_add (measure_mono hsub') le_rfl
            _ = μΘ {Real.arccos (1 - 2 * y / a)} := add_zero _
        exact le_antisymm (hae_le.trans hsing.le) zero_le
      rw [lintegral_congr_ae hslice, lintegral_zero]
    exact measure_mono_null hsub hmeas_zero
  have hgLim_meas : Measurable gLim :=
    Real.measurable_log.comp (continuous_abs.measurable.comp (measurable_const.sub continuous_Φ.measurable))
  have hgLim_int : Integrable gLim (μA.prod μΘ) := by
    have hnonpos : ∀ᵐ p ∂(μA.prod μΘ), gLim p ≤ 0 := by
      filter_upwards [hbound_le1] with p hp
      exact Real.log_nonpos (abs_nonneg _) hp
    have hlt_top : ∫⁻ p, ENNReal.ofReal (-gLim p) ∂(μA.prod μΘ) < ⊤ := by
      rw [lintegral_prod (fun p => ENNReal.ofReal (-gLim p))
        (ENNReal.measurable_ofReal.comp hgLim_meas.neg).aemeasurable]
      have hinner : ∀ᵐ a ∂μA,
          (∫⁻ θ, ENNReal.ofReal (-gLim (a, θ)) ∂μΘ) = ENNReal.ofReal (-Real.log (a / 4)) := by
        have hae : ∀ᵐ a ∂μA, a ∈ Set.Icc (1 / 4 : ℝ) 1 := by rw [ae_iff]; exact μA_compl_Icc
        filter_upwards [hae] with a ha
        have ha_pos : 0 < a := by linarith [ha.1]
        have hu : 1 - 2 * y / a ∈ Set.Icc (-1 : ℝ) 1 := by
          have h1 : 0 ≤ 2 * y / a := div_nonneg (by linarith [hy.1]) ha_pos.le
          have h2 : 2 * y / a ≤ 2 := by rw [div_le_iff₀ ha_pos]; linarith [hy.2, ha.1]
          exact ⟨by linarith, by linarith⟩
        set φ := Real.arccos (1 - 2 * y / a)
        have hslice_int : Integrable (fun θ => -gLim (a, θ)) μΘ := by
          rw [μΘ, integrable_withDensity_iff_integrable_smul₀' measurable_const.aemeasurable
            (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
          obtain ⟨h1, h2⟩ := integrable_log_abs_sin_shift_half φ
          have h_ii : IntervalIntegrable (fun θ => Real.log |y - Φ (a, θ)|) volume 0 Real.pi := by
            have hy_eq : y = (a / 2) * (1 - Real.cos φ) := by
              rw [Real.cos_arccos hu.1 hu.2]; field_simp [ha_pos.ne']; ring
            have hbad : (volume {θ : ℝ | Real.sin ((θ + φ) / 2) = 0 ∨ Real.sin ((θ - φ) / 2) = 0}) = 0 := by
              have hcnt1 : ({θ : ℝ | Real.sin ((θ + φ) / 2) = 0}).Countable := by
                have hsub : {θ : ℝ | Real.sin ((θ + φ) / 2) = 0} ⊆ Set.range (fun k : ℤ => 2 * (k : ℝ) * Real.pi - φ) := by
                  intro θ hθ; rw [Set.mem_ofPred_eq, Real.sin_eq_zero_iff] at hθ
                  obtain ⟨k, hk⟩ := hθ; exact ⟨k, by linarith⟩
                exact (Set.countable_range _).mono hsub
              have hcnt2 : ({θ : ℝ | Real.sin ((θ - φ) / 2) = 0}).Countable := by
                have hsub : {θ : ℝ | Real.sin ((θ - φ) / 2) = 0} ⊆ Set.range (fun k : ℤ => 2 * (k : ℝ) * Real.pi + φ) := by
                  intro θ hθ; rw [Set.mem_ofPred_eq, Real.sin_eq_zero_iff] at hθ
                  obtain ⟨k, hk⟩ := hθ; exact ⟨k, by linarith⟩
                exact (Set.countable_range _).mono hsub
              exact (hcnt1.union hcnt2).measure_zero volume
            have hne : ∀ᵐ θ ∂volume, Real.sin ((θ + φ) / 2) ≠ 0 ∧ Real.sin ((θ - φ) / 2) ≠ 0 := by
              rw [ae_iff]
              have hset : {θ : ℝ | ¬ (Real.sin ((θ + φ) / 2) ≠ 0 ∧ Real.sin ((θ - φ) / 2) ≠ 0)} =
                  {θ : ℝ | Real.sin ((θ + φ) / 2) = 0 ∨ Real.sin ((θ - φ) / 2) = 0} := by
                ext θ; simp only [Set.mem_ofPred_eq, not_and_or, not_not]
              rw [hset]
              exact hbad
            refine (((intervalIntegrable_const (c := Real.log (a / 2) + Real.log 2)).add h1).add h2).congr_ae ?_
            change ∀ᵐ θ ∂volume.restrict (Set.uIoc 0 Real.pi), _
            rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
            filter_upwards [hne] with θ ⟨hs1, hs2⟩ _
            have hsub_eq : y - Φ (a, θ) = (a / 2) * (Real.cos θ - Real.cos φ) := by
              dsimp [Φ]; rw [hy_eq]; ring
            have htrig : Real.cos φ - Real.cos θ = 2 * Real.sin ((θ + φ) / 2) * Real.sin ((θ - φ) / 2) := by
              have h := Real.cos_sub_cos φ θ
              have hodd : Real.sin ((φ - θ) / 2) = -Real.sin ((θ - φ) / 2) := by
                rw [← Real.sin_neg]; congr 1; ring
              have hcomm : (φ + θ) / 2 = (θ + φ) / 2 := by ring
              rw [h, hcomm, hodd]; ring
            have hprod_ne : Real.cos φ - Real.cos θ ≠ 0 := by
              rw [htrig]; exact mul_ne_zero (mul_ne_zero (by norm_num) hs1) hs2
            rw [hsub_eq, abs_mul, abs_of_pos (by positivity : 0 < a / 2), abs_sub_comm,
              Real.log_mul (by positivity) (abs_ne_zero.mpr hprod_ne),
              htrig, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
              Real.log_mul (by positivity) (abs_ne_zero.mpr hs2),
              Real.log_mul (by norm_num) (abs_ne_zero.mpr hs1)]
            ring
          rw [intervalIntegrable_iff_integrableOn_Icc_of_le Real.pi_pos.le] at h_ii
          have h_neg := h_ii.neg.const_mul (ENNReal.ofReal (1 / Real.pi)).toReal
          simpa only [smul_eq_mul, gLim, Pi.neg_apply] using h_neg
        have hslice_nn : 0 ≤ᵐ[μΘ] fun θ => -gLim (a, θ) := by
          have hθae : ∀ᵐ θ ∂μΘ, θ ∈ Set.Icc (0 : ℝ) Real.pi := by rw [ae_iff]; exact μΘ_compl_Icc
          filter_upwards [hθae] with θ _
          have hΦ0 : 0 ≤ Φ (a, θ) := by dsimp [Φ]; nlinarith [Real.cos_le_one θ, ha.1]
          have hΦ1 : Φ (a, θ) ≤ 1 := by dsimp [Φ]; nlinarith [Real.neg_one_le_cos θ, ha.1, ha.2]
          have hle1 : |y - Φ (a, θ)| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
          exact neg_nonneg.mpr (Real.log_nonpos (abs_nonneg _) hle1)
        rw [← ofReal_integral_eq_lintegral_ofReal hslice_int hslice_nn, integral_neg,
          integral_μΘ_log_abs hy ha]
      rw [lintegral_congr_ae hinner]
      have hle_const : ∀ᵐ a ∂μA, ENNReal.ofReal (-Real.log (a / 4)) ≤ ENNReal.ofReal (Real.log 16) := by
        have hae : ∀ᵐ a ∂μA, a ∈ Set.Icc (1 / 4 : ℝ) 1 := by rw [ae_iff]; exact μA_compl_Icc
        filter_upwards [hae] with a ha
        apply ENNReal.ofReal_le_ofReal
        have h1 : (1 / 16 : ℝ) ≤ a / 4 := by linarith [ha.1]
        have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 16) h1
        rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub] at hlog
        linarith
      calc ∫⁻ a, ENNReal.ofReal (-Real.log (a / 4)) ∂μA
          ≤ ∫⁻ _a, ENNReal.ofReal (Real.log 16) ∂μA := lintegral_mono_ae hle_const
        _ = ENNReal.ofReal (Real.log 16) * μA Set.univ := lintegral_const _
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μA _)
    refine ⟨hgLim_meas.aestronglyMeasurable, ?_⟩
    show ∫⁻ p, ‖gLim p‖ₑ ∂(μA.prod μΘ) < ⊤
    have hae_eq : ∀ᵐ p ∂(μA.prod μΘ), ‖gLim p‖ₑ = ENNReal.ofReal (-gLim p) := by
      filter_upwards [hnonpos] with p hp
      rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonpos hp]
    rw [lintegral_congr_ae hae_eq]
    exact hlt_top
  have hint_lim : ∫ p, gLim p ∂(μA.prod μΘ) = 1 - 3 * Real.log 2 := by
    rw [integral_prod gLim hgLim_int]
    have hae : ∀ᵐ a ∂μA, (∫ θ, gLim (a, θ) ∂μΘ) = Real.log (a / 4) := by
      have ha1 : ∀ᵐ a ∂μA, a ∈ Set.Icc (1 / 4 : ℝ) 1 := by rw [ae_iff]; exact μA_compl_Icc
      filter_upwards [ha1] with a ha
      exact integral_μΘ_log_abs hy ha
    rw [integral_congr_ae hae, integral_μA_eq, integral_log_div_four_mul_w]
  have htendsto : Tendsto (fun n : ℕ => ∫ p, g n p ∂(μA.prod μΘ)) atTop (𝓝 (1 - 3 * Real.log 2)) := by
    rw [← hint_lim]
    refine tendsto_integral_of_dominated_convergence (bound := fun p => ‖gLim p‖) ?_ ?_ ?_ ?_
    · intro n
      refine (Real.measurable_log.comp ?_).aestronglyMeasurable
      exact (continuous_abs.measurable.comp (measurable_const.sub continuous_Φ.measurable)).max
        measurable_const
    · exact hgLim_int.norm
    · intro n
      filter_upwards [hbound_le1, hne_ae] with p hp1 hpne
      have habs_pos : 0 < |y - Φ p| := abs_pos.mpr hpne
      have hexp_le1 : Real.exp (-((n : ℝ) + 1)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
      have hmax_le1 : max |y - Φ p| (Real.exp (-((n : ℝ) + 1))) ≤ 1 := max_le hp1 hexp_le1
      have hmax_ge : |y - Φ p| ≤ max |y - Φ p| (Real.exp (-((n : ℝ) + 1))) := le_max_left _ _
      have hg_nonpos : g n p ≤ 0 := Real.log_nonpos (lt_of_lt_of_le habs_pos hmax_ge).le hmax_le1
      have hg_ge : gLim p ≤ g n p := Real.log_le_log habs_pos hmax_ge
      have hlim_nonpos : gLim p ≤ 0 := Real.log_nonpos habs_pos.le hp1
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonpos hg_nonpos, abs_of_nonpos hlim_nonpos]
      linarith
    · filter_upwards [hne_ae] with p hpne
      have habs_pos : 0 < |y - Φ p| := abs_pos.mpr hpne
      have hexp0 : Tendsto (fun n : ℕ => Real.exp (-((n : ℝ) + 1))) atTop (𝓝 0) := by
        have hneg : Tendsto (fun n : ℕ => -((n : ℝ) + 1)) atTop atBot :=
          tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
        exact Real.tendsto_exp_atBot.comp hneg
      have hev : ∀ᶠ n : ℕ in atTop, Real.exp (-((n : ℝ) + 1)) ≤ |y - Φ p| :=
        hexp0.eventually (Iic_mem_nhds habs_pos)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with n hn
      dsimp [g, gLim]
      rw [max_eq_left hn]
  have hev := htendsto.eventually (Iio_mem_nhds (show 1 - 3 * Real.log 2 < 1 - 3 * Real.log 2 + ε by linarith))
  obtain ⟨n, hn⟩ := hev.exists
  refine ⟨(n : ℝ) + 1, by positivity, ?_⟩
  have hmap_int : ∫ t in Set.Icc (0 : ℝ) 1, Real.log (max |y - t| (Real.exp (-((n : ℝ) + 1)))) ∂μ =
      ∫ p, g n p ∂(μA.prod μΘ) := by
    have hae_Icc : (Set.Icc (0 : ℝ) 1 : Set ℝ) =ᵐ[μ] Set.univ := by
      rw [ae_eq_set]
      exact ⟨measure_mono_null (fun _ h => h.2 trivial) measure_empty,
        measure_mono_null (fun _ h => h.2) μ_compl_Icc⟩
    rw [setIntegral_congr_set hae_Icc, Measure.restrict_univ, μ]
    have hcont_f : Continuous (fun t : ℝ => Real.log (max |y - t| (Real.exp (-((n : ℝ) + 1))))) := by
      refine Continuous.log ?_ fun t => (lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _)).ne'
      exact (continuous_abs.comp (continuous_const.sub continuous_id)).max continuous_const
    exact integral_map continuous_Φ.measurable.aemeasurable hcont_f.aestronglyMeasurable
  rw [hmap_int]
  exact hn.le

end Erdos704DaviesR1H1R1H2

open Filter MeasureTheory Real Set Topology Erdos704DaviesR1H1R1H2
open scoped BigOperators Classical ENNReal

theorem OMA.solution : OMA.R_Erdos704_erdos_704_variants_davies_lower_R1_H1_R1.H2 :=
  ⟨μ, inferInstance, μ_Icc_zero_one, μ_compl_Icc, integral_μ_right, μ_cdf_continuousOn,
    μ_Icc_zero_zero, μ_Icc_zero_quarter_pos, fun _ _ h0 h12 h2 => μ_cdf_slope h0 h12 h2,
    fun _ hy _ hε => log_potential_bound hy hε⟩

