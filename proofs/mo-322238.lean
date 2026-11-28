import OMAStatements.S_mo_322238

-- Problem: Distribution of weighted sum of non-central chi-squared r.v.'s: log-concave?
-- Upstream: formal-conjectures statements/mo-322238.lean:0 (declaration OMA.S_mo_322238.main)
-- Credit: @krzysztoff1 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Counterexample: n = 2, δ = 0, w = (1, 2). With Z = (Z₁, Z₂) standard Gaussian in the plane and
Z = (r cos t, r sin t), the variable X = Z₁² + 2 Z₂² equals r² q(t) with q(t) = 1 + sin² t, so
X is a mixture over the uniform angle t of exponential laws with rate a(t) = 1 / (2 q(t)):
its density is g(x) = (1/2π) ∫_{-π}^{π} a(t) e^{-x a(t)} dt for x > 0 and 0 for x ≤ 0.
Since a is not constant, g is strictly log-convex on (0, ∞), so no version of the density is
log-concave.
-/

namespace MO322238

open MeasureTheory ProbabilityTheory Real Set

/-- The rate of the exponential law in direction `t`. -/
noncomputable def a (t : ℝ) : ℝ := 1 / (2 * (1 + sin t ^ 2))

/-- The density of `Z₁² + 2 Z₂²`. -/
noncomputable def g (x : ℝ) : ℝ :=
  if 0 < x then (1 / (2 * π)) * ∫ t in (-π)..π, a t * exp (-(x * a t)) else 0

/-- The distribution function of `Z₁² + 2 Z₂²`, as an extended nonnegative real. -/
noncomputable def G (s : ℝ) : ENNReal :=
  if 0 ≤ s then ∫⁻ t in Ioo (-π) π, ENNReal.ofReal ((1 - exp (-(s * a t))) / (2 * π)) else 0

/-- The standard Gaussian density in the plane. -/
noncomputable def φ2 (z : ℝ × ℝ) : ℝ := exp (-(z.1 ^ 2 + z.2 ^ 2) / 2) / (2 * π)

/-- The quadratic form `z₁² + 2 z₂²`. -/
def Q (z : ℝ × ℝ) : ℝ := z.1 ^ 2 + 2 * z.2 ^ 2

/-- The probability space: two independent standard Gaussians. -/
noncomputable abbrev μ0 : Measure (Fin 2 → ℝ) := Measure.pi fun _ => gaussianReal 0 1

/-- The weights. -/
noncomputable abbrev w0 : Fin 2 → ℝ := ![1, 2]

/-! ### Step 1: the probability space -/

lemma law_sq (i : Fin 2) :
    μ0.map (fun ω => ω i ^ 2) = OMA.S_mo_322238.chiSq ((fun _ : Fin 2 => (0 : ℝ)) i) := by
  have h := (measurePreserving_eval (fun _ : Fin 2 => gaussianReal 0 1) i).map_eq
  simp only [OMA.S_mo_322238.chiSq, Real.sqrt_zero]
  rw [← h]
  exact (Measure.map_map (g := fun z : ℝ => z ^ 2) (f := fun ω : Fin 2 → ℝ => ω i) (μ := μ0) (by fun_prop) (measurable_pi_apply i)).symm

lemma indep_sq : iIndepFun (fun (i : Fin 2) (ω : Fin 2 → ℝ) => ω i ^ 2) μ0 :=
  iIndepFun_pi (μ := fun _ => gaussianReal 0 1) (X := fun _ x => x ^ 2)
    (fun _ => (measurable_id.pow_const 2).aemeasurable)

lemma measurable_sq (i : Fin 2) : Measurable (fun ω : Fin 2 → ℝ => ω i ^ 2) :=
  (measurable_pi_apply i).pow_const 2

/-! ### Properties of `a` and `g` -/

lemma a_pos (t : ℝ) : 0 < a t := by
  unfold a; positivity

lemma continuous_a : Continuous a := by
  unfold a
  exact continuous_const.div (by fun_prop) (fun t => by positivity)

lemma g_nonneg (x : ℝ) : 0 ≤ g x := by
  unfold g
  split_ifs
  · apply mul_nonneg (by positivity)
    apply intervalIntegral.integral_nonneg (by linarith [pi_pos])
    intro t _
    exact mul_nonneg (a_pos t).le (exp_pos _).le
  · exact le_rfl

lemma g_measurable : Measurable g := by
  unfold g
  refine Measurable.ite measurableSet_Ioi ?_ measurable_const
  refine (continuous_const.mul ?_).measurable
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun x t => a t * exp (-(x * a t))) (by
      have := continuous_a
      fun_prop) _ _

/-! ### Step 2: the law of the weighted sum -/

lemma law_eq_planar :
    μ0.map (fun ω => ∑ i, w0 i * ω i ^ 2) =
      ((volume : Measure (ℝ × ℝ)).withDensity fun z => ENNReal.ofReal (φ2 z)).map Q := by
  have hQ : Measurable Q := by unfold Q; fun_prop
  have hfun : (fun ω : Fin 2 → ℝ => ∑ i, w0 i * ω i ^ 2) = Q ∘ MeasurableEquiv.finTwoArrow := by
    funext ω
    simp [Q, w0, Fin.sum_univ_two, MeasurableEquiv.finTwoArrow_apply]
  have hmp := (measurePreserving_finTwoArrow (gaussianReal 0 1)).map_eq
  rw [hfun, ← Measure.map_map hQ MeasurableEquiv.finTwoArrow.measurable, μ0, hmp]
  congr 1
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    prod_withDensity₀ (measurable_gaussianPDF 0 1).aemeasurable
      (measurable_gaussianPDF 0 1).aemeasurable, ← Measure.volume_eq_prod]
  congr 1
  funext z
  rw [gaussianPDF_def, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 1 _)]
  congr 1
  simp only [gaussianPDFReal, φ2, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_mul_mul_comm, ← exp_add, ← mul_inv, ← sqrt_mul (by positivity), sqrt_mul_self (by positivity)]
  rw [div_eq_mul_inv, mul_comm]
  congr 2
  ring

lemma lintegral_Ioc_ftc (f F : ℝ → ℝ) (b : ℝ) (hb : 0 ≤ b) (hf : Continuous f)
    (hnn : ∀ x, 0 ≤ x → 0 ≤ f x) (hF : ∀ x, HasDerivAt F (f x) x) :
    ∫⁻ x in Ioc 0 b, ENNReal.ofReal (f x) = ENNReal.ofReal (F b - F 0) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((hf.integrableOn_Icc).mono_set Ioc_subset_Icc_self)
    ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall
      (fun x hx => hnn x hx.1.le))),
    ← intervalIntegral.integral_of_le hb,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hF x)
      (hf.intervalIntegrable _ _)]

lemma g_eq_lintegral (x : ℝ) (hx : 0 < x) :
    ENNReal.ofReal (g x) = ∫⁻ t in Ioo (-π) π, ENNReal.ofReal (a t * exp (-(x * a t)) / (2 * π)) := by
  have hc : Continuous fun t => a t * exp (-(x * a t)) / (2 * π) := by
    have := continuous_a; fun_prop
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((hc.integrableOn_Icc).mono_set Ioo_subset_Icc_self)
    (Filter.Eventually.of_forall (fun t => by
      have := a_pos t; positivity)),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [pi_pos]),
    g, if_pos hx, intervalIntegral.integral_div]
  congr 1; ring

lemma inner_x (t s : ℝ) (hs : 0 ≤ s) :
    ∫⁻ x in Iic s, (if 0 < x then ENNReal.ofReal (a t * exp (-(x * a t)) / (2 * π)) else 0) =
      ENNReal.ofReal ((1 - exp (-(s * a t))) / (2 * π)) := by
  have ha := a_pos t
  have h1 : (fun x => if 0 < x then ENNReal.ofReal (a t * exp (-(x * a t)) / (2 * π)) else 0) =
      (Ioi 0).indicator (fun x => ENNReal.ofReal (a t * exp (-(x * a t)) / (2 * π))) := by
    funext x; simp [indicator]
  rw [h1, lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    Ioi_inter_Iic]
  rw [lintegral_Ioc_ftc _ (fun x => -exp (-(x * a t)) / (2 * π)) s hs (by
      have := continuous_a; fun_prop) (fun x _ => by positivity)]
  · congr 1; simp; ring
  · intro x
    have h := ((((hasDerivAt_id' x).mul_const (a t)).neg.exp).neg).div_const (2 * π)
    exact h.congr_deriv (by simp only [Pi.neg_apply]; ring)

lemma density_Iic (s : ℝ) :
    ((volume : Measure ℝ).withDensity fun x => ENNReal.ofReal (g x)) (Iic s) = G s := by
  rw [withDensity_apply _ measurableSet_Iic]
  by_cases hs : 0 ≤ s
  · rw [G, if_pos hs]
    have hK : ∀ x, ENNReal.ofReal (g x) = ∫⁻ t in Ioo (-π) π,
        (if 0 < x then ENNReal.ofReal (a t * exp (-(x * a t)) / (2 * π)) else 0) := by
      intro x
      by_cases hx : 0 < x
      · simp only [if_pos hx]; exact g_eq_lintegral x hx
      · simp [hx, g]
    simp_rw [hK]
    rw [lintegral_lintegral_swap]
    · exact setLIntegral_congr_fun measurableSet_Ioo (fun t _ => inner_x t s hs)
    · apply Measurable.aemeasurable
      apply Measurable.ite (measurableSet_lt measurable_const measurable_fst) _ measurable_const
      have := continuous_a
      apply Measurable.ennreal_ofReal
      fun_prop
  · rw [G, if_neg hs]
    apply setLIntegral_eq_zero_iff' measurableSet_Iic g_measurable.ennreal_ofReal.aemeasurable |>.mpr
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    have : ¬ 0 < x := by simp only [mem_Iic] at hx; linarith
    simp [g, this]

lemma Q_polar (r t : ℝ) : Q (r * cos t, r * sin t) = r ^ 2 * (1 + sin t ^ 2) := by
  simp only [Q]; nlinarith [sin_sq_add_cos_sq t]

lemma φ2_polar (r t : ℝ) : φ2 (r * cos t, r * sin t) = exp (-(r ^ 2) / 2) / (2 * π) := by
  simp only [φ2]
  congr 3
  nlinarith [sin_sq_add_cos_sq t]

lemma radial (t s : ℝ) (hs : 0 ≤ s) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r •
      (Q ⁻¹' Iic s).indicator (fun z => ENNReal.ofReal (φ2 z)) (r * cos t, r * sin t) =
      ENNReal.ofReal ((1 - exp (-(s * a t))) / (2 * π)) := by
  set q := 1 + sin t ^ 2 with hq
  have hq0 : 0 < q := by positivity
  set R := √(s / q) with hR
  have hR0 : 0 ≤ R := sqrt_nonneg _
  have hpt : ∀ r ∈ Ioi (0 : ℝ), ENNReal.ofReal r •
      (Q ⁻¹' Iic s).indicator (fun z => ENNReal.ofReal (φ2 z)) (r * cos t, r * sin t) =
      (Iic R).indicator (fun r => ENNReal.ofReal (r * exp (-(r ^ 2) / 2) / (2 * π))) r := by
    intro r hr
    have hr : 0 < r := hr
    have hiff : r ^ 2 * q ≤ s ↔ r ≤ R := by
      rw [hR, Real.le_sqrt hr.le (div_nonneg hs hq0.le), le_div_iff₀ hq0]
    by_cases h : r ≤ R
    · have h' : (r * cos t, r * sin t) ∈ Q ⁻¹' Iic s := by
        simp only [mem_preimage, mem_Iic, Q_polar]; exact hiff.2 h
      rw [indicator_of_mem h', indicator_of_mem (show r ∈ Iic R from h), φ2_polar, smul_eq_mul,
        ← ENNReal.ofReal_mul hr.le]
      congr 1; ring
    · have h' : (r * cos t, r * sin t) ∉ Q ⁻¹' Iic s := by
        simp only [mem_preimage, mem_Iic, Q_polar]; exact fun hh => h (hiff.1 hh)
      rw [indicator_of_notMem h', indicator_of_notMem (show r ∉ Iic R from h), smul_zero]
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt, lintegral_indicator measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic, Iic_inter_Ioi]
  rw [lintegral_Ioc_ftc _ (fun r => -exp (-(r ^ 2) / 2) / (2 * π)) R hR0 (by fun_prop)
    (fun x hx => by positivity)]
  · congr 1
    have hR2 : R ^ 2 = s / q := sq_sqrt (div_nonneg hs hq0.le)
    have ha : s * a t = s / q / 2 := by simp only [a, hq]; field_simp
    simp only [hR2, ha]; ring_nf; simp
  · intro x
    have h := (((hasDerivAt_pow 2 x).neg.div_const 2).exp.neg).div_const (2 * π)
    exact h.congr_deriv (by simp only [Pi.neg_apply]; ring)

lemma measurable_Q : Measurable Q := by unfold Q; fun_prop

lemma planar_Iic (s : ℝ) :
    (((volume : Measure (ℝ × ℝ)).withDensity fun z => ENNReal.ofReal (φ2 z)).map Q) (Iic s) =
      G s := by
  rw [Measure.map_apply measurable_Q measurableSet_Iic,
    withDensity_apply _ (measurable_Q measurableSet_Iic)]
  by_cases hs : 0 ≤ s
  · rw [G, if_pos hs, ← lintegral_indicator (measurable_Q measurableSet_Iic),
      ← lintegral_comp_polarCoord_symm, polarCoord_target, Measure.volume_eq_prod ℝ ℝ,
      ← Measure.prod_restrict, lintegral_prod_symm]
    · refine setLIntegral_congr_fun measurableSet_Ioo (fun t _ => ?_)
      simp only [polarCoord_symm_apply]
      exact radial t s hs
    · apply Measurable.aemeasurable
      simp only [polarCoord_symm_apply]
      refine (ENNReal.measurable_ofReal.comp measurable_fst).smul ?_
      refine Measurable.comp (g := (Q ⁻¹' Iic s).indicator (fun z => ENNReal.ofReal (φ2 z)))
        ?_ (by fun_prop)
      refine Measurable.indicator ?_ (measurable_Q measurableSet_Iic)
      apply Measurable.ennreal_ofReal
      unfold φ2; fun_prop
  · rw [G, if_neg hs]
    have : Q ⁻¹' Iic s = ∅ := by
      ext z
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false, not_le, Q]
      nlinarith [sq_nonneg z.1, sq_nonneg z.2]
    rw [this, Measure.restrict_empty, lintegral_zero_measure]

lemma law_sum :
    μ0.map (fun ω => ∑ i, w0 i * ω i ^ 2) =
      (volume : Measure ℝ).withDensity fun x => ENNReal.ofReal (g x) := by
  have : IsProbabilityMeasure (μ0.map (fun ω => ∑ i, w0 i * ω i ^ 2)) :=
    Measure.isProbabilityMeasure_map (Finset.measurable_sum _ (fun i _ => measurable_const.mul (measurable_sq i))).aemeasurable
  refine Measure.ext_of_Iic _ _ (fun s => ?_)
  rw [law_eq_planar, planar_Iic, density_Iic]

/-! ### Step 3: strict log-convexity of `g` -/

/-- The integral part of `g`. -/
noncomputable def I (y : ℝ) : ℝ := ∫ t in (-π)..π, a t * exp (-(y * a t))

lemma continuous_I_integrand (y : ℝ) : Continuous fun t => a t * exp (-(y * a t)) := by
  have := continuous_a; fun_prop

lemma I_pos (y : ℝ) : 0 < I y :=
  intervalIntegral.intervalIntegral_pos_of_pos_on
    ((continuous_I_integrand y).intervalIntegrable _ _)
    (fun t _ => mul_pos (a_pos t) (exp_pos _)) (by linarith [pi_pos])

lemma g_eq_I (y : ℝ) (hy : 0 < y) : g y = (1 / (2 * π)) * I y := by
  rw [g, if_pos hy, I]

/-- Pointwise AM-GM: `2 e^{-(x+1)a} ≤ λ e^{-x a} + λ⁻¹ e^{-(x+2)a}`, with equality iff
`λ e^a = 1`. -/
lemma amgm_point (x l s : ℝ) (hl : 0 < l) (hs : 0 < s) :
    2 * (s * exp (-((x + 1) * s))) ≤
      s * (l * exp (-(x * s)) + l⁻¹ * exp (-((x + 2) * s))) ∧
    (l * exp s ≠ 1 → 2 * (s * exp (-((x + 1) * s))) <
      s * (l * exp (-(x * s)) + l⁻¹ * exp (-((x + 2) * s)))) := by
  set E := exp (-((x + 1) * s)) with hE
  set k := l * exp s with hk
  have hk0 : 0 < k := by positivity
  have h1 : exp (-(x * s)) = E * exp s := by rw [hE, ← exp_add]; ring_nf
  have h2 : exp (-((x + 2) * s)) = E * (exp s)⁻¹ := by
    rw [hE, ← exp_neg, ← exp_add]; ring_nf
  have hR : s * (l * exp (-(x * s)) + l⁻¹ * exp (-((x + 2) * s))) = s * E * (k + k⁻¹) := by
    rw [h1, h2, hk, mul_inv]; ring
  have hE0 : 0 < s * E := by positivity
  rw [hR]
  have hkk : k + k⁻¹ - 2 = (k - 1) ^ 2 / k := by field_simp; ring
  constructor
  · have : 0 ≤ k + k⁻¹ - 2 := by rw [hkk]; positivity
    nlinarith
  · intro hne
    have : 0 < k + k⁻¹ - 2 := by
      have hne' : k - 1 ≠ 0 := sub_ne_zero.2 hne
      rw [hkk]; positivity
    nlinarith

lemma I_amgm (x l : ℝ) (hl : 0 < l) : 2 * I (x + 1) < l * I x + l⁻¹ * I (x + 2) := by
  have hc0 := continuous_I_integrand
  have hrhs : l * I x + l⁻¹ * I (x + 2) =
      ∫ t in (-π)..π, a t * (l * exp (-(x * a t)) + l⁻¹ * exp (-((x + 2) * a t))) := by
    have e : (fun t => a t * (l * exp (-(x * a t)) + l⁻¹ * exp (-((x + 2) * a t)))) =
        fun t => l * (a t * exp (-(x * a t))) + l⁻¹ * (a t * exp (-((x + 2) * a t))) := by
      funext t; ring
    rw [e, intervalIntegral.integral_add (((hc0 x).intervalIntegrable _ _).const_mul _)
      (((hc0 (x + 2)).intervalIntegrable _ _).const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, I, I]
  have hlhs : 2 * I (x + 1) = ∫ t in (-π)..π, 2 * (a t * exp (-((x + 1) * a t))) := by
    rw [intervalIntegral.integral_const_mul, I]
  rw [hrhs, hlhs]
  have := continuous_a
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by linarith [pi_pos]) (by fun_prop) (by fun_prop)
  · intro t _; exact (amgm_point x l (a t) hl (a_pos t)).1
  · -- a 0 = 1/2 and a (π/2) = 1/4, so l e^{a t} ≠ 1 at one of these points
    have ha0 : a 0 = 1 / 2 := by simp [a]
    have ha1 : a (π / 2) = 1 / 4 := by simp [a]; norm_num
    by_cases h : l * exp (a 0) = 1
    · refine ⟨π / 2, ⟨by linarith [pi_pos], by linarith [pi_pos]⟩, ?_⟩
      refine (amgm_point x l (a (π / 2)) hl (a_pos _)).2 ?_
      intro h'
      rw [ha0] at h; rw [ha1] at h'
      have : exp (1 / 2 : ℝ) = exp (1 / 4) := by
        have := h.trans h'.symm
        exact mul_left_cancel₀ hl.ne' this
      have := exp_injective this
      norm_num at this
    · exact ⟨0, ⟨by linarith [pi_pos], by linarith [pi_pos]⟩,
        (amgm_point x l (a 0) hl (a_pos _)).2 h⟩

lemma g_strict (x : ℝ) (hx : 0 < x) : g (x + 1) ^ 2 < g x * g (x + 2) := by
  have h0 := I_pos x
  have h2 := I_pos (x + 2)
  have h1 := I_pos (x + 1)
  set u := √(I (x + 2)) with hu
  set v := √(I x) with hv
  have hu0 : 0 < u := sqrt_pos.2 h2
  have hv0 : 0 < v := sqrt_pos.2 h0
  have key := I_amgm x (u / v) (div_pos hu0 hv0)
  have hu2 : u ^ 2 = I (x + 2) := sq_sqrt h2.le
  have hv2 : v ^ 2 = I x := sq_sqrt h0.le
  have e1 : u / v * I x = u * v := by rw [← hv2]; field_simp
  have e2 : (u / v)⁻¹ * I (x + 2) = u * v := by rw [← hu2, inv_div]; field_simp
  rw [e1, e2] at key
  have hlt : I (x + 1) < u * v := by linarith
  have hsq : I (x + 1) ^ 2 < I x * I (x + 2) := by
    calc I (x + 1) ^ 2 < (u * v) ^ 2 := by gcongr
      _ = I x * I (x + 2) := by rw [mul_pow, hu2, hv2, mul_comm]
  rw [g_eq_I _ (by linarith), g_eq_I _ hx, g_eq_I _ (by linarith)]
  have hc : 0 < 1 / (2 * π) := by positivity
  calc (1 / (2 * π) * I (x + 1)) ^ 2 = (1 / (2 * π)) ^ 2 * I (x + 1) ^ 2 := by ring
    _ < (1 / (2 * π)) ^ 2 * (I x * I (x + 2)) := by gcongr
    _ = _ := by ring

/-! ### Step 4: a log-concave density would be measurable and equal to `g` a.e. -/

lemma quasiconcave_of_logconcave (f : ℝ → ℝ) (hf0 : ∀ x, 0 ≤ f x)
    (hf : ∀ x y θ : ℝ, 0 ≤ θ → θ ≤ 1 → f x ^ θ * f y ^ (1 - θ) ≤ f (θ * x + (1 - θ) * y))
    (x y θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : min (f x) (f y) ≤ f (θ * x + (1 - θ) * y) := by
  set m := min (f x) (f y) with hm
  have hm0 : 0 ≤ m := le_min (hf0 x) (hf0 y)
  have hmx : m ^ θ ≤ f x ^ θ := rpow_le_rpow hm0 (min_le_left _ _) h0
  have hmy : m ^ (1 - θ) ≤ f y ^ (1 - θ) := rpow_le_rpow hm0 (min_le_right _ _) (by linarith)
  have hsplit : m = m ^ θ * m ^ (1 - θ) := by
    rw [← rpow_add' hm0 (by norm_num), add_sub_cancel, rpow_one]
  calc m = m ^ θ * m ^ (1 - θ) := hsplit
    _ ≤ f x ^ θ * f y ^ (1 - θ) :=
        mul_le_mul hmx hmy (rpow_nonneg hm0 _) (rpow_nonneg (hf0 x) _)
    _ ≤ _ := hf x y θ h0 h1

lemma measurable_of_quasiconcave (f : ℝ → ℝ)
    (hf : ∀ x y θ : ℝ, 0 ≤ θ → θ ≤ 1 → min (f x) (f y) ≤ f (θ * x + (1 - θ) * y)) :
    Measurable f := by
  refine measurable_of_Ioi (fun r => Set.OrdConnected.measurableSet ⟨fun x hx y hy z hz => ?_⟩)
  simp only [mem_preimage, mem_Ioi] at hx hy ⊢
  rcases eq_or_lt_of_le (hz.1.trans hz.2) with hxy | hxy
  · have : z = x := le_antisymm (hxy ▸ hz.2) hz.1
    rw [this]; exact hx
  · have hpos : 0 < y - x := by linarith
    have key := hf x y ((y - z) / (y - x)) (div_nonneg (by linarith [hz.2]) hpos.le)
      ((div_le_one hpos).2 (by linarith [hz.1]))
    have hz' : (y - z) / (y - x) * x + (1 - (y - z) / (y - x)) * y = z := by
      field_simp; ring
    rw [hz'] at key
    exact lt_of_lt_of_le (lt_min hx hy) key

lemma ae_eq_of_withDensity_eq (f h : ℝ → ℝ) (hf : Measurable f) (hh : Measurable h)
    (hf0 : ∀ x, 0 ≤ f x) (hh0 : ∀ x, 0 ≤ h x)
    (heq : (volume : Measure ℝ).withDensity (fun x => ENNReal.ofReal (f x)) =
      (volume : Measure ℝ).withDensity (fun x => ENNReal.ofReal (h x))) :
    f =ᵐ[volume] h := by
  have := (withDensity_eq_iff_of_sigmaFinite hf.ennreal_ofReal.aemeasurable
    hh.ennreal_ofReal.aemeasurable).1 heq
  filter_upwards [this] with x hx
  exact (ENNReal.ofReal_eq_ofReal_iff (hf0 x) (hh0 x)).1 hx

lemma exists_triple (f h : ℝ → ℝ) (hfh : f =ᵐ[volume] h) :
    ∃ x, 0 < x ∧ f x = h x ∧ f (x + 1) = h (x + 1) ∧ f (x + 2) = h (x + 2) := by
  have h1 : (fun x => f (x + 1)) =ᵐ[volume] (fun x => h (x + 1)) :=
    (measurePreserving_add_right volume (1 : ℝ)).quasiMeasurePreserving.ae_eq_comp hfh
  have h2 : (fun x => f (x + 2)) =ᵐ[volume] (fun x => h (x + 2)) :=
    (measurePreserving_add_right volume (2 : ℝ)).quasiMeasurePreserving.ae_eq_comp hfh
  have hne : (volume.restrict (Ioo (0 : ℝ) 1)) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero, Real.volume_Ioo]; norm_num
  have := ae_neBot.2 hne
  have hall : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      x ∈ Ioo (0 : ℝ) 1 ∧ f x = h x ∧ f (x + 1) = h (x + 1) ∧ f (x + 2) = h (x + 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hfh,
      ae_restrict_of_ae h1, ae_restrict_of_ae h2] with x hx e0 e1 e2
    exact ⟨hx, e0, e1, e2⟩
  obtain ⟨x, hx, e0, e1, e2⟩ := hall.exists
  exact ⟨x, hx.1, e0, e1, e2⟩

/-- A log-concave `f` agreeing with `g` at `x, x + 1, x + 2` (with `x > 0`) is impossible. -/
lemma false_of_triple (f : ℝ → ℝ)
    (hf : ∀ x y θ : ℝ, 0 ≤ θ → θ ≤ 1 → f x ^ θ * f y ^ (1 - θ) ≤ f (θ * x + (1 - θ) * y))
    (x : ℝ) (hx : 0 < x) (h0 : f x = g x) (h1 : f (x + 1) = g (x + 1))
    (h2 : f (x + 2) = g (x + 2)) : False := by
  have key := hf x (x + 2) (1 / 2) (by norm_num) (by norm_num)
  have hmid : 1 / 2 * x + (1 - 1 / 2) * (x + 2) = x + 1 := by ring
  rw [hmid, h0, h1, h2, ← sqrt_eq_rpow, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
    ← sqrt_eq_rpow] at key
  have hP : 0 ≤ √(g x) * √(g (x + 2)) := by positivity
  have hsq : (√(g x) * √(g (x + 2))) ^ 2 = g x * g (x + 2) := by
    rw [mul_pow, sq_sqrt (g_nonneg x), sq_sqrt (g_nonneg _)]
  have := pow_le_pow_left₀ hP key 2
  linarith [g_strict x hx]

/-- The law of `Z₁² + 2 Z₂²` has no log-concave density. -/
lemma not_logconcave :
    ¬ OMA.S_mo_322238.HasLogConcaveDensity (μ0.map fun ω => ∑ i, w0 i * ω i ^ 2) := by
  rintro ⟨f, hf0, hfeq, hf⟩
  rw [law_sum] at hfeq
  have hfm : Measurable f := measurable_of_quasiconcave f (quasiconcave_of_logconcave f hf0 hf)
  have hae : f =ᵐ[volume] g :=
    ae_eq_of_withDensity_eq f g hfm g_measurable hf0 g_nonneg hfeq.symm
  obtain ⟨x, hx, h0, h1, h2⟩ := exists_triple f g hae
  exact false_of_triple f hf x hx h0 h1 h2

end MO322238

theorem OMA.solution : type_of% @OMA.S_mo_322238.main := by
  intro H
  have hw : ∀ i, 0 < MO322238.w0 i := by
    intro i; fin_cases i <;> simp [MO322238.w0]
  exact MO322238.not_logconcave
    (H 2 (fun _ => 0) MO322238.w0 le_rfl (fun _ => le_rfl) hw (Fin 2 → ℝ) MO322238.μ0
      (fun i ω => ω i ^ 2) MO322238.measurable_sq MO322238.indep_sq MO322238.law_sq)
