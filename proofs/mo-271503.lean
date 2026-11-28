import OMAStatements.S_mo_271503

/-!
# Proof of mo-271503: Median and mean of the sample mean of i.i.d. log-normal

We prove that for any `n ≥ 1`, `μ ∈ ℝ`, `σ > 0`, and i.i.d. `x₁, …, xₙ ~ Lognormal(μ, σ²)`,
every median `m` of the sample mean `y = (1/n) ∑ᵢ xᵢ` satisfies `m < 𝔼[y]`.

Proof outline:
1. Gaussian CDF `Phi`, quantile function `PhiInv`, and the tangent-line concavity of the
   Gaussian isoperimetric profile `u ↦ phi (PhiInv u)`.
2. 1D heat semigroup `F(t, x) = PhiInv (P_t (Phi ∘ f) x)`, its PDE `F_t = (1/2) (F_xx - F F_x^2)`,
   uniform gradient bound `|F_x| ≤ S`, and a self-contained proof of the 1D functional Ehrhard
   inequality (`ehrhard_1d_lipschitz`) via the parabolic maximum principle.
3. Induction on `n ≥ 1`: the law of `∑ᵢ exp (σ Zᵢ)` (`Zᵢ ~ N(0, 1)` i.i.d.) equals the pushforward
   of `N(0, 1)` by a strictly increasing, continuous, convex, positive quantile function `Qₙ`
   (`exists_goodQuantile_lognormLaw`), using `S`-Lipschitz sup-convolution regularization and
   the 1D Ehrhard inequality at each convolution step.
4. Strict Jensen inequality (`convex_strict_jensen_gaussian`) shows `Qₙ 0 < 𝔼[Qₙ(G)]`, giving
   `ℙ(y < 𝔼[y]) > 1/2` and therefore `m < 𝔼[y]` for every median `m` of `y`.
-/

namespace OMA.P271503

open MeasureTheory ProbabilityTheory Filter Set Real
open scoped Topology NNReal ENNReal

section GaussianCDF

/-- Standard normal probability density function. -/
noncomputable def phi (x : ℝ) : ℝ :=
  gaussianPDFReal 0 1 x

/-- Standard normal cumulative distribution function. -/
noncomputable def Phi (x : ℝ) : ℝ :=
  ∫ t in Iic x, phi t

lemma phi_eq (x : ℝ) : phi x = (√(2 * π))⁻¹ * exp (-x ^ 2 / 2) := by
  simp [phi, gaussianPDFReal]

lemma phi_pos (x : ℝ) : 0 < phi x :=
  gaussianPDFReal_pos 0 1 x one_ne_zero

lemma phi_nonneg (x : ℝ) : 0 ≤ phi x :=
  (phi_pos x).le

lemma phi_neg (x : ℝ) : phi (-x) = phi x := by
  simp [phi_eq]

lemma integrable_phi : Integrable phi :=
  integrable_gaussianPDFReal 0 1

lemma integral_phi_eq_one : ∫ x, phi x = 1 :=
  integral_gaussianPDFReal_eq_one 0 one_ne_zero

lemma hasDerivAt_phi (x : ℝ) : HasDerivAt phi (-x * phi x) x := by
  have h1 : HasDerivAt (fun t : ℝ => -t ^ 2 / 2) (-x) x := by
    have := ((hasDerivAt_pow 2 x).neg).div_const 2
    exact this.congr_deriv (by ring)
  have h2 : HasDerivAt (fun t : ℝ => (√(2 * π))⁻¹ * exp (-t ^ 2 / 2))
      ((√(2 * π))⁻¹ * (exp (-x ^ 2 / 2) * (-x))) x :=
    (h1.exp).const_mul _
  have hfun : (fun t : ℝ => (√(2 * π))⁻¹ * exp (-t ^ 2 / 2)) = phi := by
    ext t; exact (phi_eq t).symm
  rw [hfun] at h2
  exact h2.congr_deriv (by rw [phi_eq]; ring)

lemma continuous_phi : Continuous phi :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_phi x).continuousAt

lemma phi_le_one (x : ℝ) : phi x ≤ 1 := by
  rw [phi_eq]
  have h1 : exp (-x ^ 2 / 2) ≤ 1 := exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  have h2 : 1 ≤ √(2 * π) := by
    rw [one_le_sqrt]
    nlinarith [Real.pi_gt_three]
  have h3 : (√(2 * π))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h2
  nlinarith [exp_pos (-x ^ 2 / 2)]

lemma abs_deriv_phi_le_one (x : ℝ) : |-x * phi x| ≤ 1 := by
  rw [abs_mul, abs_neg, abs_of_pos (phi_pos x), phi_eq]
  have hsq : |x| ≤ exp (x ^ 2 / 2) := by
    have h1 : 1 + x ^ 2 / 2 ≤ exp (x ^ 2 / 2) := by
      linarith [add_one_le_exp (x ^ 2 / 2)]
    have h2 : |x| ≤ 1 + x ^ 2 / 2 := by
      have : (|x| - 1) ^ 2 ≥ 0 := sq_nonneg _
      have : |x| ^ 2 = x ^ 2 := sq_abs x
      nlinarith
    linarith
  have hmul : |x| * exp (-x ^ 2 / 2) ≤ 1 := by
    have hexp : exp (-x ^ 2 / 2) = (exp (x ^ 2 / 2))⁻¹ := by
      rw [neg_div, exp_neg]
    rw [hexp]
    exact (mul_inv_le_iff₀ (exp_pos _)).mpr (by linarith)
  have hsqrt : (√(2 * π))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by rw [one_le_sqrt]; nlinarith [Real.pi_gt_three])
  calc |x| * ((√(2 * π))⁻¹ * exp (-x ^ 2 / 2))
      = (√(2 * π))⁻¹ * (|x| * exp (-x ^ 2 / 2)) := by ring
    _ ≤ 1 * 1 := mul_le_mul hsqrt hmul (by positivity) zero_le_one
    _ = 1 := one_mul 1

lemma phi_lipschitz (x y : ℝ) : |phi x - phi y| ≤ |x - y| := by
  have hdiff : Differentiable ℝ phi := fun t => (hasDerivAt_phi t).differentiableAt
  have hbound : ∀ t : ℝ, ‖deriv phi t‖ ≤ 1 := fun t => by
    rw [(hasDerivAt_phi t).deriv, Real.norm_eq_abs]
    exact abs_deriv_phi_le_one t
  have hlip := Convex.norm_image_sub_le_of_norm_deriv_le (fun t _ => hdiff t)
    (fun t _ => hbound t) convex_univ (mem_univ y) (mem_univ x)
  simpa [Real.norm_eq_abs] using hlip

lemma Phi_eq_gaussianReal (x : ℝ) : Phi x = (gaussianReal 0 1).real (Iic x) := by
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero (Iic x)]
  rw [ENNReal.toReal_ofReal]
  · rfl
  · exact setIntegral_nonneg measurableSet_Iic fun t _ => phi_nonneg t

lemma Phi_sub_Phi_of_le {a b : ℝ} (hab : a ≤ b) : Phi b - Phi a = ∫ t in a..b, phi t := by
  unfold Phi
  have hunion : Iic b = Iic a ∪ Ioc a b := (Iic_union_Ioc_eq_Iic hab).symm
  have hdisj : Disjoint (Iic a) (Ioc a b) := Iic_disjoint_Ioc le_rfl
  rw [hunion, setIntegral_union hdisj measurableSet_Ioc integrable_phi.integrableOn
    integrable_phi.integrableOn, add_sub_cancel_left, intervalIntegral.integral_of_le hab]

lemma Phi_sub_Phi (a b : ℝ) : Phi b - Phi a = ∫ t in a..b, phi t := by
  rcases le_total a b with hab | hba
  · exact Phi_sub_Phi_of_le hab
  · rw [intervalIntegral.integral_symm, ← Phi_sub_Phi_of_le hba]; ring

lemma hasDerivAt_Phi (x : ℝ) : HasDerivAt Phi (phi x) x := by
  have h : HasDerivAt (fun y : ℝ => Phi 0 + ∫ t in (0 : ℝ)..y, phi t) (phi x) x := by
    have h1 := intervalIntegral.integral_hasDerivAt_right (continuous_phi.intervalIntegrable 0 x)
      (continuous_phi.stronglyMeasurableAtFilter volume (𝓝 x)) continuous_phi.continuousAt
    simpa using h1.const_add (Phi 0)
  convert h using 1
  ext y
  linarith [Phi_sub_Phi 0 y]

lemma continuous_Phi : Continuous Phi :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_Phi x).continuousAt

lemma Phi_strictMono : StrictMono Phi :=
  strictMono_of_deriv_pos fun x => by
    rw [(hasDerivAt_Phi x).deriv]
    exact phi_pos x

lemma Phi_nonneg (x : ℝ) : 0 ≤ Phi x :=
  setIntegral_nonneg measurableSet_Iic fun t _ => phi_nonneg t

lemma Phi_le_one (x : ℝ) : Phi x ≤ 1 := by
  rw [← integral_phi_eq_one]
  exact setIntegral_le_integral integrable_phi (ae_of_all _ phi_nonneg)

lemma Phi_pos (x : ℝ) : 0 < Phi x :=
  lt_of_le_of_lt (Phi_nonneg (x - 1)) (Phi_strictMono (by linarith))

lemma Phi_lt_one (x : ℝ) : Phi x < 1 :=
  lt_of_lt_of_le (Phi_strictMono (by linarith : x < x + 1)) (Phi_le_one (x + 1))

lemma Phi_lipschitz (x y : ℝ) : |Phi x - Phi y| ≤ |x - y| := by
  have hdiff : Differentiable ℝ Phi := fun t => (hasDerivAt_Phi t).differentiableAt
  have hbound : ∀ t : ℝ, ‖deriv Phi t‖ ≤ 1 := fun t => by
    rw [(hasDerivAt_Phi t).deriv, Real.norm_eq_abs, abs_of_pos (phi_pos t)]
    exact phi_le_one t
  have hlip := Convex.norm_image_sub_le_of_norm_deriv_le (fun t _ => hdiff t)
    (fun t _ => hbound t) convex_univ (mem_univ y) (mem_univ x)
  simpa [Real.norm_eq_abs] using hlip

lemma Phi_zero : Phi 0 = 1 / 2 := by
  have hsum : (∫ t in Iic (0 : ℝ), phi t) + (∫ t in (Iic (0 : ℝ))ᶜ, phi t) = ∫ t, phi t :=
    integral_add_compl measurableSet_Iic integrable_phi
  have hcompl : (Iic (0 : ℝ))ᶜ = Ioi 0 := compl_Iic
  rw [hcompl, integral_phi_eq_one] at hsum
  have hsym : ∫ t in Ioi (0 : ℝ), phi t = ∫ t in Iic (0 : ℝ), phi t := by
    have h1 := integral_comp_neg_Ioi (c := (0 : ℝ)) (f := phi)
    rw [neg_zero] at h1
    simp_rw [phi_neg] at h1
    exact h1
  unfold Phi
  linarith

lemma Phi_tendsto_zero : Tendsto Phi atBot (𝓝 0) := by
  have h1 : ∀ x : ℝ, Phi x = ∫ t, (Iic x).indicator phi t := fun x =>
    (integral_indicator measurableSet_Iic).symm
  change Tendsto (fun x => Phi x) atBot (𝓝 0)
  simp_rw [h1]
  have h0 : (0 : ℝ) = ∫ _ : ℝ, (0 : ℝ) := (integral_zero ℝ ℝ).symm
  rw [h0]
  refine tendsto_integral_filter_of_dominated_convergence phi ?_ ?_ integrable_phi ?_
  · exact Eventually.of_forall fun x =>
      (continuous_phi.aestronglyMeasurable).indicator measurableSet_Iic
  · exact Eventually.of_forall fun x => ae_of_all _ fun t => by
      rw [Real.norm_eq_abs]
      by_cases ht : t ∈ Iic x
      · rw [Set.indicator_of_mem ht, abs_of_nonneg (phi_nonneg t)]
      · rw [Set.indicator_of_notMem ht, abs_zero]
        exact phi_nonneg t
  · refine ae_of_all _ fun t => tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_lt_atBot t] with x hx
    exact (Set.indicator_of_notMem (show t ∉ Iic x from not_le.mpr hx) phi).symm

lemma Phi_tendsto_one : Tendsto Phi atTop (𝓝 1) := by
  have h1 : ∀ x : ℝ, Phi x = ∫ t, (Iic x).indicator phi t := fun x =>
    (integral_indicator measurableSet_Iic).symm
  change Tendsto (fun x => Phi x) atTop (𝓝 1)
  simp_rw [h1, ← integral_phi_eq_one]
  refine tendsto_integral_filter_of_dominated_convergence phi ?_ ?_ integrable_phi ?_
  · exact Eventually.of_forall fun x =>
      (continuous_phi.aestronglyMeasurable).indicator measurableSet_Iic
  · exact Eventually.of_forall fun x => ae_of_all _ fun t => by
      rw [Real.norm_eq_abs]
      by_cases ht : t ∈ Iic x
      · rw [Set.indicator_of_mem ht, abs_of_nonneg (phi_nonneg t)]
      · rw [Set.indicator_of_notMem ht, abs_zero]
        exact phi_nonneg t
  · refine ae_of_all _ fun t => tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop t] with x hx
    exact (Set.indicator_of_mem (show t ∈ Iic x from hx) phi).symm

lemma Phi_surj_Ioo {u : ℝ} (hu : u ∈ Ioo 0 1) : ∃ x : ℝ, Phi x = u := by
  have ha : ∃ a : ℝ, Phi a < u := (Phi_tendsto_zero.eventually (gt_mem_nhds hu.1)).exists
  have hb : ∃ b : ℝ, u < Phi b := (Phi_tendsto_one.eventually (lt_mem_nhds hu.2)).exists
  obtain ⟨a, ha⟩ := ha
  obtain ⟨b, hb⟩ := hb
  have hab : a ≤ b := le_of_lt (Phi_strictMono.lt_iff_lt.mp (ha.trans hb))
  obtain ⟨x, _, hx⟩ := intermediate_value_Icc hab continuous_Phi.continuousOn ⟨ha.le, hb.le⟩
  exact ⟨x, hx⟩

/-- Inverse of the standard normal CDF on `(0, 1)`. -/
noncomputable def PhiInv (u : ℝ) : ℝ :=
  if hu : u ∈ Ioo 0 1 then Classical.choose (Phi_surj_Ioo hu) else 0

lemma Phi_PhiInv {u : ℝ} (hu : u ∈ Ioo 0 1) : Phi (PhiInv u) = u := by
  simp only [PhiInv, dif_pos hu]
  exact Classical.choose_spec (Phi_surj_Ioo hu)

lemma PhiInv_Phi (x : ℝ) : PhiInv (Phi x) = x :=
  Phi_strictMono.injective (Phi_PhiInv ⟨Phi_pos x, Phi_lt_one x⟩)

lemma PhiInv_strictMonoOn : StrictMonoOn PhiInv (Ioo 0 1) := by
  intro u hu v hv huv
  by_contra hle
  push Not at hle
  have := Phi_strictMono.monotone hle
  rw [Phi_PhiInv hu, Phi_PhiInv hv] at this
  linarith

lemma PhiInv_zero_half : PhiInv (1 / 2) = 0 := by
  rw [← Phi_zero, PhiInv_Phi]

lemma continuousAt_PhiInv {u : ℝ} (hu : u ∈ Ioo 0 1) : ContinuousAt PhiInv u := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  set x := PhiInv u
  have hl : Phi (x - ε) < u := by
    rw [← Phi_PhiInv hu]
    exact Phi_strictMono (by linarith)
  have hr : u < Phi (x + ε) := by
    rw [← Phi_PhiInv hu]
    exact Phi_strictMono (by linarith)
  set δ := min (min (u - Phi (x - ε)) (Phi (x + ε) - u)) (min u (1 - u))
  have hδ : 0 < δ := lt_min (lt_min (by linarith) (by linarith)) (lt_min hu.1 (by linarith [hu.2]))
  refine ⟨δ, hδ, fun v hv => ?_⟩
  rw [Real.dist_eq] at hv ⊢
  have hv_mem : v ∈ Ioo 0 1 := by
    constructor
    · have : δ ≤ u := le_trans (min_le_right _ _) (min_le_left _ _)
      linarith [(abs_lt.mp hv).1]
    · have : δ ≤ 1 - u := le_trans (min_le_right _ _) (min_le_right _ _)
      linarith [(abs_lt.mp hv).2]
  have h1 : Phi (x - ε) < v := by
    have : δ ≤ u - Phi (x - ε) := le_trans (min_le_left _ _) (min_le_left _ _)
    linarith [(abs_lt.mp hv).1]
  have h2 : v < Phi (x + ε) := by
    have : δ ≤ Phi (x + ε) - u := le_trans (min_le_left _ _) (min_le_right _ _)
    linarith [(abs_lt.mp hv).2]
  have hx1 : x - ε < PhiInv v := by
    rw [← PhiInv_Phi (x - ε)]
    exact PhiInv_strictMonoOn ⟨Phi_pos _, Phi_lt_one _⟩ hv_mem h1
  have hx2 : PhiInv v < x + ε := by
    rw [← PhiInv_Phi (x + ε)]
    exact PhiInv_strictMonoOn hv_mem ⟨Phi_pos _, Phi_lt_one _⟩ h2
  rw [abs_lt]
  exact ⟨by linarith, by linarith⟩

lemma hasDerivAt_PhiInv {u : ℝ} (hu : u ∈ Ioo 0 1) :
    HasDerivAt PhiInv (phi (PhiInv u))⁻¹ u := by
  have hne : phi (PhiInv u) ≠ 0 := (phi_pos _).ne'
  have hleft : ∀ᶠ v in 𝓝 u, Phi (PhiInv v) = v := by
    filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
    exact Phi_PhiInv hv
  exact (hasDerivAt_Phi (PhiInv u)).of_local_left_inverse (continuousAt_PhiInv hu) hne hleft

lemma hasDerivAt_isoProfile {u : ℝ} (hu : u ∈ Ioo 0 1) :
    HasDerivAt (fun v => phi (PhiInv v)) (-PhiInv u) u := by
  have h := (hasDerivAt_phi (PhiInv u)).comp u (hasDerivAt_PhiInv hu)
  have hne : phi (PhiInv u) ≠ 0 := (phi_pos _).ne'
  exact h.congr_deriv (by rw [mul_assoc, mul_inv_cancel₀ hne, mul_one])

/-- Tangent-line inequality for the concave Gaussian isoperimetric profile `u ↦ phi (PhiInv u)`. -/
lemma isoProfile_le_tangent {u u₀ : ℝ} (hu : u ∈ Ioo 0 1) (hu₀ : u₀ ∈ Ioo 0 1) :
    phi (PhiInv u) ≤ phi (PhiInv u₀) + (-PhiInv u₀) * (u - u₀) := by
  rcases lt_trichotomy u u₀ with hlt | rfl | hgt
  · have hsub : Icc u u₀ ⊆ Ioo 0 1 := fun z hz => ⟨lt_of_lt_of_le hu.1 hz.1, lt_of_le_of_lt hz.2 hu₀.2⟩
    have hcont : ContinuousOn (fun v => phi (PhiInv v)) (Icc u u₀) :=
      fun z hz => (hasDerivAt_isoProfile (hsub hz)).continuousAt.continuousWithinAt
    have hdiff : ∀ z ∈ Ioo u u₀, HasDerivAt (fun v => phi (PhiInv v)) (-PhiInv z) z :=
      fun z hz => hasDerivAt_isoProfile (hsub ⟨hz.1.le, hz.2.le⟩)
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun v => phi (PhiInv v))
      (fun v => -PhiInv v) hlt hcont hdiff
    have hc_mem : c ∈ Ioo 0 1 := hsub ⟨hc.1.le, hc.2.le⟩
    have hle : PhiInv c ≤ PhiInv u₀ := (PhiInv_strictMonoOn hc_mem hu₀ hc.2).le
    have hdiv : phi (PhiInv u₀) - phi (PhiInv u) = (-PhiInv c) * (u₀ - u) := by
      rw [hslope, div_mul_cancel₀ _ (sub_ne_zero.mpr hlt.ne')]
    nlinarith
  · simp
  · have hsub : Icc u₀ u ⊆ Ioo 0 1 := fun z hz => ⟨lt_of_lt_of_le hu₀.1 hz.1, lt_of_le_of_lt hz.2 hu.2⟩
    have hcont : ContinuousOn (fun v => phi (PhiInv v)) (Icc u₀ u) :=
      fun z hz => (hasDerivAt_isoProfile (hsub hz)).continuousAt.continuousWithinAt
    have hdiff : ∀ z ∈ Ioo u₀ u, HasDerivAt (fun v => phi (PhiInv v)) (-PhiInv z) z :=
      fun z hz => hasDerivAt_isoProfile (hsub ⟨hz.1.le, hz.2.le⟩)
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun v => phi (PhiInv v))
      (fun v => -PhiInv v) hgt hcont hdiff
    have hc_mem : c ∈ Ioo 0 1 := hsub ⟨hc.1.le, hc.2.le⟩
    have hle : PhiInv u₀ ≤ PhiInv c := (PhiInv_strictMonoOn hu₀ hc_mem hc.1).le
    have hdiv : phi (PhiInv u) - phi (PhiInv u₀) = (-PhiInv c) * (u - u₀) := by
      rw [hslope, div_mul_cancel₀ _ (sub_ne_zero.mpr hgt.ne')]
    nlinarith

/-- Elementary Gaussian tail shift inequality: for `v ≤ 0` and `A ≥ 0`,
`Phi (v - A) ≤ exp (-A^2 / 2) * Phi v`. -/
lemma Phi_sub_le_exp_mul_Phi {v A : ℝ} (hv : v ≤ 0) (hA : 0 ≤ A) :
    Phi (v - A) ≤ exp (-A ^ 2 / 2) * Phi v := by
  unfold Phi
  have hshift : ∫ t in Iic (v - A), phi t = ∫ t in Iic v, phi (t - A) := by
    have h1 : ∀ c : ℝ, ∫ t in Iic c, phi t = ∫ t, (Iic c).indicator phi t := fun c =>
      (integral_indicator measurableSet_Iic).symm
    have h2 : ∫ t in Iic v, phi (t - A) = ∫ t, (Iic v).indicator (fun s => phi (s - A)) t :=
      (integral_indicator measurableSet_Iic).symm
    rw [h1, h2]
    rw [← integral_sub_right_eq_self (fun t => (Iic (v - A)).indicator phi t) A]
    congr 1
    ext t
    by_cases ht : t ≤ v
    · have ht' : t - A ≤ v - A := by linarith
      simp [Set.indicator_of_mem (show t ∈ Iic v from ht),
        Set.indicator_of_mem (show t - A ∈ Iic (v - A) from ht')]
    · have ht' : ¬ t - A ≤ v - A := by linarith
      simp [Set.indicator_of_notMem (show t ∉ Iic v from ht),
        Set.indicator_of_notMem (show t - A ∉ Iic (v - A) from ht')]
  rw [hshift, ← integral_const_mul]
  refine setIntegral_mono_on ?_ (integrable_phi.const_mul _).integrableOn measurableSet_Iic ?_
  · exact (integrable_phi.comp_sub_right A).integrableOn
  · intro t ht
    have ht0 : t ≤ 0 := le_trans ht hv
    rw [phi_eq, phi_eq]
    have hexp : exp (-(t - A) ^ 2 / 2) = exp (A * t - A ^ 2 / 2) * exp (-t ^ 2 / 2) := by
      rw [← exp_add]
      congr 1
      ring
    rw [hexp]
    have hle : exp (A * t - A ^ 2 / 2) ≤ exp (-A ^ 2 / 2) :=
      exp_le_exp.mpr (by nlinarith)
    have hpos : 0 ≤ (√(2 * π))⁻¹ * exp (-t ^ 2 / 2) := by positivity
    calc (√(2 * π))⁻¹ * (exp (A * t - A ^ 2 / 2) * exp (-t ^ 2 / 2))
        = exp (A * t - A ^ 2 / 2) * ((√(2 * π))⁻¹ * exp (-t ^ 2 / 2)) := by ring
      _ ≤ exp (-A ^ 2 / 2) * ((√(2 * π))⁻¹ * exp (-t ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_right hle hpos

/-- For any `c₀ ∈ (0, 1)`, there exists `A ≥ 0` such that `PhiInv (c₀ * Phi v) ≥ v - A`
for all `v ≤ 0`. -/
lemma exists_shift_PhiInv_mul_Phi {c₀ : ℝ} (hc₀ : 0 < c₀) (hc₁ : c₀ ≤ 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ v : ℝ, v ≤ 0 → v - A ≤ PhiInv (c₀ * Phi v) := by
  set A := √(2 * (-Real.log c₀))
  have hlog : 0 ≤ -Real.log c₀ := by
    have := Real.log_nonpos hc₀.le hc₁
    linarith
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  refine ⟨A, hA, fun v hv => ?_⟩
  have hAsq : A ^ 2 = 2 * (-Real.log c₀) := Real.sq_sqrt (by linarith)
  have hexp : exp (-A ^ 2 / 2) = c₀ := by
    rw [hAsq, show -(2 * -Real.log c₀) / 2 = Real.log c₀ by ring, Real.exp_log hc₀]
  have hle : Phi (v - A) ≤ c₀ * Phi v := by
    rw [← hexp]
    exact Phi_sub_le_exp_mul_Phi hv hA
  have hmem : c₀ * Phi v ∈ Ioo 0 1 := by
    constructor
    · exact mul_pos hc₀ (Phi_pos v)
    · calc c₀ * Phi v ≤ 1 * Phi v := mul_le_mul_of_nonneg_right hc₁ (Phi_nonneg v)
        _ = Phi v := one_mul _
        _ < 1 := Phi_lt_one v
  rw [← PhiInv_Phi (v - A)]
  rcases eq_or_lt_of_le hle with heq | hlt
  · rw [heq]
  · exact (PhiInv_strictMonoOn ⟨Phi_pos _, Phi_lt_one _⟩ hmem hlt).le

end GaussianCDF

section HeatSemigroup

/-- 1D heat kernel at time `t > 0`. -/
noncomputable def heatKer (t u : ℝ) : ℝ :=
  (√(2 * π * t))⁻¹ * exp (-u ^ 2 / (2 * t))

/-- First spatial derivative `-∂_u heatKer t u = (u / t) * heatKer t u`. -/
noncomputable def heatKer_x (t u : ℝ) : ℝ :=
  (u / t) * heatKer t u

/-- Second spatial derivative `∂_{uu} heatKer t u = ((u^2 / t - 1) / t) * heatKer t u`. -/
noncomputable def heatKer_xx (t u : ℝ) : ℝ :=
  ((u ^ 2 / t - 1) / t) * heatKer t u

/-- 1D heat semigroup `P_t f (x)`. -/
noncomputable def heat (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  if t ≤ 0 then f x else ∫ y, f y * heatKer t (y - x)

/-- First spatial derivative of `heat f t`. -/
noncomputable def heat_x (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  ∫ y, f y * heatKer_x t (y - x)

/-- Second spatial derivative of `heat f t`. -/
noncomputable def heat_xx (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  ∫ y, f y * heatKer_xx t (y - x)

lemma heatKer_pos {t : ℝ} (ht : 0 < t) (u : ℝ) : 0 < heatKer t u := by
  unfold heatKer
  positivity

lemma heatKer_nonneg {t : ℝ} (ht : 0 < t) (u : ℝ) : 0 ≤ heatKer t u :=
  (heatKer_pos ht u).le

lemma heatKer_eq_gaussianPDFReal {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    heatKer t (y - x) = gaussianPDFReal x (Real.toNNReal t) y := by
  simp [heatKer, gaussianPDFReal, Real.coe_toNNReal t ht.le]

lemma heat_of_pos (f : ℝ → ℝ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    heat f t x = ∫ y, f y * heatKer t (y - x) := by
  simp [heat, not_le.mpr ht]

lemma heat_zero (f : ℝ → ℝ) (x : ℝ) : heat f 0 x = f x := by
  simp [heat]

lemma heat_eq_integral_phi (f : ℝ → ℝ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    heat f t x = ∫ z, f (x + √t * z) * phi z := by
  rw [heat_of_pos f ht x]
  have h1 : ∫ y, f y * heatKer t (y - x) = ∫ u, f (x + u) * heatKer t u := by
    rw [← integral_add_left_eq_self (fun y => f y * heatKer t (y - x)) x]
    congr 1; ext u; ring_nf
  rw [h1]
  have hst : 0 < √t := Real.sqrt_pos.mpr ht
  have hmul := Measure.integral_comp_mul_left (fun u => f (x + u) * heatKer t u) (√t)
  rw [abs_of_pos (inv_pos.mpr hst), smul_eq_mul] at hmul
  have h2 : ∫ u, f (x + u) * heatKer t u = √t * ∫ z, f (x + √t * z) * heatKer t (√t * z) := by
    rw [hmul, ← mul_assoc, mul_inv_cancel₀ hst.ne', one_mul]
  rw [h2, ← integral_const_mul]
  congr 1
  ext z
  have hker : √t * heatKer t (√t * z) = phi z := by
    rw [heatKer, phi_eq]
    have hsq : (√t * z) ^ 2 / (2 * t) = z ^ 2 / 2 := by
      rw [mul_pow, Real.sq_sqrt ht.le]
      field_simp [ht.ne']
    rw [show -(√t * z) ^ 2 / (2 * t) = -((√t * z) ^ 2 / (2 * t)) by ring, hsq,
      show -(z ^ 2 / 2) = -z ^ 2 / 2 by ring]
    have hrt : √(2 * π * t) = √(2 * π) * √t := Real.sqrt_mul (by positivity) t
    rw [hrt, mul_inv]
    have hst_ne : √t ≠ 0 := hst.ne'
    field_simp [hst_ne]
  calc √t * (f (x + √t * z) * heatKer t (√t * z))
      = f (x + √t * z) * (√t * heatKer t (√t * z)) := by ring
    _ = f (x + √t * z) * phi z := by rw [hker]

lemma heat_eq_integral_gaussianReal (f : ℝ → ℝ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    heat f t x = ∫ z, f (x + √t * z) ∂(gaussianReal 0 1) := by
  rw [heat_eq_integral_phi f ht x, integral_gaussianReal_eq_integral_smul one_ne_zero]
  congr 1
  ext z
  simp [phi, smul_eq_mul, mul_comm]

lemma integrable_abs_mul_phi : Integrable (fun z : ℝ => |z| * phi z) := by
  have hdom : Integrable (fun z : ℝ => 2 * (√(2 * π))⁻¹ * exp (-(1 / 4 : ℝ) * z ^ 2)) :=
    (integrable_exp_neg_mul_sq (by norm_num)).const_mul _
  refine hdom.mono' (continuous_abs.mul continuous_phi).aestronglyMeasurable (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg z) (phi_nonneg z)), phi_eq]
  have h1 : |z| ≤ 2 * exp (z ^ 2 / 4) := by
    have h1a : 1 + z ^ 2 / 4 ≤ exp (z ^ 2 / 4) := by linarith [add_one_le_exp (z ^ 2 / 4)]
    have h1b : |z| ≤ 2 + z ^ 2 / 2 := by
      have : (|z| - 1) ^ 2 ≥ 0 := sq_nonneg _
      have : |z| ^ 2 = z ^ 2 := sq_abs z
      nlinarith
    linarith
  have h2 : exp (-z ^ 2 / 2) = exp (-z ^ 2 / 4) * exp (-(1 / 4 : ℝ) * z ^ 2) := by
    rw [← exp_add]; congr 1; ring
  have h3 : |z| * exp (-z ^ 2 / 2) ≤ 2 * exp (-(1 / 4 : ℝ) * z ^ 2) := by
    rw [h2]
    have h4 : |z| * exp (-z ^ 2 / 4) ≤ 2 := by
      have : exp (-z ^ 2 / 4) = (exp (z ^ 2 / 4))⁻¹ := by rw [neg_div, exp_neg]
      rw [this]
      exact (mul_inv_le_iff₀ (exp_pos _)).mpr (by linarith)
    nlinarith [exp_pos (-(1 / 4 : ℝ) * z ^ 2)]
  have hpos : 0 ≤ (√(2 * π))⁻¹ := by positivity
  calc |z| * ((√(2 * π))⁻¹ * exp (-z ^ 2 / 2))
      = (√(2 * π))⁻¹ * (|z| * exp (-z ^ 2 / 2)) := by ring
    _ ≤ (√(2 * π))⁻¹ * (2 * exp (-(1 / 4 : ℝ) * z ^ 2)) := mul_le_mul_of_nonneg_left h3 hpos
    _ = 2 * (√(2 * π))⁻¹ * exp (-(1 / 4 : ℝ) * z ^ 2) := by ring

lemma heat_integrable_phi {f : ℝ → ℝ} (hfc : Continuous f)
    (hfb : ∀ y, |f y| ≤ 1) {t : ℝ} (x : ℝ) :
    Integrable (fun z => f (x + √t * z) * phi z) := by
  refine integrable_phi.mono' ((hfc.comp (by fun_prop)).mul continuous_phi).aestronglyMeasurable
    (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (phi_nonneg z)]
  nlinarith [hfb (x + √t * z), phi_nonneg z]

lemma heat_mem_Ioo {f : ℝ → ℝ} (hfc : Continuous f) (hf01 : ∀ y, f y ∈ Ioo 0 1)
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ) : heat f t x ∈ Ioo 0 1 := by
  rcases eq_or_lt_of_le ht with rfl | htpos
  · rw [heat_zero]; exact hf01 x
  · rw [heat_eq_integral_phi f htpos x]
    have hfb : ∀ y, |f y| ≤ 1 := fun y => abs_le.mpr ⟨by linarith [(hf01 y).1], (hf01 y).2.le⟩
    have hint := heat_integrable_phi hfc hfb (t := t) x
    have hcont : Continuous (fun z => f (x + √t * z) * phi z) :=
      (hfc.comp (by fun_prop)).mul continuous_phi
    have hcomp : IsCompact (Icc (-1 : ℝ) 1) := isCompact_Icc
    have hne : (Icc (-1 : ℝ) 1).Nonempty := ⟨0, by norm_num⟩
    constructor
    · obtain ⟨z₀, hz₀, hmin⟩ := hcomp.exists_isMinOn hne hcont.continuousOn
      have hpos : 0 < f (x + √t * z₀) * phi z₀ := mul_pos (hf01 _).1 (phi_pos _)
      have h1 : (∫ z in Icc (-1 : ℝ) 1, f (x + √t * z) * phi z) ≤ ∫ z, f (x + √t * z) * phi z :=
        setIntegral_le_integral hint (ae_of_all _ fun z => mul_nonneg (hf01 _).1.le (phi_nonneg z))
      have h2 : (∫ z in Icc (-1 : ℝ) 1, (f (x + √t * z₀) * phi z₀)) ≤
          ∫ z in Icc (-1 : ℝ) 1, f (x + √t * z) * phi z :=
        setIntegral_mono_on (integrableOn_const (by simp)) hint.integrableOn measurableSet_Icc
          fun z hz => hmin hz
      have h3 : (∫ _ in Icc (-1 : ℝ) 1, (f (x + √t * z₀) * phi z₀)) =
          2 * (f (x + √t * z₀) * phi z₀) := by
        rw [setIntegral_const, Measure.real_def, Real.volume_Icc]
        norm_num
      linarith
    · have hcont' : Continuous (fun z => (1 - f (x + √t * z)) * phi z) :=
        ((continuous_const.sub (hfc.comp (by fun_prop))).mul continuous_phi)
      obtain ⟨z₀, hz₀, hmin⟩ := hcomp.exists_isMinOn hne hcont'.continuousOn
      have hpos : 0 < (1 - f (x + √t * z₀)) * phi z₀ :=
        mul_pos (sub_pos.mpr (hf01 _).2) (phi_pos _)
      have hint' : Integrable (fun z => (1 - f (x + √t * z)) * phi z) := by
        have : (fun z => (1 - f (x + √t * z)) * phi z) = fun z => phi z - f (x + √t * z) * phi z := by
          ext z; ring
        rw [this]
        exact integrable_phi.sub hint
      have h1 : (∫ z in Icc (-1 : ℝ) 1, (1 - f (x + √t * z)) * phi z) ≤
          ∫ z, (1 - f (x + √t * z)) * phi z :=
        setIntegral_le_integral hint' (ae_of_all _ fun z =>
          mul_nonneg (sub_nonneg.mpr (hf01 _).2.le) (phi_nonneg z))
      have h2 : (∫ z in Icc (-1 : ℝ) 1, ((1 - f (x + √t * z₀)) * phi z₀)) ≤
          ∫ z in Icc (-1 : ℝ) 1, (1 - f (x + √t * z)) * phi z :=
        setIntegral_mono_on (integrableOn_const (by simp)) hint'.integrableOn measurableSet_Icc
          fun z hz => hmin hz
      have h3 : (∫ _ in Icc (-1 : ℝ) 1, ((1 - f (x + √t * z₀)) * phi z₀)) =
          2 * ((1 - f (x + √t * z₀)) * phi z₀) := by
        rw [setIntegral_const, Measure.real_def, Real.volume_Icc]
        norm_num
      have h4 : (∫ z, (1 - f (x + √t * z)) * phi z) = 1 - ∫ z, f (x + √t * z) * phi z := by
        have : (fun z => (1 - f (x + √t * z)) * phi z) = fun z => phi z - f (x + √t * z) * phi z := by
          ext z; ring
        rw [this, integral_sub integrable_phi hint, integral_phi_eq_one]
      linarith

lemma heat_antitone {f : ℝ → ℝ} (hfc : Continuous f) (hfb : ∀ y, |f y| ≤ 1)
    (hanti : Antitone f) {t : ℝ} (ht : 0 ≤ t) : Antitone (heat f t) := by
  intro x₁ x₂ hx
  rcases eq_or_lt_of_le ht with rfl | htpos
  · simp [heat_zero, hanti hx]
  · rw [heat_eq_integral_phi f htpos x₁, heat_eq_integral_phi f htpos x₂]
    refine integral_mono (heat_integrable_phi hfc hfb x₂) (heat_integrable_phi hfc hfb x₁) fun z => ?_
    exact mul_le_mul_of_nonneg_right (hanti (by linarith)) (phi_nonneg z)

lemma heat_mono_fun {f g : ℝ → ℝ} (hfc : Continuous f) (hgc : Continuous g)
    (hfb : ∀ y, |f y| ≤ 1) (hgb : ∀ y, |g y| ≤ 1)
    (hle : ∀ y, f y ≤ g y) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    heat f t x ≤ heat g t x := by
  rcases eq_or_lt_of_le ht with rfl | htpos
  · simpa [heat_zero] using hle x
  · rw [heat_eq_integral_phi f htpos x, heat_eq_integral_phi g htpos x]
    refine integral_mono (heat_integrable_phi hfc hfb x) (heat_integrable_phi hgc hgb x) fun z => ?_
    exact mul_le_mul_of_nonneg_right (hle _) (phi_nonneg z)

lemma heat_joint_continuous {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ x y, |f x - f y| ≤ L * |x - y|) (hfb : ∀ y, |f y| ≤ 1) :
    ContinuousOn (fun p : ℝ × ℝ => heat f p.1 p.2) (Ici (0 : ℝ) ×ˢ univ) := by
  have hfc : Continuous f := by
    rw [Metric.continuous_iff]
    intro x ε hε
    refine ⟨ε / (L + 1), by positivity, fun y hy => ?_⟩
    rw [Real.dist_eq] at hy ⊢
    have h1 := hlip y x
    have h2 : L * |y - x| < (L + 1) * (ε / (L + 1)) := by
      have : L * |y - x| ≤ (L + 1) * |y - x| := by nlinarith [abs_nonneg (y - x)]
      have : (L + 1) * |y - x| < (L + 1) * (ε / (L + 1)) := by nlinarith
      linarith
    rw [mul_div_cancel₀ _ (by linarith)] at h2
    linarith
  set M₁ := ∫ z : ℝ, |z| * phi z
  have hM₁ : 0 ≤ M₁ := integral_nonneg fun z => mul_nonneg (abs_nonneg z) (phi_nonneg z)
  have hbound : ∀ t₁ t₂ x₁ x₂ : ℝ, 0 ≤ t₁ → 0 ≤ t₂ →
      |heat f t₁ x₁ - heat f t₂ x₂| ≤ L * |x₁ - x₂| + L * |√t₁ - √t₂| * M₁ := by
    intro t₁ t₂ x₁ x₂ ht₁ ht₂
    have heq : ∀ t x, 0 ≤ t → heat f t x = ∫ z, f (x + √t * z) * phi z := by
      intro t x ht
      rcases eq_or_lt_of_le ht with rfl | htp
      · simp [heat_zero, integral_const_mul, integral_phi_eq_one]
      · exact heat_eq_integral_phi f htp x
    rw [heq t₁ x₁ ht₁, heq t₂ x₂ ht₂,
      ← integral_sub (heat_integrable_phi hfc hfb x₁) (heat_integrable_phi hfc hfb x₂)]
    have h1 : |∫ z, (f (x₁ + √t₁ * z) * phi z - f (x₂ + √t₂ * z) * phi z)| ≤
        ∫ z, |f (x₁ + √t₁ * z) - f (x₂ + √t₂ * z)| * phi z := by
      calc |∫ z, (f (x₁ + √t₁ * z) * phi z - f (x₂ + √t₂ * z) * phi z)|
          ≤ ∫ z, |f (x₁ + √t₁ * z) * phi z - f (x₂ + √t₂ * z) * phi z| := by
            simpa [Real.norm_eq_abs] using
              norm_integral_le_integral_norm (fun z => f (x₁ + √t₁ * z) * phi z - f (x₂ + √t₂ * z) * phi z)
        _ = ∫ z, |f (x₁ + √t₁ * z) - f (x₂ + √t₂ * z)| * phi z := by
            congr 1; ext z
            rw [← sub_mul, abs_mul, abs_of_nonneg (phi_nonneg z)]
    have hint1 : Integrable (fun z => |f (x₁ + √t₁ * z) - f (x₂ + √t₂ * z)| * phi z) := by
      have : (fun z => |f (x₁ + √t₁ * z) - f (x₂ + √t₂ * z)| * phi z) =
          fun z => ‖f (x₁ + √t₁ * z) * phi z - f (x₂ + √t₂ * z) * phi z‖ := by
        ext z; rw [Real.norm_eq_abs, ← sub_mul, abs_mul, abs_of_nonneg (phi_nonneg z)]
      rw [this]
      exact ((heat_integrable_phi hfc hfb x₁).sub (heat_integrable_phi hfc hfb x₂)).norm
    have hint2 : Integrable (fun z => (L * |x₁ - x₂|) * phi z + (L * |√t₁ - √t₂|) * (|z| * phi z)) :=
      (integrable_phi.const_mul _).add (integrable_abs_mul_phi.const_mul _)
    have h2 : (∫ z, |f (x₁ + √t₁ * z) - f (x₂ + √t₂ * z)| * phi z) ≤
        ∫ z, ((L * |x₁ - x₂|) * phi z + (L * |√t₁ - √t₂|) * (|z| * phi z)) := by
      refine integral_mono hint1 hint2 fun z => ?_
      have hlipz := hlip (x₁ + √t₁ * z) (x₂ + √t₂ * z)
      have htri : |(x₁ + √t₁ * z) - (x₂ + √t₂ * z)| ≤ |x₁ - x₂| + |√t₁ - √t₂| * |z| := by
        have : (x₁ + √t₁ * z) - (x₂ + √t₂ * z) = (x₁ - x₂) + (√t₁ - √t₂) * z := by ring
        rw [this, ← abs_mul]
        exact abs_add_le _ _
      have h3 : |f (x₁ + √t₁ * z) - f (x₂ + √t₂ * z)| ≤ L * |x₁ - x₂| + L * |√t₁ - √t₂| * |z| := by
        nlinarith [hlipz, htri]
      nlinarith [phi_nonneg z]
    have h3 : (∫ z, ((L * |x₁ - x₂|) * phi z + (L * |√t₁ - √t₂|) * (|z| * phi z))) =
        L * |x₁ - x₂| + L * |√t₁ - √t₂| * M₁ := by
      rw [integral_add (integrable_phi.const_mul _) (integrable_abs_mul_phi.const_mul _),
        integral_const_mul, integral_const_mul, integral_phi_eq_one, mul_one, mul_assoc]
    linarith
  intro p hp
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hsqrt_cont : ContinuousAt Real.sqrt p.1 := Real.continuous_sqrt.continuousAt
  rw [Metric.continuousAt_iff] at hsqrt_cont
  obtain ⟨δ₁, hδ₁, hsq⟩ := hsqrt_cont (ε / (2 * (L * M₁ + 1))) (by positivity)
  set δ := min δ₁ (ε / (2 * (L + 1)))
  have hδ : 0 < δ := lt_min hδ₁ (by positivity)
  refine ⟨δ, hδ, fun q hq hdist => ?_⟩
  rw [Real.dist_eq]
  have hd1 : dist q.1 p.1 < δ₁ := lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) hdist) (min_le_left _ _)
  have hd2 : |q.2 - p.2| < ε / (2 * (L + 1)) := by
    have := lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hdist) (min_le_right _ _)
    rwa [Real.dist_eq] at this
  have hsq' : |√q.1 - √p.1| < ε / (2 * (L * M₁ + 1)) := by
    simpa [Real.dist_eq] using hsq hd1
  have hb := hbound q.1 p.1 q.2 p.2 hq.1 hp.1
  have ht1 : L * |q.2 - p.2| < ε / 2 := by
    have : L * |q.2 - p.2| ≤ (L + 1) * |q.2 - p.2| := by nlinarith [abs_nonneg (q.2 - p.2)]
    have : (L + 1) * |q.2 - p.2| < (L + 1) * (ε / (2 * (L + 1))) := by nlinarith
    have : (L + 1) * (ε / (2 * (L + 1))) = ε / 2 := by field_simp
    linarith
  have ht2 : L * |√q.1 - √p.1| * M₁ < ε / 2 := by
    have hLM : 0 ≤ L * M₁ := mul_nonneg hL hM₁
    have : L * |√q.1 - √p.1| * M₁ = (L * M₁) * |√q.1 - √p.1| := by ring
    have hle1 : (L * M₁) * |√q.1 - √p.1| ≤ (L * M₁ + 1) * |√q.1 - √p.1| := by
      nlinarith [abs_nonneg (√q.1 - √p.1)]
    have hlt2 : (L * M₁ + 1) * |√q.1 - √p.1| < (L * M₁ + 1) * (ε / (2 * (L * M₁ + 1))) := by
      nlinarith
    have heq2 : (L * M₁ + 1) * (ε / (2 * (L * M₁ + 1))) = ε / 2 := by field_simp
    linarith
  linarith

/-- Pointwise derivatives of `heatKer`. -/
lemma hasDerivAt_heatKer_x {t : ℝ} (ht : 0 < t) (y x : ℝ) :
    HasDerivAt (fun s => heatKer t (y - s)) (heatKer_x t (y - x)) x := by
  have h1 : HasDerivAt (fun s => -(y - s) ^ 2 / (2 * t)) ((y - x) / t) x := by
    have hsub : HasDerivAt (fun s => y - s) (-1) x := (hasDerivAt_id x).const_sub y
    have hsq := hsub.pow 2
    have hneg := hsq.neg
    have hdiv := hneg.div_const (2 * t)
    exact hdiv.congr_deriv (by field_simp [ht.ne']; ring)
  have h2 := (h1.exp).const_mul (√(2 * π * t))⁻¹
  exact h2.congr_deriv (by unfold heatKer_x heatKer; ring)

lemma hasDerivAt_heatKer_xx {t : ℝ} (ht : 0 < t) (y x : ℝ) :
    HasDerivAt (fun s => heatKer_x t (y - s)) (heatKer_xx t (y - x)) x := by
  have h1 : HasDerivAt (fun s => (y - s) / t) (-1 / t) x :=
    ((hasDerivAt_id x).const_sub y).div_const t
  have h2 := hasDerivAt_heatKer_x ht y x
  have h3 := h1.mul h2
  exact h3.congr_deriv (by unfold heatKer_xx heatKer_x; field_simp [ht.ne']; ring)

lemma hasDerivAt_heatKer_t {t : ℝ} (ht : 0 < t) (u : ℝ) :
    HasDerivAt (fun s => heatKer s u) ((1 / 2) * heatKer_xx t u) t := by
  have h2pt : 0 < 2 * π * t := by positivity
  have hsqrt : HasDerivAt (fun s => √(2 * π * s)) ((2 * π) / (2 * √(2 * π * t))) t := by
    have hlin : HasDerivAt (fun s => 2 * π * s) (2 * π) t := by
      have := (hasDerivAt_id t).const_mul (2 * π)
      exact this.congr_deriv (mul_one _)
    exact (hlin.sqrt h2pt.ne').congr_deriv (by ring)
  have hinv : HasDerivAt (fun s => (√(2 * π * s))⁻¹)
      (-((2 * π) / (2 * √(2 * π * t))) / (√(2 * π * t)) ^ 2) t :=
    hsqrt.inv (Real.sqrt_pos.mpr h2pt).ne'
  have hexp_arg : HasDerivAt (fun s => -u ^ 2 / (2 * s)) (u ^ 2 / (2 * t ^ 2)) t := by
    have hlin : HasDerivAt (fun s => 2 * s) 2 t := by
      have := (hasDerivAt_id t).const_mul (2 : ℝ)
      exact this.congr_deriv (mul_one _)
    have hdiv := (hasDerivAt_const t (-u ^ 2)).div hlin (by positivity)
    exact hdiv.congr_deriv (by field_simp [ht.ne']; ring)
  have hexp := hexp_arg.exp
  have hprod := hinv.mul hexp
  exact hprod.congr_deriv (by
    unfold heatKer_xx heatKer
    have hsq : (√(2 * π * t)) ^ 2 = 2 * π * t := Real.sq_sqrt h2pt.le
    have hrt_ne : √(2 * π * t) ≠ 0 := (Real.sqrt_pos.mpr h2pt).ne'
    rw [hsq]
    field_simp [ht.ne', hrt_ne, Real.pi_ne_zero]
    ring)

/-- Helper bound: `w^2 * exp (-c * w^2) ≤ (2 / c) * exp (-(c / 2) * w^2)` for `c > 0`. -/
lemma sq_mul_exp_neg_le {c : ℝ} (hc : 0 < c) (w : ℝ) :
    w ^ 2 * exp (-c * w ^ 2) ≤ (2 / c) * exp (-(c / 2) * w ^ 2) := by
  have h1 : (c / 2) * w ^ 2 ≤ exp ((c / 2) * w ^ 2) := by
    linarith [add_one_le_exp ((c / 2) * w ^ 2)]
  have h2 : exp (-c * w ^ 2) = (exp ((c / 2) * w ^ 2))⁻¹ * exp (-(c / 2) * w ^ 2) := by
    rw [← exp_neg, ← exp_add]; congr 1; ring
  rw [h2]
  have h3 : (c / 2) * w ^ 2 * (exp ((c / 2) * w ^ 2))⁻¹ ≤ 1 :=
    (mul_inv_le_iff₀ (exp_pos _)).mpr (by linarith)
  have h4 : w ^ 2 * (exp ((c / 2) * w ^ 2))⁻¹ ≤ 2 / c := by
    have : (c / 2) * (w ^ 2 * (exp ((c / 2) * w ^ 2))⁻¹) ≤ 1 := by linarith
    have hc2 : 0 < c / 2 := by positivity
    calc w ^ 2 * (exp ((c / 2) * w ^ 2))⁻¹
        = (2 / c) * ((c / 2) * (w ^ 2 * (exp ((c / 2) * w ^ 2))⁻¹)) := by field_simp [hc.ne']
      _ ≤ (2 / c) * 1 := mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 / c := mul_one _
  nlinarith [exp_pos (-(c / 2) * w ^ 2)]

/-- Uniform Gaussian dominating bound for `heatKer`, `heatKer_x`, `heatKer_xx` on a local box. -/
lemma heatKer_local_dom {t₀ : ℝ} (ht₀ : 0 < t₀) (x₀ : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ t ∈ Ioo (t₀ / 2) (2 * t₀), ∀ x ∈ Ioo (x₀ - 1) (x₀ + 1), ∀ y : ℝ,
        |heatKer t (y - x)| ≤ C * exp (-(1 / (16 * t₀)) * (y - x₀) ^ 2) ∧
        |heatKer_x t (y - x)| ≤ C * exp (-(1 / (16 * t₀)) * (y - x₀) ^ 2) ∧
        |heatKer_xx t (y - x)| ≤ C * exp (-(1 / (16 * t₀)) * (y - x₀) ^ 2) := by
  set K₀ := (√(π * t₀))⁻¹ * exp (1 / t₀)
  have hK₀ : 0 < K₀ := by positivity
  set M := max 1 (max (2 / t₀) (4 / t₀ ^ 2))
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  set C := K₀ * M * (3 + 32 * t₀)
  have hC : 0 < C := by positivity
  refine ⟨C, hC, fun t ht x hx y => ?_⟩
  have ht_pos : 0 < t := by linarith [ht.1]
  have hker_le : heatKer t (y - x) ≤ K₀ * exp (-(1 / (8 * t₀)) * (y - x₀) ^ 2) := by
    unfold heatKer
    have hrt : √(π * t₀) ≤ √(2 * π * t) := Real.sqrt_le_sqrt (by nlinarith [ht.1, Real.pi_pos])
    have hinv : (√(2 * π * t))⁻¹ ≤ (√(π * t₀))⁻¹ :=
      inv_anti₀ (Real.sqrt_pos.mpr (by positivity)) hrt
    have hsq_u : (y - x₀) ^ 2 ≤ 2 * (y - x) ^ 2 + 2 := by
      have hx1 : (x - x₀) ^ 2 ≤ 1 := by
        have habs : |x - x₀| ≤ 1 := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
        have hsq : |x - x₀| ^ 2 ≤ 1 ^ 2 := by nlinarith [abs_nonneg (x - x₀)]
        rwa [sq_abs, one_pow] at hsq
      have : (y - x₀) = (y - x) + (x - x₀) := by ring
      nlinarith [sq_nonneg ((y - x) - (x - x₀))]
    have hexp_arg : -(y - x) ^ 2 / (2 * t) ≤ 1 / t₀ - (1 / (8 * t₀)) * (y - x₀) ^ 2 := by
      have h1 : -(y - x) ^ 2 ≤ -((y - x₀) ^ 2 / 2 - 1) := by linarith
      have h2 : -(y - x) ^ 2 / (2 * t) ≤ -((y - x₀) ^ 2 / 2 - 1) / (2 * t) :=
        div_le_div_of_nonneg_right h1 (by positivity)
      have h3 : -((y - x₀) ^ 2 / 2 - 1) / (2 * t) = 1 / (2 * t) - (y - x₀) ^ 2 / (4 * t) := by
        field_simp [ht_pos.ne']; ring
      have h4 : 1 / (2 * t) ≤ 1 / t₀ := by
        rw [div_le_div_iff₀ (by positivity) ht₀]; nlinarith [ht.1]
      have h5 : (1 / (8 * t₀)) * (y - x₀) ^ 2 ≤ (y - x₀) ^ 2 / (4 * t) := by
        have : (1 / (8 * t₀)) * (y - x₀) ^ 2 = (y - x₀) ^ 2 / (8 * t₀) := by ring
        rw [this, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [ht.2, sq_nonneg (y - x₀)]
      linarith
    have hexp : exp (-(y - x) ^ 2 / (2 * t)) ≤ exp (1 / t₀) * exp (-(1 / (8 * t₀)) * (y - x₀) ^ 2) := by
      rw [← exp_add]
      exact exp_le_exp.mpr (by linarith)
    calc (√(2 * π * t))⁻¹ * exp (-(y - x) ^ 2 / (2 * t))
        ≤ (√(π * t₀))⁻¹ * (exp (1 / t₀) * exp (-(1 / (8 * t₀)) * (y - x₀) ^ 2)) :=
          mul_le_mul hinv hexp (by positivity) (by positivity)
      _ = K₀ * exp (-(1 / (8 * t₀)) * (y - x₀) ^ 2) := by ring
  have hexp_mono : exp (-(1 / (8 * t₀)) * (y - x₀) ^ 2) ≤ exp (-(1 / (16 * t₀)) * (y - x₀) ^ 2) :=
    exp_le_exp.mpr (by
      have hle : (1 / (16 * t₀)) * (y - x₀) ^ 2 ≤ (1 / (8 * t₀)) * (y - x₀) ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        linarith
      linarith)
  have hsq_exp : (y - x₀) ^ 2 * exp (-(1 / (8 * t₀)) * (y - x₀) ^ 2) ≤
      (16 * t₀) * exp (-(1 / (16 * t₀)) * (y - x₀) ^ 2) := by
    have h := sq_mul_exp_neg_le (c := 1 / (8 * t₀)) (by positivity) (y - x₀)
    have hc1 : 2 / (1 / (8 * t₀)) = 16 * t₀ := by field_simp [ht₀.ne']; ring
    have hc2 : (1 / (8 * t₀)) / 2 = 1 / (16 * t₀) := by field_simp [ht₀.ne']; ring
    rw [hc1, hc2] at h
    exact h
  have hu_sq : (y - x) ^ 2 ≤ 2 * (y - x₀) ^ 2 + 2 := by
    have hx1 : (x - x₀) ^ 2 ≤ 1 := by
      have habs : |x - x₀| ≤ 1 := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
      have hsq : |x - x₀| ^ 2 ≤ 1 ^ 2 := by nlinarith [abs_nonneg (x - x₀)]
      rwa [sq_abs, one_pow] at hsq
    have : (y - x) = (y - x₀) - (x - x₀) := by ring
    nlinarith [sq_nonneg ((y - x₀) + (x - x₀))]
  have hpoly_exp : (3 + 2 * (y - x₀) ^ 2) * exp (-(1 / (8 * t₀)) * (y - x₀) ^ 2) ≤
      (3 + 32 * t₀) * exp (-(1 / (16 * t₀)) * (y - x₀) ^ 2) := by
    nlinarith [hexp_mono, hsq_exp]
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM2 : 1 / t ≤ M := by
    have h1 : 1 / t ≤ 2 / t₀ := by rw [div_le_div_iff₀ ht_pos ht₀]; linarith [ht.1]
    exact h1.trans (le_trans (le_max_left _ _) (le_max_right _ _))
  have hM3 : 1 / t ^ 2 ≤ M := by
    have h1 : 1 / t ^ 2 ≤ 4 / t₀ ^ 2 := by
      rw [div_le_div_iff₀ (sq_pos_of_pos ht_pos) (sq_pos_of_pos ht₀)]
      nlinarith [ht.1]
    exact h1.trans (le_trans (le_max_right _ _) (le_max_right _ _))
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_of_pos (heatKer_pos ht_pos _)]
    have h1 : 1 ≤ M * (3 + 32 * t₀) := by nlinarith
    calc heatKer t (y - x) ≤ K₀ * exp (-(1 / (8 * t₀)) * (y - x₀) ^ 2) := hker_le
      _ ≤ K₀ * exp (-(1 / (16 * t₀)) * (y - x₀) ^ 2) := by nlinarith [hexp_mono]
      _ ≤ C * exp (-(1 / (16 * t₀)) * (y - x₀) ^ 2) := by
          have : K₀ ≤ C := by dsimp [C]; nlinarith
          nlinarith [exp_pos (-(1 / (16 * t₀)) * (y - x₀) ^ 2)]
  · unfold heatKer_x
    rw [abs_mul, abs_div, abs_of_pos ht_pos, abs_of_pos (heatKer_pos ht_pos _)]
    have hu_abs : |y - x| ≤ 3 + 2 * (y - x₀) ^ 2 := by
      have : |y - x| ≤ 1 + (y - x) ^ 2 := by
        have : (|y - x| - 1) ^ 2 ≥ 0 := sq_nonneg _
        nlinarith [sq_abs (y - x)]
      linarith
    calc |y - x| / t * heatKer t (y - x)
        = (1 / t) * (|y - x| * heatKer t (y - x)) := by ring
      _ ≤ M * ((3 + 2 * (y - x₀) ^ 2) * (K₀ * exp (-(1 / (8 * t₀)) * (y - x₀) ^ 2))) := by
          refine mul_le_mul hM2 ?_ (mul_nonneg (abs_nonneg _) (heatKer_nonneg ht_pos _)) hM.le
          exact mul_le_mul hu_abs hker_le (heatKer_nonneg ht_pos _) (by positivity)
      _ = K₀ * M * ((3 + 2 * (y - x₀) ^ 2) * exp (-(1 / (8 * t₀)) * (y - x₀) ^ 2)) := by ring
      _ ≤ K₀ * M * ((3 + 32 * t₀) * exp (-(1 / (16 * t₀)) * (y - x₀) ^ 2)) := by
          exact mul_le_mul_of_nonneg_left hpoly_exp (by positivity)
      _ = C * exp (-(1 / (16 * t₀)) * (y - x₀) ^ 2) := by ring
  · unfold heatKer_xx
    rw [abs_mul, abs_div, abs_of_pos ht_pos, abs_of_pos (heatKer_pos ht_pos _)]
    have hnum : |(y - x) ^ 2 / t - 1| / t ≤ (1 / t ^ 2) * (y - x) ^ 2 + (1 / t) := by
      have htri : |(y - x) ^ 2 / t - 1| ≤ (y - x) ^ 2 / t + 1 :=
        abs_le.mpr ⟨by linarith [div_nonneg (sq_nonneg (y - x)) ht_pos.le], by linarith⟩
      have hdiv := div_le_div_of_nonneg_right htri ht_pos.le
      calc |(y - x) ^ 2 / t - 1| / t ≤ ((y - x) ^ 2 / t + 1) / t := hdiv
        _ = (1 / t ^ 2) * (y - x) ^ 2 + 1 / t := by field_simp [ht_pos.ne']
    have hfac : |(y - x) ^ 2 / t - 1| / t ≤ M * (3 + 2 * (y - x₀) ^ 2) := by
      calc |(y - x) ^ 2 / t - 1| / t
          ≤ (1 / t ^ 2) * (y - x) ^ 2 + 1 / t := hnum
        _ ≤ M * (2 * (y - x₀) ^ 2 + 2) + M := by
            have h1 : (1 / t ^ 2) * (y - x) ^ 2 ≤ M * (2 * (y - x₀) ^ 2 + 2) :=
              mul_le_mul hM3 hu_sq (sq_nonneg _) hM.le
            linarith
        _ = M * (3 + 2 * (y - x₀) ^ 2) := by ring
    calc |(y - x) ^ 2 / t - 1| / t * heatKer t (y - x)
        ≤ (M * (3 + 2 * (y - x₀) ^ 2)) * (K₀ * exp (-(1 / (8 * t₀)) * (y - x₀) ^ 2)) :=
          mul_le_mul hfac hker_le (heatKer_nonneg ht_pos _) (by positivity)
      _ = K₀ * M * ((3 + 2 * (y - x₀) ^ 2) * exp (-(1 / (8 * t₀)) * (y - x₀) ^ 2)) := by ring
      _ ≤ K₀ * M * ((3 + 32 * t₀) * exp (-(1 / (16 * t₀)) * (y - x₀) ^ 2)) :=
          mul_le_mul_of_nonneg_left hpoly_exp (by positivity)
      _ = C * exp (-(1 / (16 * t₀)) * (y - x₀) ^ 2) := by ring

lemma hasDerivAt_heat_x {f : ℝ → ℝ} (hfc : Continuous f) (hfb : ∀ y, |f y| ≤ 1)
    {t : ℝ} (ht : 0 < t) (x₀ : ℝ) :
    HasDerivAt (heat f t) (heat_x f t x₀) x₀ := by
  obtain ⟨C, hC, hdom⟩ := heatKer_local_dom ht x₀
  set bound : ℝ → ℝ := fun y => C * exp (-(1 / (16 * t)) * (y - x₀) ^ 2)
  have hbound_int : Integrable bound :=
    ((integrable_exp_neg_mul_sq (by positivity)).comp_sub_right x₀).const_mul C
  have hEq : heat f t = fun x => ∫ y, f y * heatKer t (y - x) := by
    ext x; exact heat_of_pos f ht x
  rw [hEq]
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x y => f y * heatKer t (y - x))
    (F' := fun x y => f y * heatKer_x t (y - x))
    (bound := bound) (x₀ := x₀) (s := Ioo (x₀ - 1) (x₀ + 1))
    (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
    (Eventually.of_forall fun x => (hfc.mul (by unfold heatKer; fun_prop)).aestronglyMeasurable)
    (hbound_int.mono' (hfc.mul (by unfold heatKer; fun_prop)).aestronglyMeasurable
      (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_mul]
        have hd := (hdom t ⟨by linarith, by linarith⟩ x₀ ⟨by linarith, by linarith⟩ y).1
        calc |f y| * |heatKer t (y - x₀)| ≤ 1 * bound y :=
              mul_le_mul (hfb y) hd (abs_nonneg _) zero_le_one
          _ = bound y := one_mul _))
    ((hfc.mul (by unfold heatKer_x heatKer; fun_prop)).aestronglyMeasurable)
    (ae_of_all _ fun y x hx => by
      rw [Real.norm_eq_abs, abs_mul]
      have hd := (hdom t ⟨by linarith, by linarith⟩ x hx y).2.1
      calc |f y| * |heatKer_x t (y - x)| ≤ 1 * bound y :=
            mul_le_mul (hfb y) hd (abs_nonneg _) zero_le_one
        _ = bound y := one_mul _)
    hbound_int
    (ae_of_all _ fun y x _ => (hasDerivAt_heatKer_x ht y x).const_mul (f y))
  exact h.2

lemma hasDerivAt_heat_xx {f : ℝ → ℝ} (hfc : Continuous f) (hfb : ∀ y, |f y| ≤ 1)
    {t : ℝ} (ht : 0 < t) (x₀ : ℝ) :
    HasDerivAt (heat_x f t) (heat_xx f t x₀) x₀ := by
  obtain ⟨C, hC, hdom⟩ := heatKer_local_dom ht x₀
  set bound : ℝ → ℝ := fun y => C * exp (-(1 / (16 * t)) * (y - x₀) ^ 2)
  have hbound_int : Integrable bound :=
    ((integrable_exp_neg_mul_sq (by positivity)).comp_sub_right x₀).const_mul C
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x y => f y * heatKer_x t (y - x))
    (F' := fun x y => f y * heatKer_xx t (y - x))
    (bound := bound) (x₀ := x₀) (s := Ioo (x₀ - 1) (x₀ + 1))
    (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
    (Eventually.of_forall fun x => (hfc.mul (by unfold heatKer_x heatKer; fun_prop)).aestronglyMeasurable)
    (hbound_int.mono' (hfc.mul (by unfold heatKer_x heatKer; fun_prop)).aestronglyMeasurable
      (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_mul]
        have hd := (hdom t ⟨by linarith, by linarith⟩ x₀ ⟨by linarith, by linarith⟩ y).2.1
        calc |f y| * |heatKer_x t (y - x₀)| ≤ 1 * bound y :=
              mul_le_mul (hfb y) hd (abs_nonneg _) zero_le_one
          _ = bound y := one_mul _))
    ((hfc.mul (by unfold heatKer_xx heatKer; fun_prop)).aestronglyMeasurable)
    (ae_of_all _ fun y x hx => by
      rw [Real.norm_eq_abs, abs_mul]
      have hd := (hdom t ⟨by linarith, by linarith⟩ x hx y).2.2
      calc |f y| * |heatKer_xx t (y - x)| ≤ 1 * bound y :=
            mul_le_mul (hfb y) hd (abs_nonneg _) zero_le_one
        _ = bound y := one_mul _)
    hbound_int
    (ae_of_all _ fun y x _ => (hasDerivAt_heatKer_xx ht y x).const_mul (f y))
  exact h.2

lemma hasDerivAt_heat_t {f : ℝ → ℝ} (hfc : Continuous f) (hfb : ∀ y, |f y| ≤ 1)
    {t₀ : ℝ} (ht₀ : 0 < t₀) (x₀ : ℝ) :
    HasDerivAt (fun s => heat f s x₀) ((1 / 2) * heat_xx f t₀ x₀) t₀ := by
  obtain ⟨C, hC, hdom⟩ := heatKer_local_dom ht₀ x₀
  set bound : ℝ → ℝ := fun y => C * exp (-(1 / (16 * t₀)) * (y - x₀) ^ 2)
  have hbound_int : Integrable bound :=
    ((integrable_exp_neg_mul_sq (by positivity)).comp_sub_right x₀).const_mul C
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s y => f y * heatKer s (y - x₀))
    (F' := fun s y => f y * ((1 / 2) * heatKer_xx s (y - x₀)))
    (bound := bound) (x₀ := t₀) (s := Ioo (t₀ / 2) (2 * t₀))
    (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
    (Eventually.of_forall fun s => (hfc.mul (by unfold heatKer; fun_prop)).aestronglyMeasurable)
    (hbound_int.mono' (hfc.mul (by unfold heatKer; fun_prop)).aestronglyMeasurable
      (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_mul]
        have hd := (hdom t₀ ⟨by linarith, by linarith⟩ x₀ ⟨by linarith, by linarith⟩ y).1
        calc |f y| * |heatKer t₀ (y - x₀)| ≤ 1 * bound y :=
              mul_le_mul (hfb y) hd (abs_nonneg _) zero_le_one
          _ = bound y := one_mul _))
    ((hfc.mul (by unfold heatKer_xx heatKer; fun_prop)).aestronglyMeasurable)
    (ae_of_all _ fun y s hs => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      have hd := (hdom s hs x₀ ⟨by linarith, by linarith⟩ y).2.2
      calc |f y| * (1 / 2 * |heatKer_xx s (y - x₀)|)
          ≤ 1 * (1 * bound y) := by
            have h1 : 1 / 2 * |heatKer_xx s (y - x₀)| ≤ 1 * bound y := by
              change 1 / 2 * |heatKer_xx s (y - x₀)| ≤ 1 * (C * exp (-(1 / (16 * t₀)) * (y - x₀) ^ 2))
              linarith [hd, abs_nonneg (heatKer_xx s (y - x₀))]
            exact mul_le_mul (hfb y) h1 (by positivity) zero_le_one
        _ = bound y := by ring)
    hbound_int
    (ae_of_all _ fun y s hs => (hasDerivAt_heatKer_t (by linarith [hs.1]) (y - x₀)).const_mul (f y))
  have hderiv : HasDerivAt (fun s => ∫ y, f y * heatKer s (y - x₀))
      ((1 / 2) * heat_xx f t₀ x₀) t₀ := by
    refine h.2.congr_deriv ?_
    unfold heat_xx
    rw [← integral_const_mul]
    congr 1; ext y; ring
  refine hderiv.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds ht₀] with s hs
  exact heat_of_pos f hs x₀

/-- Normalized heat flow `F f t x = PhiInv (heat f t x)`. -/
noncomputable def FFlow (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  PhiInv (heat f t x)

noncomputable def FFlow_x (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  heat_x f t x / phi (FFlow f t x)

noncomputable def FFlow_xx (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  heat_xx f t x / phi (FFlow f t x) + FFlow f t x * (FFlow_x f t x) ^ 2

lemma hasDerivAt_FFlow_x {f : ℝ → ℝ} (hfc : Continuous f) (hf01 : ∀ y, f y ∈ Ioo 0 1)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (FFlow f t) (FFlow_x f t x) x := by
  have hfb : ∀ y, |f y| ≤ 1 := fun y => abs_le.mpr ⟨by linarith [(hf01 y).1], (hf01 y).2.le⟩
  have h1 := hasDerivAt_PhiInv (heat_mem_Ioo hfc hf01 ht.le x)
  have h2 := hasDerivAt_heat_x hfc hfb ht x
  exact (h1.comp x h2).congr_deriv (by unfold FFlow_x FFlow; ring)

lemma hasDerivAt_FFlow_xx {f : ℝ → ℝ} (hfc : Continuous f) (hf01 : ∀ y, f y ∈ Ioo 0 1)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (FFlow_x f t) (FFlow_xx f t x) x := by
  have hfb : ∀ y, |f y| ≤ 1 := fun y => abs_le.mpr ⟨by linarith [(hf01 y).1], (hf01 y).2.le⟩
  have h1 := hasDerivAt_heat_xx hfc hfb ht x
  have h2 := (hasDerivAt_phi (FFlow f t x)).comp x (hasDerivAt_FFlow_x hfc hf01 ht x)
  have hne : phi (FFlow f t x) ≠ 0 := (phi_pos _).ne'
  have h3 := h1.div h2 hne
  exact h3.congr_deriv (by
    simp only [Function.comp_apply]
    unfold FFlow_xx FFlow_x
    field_simp [hne]
    ring)

lemma hasDerivAt_FFlow_t {f : ℝ → ℝ} (hfc : Continuous f) (hf01 : ∀ y, f y ∈ Ioo 0 1)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => FFlow f s x)
      ((1 / 2) * (FFlow_xx f t x - FFlow f t x * (FFlow_x f t x) ^ 2)) t := by
  have hfb : ∀ y, |f y| ≤ 1 := fun y => abs_le.mpr ⟨by linarith [(hf01 y).1], (hf01 y).2.le⟩
  have h1 := hasDerivAt_PhiInv (heat_mem_Ioo hfc hf01 ht.le x)
  have h2 := hasDerivAt_heat_t hfc hfb ht x
  exact (h1.comp t h2).congr_deriv (by unfold FFlow_xx FFlow; ring)

/-- Uniform gradient bound `|∂_x (PhiInv (P_t (Phi ∘ h)))| ≤ S` for `S`-Lipschitz `h`,
proved directly via the tangent-line inequality on the isoperimetric profile `phi ∘ PhiInv`. -/
lemma abs_FFlow_x_le {h : ℝ → ℝ} {S : ℝ} (hS : 0 ≤ S)
    (hlip : ∀ x y, |h x - h y| ≤ S * |x - y|) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    |FFlow_x (fun y => Phi (h y)) t x| ≤ S := by
  set f : ℝ → ℝ := fun y => Phi (h y)
  have hhc : Continuous h := by
    rw [Metric.continuous_iff]
    intro a ε hε
    refine ⟨ε / (S + 1), by positivity, fun b hb => ?_⟩
    rw [Real.dist_eq] at hb ⊢
    have := hlip b a
    have hlt : (S + 1) * |b - a| < (S + 1) * (ε / (S + 1)) := by nlinarith
    rw [mul_div_cancel₀ _ (by linarith)] at hlt
    nlinarith [abs_nonneg (b - a)]
  have hfc : Continuous f := continuous_Phi.comp hhc
  have hf01 : ∀ y, f y ∈ Ioo 0 1 := fun y => ⟨Phi_pos _, Phi_lt_one _⟩
  have hfb : ∀ y, |f y| ≤ 1 := fun y => abs_le.mpr ⟨by linarith [(hf01 y).1], (hf01 y).2.le⟩
  set u₀ := heat f t x
  have hu₀ : u₀ ∈ Ioo 0 1 := heat_mem_Ioo hfc hf01 ht.le x
  have hphi_int : Integrable (fun z => phi (h (x + √t * z)) * phi z) := by
    refine integrable_phi.mono'
      (((continuous_phi.comp (hhc.comp (by fun_prop))).mul continuous_phi).aestronglyMeasurable)
      (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (phi_nonneg _), abs_of_nonneg (phi_nonneg _)]
    nlinarith [phi_le_one (h (x + √t * z)), phi_nonneg z]
  have hjensen : (∫ z, phi (h (x + √t * z)) * phi z) ≤ phi (PhiInv u₀) := by
    have htan : ∀ z, phi (h (x + √t * z)) * phi z ≤
        (phi (PhiInv u₀) + (-PhiInv u₀) * (f (x + √t * z) - u₀)) * phi z := fun z => by
      have h1 := isoProfile_le_tangent (u := f (x + √t * z)) (u₀ := u₀) (hf01 _) hu₀
      rw [PhiInv_Phi] at h1
      exact mul_le_mul_of_nonneg_right h1 (phi_nonneg z)
    have hrhs_int : Integrable (fun z => (phi (PhiInv u₀) + (-PhiInv u₀) * (f (x + √t * z) - u₀)) * phi z) := by
      have : (fun z => (phi (PhiInv u₀) + (-PhiInv u₀) * (f (x + √t * z) - u₀)) * phi z) =
          fun z => (phi (PhiInv u₀) + PhiInv u₀ * u₀) * phi z + (-PhiInv u₀) * (f (x + √t * z) * phi z) := by
        ext z; ring
      rw [this]
      exact (integrable_phi.const_mul _).add ((heat_integrable_phi hfc hfb x).const_mul _)
    have hle := integral_mono hphi_int hrhs_int htan
    have hrhs_eq : (∫ z, (phi (PhiInv u₀) + (-PhiInv u₀) * (f (x + √t * z) - u₀)) * phi z) =
        phi (PhiInv u₀) := by
      have : (fun z => (phi (PhiInv u₀) + (-PhiInv u₀) * (f (x + √t * z) - u₀)) * phi z) =
          fun z => (phi (PhiInv u₀) + PhiInv u₀ * u₀) * phi z + (-PhiInv u₀) * (f (x + √t * z) * phi z) := by
        ext z; ring
      rw [this, integral_add (integrable_phi.const_mul _) ((heat_integrable_phi hfc hfb x).const_mul _),
        integral_const_mul, integral_const_mul, integral_phi_eq_one, ← heat_eq_integral_phi f ht x]
      change (phi (PhiInv u₀) + PhiInv u₀ * u₀) * 1 + (-PhiInv u₀) * u₀ = phi (PhiInv u₀)
      ring
    linarith
  -- Bound |heat_x f t x| ≤ S * phi (PhiInv u₀) via finite differences
  have hdiff_bound : ∀ δ : ℝ, δ ≠ 0 →
      |heat f t (x + δ) - heat f t x| / |δ| ≤ S * (phi (PhiInv u₀) + S * |δ|) := by
    intro δ hδ
    rw [heat_eq_integral_phi f ht (x + δ), heat_eq_integral_phi f ht x,
      ← integral_sub (heat_integrable_phi hfc hfb (x + δ)) (heat_integrable_phi hfc hfb x)]
    have hpt : ∀ z : ℝ, |f (x + δ + √t * z) - f (x + √t * z)| ≤
        S * |δ| * (phi (h (x + √t * z)) + S * |δ|) := by
      intro z
      set a := h (x + √t * z)
      set b := h (x + δ + √t * z)
      have hab : |b - a| ≤ S * |δ| := by
        have := hlip (x + δ + √t * z) (x + √t * z)
        simpa [show x + δ + √t * z - (x + √t * z) = δ by ring] using this
      rcases eq_or_ne a b with heq | hne
      · simp only [f, a, b, heq, sub_self, abs_zero]
        exact mul_nonneg (mul_nonneg hS (abs_nonneg _)) (add_nonneg (phi_nonneg _) (mul_nonneg hS (abs_nonneg _)))
      · have hPhi_mvt : ∃ c : ℝ, |c - a| ≤ |b - a| ∧ Phi b - Phi a = phi c * (b - a) := by
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope Phi phi hlt
              continuous_Phi.continuousOn (fun w _ => hasDerivAt_Phi w)
            refine ⟨c, ?_, ?_⟩
            · rw [abs_of_nonneg (sub_nonneg.mpr hc.1.le), abs_of_nonneg (sub_nonneg.mpr hlt.le)]
              linarith [hc.2]
            · rw [hslope, div_mul_cancel₀ _ (sub_ne_zero.mpr hlt.ne')]
          · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope Phi phi hgt
              continuous_Phi.continuousOn (fun w _ => hasDerivAt_Phi w)
            refine ⟨c, ?_, ?_⟩
            · rw [abs_sub_comm c a, abs_sub_comm b a,
                abs_of_nonneg (sub_nonneg.mpr hc.2.le), abs_of_nonneg (sub_nonneg.mpr hgt.le)]
              linarith [hc.1]
            · have : Phi a - Phi b = phi c * (a - b) := by
                rw [hslope, div_mul_cancel₀ _ (sub_ne_zero.mpr hgt.ne')]
              linarith
        obtain ⟨c, hca, hPhi_eq⟩ := hPhi_mvt
        have hphic : phi c ≤ phi a + S * |δ| := by
          have := phi_lipschitz c a
          have : phi c - phi a ≤ |c - a| := le_trans (le_abs_self _) this
          linarith
        change |Phi b - Phi a| ≤ S * |δ| * (phi a + S * |δ|)
        rw [hPhi_eq, abs_mul, abs_of_pos (phi_pos c)]
        calc phi c * |b - a| ≤ (phi a + S * |δ|) * (S * |δ|) :=
              mul_le_mul hphic hab (abs_nonneg _) (add_nonneg (phi_nonneg _) (mul_nonneg hS (abs_nonneg _)))
          _ = S * |δ| * (phi a + S * |δ|) := by ring
    have h1 : |∫ z, (f (x + δ + √t * z) * phi z - f (x + √t * z) * phi z)| ≤
        ∫ z, (S * |δ| * (phi (h (x + √t * z)) + S * |δ|)) * phi z := by
      have hnorm := norm_integral_le_integral_norm (μ := volume)
        (fun z => f (x + δ + √t * z) * phi z - f (x + √t * z) * phi z)
      have hint_lhs : Integrable (fun z => ‖f (x + δ + √t * z) * phi z - f (x + √t * z) * phi z‖) :=
        ((heat_integrable_phi hfc hfb (x + δ)).sub (heat_integrable_phi hfc hfb x)).norm
      have hint_rhs : Integrable (fun z => (S * |δ| * (phi (h (x + √t * z)) + S * |δ|)) * phi z) := by
        have : (fun z => (S * |δ| * (phi (h (x + √t * z)) + S * |δ|)) * phi z) =
            fun z => (S * |δ|) * (phi (h (x + √t * z)) * phi z) + (S * |δ|) ^ 2 * phi z := by
          ext z; ring
        rw [this]
        exact (hphi_int.const_mul _).add (integrable_phi.const_mul _)
      have hle2 : (∫ z, ‖f (x + δ + √t * z) * phi z - f (x + √t * z) * phi z‖) ≤
          ∫ z, (S * |δ| * (phi (h (x + √t * z)) + S * |δ|)) * phi z := by
        refine integral_mono hint_lhs hint_rhs fun z => ?_
        rw [Real.norm_eq_abs, ← sub_mul, abs_mul, abs_of_nonneg (phi_nonneg z)]
        exact mul_le_mul_of_nonneg_right (hpt z) (phi_nonneg z)
      simpa [Real.norm_eq_abs] using hnorm.trans hle2
    have h2 : (∫ z, (S * |δ| * (phi (h (x + √t * z)) + S * |δ|)) * phi z) =
        S * |δ| * ((∫ z, phi (h (x + √t * z)) * phi z) + S * |δ|) := by
      have : (fun z => (S * |δ| * (phi (h (x + √t * z)) + S * |δ|)) * phi z) =
          fun z => (S * |δ|) * (phi (h (x + √t * z)) * phi z) + (S * |δ|) ^ 2 * phi z := by
        ext z; ring
      rw [this, integral_add (hphi_int.const_mul _) (integrable_phi.const_mul _),
        integral_const_mul, integral_const_mul, integral_phi_eq_one]
      ring
    have h3 : |∫ z, (f (x + δ + √t * z) * phi z - f (x + √t * z) * phi z)| ≤
        S * |δ| * (phi (PhiInv u₀) + S * |δ|) := by
      rw [h2] at h1
      have hpos : 0 ≤ S * |δ| := by positivity
      calc |∫ z, (f (x + δ + √t * z) * phi z - f (x + √t * z) * phi z)|
          ≤ S * |δ| * ((∫ z, phi (h (x + √t * z)) * phi z) + S * |δ|) := h1
        _ ≤ S * |δ| * (phi (PhiInv u₀) + S * |δ|) := by nlinarith
    rw [div_le_iff₀ (abs_pos.mpr hδ)]
    linarith
  have hlim : Tendsto (fun δ : ℝ => |heat f t (x + δ) - heat f t x| / |δ|)
      (𝓝[≠] 0) (𝓝 |heat_x f t x|) := by
    have hder := (hasDerivAt_heat_x hfc hfb ht x).tendsto_slope_zero
    have hnorm := hder.norm
    refine hnorm.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    simp only [smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_inv]
    rw [div_eq_inv_mul]
  have hlim_rhs : Tendsto (fun δ : ℝ => S * (phi (PhiInv u₀) + S * |δ|))
      (𝓝[≠] 0) (𝓝 (S * phi (PhiInv u₀))) := by
    have hcont : Continuous (fun δ : ℝ => S * (phi (PhiInv u₀) + S * |δ|)) := by fun_prop
    have ht0 := hcont.continuousAt (x := (0 : ℝ)).tendsto.mono_left (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))
    simpa using ht0
  have hle_hx : |heat_x f t x| ≤ S * phi (PhiInv u₀) :=
    le_of_tendsto_of_tendsto hlim hlim_rhs (eventually_nhdsWithin_of_forall fun δ hδ => hdiff_bound δ hδ)
  unfold FFlow_x FFlow
  rw [abs_div, abs_of_pos (phi_pos _), div_le_iff₀ (phi_pos _)]
  exact hle_hx

/-- Exact heat flow of `Phi (-S * y + C)`. -/
lemma heat_affine_Phi (S C : ℝ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    heat (fun y => Phi (-S * y + C)) t x = Phi ((-S * x + C) / √(1 + S ^ 2 * t)) := by
  set γ : Measure ℝ := gaussianReal 0 1
  have : IsProbabilityMeasure γ := inferInstance
  rw [heat_eq_integral_gaussianReal _ ht x]
  have hLHS : ∫ z, Phi (-S * (x + √t * z) + C) ∂γ =
      (γ.prod γ).real {p : ℝ × ℝ | p.2 ≤ -S * (x + √t * p.1) + C} := by
    have hmeas : MeasurableSet {p : ℝ × ℝ | p.2 ≤ -S * (x + √t * p.1) + C} :=
      measurableSet_le measurable_snd (by fun_prop)
    rw [measureReal_def, Measure.prod_apply hmeas]
    have hsec : ∀ z : ℝ, γ (Prod.mk z ⁻¹' {p : ℝ × ℝ | p.2 ≤ -S * (x + √t * p.1) + C}) =
        ENNReal.ofReal (Phi (-S * (x + √t * z) + C)) := fun z => by
      have hset : Prod.mk z ⁻¹' {p : ℝ × ℝ | p.2 ≤ -S * (x + √t * p.1) + C} =
          Iic (-S * (x + √t * z) + C) := rfl
      rw [hset, Phi_eq_gaussianReal, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    simp_rw [hsec]
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · rw [ENNReal.toReal_ofReal (integral_nonneg fun z => Phi_nonneg _)]
    · exact (integrable_const (1 : ℝ)).mono'
        ((continuous_Phi.comp (by fun_prop)).aestronglyMeasurable)
        (ae_of_all _ fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (Phi_nonneg _)]; exact Phi_le_one _)
    · exact ae_of_all _ fun z => Phi_nonneg _
  rw [hLHS]
  set g : ℝ × ℝ → ℝ := fun p => p.2 + S * √t * p.1
  have hset : {p : ℝ × ℝ | p.2 ≤ -S * (x + √t * p.1) + C} = g ⁻¹' Iic (-S * x + C) := by
    ext ⟨u, v⟩; simp only [mem_ofPred_eq, mem_preimage, mem_Iic, g]; constructor <;> intro h <;> linarith
  rw [hset, ← map_measureReal_apply (by fun_prop : Measurable g) measurableSet_Iic]
  have hind : IndepFun (fun p : ℝ × ℝ => p.2) (fun p : ℝ × ℝ => S * √t * p.1) (γ.prod γ) := by
    have h0 : IndepFun (Prod.snd : ℝ × ℝ → ℝ) (Prod.fst : ℝ × ℝ → ℝ) (γ.prod γ) :=
      (indepFun_prod (μ := γ) (ν := γ) (X := id) (Y := id) measurable_id measurable_id).symm
    exact h0.comp measurable_id (measurable_const_mul (S * √t))
  have hmap2 : (γ.prod γ).map (fun p : ℝ × ℝ => p.2) = gaussianReal 0 1 := by
    simp [γ]
  set vSt : ℝ≥0 := Real.toNNReal (S ^ 2 * t)
  have hvSt : (vSt : ℝ) = S ^ 2 * t := Real.coe_toNNReal (S ^ 2 * t) (by positivity)
  have hmap1 : (γ.prod γ).map (fun p : ℝ × ℝ => S * √t * p.1) = gaussianReal 0 vSt := by
    have hcomp : (fun p : ℝ × ℝ => S * √t * p.1) = (fun u => S * √t * u) ∘ Prod.fst := rfl
    rw [hcomp, ← Measure.map_map (by fun_prop) measurable_fst]
    have hfst : (γ.prod γ).map Prod.fst = gaussianReal 0 1 := by
      simp [γ]
    rw [hfst, gaussianReal_map_const_mul]
    congr 1
    · ring
    · ext
      simp only [NNReal.coe_mk, mul_one, hvSt]
      rw [mul_pow, Real.sq_sqrt ht.le]
  have hlaw : (γ.prod γ).map g = gaussianReal 0 (1 + vSt) := by
    simpa [g, Pi.add_def] using gaussianReal_add_gaussianReal_of_indepFun hind hmap2 hmap1
  rw [hlaw]
  set r := √(1 + S ^ 2 * t)
  have hr : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hscale : (gaussianReal 0 (1 + vSt)).map (fun u => u / r) = gaussianReal 0 1 := by
    rw [gaussianReal_map_div_const]
    congr 1
    · simp
    · ext
      simp only [NNReal.coe_div, NNReal.coe_add, NNReal.coe_one, NNReal.coe_mk, hvSt]
      have hsq : r ^ 2 = 1 + S ^ 2 * t := Real.sq_sqrt (by positivity)
      rw [hsq, div_self (by positivity)]
  rw [Phi_eq_gaussianReal, ← hscale, map_measureReal_apply (by fun_prop) measurableSet_Iic]
  congr 1
  ext u
  simp only [mem_preimage, mem_Iic, div_le_div_iff_of_pos_right hr]

/-- At a local minimum of `g` at `0` with `g' 0 = 0`, we have `0 ≤ g'' 0`. -/
lemma second_deriv_nonneg_of_isLocalMin {g g' : ℝ → ℝ} {g'' : ℝ}
    (hmin : IsLocalMin g 0)
    (hg : ∀ s, HasDerivAt g (g' s) s)
    (hg' : HasDerivAt g' g'' 0) (hg'0 : g' 0 = 0) : 0 ≤ g'' := by
  by_contra hlt
  push Not at hlt
  have hslope := hg'.tendsto_slope_zero_right
  simp only [zero_add] at hslope
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), s⁻¹ • (g' s - g' 0) < 0 :=
    hslope.eventually (gt_mem_nhds hlt)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨r₁, hr₁, h1⟩ := hev
  rw [IsLocalMin, IsMinFilter, Metric.eventually_nhds_iff] at hmin
  obtain ⟨r₂, hr₂, h2⟩ := hmin
  let s := min r₁ r₂ / 2
  have hs_pos : 0 < s := by positivity
  have hs_lt1 : s < r₁ := by dsimp [s]; linarith [min_le_left r₁ r₂]
  have hs_lt2 : s < r₂ := by dsimp [s]; linarith [min_le_right r₁ r₂]
  have hcont : ContinuousOn g (Icc 0 s) := fun z _ => (hg z).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope g g' hs_pos hcont (fun z _ => hg z)
  have hc_dist : dist c 0 < r₁ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hc.1]; linarith [hc.2]
  have hc_neg : c⁻¹ • (g' c - g' 0) < 0 := h1 hc_dist hc.1
  rw [hg'0, sub_zero, smul_eq_mul] at hc_neg
  have hg'c : g' c < 0 := by nlinarith [inv_pos.mpr hc.1]
  have hgs : g s < g 0 := by
    have : g s - g 0 = g' c * s := by
      rw [hcs, sub_zero, div_mul_cancel₀ _ hs_pos.ne']
    nlinarith
  have hge : g 0 ≤ g s := h2 (by rw [Real.dist_eq, sub_zero, abs_of_pos hs_pos]; exact hs_lt2)
  linarith

/-- At a minimum `t* ∈ (0, 1]` of `q` on `[0, 1]`, we have `q' t* ≤ 0`. -/
lemma deriv_nonpos_of_isMinOn_Icc {q : ℝ → ℝ} {t₀ q' : ℝ}
    (ht0 : 0 < t₀) (ht1 : t₀ ≤ 1)
    (hmin : ∀ t ∈ Icc (0 : ℝ) 1, q t₀ ≤ q t)
    (hq : HasDerivAt q q' t₀) : q' ≤ 0 := by
  by_contra hgt
  push Not at hgt
  have hslope := hq.tendsto_slope_zero_left
  have hev : ∀ᶠ h in 𝓝[<] (0 : ℝ), 0 < h⁻¹ • (q (t₀ + h) - q t₀) :=
    hslope.eventually (lt_mem_nhds hgt)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨r, hr, h1⟩ := hev
  let δ := min r t₀ / 2
  have hδ_pos : 0 < δ := by positivity
  have hneg : -δ < 0 := by linarith
  have hdist : dist (-δ) 0 < r := by
    rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos hδ_pos]
    dsimp [δ]; linarith [min_le_left r t₀]
  have hpos := h1 hdist hneg
  rw [smul_eq_mul] at hpos
  have hinv_neg : (-δ)⁻¹ < 0 := inv_neg''.mpr hneg
  have hlt : q (t₀ + (-δ)) < q t₀ := by nlinarith
  have hmem : t₀ + (-δ) ∈ Icc (0 : ℝ) 1 := ⟨by dsimp [δ]; linarith [min_le_right r t₀], by linarith⟩
  linarith [hmin _ hmem]

lemma continuous_of_lip {g : ℝ → ℝ} {S : ℝ} (hS : 0 ≤ S)
    (hg : ∀ x y, |g x - g y| ≤ S * |x - y|) : Continuous g := by
  rw [Metric.continuous_iff]
  intro x ε hε
  refine ⟨ε / (S + 1), by positivity, fun y hy => ?_⟩
  rw [Real.dist_eq] at hy ⊢
  have h1 := hg y x
  have h2 : (S + 1) * |y - x| < (S + 1) * (ε / (S + 1)) := by nlinarith
  rw [mul_div_cancel₀ _ (by linarith)] at h2
  nlinarith [abs_nonneg (y - x)]

lemma FFlow_joint_continuous {h : ℝ → ℝ} {S : ℝ} (hS : 0 ≤ S)
    (hlip : ∀ x y, |h x - h y| ≤ S * |x - y|) :
    ContinuousOn (fun q : ℝ × ℝ => FFlow (fun y => Phi (h y)) q.1 q.2) (Ici (0 : ℝ) ×ˢ univ) := by
  have hgl : ∀ x y, |Phi (h x) - Phi (h y)| ≤ S * |x - y| := fun x y =>
    (Phi_lipschitz (h x) (h y)).trans (hlip x y)
  have hgc : Continuous (fun y => Phi (h y)) := continuous_of_lip hS hgl
  have hgb : ∀ y, |Phi (h y)| ≤ 1 := fun y =>
    abs_le.mpr ⟨by linarith [Phi_pos (h y)], Phi_le_one _⟩
  have hhc := heat_joint_continuous hS hgl hgb
  intro q hq
  have hmem := heat_mem_Ioo hgc (fun y => ⟨Phi_pos _, Phi_lt_one _⟩) hq.1 q.2
  exact ContinuousAt.comp_continuousWithinAt (g := PhiInv)
    (f := fun p : ℝ × ℝ => heat (fun y => Phi (h y)) p.1 p.2)
    (continuousAt_PhiInv hmem) (hhc q hq)

lemma FFlow_ub_of_le {h : ℝ → ℝ} {S M₀ : ℝ} (hS : 0 ≤ S)
    (hlip : ∀ x y, |h x - h y| ≤ S * |x - y|) (hub : ∀ x, h x ≤ M₀)
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ) : FFlow (fun y => Phi (h y)) t x ≤ M₀ := by
  have hgc : Continuous (fun y => Phi (h y)) :=
    continuous_of_lip hS fun a b => (Phi_lipschitz _ _).trans (hlip a b)
  have hgb : ∀ y, |Phi (h y)| ≤ 1 := fun y => abs_le.mpr ⟨by linarith [Phi_pos (h y)], Phi_le_one _⟩
  have hle : heat (fun y => Phi (h y)) t x ≤ Phi M₀ := by
    rcases eq_or_lt_of_le ht with rfl | htp
    · rw [heat_zero]; exact Phi_strictMono.monotone (hub x)
    · rw [heat_eq_integral_phi _ htp x]
      calc ∫ z, Phi (h (x + √t * z)) * phi z
          ≤ ∫ z, Phi M₀ * phi z :=
            integral_mono (heat_integrable_phi hgc hgb x) (integrable_phi.const_mul _)
              fun z => mul_le_mul_of_nonneg_right (Phi_strictMono.monotone (hub _)) (phi_nonneg z)
        _ = Phi M₀ := by rw [integral_const_mul, integral_phi_eq_one, mul_one]
  have hm := heat_mem_Ioo hgc (fun y => ⟨Phi_pos _, Phi_lt_one _⟩) ht x
  rw [← PhiInv_Phi M₀]
  rcases eq_or_lt_of_le hle with heq | hlt
  · unfold FFlow; rw [heq]
  · exact (PhiInv_strictMonoOn hm ⟨Phi_pos _, Phi_lt_one _⟩ hlt).le

lemma FFlow_lb_nonpos_of_ge {h : ℝ → ℝ} {S M₀ : ℝ} (hS : 0 ≤ S)
    (hlip : ∀ x y, |h x - h y| ≤ S * |x - y|) (hlb : ∀ x ≤ 0, -M₀ ≤ h x)
    {t : ℝ} (ht : 0 ≤ t) {x : ℝ} (hx : x ≤ 0) :
    PhiInv ((1 / 2 : ℝ) * Phi (-M₀)) ≤ FFlow (fun y => Phi (h y)) t x := by
  have hgc : Continuous (fun y => Phi (h y)) :=
    continuous_of_lip hS fun a b => (Phi_lipschitz _ _).trans (hlip a b)
  have hgb : ∀ y, |Phi (h y)| ≤ 1 := fun y => abs_le.mpr ⟨by linarith [Phi_pos (h y)], Phi_le_one _⟩
  have hc_lb : (1 / 2 : ℝ) * Phi (-M₀) ∈ Ioo 0 1 :=
    ⟨by nlinarith [Phi_pos (-M₀)], by nlinarith [Phi_lt_one (-M₀)]⟩
  have hge : (1 / 2 : ℝ) * Phi (-M₀) ≤ heat (fun y => Phi (h y)) t x := by
    rcases eq_or_lt_of_le ht with rfl | htp
    · rw [heat_zero]
      have h1 : Phi (-M₀) ≤ Phi (h x) := Phi_strictMono.monotone (hlb x hx)
      linarith [Phi_pos (-M₀)]
    · rw [heat_eq_integral_phi _ htp x]
      have hsub : (∫ z in Iic (0 : ℝ), Phi (h (x + √t * z)) * phi z) ≤
          ∫ z, Phi (h (x + √t * z)) * phi z :=
        setIntegral_le_integral (heat_integrable_phi hgc hgb x)
          (ae_of_all _ fun z => mul_nonneg (Phi_nonneg _) (phi_nonneg z))
      have hmono : (∫ z in Iic (0 : ℝ), Phi (-M₀) * phi z) ≤
          ∫ z in Iic (0 : ℝ), Phi (h (x + √t * z)) * phi z := by
        refine setIntegral_mono_on (integrable_phi.const_mul _).integrableOn
          (heat_integrable_phi hgc hgb x).integrableOn measurableSet_Iic fun z hz => ?_
        have harg : x + √t * z ≤ 0 := by nlinarith [Real.sqrt_nonneg t, show z ≤ 0 from hz]
        exact mul_le_mul_of_nonneg_right (Phi_strictMono.monotone (hlb _ harg)) (phi_nonneg z)
      have h2 : (∫ z in Iic (0 : ℝ), Phi (-M₀) * phi z) = (1 / 2 : ℝ) * Phi (-M₀) := by
        rw [integral_const_mul]; change Phi (-M₀) * Phi 0 = (1 / 2) * Phi (-M₀); rw [Phi_zero]; ring
      linarith
  have hm := heat_mem_Ioo hgc (fun y => ⟨Phi_pos _, Phi_lt_one _⟩) ht x
  rcases eq_or_lt_of_le hge with heq | hlt
  · unfold FFlow; rw [heq]
  · exact (PhiInv_strictMonoOn hc_lb hm hlt).le

lemma FFlow_abs_le_linear {h : ℝ → ℝ} {S M₀ : ℝ} (hS : 0 ≤ S)
    (hlip : ∀ x y, |h x - h y| ≤ S * |x - y|) (hub : ∀ x, h x ≤ M₀) (hlb : ∀ x ≤ 0, -M₀ ≤ h x)
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    |FFlow (fun y => Phi (h y)) t x| ≤ max |M₀| (|PhiInv ((1 / 2 : ℝ) * Phi (-M₀))| + 1) + S * |x| := by
  let M₁ := max |M₀| (|PhiInv ((1 / 2 : ℝ) * Phi (-M₀))| + 1)
  have hgc : Continuous (fun y => Phi (h y)) :=
    continuous_of_lip hS fun a b => (Phi_lipschitz _ _).trans (hlip a b)
  have h0_le : |FFlow (fun y => Phi (h y)) t 0| ≤ M₁ := by
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have h1 := FFlow_lb_nonpos_of_ge hS hlip hlb ht le_rfl
      have h2 : |PhiInv ((1 / 2 : ℝ) * Phi (-M₀))| ≤ M₁ := le_trans (by linarith) (le_max_right _ _)
      linarith [neg_abs_le (PhiInv ((1 / 2 : ℝ) * Phi (-M₀)))]
    · have h1 := FFlow_ub_of_le hS hlip hub ht 0
      have h2 : |M₀| ≤ M₁ := le_max_left _ _
      linarith [le_abs_self M₀]
  have hdiff_le : |FFlow (fun y => Phi (h y)) t x - FFlow (fun y => Phi (h y)) t 0| ≤ S * |x| := by
    rcases eq_or_lt_of_le ht with rfl | htp
    · simp only [FFlow, heat_zero, PhiInv_Phi]
      simpa [sub_zero] using hlip x 0
    · have hdiff : Differentiable ℝ (FFlow (fun y => Phi (h y)) t) := fun u =>
        (hasDerivAt_FFlow_x hgc (fun y => ⟨Phi_pos _, Phi_lt_one _⟩) htp u).differentiableAt
      have hbd : ∀ u : ℝ, ‖deriv (FFlow (fun y => Phi (h y)) t) u‖ ≤ S := fun u => by
        rw [(hasDerivAt_FFlow_x hgc (fun y => ⟨Phi_pos _, Phi_lt_one _⟩) htp u).deriv, Real.norm_eq_abs]
        exact abs_FFlow_x_le hS hlip htp u
      have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (fun u _ => hdiff u)
        (fun u _ => hbd u) convex_univ (mem_univ 0) (mem_univ x)
      simpa [Real.norm_eq_abs, sub_zero] using hmv
  have htri : |FFlow (fun y => Phi (h y)) t x| ≤
      |FFlow (fun y => Phi (h y)) t x - FFlow (fun y => Phi (h y)) t 0| + |FFlow (fun y => Phi (h y)) t 0| := by
    simpa using abs_add_le (FFlow (fun y => Phi (h y)) t x - FFlow (fun y => Phi (h y)) t 0)
      (FFlow (fun y => Phi (h y)) t 0)
  linarith

lemma FFlow_le_affine {h : ℝ → ℝ} {S C : ℝ} (hS : 0 ≤ S)
    (hlip : ∀ x y, |h x - h y| ≤ S * |x - y|) (htail : ∀ x, h x ≤ -S * x + C)
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    FFlow (fun y => Phi (h y)) t x ≤ (-S * x + C) / √(1 + S ^ 2 * t) := by
  have hgc : Continuous (fun y => Phi (h y)) :=
    continuous_of_lip hS fun a b => (Phi_lipschitz _ _).trans (hlip a b)
  have hgb : ∀ y, |Phi (h y)| ≤ 1 := fun y => abs_le.mpr ⟨by linarith [Phi_pos (h y)], Phi_le_one _⟩
  have haff_c : Continuous (fun v => Phi (-S * v + C)) := continuous_Phi.comp (by fun_prop)
  have haff_b : ∀ v, |Phi (-S * v + C)| ≤ 1 := fun v =>
    abs_le.mpr ⟨by linarith [Phi_pos (-S * v + C)], Phi_le_one _⟩
  have hle : heat (fun v => Phi (h v)) t x ≤ Phi ((-S * x + C) / √(1 + S ^ 2 * t)) := by
    rcases eq_or_lt_of_le ht with rfl | htp
    · rw [heat_zero]; simp only [mul_zero, add_zero, sqrt_one, div_one]
      exact Phi_strictMono.monotone (htail x)
    · rw [← heat_affine_Phi S C htp x]
      exact heat_mono_fun hgc haff_c hgb haff_b (fun v => Phi_strictMono.monotone (htail v)) ht x
  have hm := heat_mem_Ioo hgc (fun v => ⟨Phi_pos _, Phi_lt_one _⟩) ht x
  rw [← PhiInv_Phi ((-S * x + C) / √(1 + S ^ 2 * t))]
  rcases eq_or_lt_of_le hle with heq | hlt
  · unfold FFlow; rw [heq]
  · exact (PhiInv_strictMonoOn hm ⟨Phi_pos _, Phi_lt_one _⟩ hlt).le

lemma ehrhard_H_lower_bound {h₁ h₂ h₃ : ℝ → ℝ} {S M₀ B₀ C₁ C₂ C₃ lam : ℝ}
    (hS : 0 ≤ S) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hlip₁ : ∀ x y, |h₁ x - h₁ y| ≤ S * |x - y|)
    (hlip₂ : ∀ x y, |h₂ x - h₂ y| ≤ S * |x - y|)
    (hlip₃ : ∀ x y, |h₃ x - h₃ y| ≤ S * |x - y|)
    (hub₁ : ∀ x, h₁ x ≤ M₀) (hub₂ : ∀ x, h₂ x ≤ M₀)
    (htail₁ : ∀ x, h₁ x ≤ -S * x + C₁)
    (htail₂ : ∀ x, h₂ x ≤ -S * x + C₂)
    (htail₃ : ∀ x, min B₀ (-S * x + C₃) ≤ h₃ x) :
    ∃ B : ℝ, 0 < B ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ x y,
      -B ≤ FFlow (fun u => Phi (h₃ u)) t (lam * x + (1 - lam) * y) -
        lam * FFlow (fun u => Phi (h₁ u)) t x - (1 - lam) * FFlow (fun u => Phi (h₂ u)) t y := by
  obtain ⟨A, hA_nonneg, hA_shift⟩ := exists_shift_PhiInv_mul_Phi (Phi_pos B₀) (Phi_le_one B₀)
  let c₃ := (1 / 2 : ℝ) * Phi B₀
  have hc₃ : c₃ ∈ Ioo 0 1 := ⟨by dsimp [c₃]; nlinarith [Phi_pos B₀], by dsimp [c₃]; nlinarith [Phi_lt_one B₀]⟩
  let B := max 1 (max (M₀ - PhiInv c₃ + 1) (|C₃ - lam * C₁ - (1 - lam) * C₂| + A + 1))
  have hB_pos : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hfc₃ : Continuous (fun u => Phi (h₃ u)) :=
    continuous_of_lip hS fun a b => (Phi_lipschitz _ _).trans (hlip₃ a b)
  have hfb₃ : ∀ u, |Phi (h₃ u)| ≤ 1 := fun u => abs_le.mpr ⟨by linarith [Phi_pos (h₃ u)], Phi_le_one _⟩
  refine ⟨B, hB_pos, fun t ht x y => ?_⟩
  have h1u := FFlow_le_affine hS hlip₁ htail₁ ht.1 x
  have h2u := FFlow_le_affine hS hlip₂ htail₂ ht.1 y
  let z := lam * x + (1 - lam) * y
  let v := (-S * z + C₃) / √(1 + S ^ 2 * t)
  have h3_prod : Phi B₀ * Phi v ≤ heat (fun u => Phi (h₃ u)) t z := by
    have hpt : ∀ u, Phi B₀ * Phi (-S * u + C₃) ≤ Phi (h₃ u) := fun u => by
      have hmin : min (Phi B₀) (Phi (-S * u + C₃)) ≤ Phi (h₃ u) := by
        rcases le_total B₀ (-S * u + C₃) with hle | hle
        · rw [min_eq_left (Phi_strictMono.monotone hle)]
          exact Phi_strictMono.monotone ((min_eq_left hle).symm ▸ htail₃ u)
        · rw [min_eq_right (Phi_strictMono.monotone hle)]
          exact Phi_strictMono.monotone ((min_eq_right hle).symm ▸ htail₃ u)
      have hmul_le : Phi B₀ * Phi (-S * u + C₃) ≤ min (Phi B₀) (Phi (-S * u + C₃)) :=
        le_min (by nlinarith [Phi_pos B₀, Phi_le_one (-S * u + C₃)])
          (by nlinarith [Phi_pos (-S * u + C₃), Phi_le_one B₀])
      linarith
    rcases eq_or_lt_of_le ht.1 with rfl | htp
    · simpa [heat_zero, v] using hpt z
    · rw [← heat_affine_Phi S C₃ htp z, heat_eq_integral_phi _ htp z, heat_eq_integral_phi _ htp z,
        ← integral_const_mul]
      have haff_c : Continuous (fun u => Phi (-S * u + C₃)) := continuous_Phi.comp (by fun_prop)
      have haff_b : ∀ u, |Phi (-S * u + C₃)| ≤ 1 := fun u =>
        abs_le.mpr ⟨by linarith [Phi_pos (-S * u + C₃)], Phi_le_one _⟩
      refine integral_mono ((heat_integrable_phi haff_c haff_b z).const_mul (Phi B₀))
        (heat_integrable_phi hfc₃ hfb₃ z) fun w => ?_
      have := hpt (z + √t * w)
      calc Phi B₀ * (Phi (-S * (z + √t * w) + C₃) * phi w)
          = (Phi B₀ * Phi (-S * (z + √t * w) + C₃)) * phi w := by ring
        _ ≤ Phi (h₃ (z + √t * w)) * phi w := mul_le_mul_of_nonneg_right this (phi_nonneg w)
  have hm3 := heat_mem_Ioo hfc₃ (fun u => ⟨Phi_pos _, Phi_lt_one _⟩) ht.1 z
  have hprod_mem : Phi B₀ * Phi v ∈ Ioo 0 1 :=
    ⟨mul_pos (Phi_pos B₀) (Phi_pos v), by nlinarith [Phi_pos B₀, Phi_lt_one B₀, Phi_lt_one v]⟩
  have hF3_ge_inv : PhiInv (Phi B₀ * Phi v) ≤ FFlow (fun u => Phi (h₃ u)) t z := by
    rcases eq_or_lt_of_le h3_prod with heq | hlt
    · unfold FFlow; rw [heq]
    · exact (PhiInv_strictMonoOn hprod_mem hm3 hlt).le
  by_cases hv : v ≤ 0
  · have hF3_ge : v - A ≤ FFlow (fun u => Phi (h₃ u)) t z := (hA_shift v hv).trans hF3_ge_inv
    have hsqrt_ge1 : 1 ≤ √(1 + S ^ 2 * t) := by rw [one_le_sqrt]; nlinarith [sq_nonneg S, ht.1]
    have hdiff_eq : v - lam * ((-S * x + C₁) / √(1 + S ^ 2 * t)) -
        (1 - lam) * ((-S * y + C₂) / √(1 + S ^ 2 * t)) =
        (C₃ - lam * C₁ - (1 - lam) * C₂) / √(1 + S ^ 2 * t) := by dsimp [v, z]; ring
    have hdiv_ge : -|C₃ - lam * C₁ - (1 - lam) * C₂| ≤
        (C₃ - lam * C₁ - (1 - lam) * C₂) / √(1 + S ^ 2 * t) := by
      have habs := neg_abs_le (C₃ - lam * C₁ - (1 - lam) * C₂)
      rw [le_div_iff₀ (lt_of_lt_of_le zero_lt_one hsqrt_ge1)]
      nlinarith [abs_nonneg (C₃ - lam * C₁ - (1 - lam) * C₂)]
    have hB2 : |C₃ - lam * C₁ - (1 - lam) * C₂| + A + 1 ≤ B :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    have h1m : lam * FFlow (fun u => Phi (h₁ u)) t x ≤ lam * ((-S * x + C₁) / √(1 + S ^ 2 * t)) :=
      mul_le_mul_of_nonneg_left h1u hlam0.le
    have h2m : (1 - lam) * FFlow (fun u => Phi (h₂ u)) t y ≤ (1 - lam) * ((-S * y + C₂) / √(1 + S ^ 2 * t)) :=
      mul_le_mul_of_nonneg_left h2u (by linarith)
    change -B ≤ FFlow (fun u => Phi (h₃ u)) t z - lam * FFlow (fun u => Phi (h₁ u)) t x -
      (1 - lam) * FFlow (fun u => Phi (h₂ u)) t y
    linarith
  · push Not at hv
    have hPhi_ge : c₃ ≤ Phi B₀ * Phi v := by
      have h1 : 1 / 2 ≤ Phi v := by rw [← Phi_zero]; exact (Phi_strictMono hv).le
      dsimp [c₃]; nlinarith [Phi_pos B₀]
    have hF3_ge : PhiInv c₃ ≤ FFlow (fun u => Phi (h₃ u)) t z := by
      have h1 : PhiInv c₃ ≤ PhiInv (Phi B₀ * Phi v) := by
        rcases eq_or_lt_of_le hPhi_ge with heq | hlt
        · rw [heq]
        · exact (PhiInv_strictMonoOn hc₃ hprod_mem hlt).le
      exact h1.trans hF3_ge_inv
    have hB1 : M₀ - PhiInv c₃ + 1 ≤ B := le_trans (le_max_left _ _) (le_max_right _ _)
    have h1m : lam * FFlow (fun u => Phi (h₁ u)) t x ≤ lam * M₀ :=
      mul_le_mul_of_nonneg_left (FFlow_ub_of_le hS hlip₁ hub₁ ht.1 x) hlam0.le
    have h2m : (1 - lam) * FFlow (fun u => Phi (h₂ u)) t y ≤ (1 - lam) * M₀ :=
      mul_le_mul_of_nonneg_left (FFlow_ub_of_le hS hlip₂ hub₂ ht.1 y) (by linarith)
    change -B ≤ FFlow (fun u => Phi (h₃ u)) t z - lam * FFlow (fun u => Phi (h₁ u)) t x -
      (1 - lam) * FFlow (fun u => Phi (h₂ u)) t y
    linarith

/-- Optimality conditions at a global minimum `(t₀, x₀, y₀)` of `U` on `[0, 1] × ℝ²` with `0 < t₀`. -/
lemma ehrhard_opt_conds {f₁ f₂ f₃ : ℝ → ℝ} {lam ε δ t₀ x₀ y₀ : ℝ}
    (hfc₁ : Continuous f₁) (hfc₂ : Continuous f₂) (hfc₃ : Continuous f₃)
    (hf01₁ : ∀ y, f₁ y ∈ Ioo 0 1) (hf01₂ : ∀ y, f₂ y ∈ Ioo 0 1) (hf01₃ : ∀ y, f₃ y ∈ Ioo 0 1)
    (ht0 : 0 < t₀) (ht1 : t₀ ≤ 1)
    (hglobal : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x y,
      FFlow f₃ t₀ (lam * x₀ + (1 - lam) * y₀) - lam * FFlow f₁ t₀ x₀ - (1 - lam) * FFlow f₂ t₀ y₀ +
        ε * t₀ + δ * (x₀ ^ 2 + y₀ ^ 2) ≤
      FFlow f₃ t (lam * x + (1 - lam) * y) - lam * FFlow f₁ t x - (1 - lam) * FFlow f₂ t y +
        ε * t + δ * (x ^ 2 + y ^ 2)) :
    let z₀ := lam * x₀ + (1 - lam) * y₀
    (lam * FFlow_x f₃ t₀ z₀ - lam * FFlow_x f₁ t₀ x₀ + 2 * δ * x₀ = 0) ∧
    ((1 - lam) * FFlow_x f₃ t₀ z₀ - (1 - lam) * FFlow_x f₂ t₀ y₀ + 2 * δ * y₀ = 0) ∧
    (0 ≤ FFlow_xx f₃ t₀ z₀ - lam * FFlow_xx f₁ t₀ x₀ - (1 - lam) * FFlow_xx f₂ t₀ y₀ + 4 * δ) ∧
    ((1 / 2) * (FFlow_xx f₃ t₀ z₀ - FFlow f₃ t₀ z₀ * FFlow_x f₃ t₀ z₀ ^ 2) -
      lam * ((1 / 2) * (FFlow_xx f₁ t₀ x₀ - FFlow f₁ t₀ x₀ * FFlow_x f₁ t₀ x₀ ^ 2)) -
      (1 - lam) * ((1 / 2) * (FFlow_xx f₂ t₀ y₀ - FFlow f₂ t₀ y₀ * FFlow_x f₂ t₀ y₀ ^ 2)) + ε ≤ 0) := by
  intro z₀
  let U : ℝ → ℝ → ℝ → ℝ := fun t x y =>
    FFlow f₃ t (lam * x + (1 - lam) * y) - lam * FFlow f₁ t x - (1 - lam) * FFlow f₂ t y +
      ε * t + δ * (x ^ 2 + y ^ 2)
  have ht_mem : t₀ ∈ Icc (0 : ℝ) 1 := ⟨ht0.le, ht1⟩
  have hdx : lam * FFlow_x f₃ t₀ z₀ - lam * FFlow_x f₁ t₀ x₀ + 2 * δ * x₀ = 0 := by
    have hmin_x : IsLocalMin (fun x => U t₀ x y₀) x₀ :=
      Filter.Eventually.of_forall fun x => hglobal t₀ ht_mem x y₀
    have hd3 : HasDerivAt (fun x => FFlow f₃ t₀ (lam * x + (1 - lam) * y₀)) (FFlow_x f₃ t₀ z₀ * lam) x₀ := by
      have hlin : HasDerivAt (fun x => lam * x + (1 - lam) * y₀) lam x₀ := by
        simpa using ((hasDerivAt_id x₀).const_mul lam).add_const ((1 - lam) * y₀)
      exact HasDerivAt.comp (h₂ := FFlow f₃ t₀) x₀ (hasDerivAt_FFlow_x hfc₃ hf01₃ ht0 z₀) hlin
    have hd1 := (hasDerivAt_FFlow_x hfc₁ hf01₁ ht0 x₀).const_mul lam
    have hdsq : HasDerivAt (fun x => δ * (x ^ 2 + y₀ ^ 2)) (2 * δ * x₀) x₀ :=
      (((hasDerivAt_pow 2 x₀).add_const (y₀ ^ 2)).const_mul δ).congr_deriv (by ring)
    have hdU : HasDerivAt (fun x => U t₀ x y₀) (lam * FFlow_x f₃ t₀ z₀ - lam * FFlow_x f₁ t₀ x₀ + 2 * δ * x₀) x₀ :=
      ((((hd3.sub hd1).sub_const ((1 - lam) * FFlow f₂ t₀ y₀)).add_const (ε * t₀)).add hdsq).congr_deriv (by ring)
    exact hmin_x.hasDerivAt_eq_zero hdU
  have hdy : (1 - lam) * FFlow_x f₃ t₀ z₀ - (1 - lam) * FFlow_x f₂ t₀ y₀ + 2 * δ * y₀ = 0 := by
    have hmin_y : IsLocalMin (fun y => U t₀ x₀ y) y₀ :=
      Filter.Eventually.of_forall fun y => hglobal t₀ ht_mem x₀ y
    have hd3 : HasDerivAt (fun y => FFlow f₃ t₀ (lam * x₀ + (1 - lam) * y)) (FFlow_x f₃ t₀ z₀ * (1 - lam)) y₀ := by
      have hlin : HasDerivAt (fun y => lam * x₀ + (1 - lam) * y) (1 - lam) y₀ := by
        simpa using ((hasDerivAt_id y₀).const_mul (1 - lam)).const_add (lam * x₀)
      exact HasDerivAt.comp (h₂ := FFlow f₃ t₀) y₀ (hasDerivAt_FFlow_x hfc₃ hf01₃ ht0 z₀) hlin
    have hd2 := (hasDerivAt_FFlow_x hfc₂ hf01₂ ht0 y₀).const_mul (1 - lam)
    have hdsq : HasDerivAt (fun y => δ * (x₀ ^ 2 + y ^ 2)) (2 * δ * y₀) y₀ :=
      (((hasDerivAt_pow 2 y₀).const_add (x₀ ^ 2)).const_mul δ).congr_deriv (by ring)
    have hdU : HasDerivAt (fun y => U t₀ x₀ y)
        ((1 - lam) * FFlow_x f₃ t₀ z₀ - (1 - lam) * FFlow_x f₂ t₀ y₀ + 2 * δ * y₀) y₀ :=
      ((((hd3.sub_const (lam * FFlow f₁ t₀ x₀)).sub hd2).add_const (ε * t₀)).add hdsq).congr_deriv (by ring)
    exact hmin_y.hasDerivAt_eq_zero hdU
  have hd2s : 0 ≤ FFlow_xx f₃ t₀ z₀ - lam * FFlow_xx f₁ t₀ x₀ - (1 - lam) * FFlow_xx f₂ t₀ y₀ + 4 * δ := by
    let g : ℝ → ℝ := fun s => U t₀ (x₀ + s) (y₀ + s)
    let g' : ℝ → ℝ := fun s =>
      FFlow_x f₃ t₀ (z₀ + s) - lam * FFlow_x f₁ t₀ (x₀ + s) - (1 - lam) * FFlow_x f₂ t₀ (y₀ + s) +
        2 * δ * (x₀ + s) + 2 * δ * (y₀ + s)
    have hg_min : IsLocalMin g 0 :=
      Filter.Eventually.of_forall fun s => by simpa [g] using hglobal t₀ ht_mem (x₀ + s) (y₀ + s)
    have hg_deriv : ∀ s, HasDerivAt g (g' s) s := fun s => by
      have harg : ∀ u, lam * (x₀ + u) + (1 - lam) * (y₀ + u) = z₀ + u := fun u => by dsimp [z₀]; ring
      have hd3 : HasDerivAt (fun u => FFlow f₃ t₀ (lam * (x₀ + u) + (1 - lam) * (y₀ + u)))
          (FFlow_x f₃ t₀ (z₀ + s)) s := by
        simp_rw [harg]
        exact (HasDerivAt.comp (h₂ := FFlow f₃ t₀) s (hasDerivAt_FFlow_x hfc₃ hf01₃ ht0 (z₀ + s))
          ((hasDerivAt_id s).const_add z₀)).congr_deriv (mul_one _)
      have hd1 : HasDerivAt (fun u => lam * FFlow f₁ t₀ (x₀ + u)) (lam * FFlow_x f₁ t₀ (x₀ + s)) s :=
        ((HasDerivAt.comp (h₂ := FFlow f₁ t₀) s (hasDerivAt_FFlow_x hfc₁ hf01₁ ht0 (x₀ + s))
          ((hasDerivAt_id s).const_add x₀)).const_mul lam).congr_deriv (by ring)
      have hd2 : HasDerivAt (fun u => (1 - lam) * FFlow f₂ t₀ (y₀ + u))
          ((1 - lam) * FFlow_x f₂ t₀ (y₀ + s)) s :=
        ((HasDerivAt.comp (h₂ := FFlow f₂ t₀) s (hasDerivAt_FFlow_x hfc₂ hf01₂ ht0 (y₀ + s))
          ((hasDerivAt_id s).const_add y₀)).const_mul (1 - lam)).congr_deriv (by ring)
      have hdsq : HasDerivAt (fun u => δ * ((x₀ + u) ^ 2 + (y₀ + u) ^ 2))
          (2 * δ * (x₀ + s) + 2 * δ * (y₀ + s)) s := by
        have ha := (((hasDerivAt_id s).const_add x₀).pow 2).congr_deriv (by ring : 2 * (x₀ + s) ^ (2 - 1) * 1 = 2 * (x₀ + s))
        have hb := (((hasDerivAt_id s).const_add y₀).pow 2).congr_deriv (by ring : 2 * (y₀ + s) ^ (2 - 1) * 1 = 2 * (y₀ + s))
        exact ((ha.add hb).const_mul δ).congr_deriv (by ring)
      exact ((((hd3.sub hd1).sub hd2).add_const (ε * t₀)).add hdsq).congr_deriv (by dsimp [g']; ring)
    have hg'_deriv : HasDerivAt g'
        (FFlow_xx f₃ t₀ z₀ - lam * FFlow_xx f₁ t₀ x₀ - (1 - lam) * FFlow_xx f₂ t₀ y₀ + 4 * δ) 0 := by
      have hd3 : HasDerivAt (fun u => FFlow_x f₃ t₀ (z₀ + u)) (FFlow_xx f₃ t₀ z₀) 0 := by
        have h := HasDerivAt.comp (h₂ := FFlow_x f₃ t₀) 0 (hasDerivAt_FFlow_xx hfc₃ hf01₃ ht0 (z₀ + 0))
          ((hasDerivAt_id 0).const_add z₀)
        rw [add_zero, mul_one] at h
        exact h
      have hd1 : HasDerivAt (fun u => lam * FFlow_x f₁ t₀ (x₀ + u)) (lam * FFlow_xx f₁ t₀ x₀) 0 := by
        have h := (HasDerivAt.comp (h₂ := FFlow_x f₁ t₀) 0 (hasDerivAt_FFlow_xx hfc₁ hf01₁ ht0 (x₀ + 0))
          ((hasDerivAt_id 0).const_add x₀)).const_mul lam
        rw [add_zero, mul_one] at h
        exact h
      have hd2 : HasDerivAt (fun u => (1 - lam) * FFlow_x f₂ t₀ (y₀ + u)) ((1 - lam) * FFlow_xx f₂ t₀ y₀) 0 := by
        have h := (HasDerivAt.comp (h₂ := FFlow_x f₂ t₀) 0 (hasDerivAt_FFlow_xx hfc₂ hf01₂ ht0 (y₀ + 0))
          ((hasDerivAt_id 0).const_add y₀)).const_mul (1 - lam)
        rw [add_zero, mul_one] at h
        exact h
      have hl1 : HasDerivAt (fun u => 2 * δ * (x₀ + u)) (2 * δ) 0 :=
        (((hasDerivAt_id 0).const_add x₀).const_mul (2 * δ)).congr_deriv (mul_one _)
      have hl2 : HasDerivAt (fun u => 2 * δ * (y₀ + u)) (2 * δ) 0 :=
        (((hasDerivAt_id 0).const_add y₀).const_mul (2 * δ)).congr_deriv (mul_one _)
      exact ((((hd3.sub hd1).sub hd2).add hl1).add hl2).congr_deriv (by ring)
    have hg'0 : g' 0 = 0 := by dsimp [g']; simp only [add_zero]; linarith
    exact second_deriv_nonneg_of_isLocalMin hg_min hg_deriv hg'_deriv hg'0
  have hdt : (1 / 2) * (FFlow_xx f₃ t₀ z₀ - FFlow f₃ t₀ z₀ * FFlow_x f₃ t₀ z₀ ^ 2) -
      lam * ((1 / 2) * (FFlow_xx f₁ t₀ x₀ - FFlow f₁ t₀ x₀ * FFlow_x f₁ t₀ x₀ ^ 2)) -
      (1 - lam) * ((1 / 2) * (FFlow_xx f₂ t₀ y₀ - FFlow f₂ t₀ y₀ * FFlow_x f₂ t₀ y₀ ^ 2)) + ε ≤ 0 := by
    have hd3 := hasDerivAt_FFlow_t hfc₃ hf01₃ ht0 z₀
    have hd1 := (hasDerivAt_FFlow_t hfc₁ hf01₁ ht0 x₀).const_mul lam
    have hd2 := (hasDerivAt_FFlow_t hfc₂ hf01₂ ht0 y₀).const_mul (1 - lam)
    have hde : HasDerivAt (fun s => ε * s) ε t₀ :=
      ((hasDerivAt_id t₀).const_mul ε).congr_deriv (mul_one _)
    have hdU : HasDerivAt (fun s => U s x₀ y₀)
        ((1 / 2) * (FFlow_xx f₃ t₀ z₀ - FFlow f₃ t₀ z₀ * FFlow_x f₃ t₀ z₀ ^ 2) -
          lam * ((1 / 2) * (FFlow_xx f₁ t₀ x₀ - FFlow f₁ t₀ x₀ * FFlow_x f₁ t₀ x₀ ^ 2)) -
          (1 - lam) * ((1 / 2) * (FFlow_xx f₂ t₀ y₀ - FFlow f₂ t₀ y₀ * FFlow_x f₂ t₀ y₀ ^ 2)) + ε) t₀ :=
      ((((hd3.sub hd1).sub hd2).add hde).add_const (δ * (x₀ ^ 2 + y₀ ^ 2))).congr_deriv (by ring)
    exact deriv_nonpos_of_isMinOn_Icc ht0 ht1 (fun t ht => hglobal t ht x₀ y₀) hdU
  exact ⟨hdx, hdy, hd2s, hdt⟩

/-- Pure algebraic contradiction from the optimality conditions at the minimum `(t₀, x₀, y₀)`. -/
lemma ehrhard_contra_of_opt {S M₁ B lam ε δ x₀ y₀ F1 F2 F3 F1' F2' F3' F1'' F2'' F3'' : ℝ}
    (hS : 0 ≤ S) (hM₁ : 0 < M₁) (hB : 0 < B) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hδ : 0 < δ)
    (hδ_err : (2 + 2 * B * (1 / lam + 1 / (1 - lam)) * M₁) * δ +
      (4 * S * M₁ * √B + 2 * B * (1 / lam + 1 / (1 - lam)) * S * √B) * √δ < ε)
    (hH_neg : F3 - lam * F1 - (1 - lam) * F2 < 0)
    (hδxy : δ * (x₀ ^ 2 + y₀ ^ 2) < B)
    (hF1_ub : F1 ≤ M₁) (hF2_ub : F2 ≤ M₁)
    (hF1_lb : x₀ < 0 → -M₁ ≤ F1) (hF2_lb : y₀ < 0 → -M₁ ≤ F2)
    (hF1_lin : |F1| ≤ M₁ + S * |x₀|) (hF2_lin : |F2| ≤ M₁ + S * |y₀|)
    (hF3'_nonpos : F3' ≤ 0) (hF3'_abs : |F3'| ≤ S)
    (hdx : lam * F3' - lam * F1' + 2 * δ * x₀ = 0)
    (hdy : (1 - lam) * F3' - (1 - lam) * F2' + 2 * δ * y₀ = 0)
    (hd2s : 0 ≤ F3'' - lam * F1'' - (1 - lam) * F2'' + 4 * δ)
    (hdt : (1 / 2) * (F3'' - F3 * F3' ^ 2) - lam * ((1 / 2) * (F1'' - F1 * F1' ^ 2)) -
      (1 - lam) * ((1 / 2) * (F2'' - F2 * F2' ^ 2)) + ε ≤ 0) : False := by
  have h1l_pos : 0 < 1 - lam := by linarith
  have hdx2 : δ * x₀ ^ 2 ≤ B := by
    have : 0 ≤ δ * y₀ ^ 2 := mul_nonneg hδ.le (sq_nonneg y₀)
    linarith
  have hdy2 : δ * y₀ ^ 2 ≤ B := by
    have : 0 ≤ δ * x₀ ^ 2 := mul_nonneg hδ.le (sq_nonneg x₀)
    linarith
  have hx₀_bd : |x₀| ≤ √(B / δ) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt ((le_div_iff₀ hδ).mpr (by linarith))
  have hy₀_bd : |y₀| ≤ √(B / δ) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt ((le_div_iff₀ hδ).mpr (by linarith))
  have hrt_id : δ * √(B / δ) = √(B * δ) := by
    calc δ * √(B / δ) = √(δ ^ 2) * √(B / δ) := by rw [Real.sqrt_sq hδ.le]
      _ = √(δ ^ 2 * (B / δ)) := (Real.sqrt_mul (sq_nonneg δ) _).symm
      _ = √(B * δ) := by congr 1; field_simp [hδ.ne']
  have hF1'_eq : F1' = F3' + 2 * δ * x₀ / lam := by
    have : lam * F1' = lam * F3' + 2 * δ * x₀ := by linarith
    field_simp [hlam0.ne']; linarith
  have hF2'_eq : F2' = F3' + 2 * δ * y₀ / (1 - lam) := by
    have : (1 - lam) * F2' = (1 - lam) * F3' + 2 * δ * y₀ := by linarith
    field_simp [h1l_pos.ne']; linarith
  have hcross : ∀ (F u : ℝ), F ≤ M₁ → (u < 0 → -M₁ ≤ F) → |u| ≤ √(B / δ) →
      -2 * S * M₁ * √(B * δ) ≤ 2 * δ * F3' * F * u := by
    intro F u hFub hFlb hubd
    have hrt : δ * |u| ≤ √(B * δ) := by
      calc δ * |u| ≤ δ * √(B / δ) := mul_le_mul_of_nonneg_left hubd hδ.le
        _ = √(B * δ) := hrt_id
    by_cases hu : 0 ≤ u
    · have h2 : 2 * δ * F3' * u ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity) hF3'_nonpos) hu
      have h3 : (2 * δ * F3' * u) * M₁ ≤ (2 * δ * F3' * u) * F :=
        mul_le_mul_of_nonpos_left hFub h2
      have h4 : -S ≤ F3' := neg_le_of_abs_le hF3'_abs
      have h5 : |u| = u := abs_of_nonneg hu
      have h6 : (-S) * (2 * M₁ * (δ * u)) ≤ F3' * (2 * M₁ * (δ * u)) :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
      have h7 : 2 * S * M₁ * (δ * u) ≤ 2 * S * M₁ * √(B * δ) := by
        rw [← h5]
        exact mul_le_mul_of_nonneg_left hrt (by positivity)
      linarith
    · push Not at hu
      have h1 : |F| ≤ M₁ := abs_le.mpr ⟨hFlb hu, hFub⟩
      have h2 : |2 * δ * F3' * F * u| ≤ 2 * S * M₁ * √(B * δ) := by
        have heq : |2 * δ * F3' * F * u| = 2 * |F3'| * |F| * (δ * |u|) := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
            abs_of_pos hδ]; ring
        rw [heq]
        have hs1 : |F3'| * |F| ≤ S * M₁ := mul_le_mul hF3'_abs h1 (abs_nonneg _) hS
        have hs2 : 2 * (|F3'| * |F|) * (δ * |u|) ≤ 2 * (S * M₁) * √(B * δ) :=
          mul_le_mul (by linarith) hrt (by positivity) (by positivity)
        linarith
      linarith [neg_abs_le (2 * δ * F3' * F * u)]
  have hterm_x := hcross F1 x₀ hF1_ub hF1_lb hx₀_bd
  have hterm_y := hcross F2 y₀ hF2_ub hF2_lb hy₀_bd
  have hquad : ∀ (F u w : ℝ), 0 < w → |F| ≤ M₁ + S * |u| → |u| ≤ √(B / δ) → δ * u ^ 2 ≤ B →
      -(2 * B * (1 / w) * (M₁ * δ + S * √(B * δ))) ≤ 2 * δ ^ 2 * F * u ^ 2 / w := by
    intro F u w hw hFlin hubd hdu2
    have hFu : |F| ≤ M₁ + S * √(B / δ) :=
      hFlin.trans (add_le_add_right (mul_le_mul_of_nonneg_left hubd hS) M₁)
    have habs : |2 * δ ^ 2 * F * u ^ 2 / w| ≤ 2 * B * (1 / w) * (M₁ * δ + S * √(B * δ)) := by
      rw [abs_div, abs_of_pos hw, abs_mul, abs_mul, abs_mul,
        abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos (sq_pos_of_pos hδ),
        abs_of_nonneg (sq_nonneg u)]
      have h1 : δ * |F| ≤ M₁ * δ + S * √(B * δ) := by
        calc δ * |F| ≤ δ * (M₁ + S * √(B / δ)) := mul_le_mul_of_nonneg_left hFu hδ.le
          _ = M₁ * δ + S * (δ * √(B / δ)) := by ring
          _ = M₁ * δ + S * √(B * δ) := by rw [hrt_id]
      have h2 : (δ * u ^ 2) * (δ * |F|) ≤ B * (M₁ * δ + S * √(B * δ)) :=
        mul_le_mul hdu2 h1 (by positivity) hB.le
      have hnum : 2 * δ ^ 2 * |F| * u ^ 2 ≤ 2 * B * (M₁ * δ + S * √(B * δ)) := by linarith
      calc 2 * δ ^ 2 * |F| * u ^ 2 / w
          ≤ 2 * B * (M₁ * δ + S * √(B * δ)) / w := div_le_div_of_nonneg_right hnum hw.le
        _ = 2 * B * (1 / w) * (M₁ * δ + S * √(B * δ)) := by ring
    linarith [neg_abs_le (2 * δ ^ 2 * F * u ^ 2 / w)]
  have hquad_x := hquad F1 x₀ lam hlam0 hF1_lin hx₀_bd hdx2
  have hquad_y := hquad F2 y₀ (1 - lam) h1l_pos hF2_lin hy₀_bd hdy2
  have halg : (1 / 2) * (F3'' - F3 * F3' ^ 2) - lam * ((1 / 2) * (F1'' - F1 * F1' ^ 2)) -
      (1 - lam) * ((1 / 2) * (F2'' - F2 * F2' ^ 2)) =
      (1 / 2) * (F3'' - lam * F1'' - (1 - lam) * F2'') -
        (1 / 2) * F3' ^ 2 * (F3 - lam * F1 - (1 - lam) * F2) +
        2 * δ * F3' * F1 * x₀ + 2 * δ * F3' * F2 * y₀ +
        2 * δ ^ 2 * F1 * x₀ ^ 2 / lam + 2 * δ ^ 2 * F2 * y₀ ^ 2 / (1 - lam) := by
    rw [hF1'_eq, hF2'_eq]
    field_simp [hlam0.ne', h1l_pos.ne']
    ring
  have hneg_H : 0 ≤ -(1 / 2) * F3' ^ 2 * (F3 - lam * F1 - (1 - lam) * F2) := by
    have h1 : 0 ≤ (1 / 2 : ℝ) * F3' ^ 2 := by positivity
    have h2 : 0 ≤ -(F3 - lam * F1 - (1 - lam) * F2) := by linarith
    have := mul_nonneg h1 h2
    linarith
  have herr_eq : 2 * δ + 4 * S * M₁ * √(B * δ) +
      2 * B * (1 / lam) * (M₁ * δ + S * √(B * δ)) +
      2 * B * (1 / (1 - lam)) * (M₁ * δ + S * √(B * δ)) =
      (2 + 2 * B * (1 / lam + 1 / (1 - lam)) * M₁) * δ +
      (4 * S * M₁ * √B + 2 * B * (1 / lam + 1 / (1 - lam)) * S * √B) * √δ := by
    rw [Real.sqrt_mul hB.le δ]; ring
  linarith

/-- 1D Functional Ehrhard Inequality for antitone `S`-Lipschitz functions with affine tails. -/
theorem ehrhard_1d_lipschitz {h₁ h₂ h₃ : ℝ → ℝ} {S M₀ B₀ C₁ C₂ C₃ lam : ℝ}
    (hS : 0 ≤ S) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hanti₃ : Antitone h₃)
    (hlip₁ : ∀ x y, |h₁ x - h₁ y| ≤ S * |x - y|)
    (hlip₂ : ∀ x y, |h₂ x - h₂ y| ≤ S * |x - y|)
    (hlip₃ : ∀ x y, |h₃ x - h₃ y| ≤ S * |x - y|)
    (hub₁ : ∀ x, h₁ x ≤ M₀) (hub₂ : ∀ x, h₂ x ≤ M₀)
    (hlb₁ : ∀ x ≤ 0, -M₀ ≤ h₁ x) (hlb₂ : ∀ x ≤ 0, -M₀ ≤ h₂ x)
    (htail₁ : ∀ x, h₁ x ≤ -S * x + C₁)
    (htail₂ : ∀ x, h₂ x ≤ -S * x + C₂)
    (htail₃ : ∀ x, min B₀ (-S * x + C₃) ≤ h₃ x)
    (hconv : ∀ x y, lam * h₁ x + (1 - lam) * h₂ y ≤ h₃ (lam * x + (1 - lam) * y)) :
    lam * PhiInv (∫ x, Phi (h₁ x) * phi x) + (1 - lam) * PhiInv (∫ x, Phi (h₂ x) * phi x) ≤
      PhiInv (∫ x, Phi (h₃ x) * phi x) := by
  have hfc₁ : Continuous (fun x => Phi (h₁ x)) :=
    continuous_of_lip hS fun a b => (Phi_lipschitz _ _).trans (hlip₁ a b)
  have hfc₂ : Continuous (fun x => Phi (h₂ x)) :=
    continuous_of_lip hS fun a b => (Phi_lipschitz _ _).trans (hlip₂ a b)
  have hfc₃ : Continuous (fun x => Phi (h₃ x)) :=
    continuous_of_lip hS fun a b => (Phi_lipschitz _ _).trans (hlip₃ a b)
  have hf01₁ : ∀ y, Phi (h₁ y) ∈ Ioo 0 1 := fun y => ⟨Phi_pos _, Phi_lt_one _⟩
  have hf01₂ : ∀ y, Phi (h₂ y) ∈ Ioo 0 1 := fun y => ⟨Phi_pos _, Phi_lt_one _⟩
  have hf01₃ : ∀ y, Phi (h₃ y) ∈ Ioo 0 1 := fun y => ⟨Phi_pos _, Phi_lt_one _⟩
  have hfb₃ : ∀ y, |Phi (h₃ y)| ≤ 1 := fun y => abs_le.mpr ⟨by linarith [Phi_pos (h₃ y)], Phi_le_one _⟩
  have hint_eq : ∀ g : ℝ → ℝ, (∫ x, g x * phi x) = heat g 1 0 := fun g => by
    rw [heat_eq_integral_phi g zero_lt_one 0]; simp
  rw [hint_eq (fun x => Phi (h₁ x)), hint_eq (fun x => Phi (h₂ x)), hint_eq (fun x => Phi (h₃ x))]
  suffices hgoal : 0 ≤ FFlow (fun x => Phi (h₃ x)) 1 (lam * 0 + (1 - lam) * 0) -
      lam * FFlow (fun x => Phi (h₁ x)) 1 0 - (1 - lam) * FFlow (fun x => Phi (h₂ x)) 1 0 by
    simp only [mul_zero, add_zero] at hgoal; unfold FFlow at hgoal; linarith
  have hH0 : ∀ x y, 0 ≤ FFlow (fun u => Phi (h₃ u)) 0 (lam * x + (1 - lam) * y) -
      lam * FFlow (fun u => Phi (h₁ u)) 0 x - (1 - lam) * FFlow (fun u => Phi (h₂ u)) 0 y := fun x y => by
    simp only [FFlow, heat_zero, PhiInv_Phi]; linarith [hconv x y]
  obtain ⟨B, hB_pos, hH_lb⟩ :=
    ehrhard_H_lower_bound hS hlam0 hlam1 hlip₁ hlip₂ hlip₃ hub₁ hub₂ htail₁ htail₂ htail₃
  obtain ⟨M₁, hM₁_def⟩ : ∃ M₁ : ℝ, M₁ = max |M₀| (|PhiInv ((1 / 2 : ℝ) * Phi (-M₀))| + 1) := ⟨_, rfl⟩
  have hM₁_pos : 0 < M₁ := hM₁_def ▸ lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hM₀_le_M₁ : |M₀| ≤ M₁ := hM₁_def ▸ le_max_left _ _
  have h1l_pos : 0 < 1 - lam := by linarith
  by_contra hneg
  push Not at hneg
  obtain ⟨ε, hε_pos, hU100⟩ : ∃ ε : ℝ, 0 < ε ∧
      FFlow (fun x => Phi (h₃ x)) 1 (lam * 0 + (1 - lam) * 0) -
        lam * FFlow (fun x => Phi (h₁ x)) 1 0 - (1 - lam) * FFlow (fun x => Phi (h₂ x)) 1 0 + ε < 0 :=
    ⟨-(FFlow (fun x => Phi (h₃ x)) 1 (lam * 0 + (1 - lam) * 0) -
      lam * FFlow (fun x => Phi (h₁ x)) 1 0 - (1 - lam) * FFlow (fun x => Phi (h₂ x)) 1 0) / 2,
      by linarith, by linarith⟩
  obtain ⟨δ, hδ_pos, hδ_err⟩ : ∃ δ : ℝ, 0 < δ ∧
      (2 + 2 * B * (1 / lam + 1 / (1 - lam)) * M₁) * δ +
      (4 * S * M₁ * √B + 2 * B * (1 / lam + 1 / (1 - lam)) * S * √B) * √δ < ε := by
    let Kl : ℝ := 2 + 2 * B * (1 / lam + 1 / (1 - lam)) * M₁
    let Ks : ℝ := 4 * S * M₁ * √B + 2 * B * (1 / lam + 1 / (1 - lam)) * S * √B
    have hKl : 0 < Kl := by dsimp [Kl]; positivity
    have hKs : 0 ≤ Ks := by dsimp [Ks]; positivity
    refine ⟨min (ε / (4 * Kl)) ((ε / (4 * (Ks + 1))) ^ 2),
      lt_min (by positivity) (sq_pos_of_pos (by positivity)), ?_⟩
    set d := min (ε / (4 * Kl)) ((ε / (4 * (Ks + 1))) ^ 2)
    have h1 : Kl * d ≤ ε / 4 :=
      (mul_le_mul_of_nonneg_left (min_le_left _ _) hKl.le).trans_eq (by field_simp [hKl.ne'])
    have h2 : √d ≤ ε / (4 * (Ks + 1)) :=
      (Real.sqrt_le_sqrt (min_le_right _ _)).trans_eq (Real.sqrt_sq (by positivity))
    have h3 : Ks * √d ≤ ε / 4 := by
      have hk : Ks ≤ Ks + 1 := by linarith
      have hne : Ks + 1 ≠ 0 := by linarith
      calc Ks * √d ≤ (Ks + 1) * (ε / (4 * (Ks + 1))) :=
            mul_le_mul hk h2 (Real.sqrt_nonneg _) (by linarith)
        _ = ε / 4 := by field_simp [hne]
    change Kl * d + Ks * √d < ε
    linarith
  obtain ⟨R, hR_pos, hR_sq⟩ : ∃ R : ℝ, 0 < R ∧ B < δ * R ^ 2 := by
    refine ⟨√(B / δ) + 1, by positivity, ?_⟩
    have h1 : √(B / δ) < √(B / δ) + 1 := by linarith
    have h2 : (√(B / δ)) ^ 2 < (√(B / δ) + 1) ^ 2 := by nlinarith [Real.sqrt_nonneg (B / δ)]
    rw [Real.sq_sqrt (by positivity)] at h2
    linarith [(div_lt_iff₀ hδ_pos).mp h2]
  let U : ℝ × ℝ × ℝ → ℝ := fun p =>
    FFlow (fun x => Phi (h₃ x)) p.1 (lam * p.2.1 + (1 - lam) * p.2.2) -
      lam * FFlow (fun x => Phi (h₁ x)) p.1 p.2.1 - (1 - lam) * FFlow (fun x => Phi (h₂ x)) p.1 p.2.2 +
      ε * p.1 + δ * (p.2.1 ^ 2 + p.2.2 ^ 2)
  let K : Set (ℝ × ℝ × ℝ) := Icc 0 1 ×ˢ (Icc (-R) R ×ˢ Icc (-R) R)
  have hK_comp : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hK_ne : K.Nonempty := ⟨(1, 0, 0), ⟨by norm_num, by norm_num⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hU_cont : ContinuousOn U K := by
    have hc1 : ContinuousOn (fun p : ℝ × ℝ × ℝ => FFlow (fun x => Phi (h₁ x)) p.1 p.2.1) K :=
      (FFlow_joint_continuous hS hlip₁).comp (s := K) (f := fun p : ℝ × ℝ × ℝ => (p.1, p.2.1))
        (by fun_prop) (fun p hp => ⟨hp.1.1, trivial⟩)
    have hc2 : ContinuousOn (fun p : ℝ × ℝ × ℝ => FFlow (fun x => Phi (h₂ x)) p.1 p.2.2) K :=
      (FFlow_joint_continuous hS hlip₂).comp (s := K) (f := fun p : ℝ × ℝ × ℝ => (p.1, p.2.2))
        (by fun_prop) (fun p hp => ⟨hp.1.1, trivial⟩)
    have hc3 : ContinuousOn (fun p : ℝ × ℝ × ℝ => FFlow (fun x => Phi (h₃ x)) p.1 (lam * p.2.1 + (1 - lam) * p.2.2)) K :=
      (FFlow_joint_continuous hS hlip₃).comp (s := K)
        (f := fun p : ℝ × ℝ × ℝ => (p.1, lam * p.2.1 + (1 - lam) * p.2.2))
        (by fun_prop) (fun p hp => ⟨hp.1.1, trivial⟩)
    exact (((hc3.sub (continuousOn_const.mul hc1)).sub (continuousOn_const.mul hc2)).add
      (by fun_prop)).add (by fun_prop)
  obtain ⟨⟨t₀, x₀, y₀⟩, hp₀_mem, hp₀_min⟩ := hK_comp.exists_isMinOn hK_ne hU_cont
  have hU_neg : U (t₀, x₀, y₀) < 0 := by
    have hle : U (t₀, x₀, y₀) ≤ U (1, 0, 0) :=
      hp₀_min ⟨⟨by norm_num, by norm_num⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    have hval : U (1, 0, 0) = FFlow (fun x => Phi (h₃ x)) 1 (lam * 0 + (1 - lam) * 0) -
        lam * FFlow (fun x => Phi (h₁ x)) 1 0 - (1 - lam) * FFlow (fun x => Phi (h₂ x)) 1 0 + ε := by
      simp [U]
    linarith
  have hglobal : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x y, U (t₀, x₀, y₀) ≤ U (t, x, y) := by
    intro t ht x y
    by_cases hxy : x ∈ Icc (-R) R ∧ y ∈ Icc (-R) R
    · exact hp₀_min ⟨ht, hxy.1, hxy.2⟩
    · have hsq_ge : R ^ 2 ≤ x ^ 2 + y ^ 2 := by
        by_cases hx : x ∈ Icc (-R) R
        · have hy : y ∉ Icc (-R) R := fun h => hxy ⟨hx, h⟩
          have : R < |y| := by
            rw [lt_abs]; by_contra h; push Not at h; exact hy ⟨by linarith, by linarith⟩
          have : R ^ 2 ≤ y ^ 2 := by nlinarith [sq_abs y, abs_nonneg y]
          linarith [sq_nonneg x]
        · have : R < |x| := by
            rw [lt_abs]; by_contra h; push Not at h; exact hx ⟨by linarith, by linarith⟩
          have : R ^ 2 ≤ x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
          linarith [sq_nonneg y]
      have hδR2 : B < δ * (x ^ 2 + y ^ 2) :=
        lt_of_lt_of_le hR_sq (mul_le_mul_of_nonneg_left hsq_ge hδ_pos.le)
      have hU_pos : 0 < U (t, x, y) := by
        dsimp [U]
        have := hH_lb t ht x y
        have : 0 ≤ ε * t := mul_nonneg hε_pos.le ht.1
        linarith
      linarith
  have ht₀_pos : 0 < t₀ := by
    by_contra hle; push Not at hle
    have ht0 : t₀ = 0 := le_antisymm hle hp₀_mem.1.1
    rw [ht0] at hU_neg; dsimp [U] at hU_neg
    have := hH0 x₀ y₀
    have : 0 ≤ δ * (x₀ ^ 2 + y₀ ^ 2) := by positivity
    linarith
  have hH_neg : FFlow (fun x => Phi (h₃ x)) t₀ (lam * x₀ + (1 - lam) * y₀) -
      lam * FFlow (fun x => Phi (h₁ x)) t₀ x₀ - (1 - lam) * FFlow (fun x => Phi (h₂ x)) t₀ y₀ < 0 := by
    dsimp [U] at hU_neg
    have : 0 ≤ ε * t₀ := mul_nonneg hε_pos.le ht₀_pos.le
    have : 0 ≤ δ * (x₀ ^ 2 + y₀ ^ 2) := by positivity
    linarith
  have hδxy_lt : δ * (x₀ ^ 2 + y₀ ^ 2) < B := by
    dsimp [U] at hU_neg
    have := hH_lb t₀ hp₀_mem.1 x₀ y₀
    have : 0 ≤ ε * t₀ := mul_nonneg hε_pos.le ht₀_pos.le
    linarith
  obtain ⟨hdx, hdy, hd2s, hdt⟩ :=
    ehrhard_opt_conds hfc₁ hfc₂ hfc₃ hf01₁ hf01₂ hf01₃ ht₀_pos hp₀_mem.1.2 hglobal
  have hF3'_nonpos : FFlow_x (fun x => Phi (h₃ x)) t₀ (lam * x₀ + (1 - lam) * y₀) ≤ 0 := by
    have hanti_F3 : Antitone (FFlow (fun x => Phi (h₃ x)) t₀) := by
      intro u₁ u₂ hu
      have h1 := heat_antitone hfc₃ hfb₃ (fun a b hab => Phi_strictMono.monotone (hanti₃ hab)) ht₀_pos.le hu
      rcases eq_or_lt_of_le h1 with heq | hlt
      · unfold FFlow; rw [heq]
      · exact (PhiInv_strictMonoOn (heat_mem_Ioo hfc₃ hf01₃ ht₀_pos.le u₂)
          (heat_mem_Ioo hfc₃ hf01₃ ht₀_pos.le u₁) hlt).le
    have hslope := (hasDerivAt_FFlow_x hfc₃ hf01₃ ht₀_pos (lam * x₀ + (1 - lam) * y₀)).tendsto_slope_zero_right
    refine le_of_tendsto hslope (eventually_nhdsWithin_of_forall fun s hs => ?_)
    rw [smul_eq_mul]
    have hle : FFlow (fun x => Phi (h₃ x)) t₀ (lam * x₀ + (1 - lam) * y₀ + s) ≤
        FFlow (fun x => Phi (h₃ x)) t₀ (lam * x₀ + (1 - lam) * y₀) :=
      hanti_F3 (by linarith [mem_Ioi.mp hs])
    exact mul_nonpos_of_nonneg_of_nonpos (inv_pos.mpr (mem_Ioi.mp hs)).le (sub_nonpos.mpr hle)
  have hF1_ub : FFlow (fun x => Phi (h₁ x)) t₀ x₀ ≤ M₁ :=
    (FFlow_ub_of_le hS hlip₁ hub₁ ht₀_pos.le x₀).trans ((le_abs_self M₀).trans hM₀_le_M₁)
  have hF2_ub : FFlow (fun x => Phi (h₂ x)) t₀ y₀ ≤ M₁ :=
    (FFlow_ub_of_le hS hlip₂ hub₂ ht₀_pos.le y₀).trans ((le_abs_self M₀).trans hM₀_le_M₁)
  have hF1_lb : x₀ < 0 → -M₁ ≤ FFlow (fun x => Phi (h₁ x)) t₀ x₀ := fun hx => by
    have ha := FFlow_lb_nonpos_of_ge hS hlip₁ hlb₁ ht₀_pos.le hx.le
    have hb : |PhiInv ((1 / 2 : ℝ) * Phi (-M₀))| ≤ M₁ :=
      hM₁_def ▸ le_trans (by linarith) (le_max_right _ _)
    linarith [neg_abs_le (PhiInv ((1 / 2 : ℝ) * Phi (-M₀)))]
  have hF2_lb : y₀ < 0 → -M₁ ≤ FFlow (fun x => Phi (h₂ x)) t₀ y₀ := fun hy => by
    have ha := FFlow_lb_nonpos_of_ge hS hlip₂ hlb₂ ht₀_pos.le hy.le
    have hb : |PhiInv ((1 / 2 : ℝ) * Phi (-M₀))| ≤ M₁ :=
      hM₁_def ▸ le_trans (by linarith) (le_max_right _ _)
    linarith [neg_abs_le (PhiInv ((1 / 2 : ℝ) * Phi (-M₀)))]
  have hF1_lin : |FFlow (fun x => Phi (h₁ x)) t₀ x₀| ≤ M₁ + S * |x₀| :=
    hM₁_def ▸ FFlow_abs_le_linear hS hlip₁ hub₁ hlb₁ ht₀_pos.le x₀
  have hF2_lin : |FFlow (fun x => Phi (h₂ x)) t₀ y₀| ≤ M₁ + S * |y₀| :=
    hM₁_def ▸ FFlow_abs_le_linear hS hlip₂ hub₂ hlb₂ ht₀_pos.le y₀
  have hF3'_abs : |FFlow_x (fun x => Phi (h₃ x)) t₀ (lam * x₀ + (1 - lam) * y₀)| ≤ S :=
    abs_FFlow_x_le hS hlip₃ ht₀_pos (lam * x₀ + (1 - lam) * y₀)
  exact ehrhard_contra_of_opt hS hM₁_pos hB_pos hlam0 hlam1 hδ_pos hδ_err hH_neg hδxy_lt
    hF1_ub hF2_ub hF1_lb hF2_lb hF1_lin hF2_lin hF3'_nonpos hF3'_abs hdx hdy hd2s hdt

end HeatSemigroup

section LognormalInduction

/-- Properties of a convex, positive, strictly increasing Gaussian quantile `Q`. -/
structure GoodQuantile (Q : ℝ → ℝ) : Prop where
  strictMono : StrictMono Q
  continuous : Continuous Q
  convex : ConvexOn ℝ univ Q
  pos : ∀ x, 0 < Q x
  tendsto_bot : Tendsto Q atBot (𝓝 0)
  tendsto_top : Tendsto Q atTop atTop

lemma GoodQuantile.exists_eq {Q : ℝ → ℝ} (hQ : GoodQuantile Q) {t : ℝ} (ht : 0 < t) :
    ∃ a : ℝ, Q a = t := by
  obtain ⟨u, hu⟩ := (hQ.tendsto_bot.eventually (gt_mem_nhds ht)).exists
  obtain ⟨v, hv⟩ := (hQ.tendsto_top.eventually (eventually_gt_atTop t)).exists
  have huv : u ≤ v := le_of_lt (hQ.strictMono.lt_iff_lt.mp (hu.trans hv))
  obtain ⟨a, _, ha⟩ := intermediate_value_Icc huv hQ.continuous.continuousOn ⟨hu.le, hv.le⟩
  exact ⟨a, ha⟩

/-- Integrand for the CDF of `Q(G₁) + exp(σ G₂)`. -/
noncomputable def convIntegrand (Q : ℝ → ℝ) (σ t x : ℝ) : ℝ :=
  if Q x < t then Phi (Real.log (t - Q x) / σ) else 0

/-- CDF of `Q(G₁) + exp(σ G₂)` at `t`. -/
noncomputable def convCDF (Q : ℝ → ℝ) (σ t : ℝ) : ℝ :=
  ∫ x, convIntegrand Q σ t x * phi x

lemma convIntegrand_nonneg (Q : ℝ → ℝ) (σ t x : ℝ) : 0 ≤ convIntegrand Q σ t x := by
  unfold convIntegrand; split_ifs
  · exact Phi_nonneg _
  · exact le_rfl

lemma convIntegrand_le_one (Q : ℝ → ℝ) (σ t x : ℝ) : convIntegrand Q σ t x ≤ 1 := by
  unfold convIntegrand; split_ifs
  · exact Phi_le_one _
  · exact zero_le_one

lemma convIntegrand_measurable {Q : ℝ → ℝ} (hQ : GoodQuantile Q) (σ t : ℝ) :
    Measurable (convIntegrand Q σ t) := by
  unfold convIntegrand
  refine Measurable.ite (measurableSet_lt hQ.continuous.measurable measurable_const) ?_ measurable_const
  exact continuous_Phi.measurable.comp ((Real.measurable_log.comp (measurable_const.sub hQ.continuous.measurable)).div_const σ)

lemma convIntegrand_integrable {Q : ℝ → ℝ} (hQ : GoodQuantile Q) (σ t : ℝ) :
    Integrable (fun x => convIntegrand Q σ t x * phi x) := by
  refine integrable_phi.mono'
    ((convIntegrand_measurable hQ σ t).mul continuous_phi.measurable).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (convIntegrand_nonneg Q σ t x),
    abs_of_nonneg (phi_nonneg x)]
  nlinarith [convIntegrand_le_one Q σ t x, phi_nonneg x]

lemma convCDF_mem_Ioo {Q : ℝ → ℝ} (hQ : GoodQuantile Q) {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) :
    convCDF Q σ t ∈ Ioo 0 1 := by
  unfold convCDF
  have hint := convIntegrand_integrable hQ σ t
  constructor
  · obtain ⟨x₀, hx₀⟩ := (hQ.tendsto_bot.eventually (gt_mem_nhds (show 0 < t / 2 by positivity))).exists
    have h1 : (∫ x in Iic x₀, Phi (Real.log (t / 2) / σ) * phi x) ≤
        ∫ x in Iic x₀, convIntegrand Q σ t x * phi x := by
      refine setIntegral_mono_on (integrable_phi.const_mul _).integrableOn
        hint.integrableOn measurableSet_Iic fun x hx => ?_
      have hQx : Q x < t / 2 := lt_of_le_of_lt (hQ.strictMono.monotone hx) hx₀
      have hQxt : Q x < t := by linarith
      unfold convIntegrand
      rw [if_pos hQxt]
      have hlog : Real.log (t / 2) / σ ≤ Real.log (t - Q x) / σ :=
        div_le_div_of_nonneg_right (Real.log_le_log (by positivity) (by linarith)) hσ.le
      exact mul_le_mul_of_nonneg_right (Phi_strictMono.monotone hlog) (phi_nonneg x)
    have h2 : (∫ x in Iic x₀, convIntegrand Q σ t x * phi x) ≤
        ∫ x, convIntegrand Q σ t x * phi x :=
      setIntegral_le_integral hint (ae_of_all _ fun x =>
        mul_nonneg (convIntegrand_nonneg Q σ t x) (phi_nonneg x))
    have h3 : (∫ x in Iic x₀, Phi (Real.log (t / 2) / σ) * phi x) =
        Phi (Real.log (t / 2) / σ) * Phi x₀ := by
      rw [integral_const_mul]; rfl
    have hpos : 0 < Phi (Real.log (t / 2) / σ) * Phi x₀ := mul_pos (Phi_pos _) (Phi_pos _)
    linarith
  · obtain ⟨x₁, hx₁⟩ := (hQ.tendsto_top.eventually (eventually_ge_atTop t)).exists
    have hint_diff : Integrable (fun x => (1 - convIntegrand Q σ t x) * phi x) := by
      have : (fun x => (1 - convIntegrand Q σ t x) * phi x) =
          fun x => phi x - convIntegrand Q σ t x * phi x := by ext x; ring
      rw [this]; exact integrable_phi.sub hint
    have hsub : (∫ x in Ici x₁, (1 - convIntegrand Q σ t x) * phi x) ≤
        ∫ x, (1 - convIntegrand Q σ t x) * phi x :=
      setIntegral_le_integral hint_diff (ae_of_all _ fun x =>
        mul_nonneg (sub_nonneg.mpr (convIntegrand_le_one Q σ t x)) (phi_nonneg x))
    have heq_Ici : (∫ x in Ici x₁, (1 - convIntegrand Q σ t x) * phi x) = ∫ x in Ici x₁, phi x := by
      refine setIntegral_congr_fun measurableSet_Ici fun x hx => ?_
      have hQx : t ≤ Q x := le_trans hx₁ (hQ.strictMono.monotone hx)
      simp [convIntegrand, not_lt.mpr hQx]
    have hIci_pos : 0 < ∫ x in Ici x₁, phi x := by
      have h1 : (∫ x in Icc x₁ (x₁ + 1), phi x) ≤ ∫ x in Ici x₁, phi x :=
        setIntegral_mono_set integrable_phi.integrableOn (ae_of_all _ phi_nonneg)
          (Eventually.of_forall fun x hx => hx.1)
      obtain ⟨z₀, _, hmin⟩ := isCompact_Icc.exists_isMinOn
        (s := Icc x₁ (x₁ + 1)) ⟨x₁, le_rfl, by linarith⟩ continuous_phi.continuousOn
      have h2 : (∫ _ in Icc x₁ (x₁ + 1), phi z₀) ≤ ∫ x in Icc x₁ (x₁ + 1), phi x :=
        setIntegral_mono_on (integrableOn_const (by simp)) integrable_phi.integrableOn
          measurableSet_Icc fun z hz => hmin hz
      have h3 : (∫ _ in Icc x₁ (x₁ + 1), phi z₀) = phi z₀ := by
        rw [setIntegral_const, Measure.real_def, Real.volume_Icc]; norm_num
      linarith [phi_pos z₀]
    have h4 : (∫ x, (1 - convIntegrand Q σ t x) * phi x) = 1 - ∫ x, convIntegrand Q σ t x * phi x := by
      have : (fun x => (1 - convIntegrand Q σ t x) * phi x) =
          fun x => phi x - convIntegrand Q σ t x * phi x := by ext x; ring
      rw [this, integral_sub integrable_phi hint, integral_phi_eq_one]
    linarith

lemma convCDF_strictMonoOn {Q : ℝ → ℝ} (hQ : GoodQuantile Q) {σ : ℝ} (hσ : 0 < σ) :
    StrictMonoOn (convCDF Q σ) (Ioi 0) := by
  intro t₁ ht₁ t₂ ht₂ hlt
  have ht₁_pos : 0 < t₁ := ht₁
  have h1 := convIntegrand_integrable hQ σ t₁
  have h2 := convIntegrand_integrable hQ σ t₂
  have hpt_le : ∀ x, convIntegrand Q σ t₁ x ≤ convIntegrand Q σ t₂ x := fun x => by
    unfold convIntegrand
    by_cases h : Q x < t₁
    · rw [if_pos h, if_pos (h.trans hlt)]
      exact Phi_strictMono.monotone (div_le_div_of_nonneg_right
        (Real.log_le_log (by linarith) (by linarith)) hσ.le)
    · rw [if_neg h]; split_ifs
      · exact Phi_nonneg _
      · exact le_rfl
  obtain ⟨x₀, hx₀⟩ := (hQ.tendsto_bot.eventually (gt_mem_nhds (show 0 < t₁ / 2 by positivity))).exists
  let diff : ℝ → ℝ := fun x => (convIntegrand Q σ t₂ x - convIntegrand Q σ t₁ x) * phi x
  have hdiff_int : Integrable diff := by
    have : diff = fun x => convIntegrand Q σ t₂ x * phi x - convIntegrand Q σ t₁ x * phi x := by
      ext x; dsimp [diff]; ring
    rw [this]; exact h2.sub h1
  have hdiff_cont : ContinuousOn diff (Icc (x₀ - 1) x₀) := by
    have heq : EqOn diff (fun x => (Phi (Real.log (t₂ - Q x) / σ) - Phi (Real.log (t₁ - Q x) / σ)) * phi x)
        (Icc (x₀ - 1) x₀) := fun x hx => by
      have hQx : Q x < t₁ := lt_of_le_of_lt (hQ.strictMono.monotone hx.2) (by linarith)
      simp [diff, convIntegrand, hQx, hQx.trans hlt]
    refine ContinuousOn.congr ?_ heq
    have hc1 : ContinuousOn (fun x => Phi (Real.log (t₁ - Q x) / σ)) (Icc (x₀ - 1) x₀) := by
      intro x hx
      have hQx : Q x < t₁ := lt_of_le_of_lt (hQ.strictMono.monotone hx.2) (by linarith)
      have hsub : ContinuousAt (fun u => t₁ - Q u) x := continuousAt_const.sub hQ.continuous.continuousAt
      exact (continuous_Phi.continuousAt.comp ((Real.continuousAt_log (by linarith)).comp hsub |>.div_const σ)).continuousWithinAt
    have hc2 : ContinuousOn (fun x => Phi (Real.log (t₂ - Q x) / σ)) (Icc (x₀ - 1) x₀) := by
      intro x hx
      have hQx : Q x < t₂ := (lt_of_le_of_lt (hQ.strictMono.monotone hx.2) (by linarith)).trans hlt
      have hsub : ContinuousAt (fun u => t₂ - Q u) x := continuousAt_const.sub hQ.continuous.continuousAt
      exact (continuous_Phi.continuousAt.comp ((Real.continuousAt_log (by linarith)).comp hsub |>.div_const σ)).continuousWithinAt
    exact (hc2.sub hc1).mul continuous_phi.continuousOn
  obtain ⟨z₀, hz₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (s := Icc (x₀ - 1) x₀) ⟨x₀, by linarith, le_rfl⟩ hdiff_cont
  have hz₀_pos : 0 < diff z₀ := by
    have hQz : Q z₀ < t₁ := lt_of_le_of_lt (hQ.strictMono.monotone hz₀.2) (by linarith)
    have hlog : Real.log (t₁ - Q z₀) / σ < Real.log (t₂ - Q z₀) / σ :=
      div_lt_div_of_pos_right (Real.log_lt_log (by linarith) (by linarith)) hσ
    have hPhi : Phi (Real.log (t₁ - Q z₀) / σ) < Phi (Real.log (t₂ - Q z₀) / σ) := Phi_strictMono hlog
    simp only [diff, convIntegrand, if_pos hQz, if_pos (hQz.trans hlt)]
    exact mul_pos (sub_pos.mpr hPhi) (phi_pos z₀)
  have hsub : (∫ x in Icc (x₀ - 1) x₀, diff x) ≤ ∫ x, diff x :=
    setIntegral_le_integral hdiff_int (ae_of_all _ fun x =>
      mul_nonneg (sub_nonneg.mpr (hpt_le x)) (phi_nonneg x))
  have hmono : (∫ _ in Icc (x₀ - 1) x₀, diff z₀) ≤ ∫ x in Icc (x₀ - 1) x₀, diff x :=
    setIntegral_mono_on (integrableOn_const (by simp)) hdiff_int.integrableOn
      measurableSet_Icc fun x hx => hmin hx
  have hconst : (∫ _ in Icc (x₀ - 1) x₀, diff z₀) = diff z₀ := by
    rw [setIntegral_const, Measure.real_def, Real.volume_Icc]; norm_num
  have hdiff_eq : (∫ x, diff x) = convCDF Q σ t₂ - convCDF Q σ t₁ := by
    have : diff = fun x => convIntegrand Q σ t₂ x * phi x - convIntegrand Q σ t₁ x * phi x := by
      ext x; dsimp [diff]; ring
    rw [this, integral_sub h2 h1]; rfl
  linarith

lemma convCDF_continuousOn {Q : ℝ → ℝ} (hQ : GoodQuantile Q) {σ : ℝ} (hσ : 0 < σ) :
    ContinuousOn (convCDF Q σ) (Ioi 0) := by
  intro t ht
  rw [ContinuousWithinAt]
  unfold convCDF
  refine tendsto_integral_filter_of_dominated_convergence phi ?_ ?_ integrable_phi ?_
  · exact Eventually.of_forall fun s =>
      ((convIntegrand_measurable hQ σ s).mul continuous_phi.measurable).aestronglyMeasurable
  · exact Eventually.of_forall fun s => ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (convIntegrand_nonneg Q σ s x),
        abs_of_nonneg (phi_nonneg x)]
      nlinarith [convIntegrand_le_one Q σ s x, phi_nonneg x]
  · refine ae_of_all _ fun x => ?_
    have hnhds : Tendsto (fun s => convIntegrand Q σ s x) (𝓝 t) (𝓝 (convIntegrand Q σ t x)) := by
      rcases lt_trichotomy (Q x) t with hlt | heq | hgt
      · have hsub : ContinuousAt (fun s : ℝ => s - Q x) t := continuousAt_id.sub continuousAt_const
        have hcont : ContinuousAt (fun s => Phi (Real.log (s - Q x) / σ)) t :=
          continuous_Phi.continuousAt.comp
            ((ContinuousAt.comp (g := Real.log) (f := fun s => s - Q x)
              (Real.continuousAt_log (show t - Q x ≠ 0 by linarith)) hsub).div_const σ)
        refine (hcont.tendsto.congr' ?_).trans (by simp [convIntegrand, hlt])
        filter_upwards [lt_mem_nhds hlt] with s hs
        simp [convIntegrand, hs]
      · simp only [convIntegrand, heq, lt_self_iff_false, ↓reduceIte]
        rw [Metric.tendsto_nhds]
        intro ε hε
        obtain ⟨M, hM⟩ := (Phi_tendsto_zero.eventually (gt_mem_nhds hε)).exists
        have hM_all : ∀ u ≤ M, Phi u < ε := fun u hu => lt_of_le_of_lt (Phi_strictMono.monotone hu) hM
        rw [Metric.eventually_nhds_iff]
        refine ⟨exp (σ * M), exp_pos _, fun s hs => ?_⟩
        rw [Real.dist_eq, sub_zero]
        by_cases hlt : t < s
        · rw [if_pos hlt, abs_of_pos (Phi_pos _)]
          have hs_sub : s - t < exp (σ * M) := by
            rw [Real.dist_eq] at hs; linarith [(abs_lt.mp hs).2]
          have hlog : Real.log (s - t) / σ ≤ M := by
            rw [div_le_iff₀ hσ]
            have := Real.log_lt_log (by linarith) hs_sub
            rw [Real.log_exp] at this
            linarith
          exact hM_all _ hlog
        · rw [if_neg hlt, abs_zero]; exact hε
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [gt_mem_nhds hgt] with s hs
        simp [convIntegrand, not_lt.mpr hs.le, not_lt.mpr hgt.le]
    exact (hnhds.mul_const (phi x)).mono_left nhdsWithin_le_nhds

lemma convCDF_tendsto_zero {Q : ℝ → ℝ} (hQ : GoodQuantile Q) {σ : ℝ} :
    Tendsto (convCDF Q σ) (𝓝[>] 0) (𝓝 0) := by
  have h0 : (0 : ℝ) = ∫ _ : ℝ, (0 : ℝ) := (integral_zero ℝ ℝ).symm
  unfold convCDF
  conv_rhs => rw [h0]
  refine tendsto_integral_filter_of_dominated_convergence phi ?_ ?_ integrable_phi ?_
  · exact Eventually.of_forall fun s =>
      ((convIntegrand_measurable hQ σ s).mul continuous_phi.measurable).aestronglyMeasurable
  · exact Eventually.of_forall fun s => ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (convIntegrand_nonneg Q σ s x),
        abs_of_nonneg (phi_nonneg x)]
      nlinarith [convIntegrand_le_one Q σ s x, phi_nonneg x]
  · refine ae_of_all _ fun x => tendsto_const_nhds.congr' ?_
    filter_upwards [nhdsWithin_le_nhds (gt_mem_nhds (hQ.pos x))] with s hs
    simp [convIntegrand, not_lt.mpr hs.le]

lemma convCDF_tendsto_one {Q : ℝ → ℝ} (hQ : GoodQuantile Q) {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (convCDF Q σ) atTop (𝓝 1) := by
  unfold convCDF
  rw [← integral_phi_eq_one]
  refine tendsto_integral_filter_of_dominated_convergence phi ?_ ?_ integrable_phi ?_
  · exact Eventually.of_forall fun s =>
      ((convIntegrand_measurable hQ σ s).mul continuous_phi.measurable).aestronglyMeasurable
  · exact Eventually.of_forall fun s => ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (convIntegrand_nonneg Q σ s x),
        abs_of_nonneg (phi_nonneg x)]
      nlinarith [convIntegrand_le_one Q σ s x, phi_nonneg x]
  · refine ae_of_all _ fun x => ?_
    have h1 : Tendsto (fun s : ℝ => Real.log (s - Q x) / σ) atTop atTop :=
      (Real.tendsto_log_atTop.comp (tendsto_id.atTop_add tendsto_const_nhds)).atTop_div_const hσ
    have h2 : Tendsto (fun s : ℝ => Phi (Real.log (s - Q x) / σ) * phi x) atTop (𝓝 (1 * phi x)) :=
      (Phi_tendsto_one.comp h1).mul_const (phi x)
    rw [one_mul] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (Q x)] with s hs
    simp [convIntegrand, hs]

/-- `S`-Lipschitz sup-convolution regularization of `u ↦ log (t - Q u) / σ` on `{u | Q u < t}`. -/
noncomputable def regH (Q : ℝ → ℝ) (σ t S x : ℝ) : ℝ :=
  sSup ((fun u => Real.log (t - Q u) / σ - S * |x - u|) '' {u | Q u < t})

lemma regH_nonempty {Q : ℝ → ℝ} (hQ : GoodQuantile Q) {t : ℝ} (ht : 0 < t) (σ S x : ℝ) :
    ((fun u => Real.log (t - Q u) / σ - S * |x - u|) '' {u | Q u < t}).Nonempty := by
  obtain ⟨a, ha⟩ := hQ.exists_eq ht
  exact ⟨_, a - 1, by rw [← ha]; exact hQ.strictMono (by linarith), rfl⟩

lemma regH_bddAbove {Q : ℝ → ℝ} (hQ : GoodQuantile Q) {σ t S : ℝ}
    (hσ : 0 < σ) (hS : 0 ≤ S) (x : ℝ) :
    BddAbove ((fun u => Real.log (t - Q u) / σ - S * |x - u|) '' {u | Q u < t}) := by
  refine ⟨Real.log t / σ, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  have hu' : Q u < t := hu
  have hQpos := hQ.pos u
  have hlog : Real.log (t - Q u) / σ ≤ Real.log t / σ :=
    div_le_div_of_nonneg_right (Real.log_le_log (by linarith) (by linarith)) hσ.le
  have : 0 ≤ S * |x - u| := mul_nonneg hS (abs_nonneg _)
  linarith

lemma regH_le_log {Q : ℝ → ℝ} (hQ : GoodQuantile Q) {σ t S : ℝ}
    (hσ : 0 < σ) (ht : 0 < t) (hS : 0 ≤ S) (x : ℝ) :
    regH Q σ t S x ≤ Real.log t / σ := by
  refine csSup_le (regH_nonempty hQ ht σ S x) ?_
  rintro _ ⟨u, hu, rfl⟩
  have hu' : Q u < t := hu
  have hQpos := hQ.pos u
  have hlog : Real.log (t - Q u) / σ ≤ Real.log t / σ :=
    div_le_div_of_nonneg_right (Real.log_le_log (by linarith) (by linarith)) hσ.le
  have : 0 ≤ S * |x - u| := mul_nonneg hS (abs_nonneg _)
  linarith

lemma regH_ge_pt {Q : ℝ → ℝ} (hQ : GoodQuantile Q) {σ t S x u : ℝ}
    (hσ : 0 < σ) (hS : 0 ≤ S) (hu : Q u < t) :
    Real.log (t - Q u) / σ - S * |x - u| ≤ regH Q σ t S x :=
  le_csSup (regH_bddAbove hQ hσ hS x) ⟨u, hu, rfl⟩

lemma regH_lip {Q : ℝ → ℝ} (hQ : GoodQuantile Q) {σ t S : ℝ}
    (hσ : 0 < σ) (ht : 0 < t) (hS : 0 ≤ S) (x y : ℝ) :
    |regH Q σ t S x - regH Q σ t S y| ≤ S * |x - y| := by
  have hle : ∀ a b, regH Q σ t S a - regH Q σ t S b ≤ S * |a - b| := fun a b => by
    suffices regH Q σ t S a ≤ regH Q σ t S b + S * |a - b| by linarith
    refine csSup_le (regH_nonempty hQ ht σ S a) ?_
    rintro _ ⟨u, hu, rfl⟩
    have h1 := regH_ge_pt hQ hσ hS (x := b) hu
    have htri : |b - u| ≤ |a - u| + |a - b| := by
      have : b - u = (a - u) - (a - b) := by ring
      rw [this]; exact abs_sub _ _
    nlinarith
  rw [abs_le]
  exact ⟨by have := hle y x; rw [abs_sub_comm] at this; linarith, hle x y⟩

lemma regH_antitone {Q : ℝ → ℝ} (hQ : GoodQuantile Q) {σ t S : ℝ}
    (hσ : 0 < σ) (ht : 0 < t) (hS : 0 ≤ S) : Antitone (regH Q σ t S) := by
  intro x₁ x₂ hx
  refine csSup_le (regH_nonempty hQ ht σ S x₂) ?_
  rintro _ ⟨u, hu, rfl⟩
  by_cases hux : u ≤ x₁
  · have h1 := regH_ge_pt hQ hσ hS (x := x₁) hu
    have habs : |x₁ - u| ≤ |x₂ - u| := by
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
    nlinarith
  · push Not at hux
    have hu' : Q u < t := hu
    have hx₁ : Q x₁ < t := (hQ.strictMono hux).trans hu'
    have h1 := regH_ge_pt hQ hσ hS (x := x₁) hx₁
    rw [sub_self, abs_zero, mul_zero, sub_zero] at h1
    have hlog : Real.log (t - Q u) / σ ≤ Real.log (t - Q x₁) / σ :=
      div_le_div_of_nonneg_right
        (Real.log_le_log (by linarith) (by linarith [hQ.strictMono hux])) hσ.le
    have : 0 ≤ S * |x₂ - u| := mul_nonneg hS (abs_nonneg _)
    linarith

lemma regH_convex_comb {Q : ℝ → ℝ} (hQ : GoodQuantile Q) {σ t₁ t₂ S lam : ℝ}
    (hσ : 0 < σ) (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) (hS : 0 ≤ S)
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (x y : ℝ) :
    lam * regH Q σ t₁ S x + (1 - lam) * regH Q σ t₂ S y ≤
      regH Q σ (lam * t₁ + (1 - lam) * t₂) S (lam * x + (1 - lam) * y) := by
  set t₃ := lam * t₁ + (1 - lam) * t₂
  set z := lam * x + (1 - lam) * y
  have h1l : 0 < 1 - lam := by linarith
  have hpair : ∀ u v, Q u < t₁ → Q v < t₂ →
      lam * (Real.log (t₁ - Q u) / σ - S * |x - u|) +
        (1 - lam) * (Real.log (t₂ - Q v) / σ - S * |y - v|) ≤ regH Q σ t₃ S z := by
    intro u v hu hv
    set w := lam * u + (1 - lam) * v
    have hQw : Q w ≤ lam * Q u + (1 - lam) * Q v :=
      hQ.convex.2 (mem_univ u) (mem_univ v) hlam0.le h1l.le (by ring)
    have hwt : Q w < t₃ := by dsimp [t₃]; nlinarith
    have hlog_conc : lam * Real.log (t₁ - Q u) + (1 - lam) * Real.log (t₂ - Q v) ≤
        Real.log (lam * (t₁ - Q u) + (1 - lam) * (t₂ - Q v)) := by
      have h := strictConcaveOn_log_Ioi.concaveOn.2 (x := t₁ - Q u) (y := t₂ - Q v)
        (mem_Ioi.mpr (by linarith)) (mem_Ioi.mpr (by linarith))
        hlam0.le h1l.le (by ring)
      simpa [smul_eq_mul] using h
    have hlog_mono : Real.log (lam * (t₁ - Q u) + (1 - lam) * (t₂ - Q v)) ≤ Real.log (t₃ - Q w) :=
      Real.log_le_log (by nlinarith) (by dsimp [t₃]; linarith)
    have hlog : lam * (Real.log (t₁ - Q u) / σ) + (1 - lam) * (Real.log (t₂ - Q v) / σ) ≤
        Real.log (t₃ - Q w) / σ := by
      have : lam * (Real.log (t₁ - Q u) / σ) + (1 - lam) * (Real.log (t₂ - Q v) / σ) =
          (lam * Real.log (t₁ - Q u) + (1 - lam) * Real.log (t₂ - Q v)) / σ := by ring
      rw [this]
      exact div_le_div_of_nonneg_right (hlog_conc.trans hlog_mono) hσ.le
    have htri : |z - w| ≤ lam * |x - u| + (1 - lam) * |y - v| := by
      have : z - w = lam * (x - u) + (1 - lam) * (y - v) := by dsimp [z, w]; ring
      rw [this]
      calc |lam * (x - u) + (1 - lam) * (y - v)|
          ≤ |lam * (x - u)| + |(1 - lam) * (y - v)| := abs_add_le _ _
        _ = lam * |x - u| + (1 - lam) * |y - v| := by
            rw [abs_mul, abs_mul, abs_of_pos hlam0, abs_of_pos h1l]
    have hge := regH_ge_pt hQ hσ hS (x := z) hwt
    nlinarith
  have hstep1 : ∀ u, Q u < t₁ →
      lam * (Real.log (t₁ - Q u) / σ - S * |x - u|) + (1 - lam) * regH Q σ t₂ S y ≤
        regH Q σ t₃ S z := fun u hu => by
    have hsub : regH Q σ t₂ S y ≤ (regH Q σ t₃ S z - lam * (Real.log (t₁ - Q u) / σ - S * |x - u|)) / (1 - lam) := by
      refine csSup_le (regH_nonempty hQ ht₂ σ S y) ?_
      rintro _ ⟨v, hv, rfl⟩
      rw [le_div_iff₀ h1l]
      linarith [hpair u v hu hv]
    have := (le_div_iff₀ h1l).mp hsub
    linarith
  have hstep2 : regH Q σ t₁ S x ≤ (regH Q σ t₃ S z - (1 - lam) * regH Q σ t₂ S y) / lam := by
    refine csSup_le (regH_nonempty hQ ht₁ σ S x) ?_
    rintro _ ⟨u, hu, rfl⟩
    rw [le_div_iff₀ hlam0]
    linarith [hstep1 u hu]
  linarith [(le_div_iff₀ hlam0).mp hstep2]

lemma regH_tendsto_convIntegrand {Q : ℝ → ℝ} (hQ : GoodQuantile Q) {σ t : ℝ}
    (hσ : 0 < σ) (ht : 0 < t) :
    Tendsto (fun S : ℝ => ∫ x, Phi (regH Q σ t S x) * phi x) atTop (𝓝 (convCDF Q σ t)) := by
  obtain ⟨a, ha⟩ := hQ.exists_eq ht
  unfold convCDF
  refine tendsto_integral_filter_of_dominated_convergence phi ?_ ?_ integrable_phi ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with S hS
    have hc : Continuous (fun x => Phi (regH Q σ t S x)) :=
      continuous_Phi.comp (continuous_of_lip hS (regH_lip hQ hσ ht hS))
    exact (hc.mul continuous_phi).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with S _
    refine ae_of_all _ fun x => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Phi_nonneg _), abs_of_nonneg (phi_nonneg x)]
    nlinarith [Phi_le_one (regH Q σ t S x), phi_nonneg x]
  · have hae : ∀ᵐ x ∂volume, x ≠ a := by
      rw [ae_iff]; simp
    filter_upwards [hae] with x hx
    suffices hpt : Tendsto (fun S : ℝ => Phi (regH Q σ t S x)) atTop (𝓝 (convIntegrand Q σ t x)) from
      hpt.mul_const (phi x)
    rcases lt_or_gt_of_ne hx with hlt | hgt
    · have hQx : Q x < t := ha ▸ hQ.strictMono hlt
      simp only [convIntegrand, if_pos hQx]
      refine continuous_Phi.continuousAt.tendsto.comp ?_
      rw [Metric.tendsto_atTop]
      intro ε hε
      have hsub : ContinuousAt (fun u => t - Q u) x := continuousAt_const.sub hQ.continuous.continuousAt
      have hcont : ContinuousAt (fun u => Real.log (t - Q u) / σ) x :=
        (ContinuousAt.comp (g := Real.log) (f := fun u => t - Q u)
          (Real.continuousAt_log (show t - Q x ≠ 0 by linarith)) hsub).div_const σ
      rw [Metric.continuousAt_iff] at hcont
      obtain ⟨δ, hδ, hclose⟩ := hcont (ε / 2) (by positivity)
      set S₀ := max 1 ((Real.log t / σ - Real.log (t - Q x) / σ) / δ + 1)
      refine ⟨S₀, fun S hS => ?_⟩
      have hS_pos : 0 ≤ S := le_trans (le_trans zero_le_one (le_max_left _ _)) hS
      have hlb : Real.log (t - Q x) / σ ≤ regH Q σ t S x := by
        simpa using regH_ge_pt hQ hσ hS_pos (x := x) hQx
      have hub : regH Q σ t S x ≤ Real.log (t - Q x) / σ + ε / 2 := by
        refine csSup_le (regH_nonempty hQ ht σ S x) ?_
        rintro _ ⟨u, hu, rfl⟩
        have hu' : Q u < t := hu
        by_cases hxu : |x - u| < δ
        · have hd : dist u x < δ := by rwa [Real.dist_eq, abs_sub_comm]
          have hc := hclose hd
          rw [Real.dist_eq] at hc
          have : 0 ≤ S * |x - u| := mul_nonneg hS_pos (abs_nonneg _)
          linarith [(abs_lt.mp hc).2]
        · push Not at hxu
          have hlog : Real.log (t - Q u) / σ ≤ Real.log t / σ :=
            div_le_div_of_nonneg_right (Real.log_le_log (by linarith) (by linarith [hQ.pos u])) hσ.le
          have hS_ge : (Real.log t / σ - Real.log (t - Q x) / σ) / δ ≤ S :=
            le_trans (by linarith) (le_trans (le_max_right _ _) hS)
          have hmul : Real.log t / σ - Real.log (t - Q x) / σ ≤ S * δ :=
            (div_le_iff₀ hδ).mp hS_ge
          have hmul2 : S * δ ≤ S * |x - u| := mul_le_mul_of_nonneg_left hxu hS_pos
          linarith
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hlb)]
      linarith
    · have hQx : t < Q x := ha ▸ hQ.strictMono hgt
      simp only [convIntegrand, if_neg (not_lt.mpr hQx.le)]
      refine Phi_tendsto_zero.comp ?_
      rw [tendsto_atBot]
      intro M
      rw [eventually_atTop]
      refine ⟨max 1 ((Real.log t / σ - M) / (x - a)), fun S hS => ?_⟩
      have hS_pos : 0 ≤ S := le_trans (le_trans zero_le_one (le_max_left _ _)) hS
      refine csSup_le (regH_nonempty hQ ht σ S x) ?_
      rintro _ ⟨u, hu, rfl⟩
      have hu' : Q u < t := hu
      have hua : u < a := hQ.strictMono.lt_iff_lt.mp (ha.symm ▸ hu')
      have habs : x - a ≤ |x - u| := by rw [abs_of_pos (by linarith)]; linarith
      have hlog : Real.log (t - Q u) / σ ≤ Real.log t / σ :=
        div_le_div_of_nonneg_right (Real.log_le_log (by linarith) (by linarith [hQ.pos u])) hσ.le
      have hS_ge : (Real.log t / σ - M) / (x - a) ≤ S := le_trans (le_max_right _ _) hS
      have hmul : Real.log t / σ - M ≤ S * (x - a) := (div_le_iff₀ (by linarith)).mp hS_ge
      have hmul2 : S * (x - a) ≤ S * |x - u| := mul_le_mul_of_nonneg_left habs hS_pos
      linarith

/-- Concavity of `t ↦ PhiInv (convCDF Q σ t)` on `(0, ∞)`. -/
theorem convCDF_PhiInv_concave {Q : ℝ → ℝ} (hQ : GoodQuantile Q) {σ : ℝ} (hσ : 0 < σ) :
    ConcaveOn ℝ (Ioi 0) (fun t => PhiInv (convCDF Q σ t)) := by
  refine ⟨convex_Ioi 0, fun t₁ ht₁ t₂ ht₂ a b ha hb hab => ?_⟩
  rcases eq_or_lt_of_le ha with rfl | ha_pos
  · have hb1 : b = 1 := by linarith
    subst hb1; simp
  rcases eq_or_lt_of_le hb with rfl | hb_pos
  · have ha1 : a = 1 := by linarith
    subst ha1; simp
  have ha1 : a < 1 := by linarith
  have hb_eq : b = 1 - a := by linarith
  subst hb_eq
  simp only [smul_eq_mul]
  set t₃ := a * t₁ + (1 - a) * t₂
  have ht₃ : 0 < t₃ := by dsimp [t₃]; nlinarith [mem_Ioi.mp ht₁, mem_Ioi.mp ht₂]
  obtain ⟨a₁, ha₁⟩ := hQ.exists_eq ht₁
  obtain ⟨a₂, ha₂⟩ := hQ.exists_eq ht₂
  obtain ⟨a₃, ha₃⟩ := hQ.exists_eq ht₃
  have hpt : ∀ S : ℝ, 1 ≤ S →
      a * PhiInv (∫ x, Phi (regH Q σ t₁ S x) * phi x) +
        (1 - a) * PhiInv (∫ x, Phi (regH Q σ t₂ S x) * phi x) ≤
      PhiInv (∫ x, Phi (regH Q σ t₃ S x) * phi x) := by
    intro S hS1
    have hS : 0 ≤ S := by linarith
    set u₁ := min 0 (a₁ - 1)
    set u₂ := min 0 (a₂ - 1)
    have hu₁ : Q u₁ < t₁ := ha₁ ▸ hQ.strictMono (lt_of_le_of_lt (min_le_right _ _) (by linarith))
    have hu₂ : Q u₂ < t₂ := ha₂ ▸ hQ.strictMono (lt_of_le_of_lt (min_le_right _ _) (by linarith))
    set M₀ := max (max (Real.log t₁ / σ) (Real.log t₂ / σ))
      (max (-(Real.log (t₁ - Q u₁) / σ - S * |u₁|)) (-(Real.log (t₂ - Q u₂) / σ - S * |u₂|)))
    have hlb : ∀ (t a_t u_t : ℝ), Q a_t = t → u_t = min 0 (a_t - 1) → Q u_t < t →
        -(Real.log (t - Q u_t) / σ - S * |u_t|) ≤ M₀ → ∀ x ≤ 0, -M₀ ≤ regH Q σ t S x := by
      intro t a_t u_t _ hu_def hut hM x hx
      by_cases hxu : x ≤ u_t
      · have hQx : Q x < t := lt_of_le_of_lt (hQ.strictMono.monotone hxu) hut
        have h1 := regH_ge_pt hQ hσ hS (x := x) hQx
        rw [sub_self, abs_zero, mul_zero, sub_zero] at h1
        have hlog : Real.log (t - Q u_t) / σ ≤ Real.log (t - Q x) / σ :=
          div_le_div_of_nonneg_right (Real.log_le_log (by linarith) (by linarith [hQ.strictMono.monotone hxu])) hσ.le
        have : 0 ≤ S * |u_t| := mul_nonneg hS (abs_nonneg _)
        linarith
      · push Not at hxu
        have h1 := regH_ge_pt hQ hσ hS (x := x) hut
        have hu0 : u_t ≤ 0 := hu_def ▸ min_le_left _ _
        have habs : |x - u_t| ≤ |u_t| := by
          rw [abs_of_pos (by linarith), abs_of_nonpos hu0]; linarith
        nlinarith
    have htail_ub : ∀ (t a_t : ℝ), 0 < t → Q a_t = t →
        ∀ x, regH Q σ t S x ≤ -S * x + (Real.log t / σ + S * a_t) := by
      intro t a_t ht hat x
      refine csSup_le (regH_nonempty hQ ht σ S x) ?_
      rintro _ ⟨u, hu, rfl⟩
      have hu' : Q u < t := hu
      have hua : u < a_t := hQ.strictMono.lt_iff_lt.mp (hat.symm ▸ hu')
      have habs : x - a_t ≤ |x - u| := le_trans (by linarith) (le_abs_self (x - u))
      have hlog : Real.log (t - Q u) / σ ≤ Real.log t / σ :=
        div_le_div_of_nonneg_right (Real.log_le_log (by linarith) (by linarith [hQ.pos u])) hσ.le
      nlinarith
    have htail_lb : ∀ x, min (Real.log (t₃ - Q (a₃ - 1)) / σ)
        (-S * x + (Real.log (t₃ - Q (a₃ - 1)) / σ + S * (a₃ - 1))) ≤ regH Q σ t₃ S x := by
      intro x
      have hu₃ : Q (a₃ - 1) < t₃ := ha₃ ▸ hQ.strictMono (by linarith)
      by_cases hx : x ≤ a₃ - 1
      · have hQx : Q x < t₃ := lt_of_le_of_lt (hQ.strictMono.monotone hx) hu₃
        have h1 := regH_ge_pt hQ hσ hS (x := x) hQx
        rw [sub_self, abs_zero, mul_zero, sub_zero] at h1
        have hlog : Real.log (t₃ - Q (a₃ - 1)) / σ ≤ Real.log (t₃ - Q x) / σ :=
          div_le_div_of_nonneg_right (Real.log_le_log (by linarith) (by linarith [hQ.strictMono.monotone hx])) hσ.le
        exact le_trans (min_le_left _ _) (hlog.trans h1)
      · push Not at hx
        have h1 := regH_ge_pt hQ hσ hS (x := x) hu₃
        rw [abs_of_pos (by linarith)] at h1
        refine le_trans (min_le_right _ _) ?_
        linarith
    exact ehrhard_1d_lipschitz hS ha_pos ha1
      (regH_antitone hQ hσ ht₃ hS)
      (regH_lip hQ hσ ht₁ hS) (regH_lip hQ hσ ht₂ hS) (regH_lip hQ hσ ht₃ hS)
      (fun x => (regH_le_log hQ hσ ht₁ hS x).trans (le_trans (le_max_left _ _) (le_max_left _ _)))
      (fun x => (regH_le_log hQ hσ ht₂ hS x).trans (le_trans (le_max_right _ _) (le_max_left _ _)))
      (hlb t₁ a₁ u₁ ha₁ rfl hu₁ (le_trans (le_max_left _ _) (le_max_right _ _)))
      (hlb t₂ a₂ u₂ ha₂ rfl hu₂ (le_trans (le_max_right _ _) (le_max_right _ _)))
      (htail_ub t₁ a₁ ht₁ ha₁) (htail_ub t₂ a₂ ht₂ ha₂) htail_lb
      (regH_convex_comb hQ hσ ht₁ ht₂ hS ha_pos ha1)
  have hL1 := (continuousAt_PhiInv (convCDF_mem_Ioo hQ hσ ht₁)).tendsto.comp
    (regH_tendsto_convIntegrand hQ hσ ht₁)
  have hL2 := (continuousAt_PhiInv (convCDF_mem_Ioo hQ hσ ht₂)).tendsto.comp
    (regH_tendsto_convIntegrand hQ hσ ht₂)
  have hL3 := (continuousAt_PhiInv (convCDF_mem_Ioo hQ hσ ht₃)).tendsto.comp
    (regH_tendsto_convIntegrand hQ hσ ht₃)
  exact le_of_tendsto_of_tendsto ((hL1.const_mul a).add (hL2.const_mul (1 - a))) hL3
    (eventually_ge_atTop (1 : ℝ) |>.mono fun S hS => hpt S hS)

/-- One step of the induction: given a `GoodQuantile Q`, the convolution of `(gaussianReal 0 1).map Q`
with `(gaussianReal 0 1).map (fun z => exp (σ * z))` is again `(gaussianReal 0 1).map Q'`
for a `GoodQuantile Q'`. -/
theorem exists_goodQuantile_conv {Q : ℝ → ℝ} (hQ : GoodQuantile Q) {σ : ℝ} (hσ : 0 < σ) :
    ∃ Q' : ℝ → ℝ, GoodQuantile Q' ∧
      ((gaussianReal 0 1).map Q) ∗ ((gaussianReal 0 1).map (fun z => exp (σ * z))) =
        (gaussianReal 0 1).map Q' := by
  let u : ℝ → ℝ := fun t => PhiInv (convCDF Q σ t)
  have hu_mono : StrictMonoOn u (Ioi 0) := fun t₁ ht₁ t₂ ht₂ hlt =>
    PhiInv_strictMonoOn (convCDF_mem_Ioo hQ hσ ht₁) (convCDF_mem_Ioo hQ hσ ht₂)
      (convCDF_strictMonoOn hQ hσ ht₁ ht₂ hlt)
  have hu_cont : ContinuousOn u (Ioi 0) := fun t ht =>
    (continuousAt_PhiInv (convCDF_mem_Ioo hQ hσ ht)).comp_continuousWithinAt
      (convCDF_continuousOn hQ hσ t ht)
  have hu_conc : ConcaveOn ℝ (Ioi 0) u := convCDF_PhiInv_concave hQ hσ
  have hu_bot : Tendsto u (𝓝[>] 0) atBot := by
    rw [tendsto_atBot]
    intro M
    have hlt := (convCDF_tendsto_zero hQ (σ := σ)).eventually (gt_mem_nhds (Phi_pos M))
    filter_upwards [hlt, self_mem_nhdsWithin] with t ht htpos
    have hmem := convCDF_mem_Ioo hQ hσ htpos
    rw [← PhiInv_Phi M]
    exact (PhiInv_strictMonoOn hmem ⟨Phi_pos M, Phi_lt_one M⟩ ht).le
  have hu_top : Tendsto u atTop atTop := by
    rw [tendsto_atTop]
    intro M
    have hgt := (convCDF_tendsto_one hQ hσ).eventually (lt_mem_nhds (Phi_lt_one M))
    filter_upwards [hgt, eventually_gt_atTop (0 : ℝ)] with t ht htpos
    have hmem := convCDF_mem_Ioo hQ hσ htpos
    rw [← PhiInv_Phi M]
    exact (PhiInv_strictMonoOn ⟨Phi_pos M, Phi_lt_one M⟩ hmem ht).le
  have hu_surj : ∀ x : ℝ, ∃ t : ℝ, 0 < t ∧ u t = x := by
    intro x
    obtain ⟨t₁, ht₁, ht₁_pos⟩ := ((hu_bot.eventually (eventually_lt_atBot x)).and self_mem_nhdsWithin).exists
    obtain ⟨t₂, ht₂, ht₂_pos⟩ := ((hu_top.eventually (eventually_gt_atTop x)).and (eventually_gt_atTop (0 : ℝ))).exists
    have hle : t₁ ≤ t₂ := le_of_not_gt fun h => by
      linarith [hu_mono ht₂_pos ht₁_pos h]
    have hsub : Icc t₁ t₂ ⊆ Ioi 0 := fun s hs => lt_of_lt_of_le (mem_Ioi.mp ht₁_pos) hs.1
    obtain ⟨t, ht, htu⟩ := intermediate_value_Icc hle (hu_cont.mono hsub) ⟨ht₁.le, ht₂.le⟩
    exact ⟨t, hsub ht, htu⟩
  let Q' : ℝ → ℝ := fun x => Classical.choose (hu_surj x)
  have hQ'_pos : ∀ x, 0 < Q' x := fun x => (Classical.choose_spec (hu_surj x)).1
  have hu_Q' : ∀ x, u (Q' x) = x := fun x => (Classical.choose_spec (hu_surj x)).2
  have hQ'_u : ∀ {t}, 0 < t → Q' (u t) = t := fun {t} ht => by
    have h1 := hu_Q' (u t)
    rcases lt_trichotomy (Q' (u t)) t with hlt | heq | hgt
    · linarith [hu_mono (hQ'_pos _) ht hlt]
    · exact heq
    · linarith [hu_mono ht (hQ'_pos _) hgt]
  have hQ'_mono : StrictMono Q' := fun x y hxy => by
    by_contra hle; push Not at hle
    rcases eq_or_lt_of_le hle with heq | hlt
    · have := congrArg u heq; rw [hu_Q', hu_Q'] at this; linarith
    · linarith [hu_mono (hQ'_pos y) (hQ'_pos x) hlt, hu_Q' x, hu_Q' y]
  have hQ'_cont : Continuous Q' := by
    rw [Metric.continuous_iff]
    intro x ε hε
    let t := Q' x
    have ht : 0 < t := hQ'_pos x
    let tL := max (t / 2) (t - ε)
    have htL_pos : 0 < tL := lt_of_lt_of_le (by positivity) (le_max_left _ _)
    have htL_lt : tL < t := max_lt (by linarith) (by linarith)
    let tR := t + ε
    have htR_pos : 0 < tR := by dsimp [tR]; linarith
    have htR_gt : t < tR := by dsimp [tR]; linarith
    have huL : u tL < x := by rw [← hu_Q' x]; exact hu_mono htL_pos ht htL_lt
    have huR : x < u tR := by rw [← hu_Q' x]; exact hu_mono ht htR_pos htR_gt
    set δ := min (x - u tL) (u tR - x)
    refine ⟨δ, lt_min (by linarith) (by linarith), fun y hy => ?_⟩
    rw [Real.dist_eq] at hy ⊢
    have h1 : u tL < y := by linarith [(abs_lt.mp hy).1, min_le_left (x - u tL) (u tR - x)]
    have h2 : y < u tR := by linarith [(abs_lt.mp hy).2, min_le_right (x - u tL) (u tR - x)]
    have hq1 : tL < Q' y := by rw [← hQ'_u htL_pos]; exact hQ'_mono h1
    have hq2 : Q' y < tR := by rw [← hQ'_u htR_pos]; exact hQ'_mono h2
    rw [abs_lt]
    exact ⟨by linarith [le_max_right (t / 2) (t - ε)], by dsimp [tR] at hq2; linarith⟩
  have hQ'_conv : ConvexOn ℝ univ Q' := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [smul_eq_mul]
    have ht_pos : 0 < a * Q' x + b * Q' y := by
      rcases eq_or_lt_of_le ha with rfl | hap
      · have : b = 1 := by linarith
        subst this; simp [hQ'_pos y]
      · nlinarith [hQ'_pos x, hQ'_pos y]
    have hconc := hu_conc.2 (hQ'_pos x) (hQ'_pos y) ha hb hab
    simp only [smul_eq_mul, hu_Q'] at hconc
    have hle := hQ'_mono.monotone hconc
    rwa [hQ'_u ht_pos] at hle
  have hQ'_bot : Tendsto Q' atBot (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    rw [eventually_atBot]
    refine ⟨u (ε / 2), fun x hx => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos (hQ'_pos x)]
    have hle : Q' x ≤ ε / 2 := by
      rw [← hQ'_u (by positivity : 0 < ε / 2)]
      exact hQ'_mono.monotone hx
    linarith
  have hQ'_top : Tendsto Q' atTop atTop := by
    rw [tendsto_atTop]
    intro M
    rw [eventually_atTop]
    set M' := max 1 M
    have hM' : 0 < M' := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    refine ⟨u M', fun x hx => ?_⟩
    have hle : M' ≤ Q' x := by rw [← hQ'_u hM']; exact hQ'_mono.monotone hx
    exact le_trans (le_max_right _ _) hle
  have hGood' : GoodQuantile Q' := ⟨hQ'_mono, hQ'_cont, hQ'_conv, hQ'_pos, hQ'_bot, hQ'_top⟩
  refine ⟨Q', hGood', ?_⟩
  -- Prove measure equality via Measure.ext_of_Iic
  set γ : Measure ℝ := gaussianReal 0 1
  have : IsProbabilityMeasure γ := inferInstance
  have hmeasQ : Measurable Q := hQ.continuous.measurable
  have hmeasE : Measurable (fun z : ℝ => exp (σ * z)) := by fun_prop
  have hmeasQ' : Measurable Q' := hQ'_cont.measurable
  have : IsProbabilityMeasure (γ.map Q) := Measure.isProbabilityMeasure_map hmeasQ.aemeasurable
  have : IsProbabilityMeasure (γ.map (fun z : ℝ => exp (σ * z))) :=
    Measure.isProbabilityMeasure_map hmeasE.aemeasurable
  have : IsProbabilityMeasure (γ.map Q') := Measure.isProbabilityMeasure_map hmeasQ'.aemeasurable
  refine Measure.ext_of_Iic _ _ fun t => ?_
  change (Measure.map (fun p : ℝ × ℝ => p.1 + p.2)
    ((γ.map Q).prod (γ.map (fun z : ℝ => exp (σ * z))))) (Iic t) = (γ.map Q') (Iic t)
  have hprod_map : ((γ.map Q).prod (γ.map (fun z : ℝ => exp (σ * z)))) =
      (γ.prod γ).map (fun p : ℝ × ℝ => (Q p.1, exp (σ * p.2))) :=
    Measure.map_prod_map γ γ hmeasQ hmeasE
  rw [hprod_map, Measure.map_map (by fun_prop) (by fun_prop)]
  rw [Measure.map_apply (by fun_prop) measurableSet_Iic,
    Measure.map_apply hmeasQ' measurableSet_Iic]
  change (γ.prod γ) ((fun p : ℝ × ℝ => Q p.1 + exp (σ * p.2)) ⁻¹' Iic t) = γ (Q' ⁻¹' Iic t)
  by_cases ht : 0 < t
  · have hLHS : (γ.prod γ) ((fun p : ℝ × ℝ => Q p.1 + exp (σ * p.2)) ⁻¹' Iic t) =
        ENNReal.ofReal (convCDF Q σ t) := by
      have hmeas : MeasurableSet ((fun p : ℝ × ℝ => Q p.1 + exp (σ * p.2)) ⁻¹' Iic t) :=
        (by fun_prop : Measurable (fun p : ℝ × ℝ => Q p.1 + exp (σ * p.2))) measurableSet_Iic
      rw [Measure.prod_apply hmeas]
      have hsec : ∀ x : ℝ, γ (Prod.mk x ⁻¹' ((fun p : ℝ × ℝ => Q p.1 + exp (σ * p.2)) ⁻¹' Iic t)) =
          ENNReal.ofReal (convIntegrand Q σ t x) := fun x => by
        by_cases hQx : Q x < t
        · have hset : Prod.mk x ⁻¹' ((fun p : ℝ × ℝ => Q p.1 + exp (σ * p.2)) ⁻¹' Iic t) =
              Iic (Real.log (t - Q x) / σ) := by
            ext y
            simp only [mem_preimage, mem_Iic]
            rw [le_div_iff₀ hσ, mul_comm y σ]
            calc (Q x + exp (σ * y) ≤ t)
                ↔ (exp (σ * y) ≤ t - Q x) := by constructor <;> intro h <;> linarith
              _ ↔ (exp (σ * y) ≤ exp (Real.log (t - Q x))) := by rw [Real.exp_log (by linarith)]
              _ ↔ (σ * y ≤ Real.log (t - Q x)) := Real.exp_le_exp
          rw [hset, convIntegrand, if_pos hQx, Phi_eq_gaussianReal, measureReal_def,
            ENNReal.ofReal_toReal (measure_ne_top _ _)]
        · have hset : Prod.mk x ⁻¹' ((fun p : ℝ × ℝ => Q p.1 + exp (σ * p.2)) ⁻¹' Iic t) = ∅ := by
            ext y; simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
            linarith [Real.exp_pos (σ * y)]
          rw [hset, measure_empty, convIntegrand, if_neg hQx, ENNReal.ofReal_zero]
      simp_rw [hsec]
      rw [← ofReal_integral_eq_lintegral_ofReal]
      · congr 1
        rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
        unfold convCDF
        congr 1; ext x; simp [phi, smul_eq_mul, mul_comm]
      · exact (integrable_const (1 : ℝ)).mono' (convIntegrand_measurable hQ σ t).aestronglyMeasurable
          (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (convIntegrand_nonneg Q σ t x)]; exact convIntegrand_le_one Q σ t x)
      · exact ae_of_all _ (convIntegrand_nonneg Q σ t)
    have hRHS : γ (Q' ⁻¹' Iic t) = ENNReal.ofReal (convCDF Q σ t) := by
      have hset : Q' ⁻¹' Iic t = Iic (u t) := by
        ext x; simp only [mem_preimage, mem_Iic]
        constructor
        · intro hx
          rcases eq_or_lt_of_le hx with rfl | hlt
          · rw [hu_Q']
          · exact (hu_mono (hQ'_pos x) ht hlt).le.trans_eq (by rfl) |> fun h => by rwa [hu_Q'] at h
        · intro hx
          rw [← hQ'_u ht]; exact hQ'_mono.monotone hx
      rw [hset, ← ENNReal.ofReal_toReal (measure_ne_top γ (Iic (u t)))]
      rw [← measureReal_def, ← Phi_eq_gaussianReal]
      dsimp [u]
      rw [Phi_PhiInv (convCDF_mem_Ioo hQ hσ ht)]
    rw [hLHS, hRHS]
  · push Not at ht
    have hL : (fun p : ℝ × ℝ => Q p.1 + exp (σ * p.2)) ⁻¹' Iic t = ∅ := by
      ext ⟨x, y⟩; simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
      linarith [hQ.pos x, Real.exp_pos (σ * y)]
    have hR : Q' ⁻¹' Iic t = ∅ := by
      ext x; simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
      linarith [hQ'_pos x]
    rw [hL, hR, measure_empty, measure_empty]

/-- Canonical `n`-fold convolution law of `exp(σ Z)` for `Z ~ N(0, 1)`. -/
noncomputable def lognormLaw (σ : ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | 1 => (gaussianReal 0 1).map (fun z => exp (σ * z))
  | n + 2 => lognormLaw σ (n + 1) ∗ (gaussianReal 0 1).map (fun z => exp (σ * z))

/-- Base case `n = 1`: `Q₁(z) = exp(σ z)` is a `GoodQuantile`. -/
lemma goodQuantile_exp {σ : ℝ} (hσ : 0 < σ) : GoodQuantile (fun z => exp (σ * z)) where
  strictMono := fun a b hab => Real.exp_strictMono (mul_lt_mul_of_pos_left hab hσ)
  continuous := by fun_prop
  convex := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [smul_eq_mul]
    have := convexOn_exp.2 (mem_univ (σ * x)) (mem_univ (σ * y)) ha hb hab
    simpa [smul_eq_mul, mul_add, mul_left_comm] using this
  pos := fun z => Real.exp_pos _
  tendsto_bot := Real.tendsto_exp_atBot.comp (Tendsto.const_mul_atBot hσ tendsto_id)
  tendsto_top := Real.tendsto_exp_atTop.comp (Tendsto.const_mul_atTop hσ tendsto_id)

/-- Induction on `n ≥ 1`: `lognormLaw σ n = (gaussianReal 0 1).map Q` for some `GoodQuantile Q`. -/
theorem exists_goodQuantile_lognormLaw {σ : ℝ} (hσ : 0 < σ) :
    ∀ n : ℕ, 0 < n → ∃ Q : ℝ → ℝ, GoodQuantile Q ∧ lognormLaw σ n = (gaussianReal 0 1).map Q
  | 0, hn => absurd hn (lt_irrefl 0)
  | 1, _ => ⟨fun z => exp (σ * z), goodQuantile_exp hσ, rfl⟩
  | n + 2, _ => by
    obtain ⟨Q, hQ, hlaw⟩ := exists_goodQuantile_lognormLaw hσ (n + 1) (Nat.succ_pos n)
    obtain ⟨Q', hQ', hconv⟩ := exists_goodQuantile_conv hQ hσ
    exact ⟨Q', hQ', by unfold lognormLaw; rw [hlaw, hconv]⟩

end LognormalInduction

section FinalTheorem

/-- Strict Jensen inequality for a positive, strictly increasing, convex function of a
standard normal variable: `Q 0 < 𝔼[Q(G)]`. -/
theorem convex_strict_jensen_gaussian {Q : ℝ → ℝ} (hQ : GoodQuantile Q)
    (hQ_int : Integrable Q (gaussianReal 0 1)) :
    Q 0 < ∫ x, Q x ∂(gaussianReal 0 1) := by
  let S : Set ℝ := (fun a => (Q 0 - Q a) / (0 - a)) '' Iio 0
  have hS_ne : S.Nonempty := ⟨_, -1, by norm_num, rfl⟩
  have hS_bdd : BddAbove S := by
    refine ⟨(Q 1 - Q 0) / (1 - 0), ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    have hsec := hQ.convex.secant_mono (mem_univ 0) (mem_univ a) (mem_univ 1)
      (ne_of_lt ha) one_ne_zero (le_of_lt (lt_trans ha zero_lt_one))
    have h1 : (Q a - Q 0) / (a - 0) = (Q 0 - Q a) / (0 - a) := by
      have : a - 0 ≠ 0 := sub_ne_zero.mpr (ne_of_lt ha)
      have : 0 - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt ha)
      field_simp; ring
    linarith
  let α := sSup S
  have hα_pos : 0 < α := by
    have hmem : (Q 0 - Q (-1)) / (0 - (-1)) ∈ S := ⟨-1, by norm_num, rfl⟩
    have hle : (Q 0 - Q (-1)) / (0 - (-1)) ≤ α := le_csSup hS_bdd hmem
    have hgt : 0 < Q 0 - Q (-1) := sub_pos.mpr (hQ.strictMono (by norm_num))
    linarith
  have hsupp : ∀ x : ℝ, Q 0 + α * x ≤ Q x := fun x => by
    rcases lt_trichotomy x 0 with hlt | rfl | hgt
    · have hle : (Q 0 - Q x) / (0 - x) ≤ α := le_csSup hS_bdd ⟨x, hlt, rfl⟩
      have hpos : 0 < 0 - x := by linarith
      have := (div_le_iff₀ hpos).mp hle
      linarith
    · simp
    · have hge : α ≤ (Q x - Q 0) / (x - 0) := by
        refine csSup_le hS_ne ?_
        rintro _ ⟨a, ha, rfl⟩
        have hsec := hQ.convex.secant_mono (mem_univ 0) (mem_univ a) (mem_univ x)
          (ne_of_lt ha) (ne_of_gt hgt) (le_of_lt (lt_trans ha hgt))
        have h1 : (Q a - Q 0) / (a - 0) = (Q 0 - Q a) / (0 - a) := by
          have : a - 0 ≠ 0 := sub_ne_zero.mpr (ne_of_lt ha)
          have : 0 - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt ha)
          field_simp; ring
        linarith
      have hpos : 0 < x - 0 := by linarith
      have := (le_div_iff₀ hpos).mp hge
      linarith
  set γ : Measure ℝ := gaussianReal 0 1
  have : IsProbabilityMeasure γ := inferInstance
  have hid_int : Integrable (fun x : ℝ => x) γ :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  have hlin_int : Integrable (fun x : ℝ => Q 0 + α * x) γ :=
    (integrable_const (Q 0)).add (hid_int.const_mul α)
  have hdiff_int : Integrable (fun x : ℝ => Q x - (Q 0 + α * x)) γ := hQ_int.sub hlin_int
  set c := -Q 0 / α - 1
  have hsub : (∫ x in Iic c, (Q x - (Q 0 + α * x)) ∂γ) ≤ ∫ x, (Q x - (Q 0 + α * x)) ∂γ :=
    setIntegral_le_integral hdiff_int (ae_of_all _ fun x => sub_nonneg.mpr (hsupp x))
  have hmono : (∫ _ in Iic c, α ∂γ) ≤ ∫ x in Iic c, (Q x - (Q 0 + α * x)) ∂γ := by
    refine setIntegral_mono_on (integrable_const α).integrableOn hdiff_int.integrableOn
      measurableSet_Iic fun x hx => ?_
    have hxc : x ≤ c := hx
    have hax : α * x ≤ -Q 0 - α := by
      have h1 : α * c = -Q 0 - α := by dsimp [c]; field_simp [hα_pos.ne']
      nlinarith [mul_le_mul_of_nonneg_left hxc hα_pos.le]
    linarith [hQ.pos x]
  have hconst_int : (∫ _ in Iic c, α ∂γ) = α * Phi c := by
    rw [setIntegral_const, smul_eq_mul, mul_comm, ← Phi_eq_gaussianReal]
  have hpos_int : 0 < ∫ x, (Q x - (Q 0 + α * x)) ∂γ :=
    lt_of_lt_of_le (mul_pos hα_pos (Phi_pos c)) (hconst_int ▸ hmono.trans hsub)
  have hlin_val : (∫ x, (Q 0 + α * x) ∂γ) = Q 0 := by
    rw [integral_add (integrable_const _) (hid_int.const_mul α), integral_const,
      probReal_univ, one_smul, integral_const_mul]
    have : ∫ x : ℝ, x ∂γ = 0 := integral_id_gaussianReal
    rw [this, mul_zero, add_zero]
  rw [integral_sub hQ_int hlin_int, hlin_val] at hpos_int
  linarith

lemma map_comp_of_aemeasurable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] {μ : Measure α} {f : α → β} {g : β → γ}
    (hg : Measurable g) (hf : AEMeasurable f μ) :
    μ.map (g ∘ f) = (μ.map f).map g := by
  ext s hs
  rw [Measure.map_apply_of_aemeasurable (hg.comp_aemeasurable hf) hs,
    Measure.map_apply hg hs, Measure.map_apply_of_aemeasurable hf (hg hs)]
  rfl

/-- Law of a sum of `n ≥ 1` i.i.d. `exp(σ Zᵢ)` variables equals `lognormLaw σ n`. -/
lemma map_sum_exp_eq_lognormLaw {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} :
    ∀ (n : ℕ), 0 < n → ∀ (z : Fin n → Ω → ℝ),
      iIndepFun z μ → (∀ i, μ.map (z i) = gaussianReal 0 1) →
      μ.map (fun ω => ∑ i : Fin n, exp (σ * z i ω)) = lognormLaw σ n
  | 0, hn, _, _, _ => absurd hn (lt_irrefl 0)
  | 1, _, z, _, hlaw => by
    have hfun : (fun ω => ∑ i : Fin 1, exp (σ * z i ω)) = (fun u => exp (σ * u)) ∘ z 0 := by
      ext ω; simp
    have hzm : AEMeasurable (z 0) μ := aemeasurable_of_map_neZero (by rw [hlaw 0]; infer_instance)
    rw [hfun, map_comp_of_aemeasurable (by fun_prop) hzm, hlaw 0]
    rfl
  | n + 2, _, z, hind, hlaw => by
    let w : Fin (n + 2) → Ω → ℝ := fun i ω => exp (σ * z i ω)
    have hzm : ∀ i, AEMeasurable (z i) μ := fun i =>
      aemeasurable_of_map_neZero (by rw [hlaw i]; infer_instance)
    have hwm : ∀ i, AEMeasurable (w i) μ := fun i =>
      (by fun_prop : Measurable (fun u => exp (σ * u))).comp_aemeasurable (hzm i)
    have hwind : iIndepFun w μ :=
      hind.comp (fun _ u => exp (σ * u)) (fun _ => by fun_prop)
    have hsplit : (fun ω => ∑ i : Fin (n + 2), w i ω) =
        (fun ω => ∑ i ∈ (Finset.univ.erase (Fin.last (n + 1))), w i ω) + w (Fin.last (n + 1)) := by
      ext ω
      simp only [Pi.add_apply]
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (Fin.last (n + 1)))]
    have hsum_fn : (∑ j ∈ (Finset.univ.erase (Fin.last (n + 1))), w j) =
        fun ω => ∑ i ∈ (Finset.univ.erase (Fin.last (n + 1))), w i ω := by
      ext ω; simp [Finset.sum_apply]
    have hind_sum : IndepFun (fun ω => ∑ i ∈ (Finset.univ.erase (Fin.last (n + 1))), w i ω)
        (w (Fin.last (n + 1))) μ :=
      hsum_fn ▸ hwind.indepFun_finsetSum_of_notMem₀ hwm (Finset.notMem_erase (Fin.last (n + 1)) Finset.univ)
    have hsum_meas : AEMeasurable (fun ω => ∑ i ∈ (Finset.univ.erase (Fin.last (n + 1))), w i ω) μ :=
      Finset.aemeasurable_fun_sum _ fun i _ => hwm i
    have hconv := hind_sum.map_add_eq_map_conv_map₀ hsum_meas (hwm (Fin.last (n + 1)))
    have herase_eq : (fun ω => ∑ i ∈ (Finset.univ.erase (Fin.last (n + 1))), w i ω) =
        fun ω => ∑ j : Fin (n + 1), exp (σ * z j.castSucc ω) := by
      ext ω
      have h1 : ∑ i : Fin (n + 2), w i ω = (∑ j : Fin (n + 1), w j.castSucc ω) + w (Fin.last (n + 1)) ω :=
        Fin.sum_univ_castSucc (fun i => w i ω)
      have h2 := Finset.sum_erase_add Finset.univ (fun i => w i ω) (Finset.mem_univ (Fin.last (n + 1)))
      linarith
    have hsub_ind : iIndepFun (fun j : Fin (n + 1) => z j.castSucc) μ :=
      hind.precomp (Fin.castSucc_injective (n + 1))
    have hih := map_sum_exp_eq_lognormLaw (σ := σ) (n + 1) (Nat.succ_pos n) (fun j => z j.castSucc)
      hsub_ind (fun j => hlaw j.castSucc)
    have hlast : μ.map (w (Fin.last (n + 1))) = (gaussianReal 0 1).map (fun u => exp (σ * u)) := by
      change μ.map ((fun u => exp (σ * u)) ∘ z (Fin.last (n + 1))) = _
      rw [map_comp_of_aemeasurable (by fun_prop) (hzm _), hlaw _]
    change μ.map (fun ω => ∑ i : Fin (n + 2), w i ω) = _
    rw [hsplit, hconv, herase_eq, hih, hlast]
    rfl

/-- Target theorem (identical to `OMA.S_mo_271503.main`). -/
theorem main_proof :
    ∀ (n : ℕ), 0 < n → ∀ (μ σ : ℝ), 0 < σ →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] (x : Fin n → Ω → ℝ),
        iIndepFun x ℙ → (∀ i, ∀ᵐ ω ∂(ℙ : Measure Ω), 0 < x i ω) →
        (∀ i, Measure.map (fun ω => Real.log (x i ω)) ℙ = gaussianReal μ (Real.toNNReal (σ ^ 2))) →
        ∀ m : ℝ,
          1 / 2 ≤ (ℙ : Measure Ω).real {ω | (1 / (n : ℝ)) * ∑ i, x i ω ≤ m} →
          1 / 2 ≤ (ℙ : Measure Ω).real {ω | m ≤ (1 / (n : ℝ)) * ∑ i, x i ω} →
          m < 𝔼[fun ω => (1 / (n : ℝ)) * ∑ i, x i ω] := by
  intro n hn μ σ hσ Ω _ _ x hind hxpos hlog m _ hm_ge
  let z : Fin n → Ω → ℝ := fun i ω => (Real.log (x i ω) - μ) / σ
  have hlogm : ∀ i, AEMeasurable (fun ω => Real.log (x i ω)) (ℙ : Measure Ω) := fun i =>
    aemeasurable_of_map_neZero (by rw [hlog i]; infer_instance)
  have hz_law : ∀ i, Measure.map (z i) (ℙ : Measure Ω) = gaussianReal 0 1 := fun i => by
    have hcomp : z i = (fun u => (u - μ) / σ) ∘ (fun ω => Real.log (x i ω)) := rfl
    rw [hcomp, map_comp_of_aemeasurable (by fun_prop) (hlogm i), hlog i]
    have hcomp2 : (fun u : ℝ => (u - μ) / σ) = (fun u => u / σ) ∘ (fun u => u - μ) := rfl
    rw [hcomp2, ← Measure.map_map (by fun_prop) (by fun_prop),
      gaussianReal_map_sub_const, gaussianReal_map_div_const]
    congr 1
    · simp
    · ext
      simp only [NNReal.coe_div, NNReal.coe_one, Real.coe_toNNReal (σ ^ 2) (sq_nonneg σ), NNReal.coe_mk]
      exact div_self (sq_pos_of_pos hσ).ne'
  have hz_meas : ∀ i, AEMeasurable (z i) (ℙ : Measure Ω) := fun i =>
    aemeasurable_of_map_neZero (by rw [hz_law i]; infer_instance)
  have hz_ind : iIndepFun z (ℙ : Measure Ω) :=
    hind.comp (fun _ t => (Real.log t - μ) / σ) (fun _ => by fun_prop)
  have hx_ae : ∀ i, x i =ᵐ[(ℙ : Measure Ω)] fun ω => exp μ * exp (σ * z i ω) := fun i => by
    filter_upwards [hxpos i] with ω hω
    dsimp [z]
    rw [mul_div_cancel₀ _ hσ.ne', ← Real.exp_add, add_sub_cancel, Real.exp_log hω]
  let S : Ω → ℝ := fun ω => ∑ i : Fin n, exp (σ * z i ω)
  have hS_meas : AEMeasurable S (ℙ : Measure Ω) :=
    Finset.aemeasurable_fun_sum _ fun i _ =>
      (by fun_prop : Measurable (fun u => exp (σ * u))).comp_aemeasurable (hz_meas i)
  have hexp_int : ∀ i, Integrable (fun ω => exp (σ * z i ω)) (ℙ : Measure Ω) := fun i => by
    have h1 : Integrable (fun u : ℝ => exp (σ * u)) (Measure.map (z i) (ℙ : Measure Ω)) := by
      rw [hz_law i]; exact integrable_exp_mul_gaussianReal σ
    exact (integrable_map_measure (by fun_prop) (hz_meas i)).mp h1
  have hS_int : Integrable S (ℙ : Measure Ω) := integrable_finsetSum _ fun i _ => hexp_int i
  have hexp_val : ∀ i, ∫ ω, exp (σ * z i ω) ∂(ℙ : Measure Ω) = exp (σ ^ 2 / 2) := fun i => by
    have hmgf := mgf_gaussianReal (hz_law i) σ
    unfold mgf at hmgf
    simpa using hmgf
  have hS_val : ∫ ω, S ω ∂(ℙ : Measure Ω) = (n : ℝ) * exp (σ ^ 2 / 2) := by
    simp only [S, integral_finsetSum _ fun i _ => hexp_int i, hexp_val, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hy_ae : (fun ω => (1 / (n : ℝ)) * ∑ i, x i ω) =ᵐ[(ℙ : Measure Ω)]
      fun ω => (exp μ / (n : ℝ)) * S ω := by
    have hall : ∀ᵐ ω ∂(ℙ : Measure Ω), ∀ i : Fin n, x i ω = exp μ * exp (σ * z i ω) :=
      ae_all_iff.mpr hx_ae
    filter_upwards [hall] with ω hω
    simp only [S, hω, ← Finset.mul_sum]
    ring
  have hEy : 𝔼[fun ω => (1 / (n : ℝ)) * ∑ i, x i ω] = exp (μ + σ ^ 2 / 2) := by
    rw [integral_congr_ae hy_ae, integral_const_mul, hS_val]
    have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    rw [Real.exp_add]
    field_simp [hn_ne]
  rw [hEy]
  -- Obtain convex quantile Q representing the law of S
  obtain ⟨Q, hQ, hQ_law⟩ := exists_goodQuantile_lognormLaw hσ n hn
  have hS_law : Measure.map S (ℙ : Measure Ω) = (gaussianReal 0 1).map Q := by
    rw [map_sum_exp_eq_lognormLaw n hn z hz_ind hz_law, hQ_law]
  have hQ_int : Integrable Q (gaussianReal 0 1) := by
    have h1 : Integrable id (Measure.map S (ℙ : Measure Ω)) :=
      (integrable_map_measure aemeasurable_id.aestronglyMeasurable hS_meas).mpr hS_int
    rw [hS_law] at h1
    exact (integrable_map_measure aemeasurable_id.aestronglyMeasurable hQ.continuous.aemeasurable).mp h1
  have hQ_exp : ∫ u, Q u ∂(gaussianReal 0 1) = (n : ℝ) * exp (σ ^ 2 / 2) := by
    have h1 : ∫ u, u ∂(Measure.map S (ℙ : Measure Ω)) = ∫ ω, S ω ∂(ℙ : Measure Ω) :=
      integral_map hS_meas aemeasurable_id.aestronglyMeasurable
    have h2 : ∫ u, u ∂((gaussianReal 0 1).map Q) = ∫ u, Q u ∂(gaussianReal 0 1) :=
      integral_map hQ.continuous.aemeasurable aemeasurable_id.aestronglyMeasurable
    rw [hS_law] at h1
    linarith [h1, h2, hS_val]
  have hQ0_lt : Q 0 < (n : ℝ) * exp (σ ^ 2 / 2) := by
    rw [← hQ_exp]; exact convex_strict_jensen_gaussian hQ hQ_int
  -- By continuity of Q at 0, pick δ > 0 with Q δ < n * exp(σ²/2)
  have hcont0 : ContinuousAt Q 0 := hQ.continuous.continuousAt
  obtain ⟨δ, hδ_pos, hQδ⟩ : ∃ δ > 0, Q δ < (n : ℝ) * exp (σ ^ 2 / 2) := by
    have hev := hcont0.tendsto.eventually (gt_mem_nhds hQ0_lt)
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨r, hr, hball⟩ := hev
    refine ⟨r / 2, by positivity, hball ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith
  have hprob_lt : 1 / 2 < (ℙ : Measure Ω).real {ω | S ω < (n : ℝ) * exp (σ ^ 2 / 2)} := by
    have h1 : (ℙ : Measure Ω).real {ω | S ω < (n : ℝ) * exp (σ ^ 2 / 2)} =
        (Measure.map S (ℙ : Measure Ω)).real (Iio ((n : ℝ) * exp (σ ^ 2 / 2))) := by
      simp only [measureReal_def]
      rw [Measure.map_apply_of_aemeasurable hS_meas measurableSet_Iio]
      rfl
    rw [h1, hS_law, map_measureReal_apply hQ.continuous.measurable measurableSet_Iio]
    have hsub : Iic δ ⊆ Q ⁻¹' Iio ((n : ℝ) * exp (σ ^ 2 / 2)) := fun u hu =>
      lt_of_le_of_lt (hQ.strictMono.monotone hu) hQδ
    have h2 : Phi δ ≤ (gaussianReal 0 1).real (Q ⁻¹' Iio ((n : ℝ) * exp (σ ^ 2 / 2))) := by
      rw [Phi_eq_gaussianReal]
      exact measureReal_mono hsub
    have h3 : 1 / 2 < Phi δ := by rw [← Phi_zero]; exact Phi_strictMono hδ_pos
    linarith
  have hset_ae : ({ω | S ω < (n : ℝ) * exp (σ ^ 2 / 2)} : Set Ω) =ᵐ[(ℙ : Measure Ω)]
      {ω | (1 / (n : ℝ)) * ∑ i, x i ω < exp (μ + σ ^ 2 / 2)} := by
    filter_upwards [hy_ae] with ω hω
    simp only [eq_iff_iff]
    change (S ω < (n : ℝ) * exp (σ ^ 2 / 2)) ↔ ((1 / (n : ℝ)) * ∑ i, x i ω < exp (μ + σ ^ 2 / 2))
    rw [hω, Real.exp_add]
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hexp_pos : 0 < exp μ := Real.exp_pos μ
    constructor
    · intro h
      calc exp μ / (n : ℝ) * S ω < exp μ / (n : ℝ) * ((n : ℝ) * exp (σ ^ 2 / 2)) :=
            mul_lt_mul_of_pos_left h (by positivity)
        _ = exp μ * exp (σ ^ 2 / 2) := by field_simp [hn_pos.ne']
    · intro h
      have h' : exp μ / (n : ℝ) * S ω < exp μ / (n : ℝ) * ((n : ℝ) * exp (σ ^ 2 / 2)) := by
        have : exp μ / (n : ℝ) * ((n : ℝ) * exp (σ ^ 2 / 2)) = exp μ * exp (σ ^ 2 / 2) := by
          field_simp [hn_pos.ne']
        linarith
      exact lt_of_mul_lt_mul_left h' (by positivity)
  have hprob_y_lt : 1 / 2 < (ℙ : Measure Ω).real {ω | (1 / (n : ℝ)) * ∑ i, x i ω < exp (μ + σ ^ 2 / 2)} := by
    rw [← measureReal_congr hset_ae]
    exact hprob_lt
  by_contra hge
  push Not at hge
  have hsub_ge : {ω | m ≤ (1 / (n : ℝ)) * ∑ i, x i ω} ⊆
      {ω | exp (μ + σ ^ 2 / 2) ≤ (1 / (n : ℝ)) * ∑ i, x i ω} := fun ω hω => le_trans hge hω
  have hge_half : 1 / 2 ≤ (ℙ : Measure Ω).real {ω | exp (μ + σ ^ 2 / 2) ≤ (1 / (n : ℝ)) * ∑ i, x i ω} :=
    hm_ge.trans (measureReal_mono hsub_ge)
  have hcompl_eq : {ω | exp (μ + σ ^ 2 / 2) ≤ (1 / (n : ℝ)) * ∑ i, x i ω} =
      {ω | (1 / (n : ℝ)) * ∑ i, x i ω < exp (μ + σ ^ 2 / 2)}ᶜ := by
    ext ω; simp [not_lt]
  have hmeas_lt : NullMeasurableSet {ω | (1 / (n : ℝ)) * ∑ i, x i ω < exp (μ + σ ^ 2 / 2)} (ℙ : Measure Ω) :=
    (hS_meas.nullMeasurable measurableSet_Iio).congr hset_ae
  rw [hcompl_eq, probReal_compl_eq_one_sub₀ hmeas_lt] at hge_half
  linarith

end FinalTheorem

end OMA.P271503

theorem OMA.solution : type_of% @OMA.S_mo_271503.main :=
  OMA.P271503.main_proof
