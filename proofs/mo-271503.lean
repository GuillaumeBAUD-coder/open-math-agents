import OMAStatements.S_mo_271503

namespace OMA.S_mo_271503_Proof

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

/-! ### Part 1: Standard Gaussian PDF `φ`, CDF `Φ`, inverse `Φinv`, and isoperimetric profile -/

private noncomputable def φ (x : ℝ) : ℝ := gaussianPDFReal 0 1 x

private lemma φ_eq (x : ℝ) : φ x = (√(2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := by
  simp [φ, gaussianPDFReal_def]

private lemma φ_pos (x : ℝ) : 0 < φ x :=
  gaussianPDFReal_pos 0 1 x one_ne_zero

private lemma φ_nonneg (x : ℝ) : 0 ≤ φ x := le_of_lt (φ_pos x)

private lemma φ_neg (x : ℝ) : φ (-x) = φ x := by
  simp [φ_eq]

private lemma continuous_φ : Continuous φ := by
  have : φ = fun x => (√(2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := funext φ_eq
  rw [this]; fun_prop

private lemma φ_le_one (x : ℝ) : φ x ≤ 1 := by
  rw [φ_eq]
  have h1 : Real.exp (-x ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  have h2 : 1 ≤ √(2 * Real.pi) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    linarith [Real.pi_gt_three]
  have h3 : (√(2 * Real.pi))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h2
  nlinarith [Real.exp_pos (-x ^ 2 / 2)]

private lemma hasDerivAt_φ (x : ℝ) : HasDerivAt φ (-x * φ x) x := by
  have hfn : φ = fun t => (√(2 * Real.pi))⁻¹ * Real.exp (-t ^ 2 / 2) := funext φ_eq
  rw [hfn]
  have h1 : HasDerivAt (fun t : ℝ => -t ^ 2 / 2) (-x) x :=
    (((hasDerivAt_pow 2 x).neg).div_const 2).congr_deriv (by norm_num; ring)
  have h2 := (h1.exp).const_mul (√(2 * Real.pi))⁻¹
  exact h2.congr_deriv (by ring)

private lemma integrable_φ : Integrable φ volume :=
  integrable_gaussianPDFReal 0 1

private lemma integral_φ : ∫ t, φ t = 1 :=
  integral_gaussianPDFReal_eq_one 0 one_ne_zero

private noncomputable def Φ (x : ℝ) : ℝ := ∫ t in Set.Iic x, φ t

private lemma Φ_eq_indicator (x : ℝ) : Φ x = ∫ t, (Set.Iic x).indicator φ t := by
  rw [Φ, integral_indicator measurableSet_Iic]

private lemma Φ_eq_add_interval (x : ℝ) : Φ x = Φ 0 + ∫ t in (0 : ℝ)..x, φ t := by
  have h := intervalIntegral.integral_Iic_sub_Iic
    (integrable_φ.integrableOn (s := Set.Iic 0))
    (integrable_φ.integrableOn (s := Set.Iic x))
  unfold Φ
  linarith

private lemma hasDerivAt_Φ (x : ℝ) : HasDerivAt Φ (φ x) x := by
  have hfun : Φ = fun y => Φ 0 + ∫ t in (0 : ℝ)..y, φ t := funext Φ_eq_add_interval
  rw [hfun]
  have h1 := intervalIntegral.integral_hasDerivAt_right
    (continuous_φ.intervalIntegrable 0 x)
    (continuous_φ.stronglyMeasurableAtFilter _ _)
    continuous_φ.continuousAt
  simpa using h1.const_add (Φ 0)

private lemma continuous_Φ : Continuous Φ :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_Φ x).continuousAt

private lemma Φ_strictMono : StrictMono Φ :=
  strictMono_of_deriv_pos fun x => by rw [(hasDerivAt_Φ x).deriv]; exact φ_pos x

private lemma Φ_zero : Φ 0 = 1 / 2 := by
  have hsum : (∫ t in Set.Iic (0 : ℝ), φ t) + (∫ t in Set.Ioi (0 : ℝ), φ t) = ∫ t, φ t := by
    have h1 := setIntegral_union (μ := volume) (f := φ)
      (s := Set.Iic (0 : ℝ)) (t := Set.Ioi (0 : ℝ))
      (Set.Iic_disjoint_Ioi le_rfl)
      measurableSet_Ioi integrable_φ.integrableOn integrable_φ.integrableOn
    rw [Set.Iic_union_Ioi, setIntegral_univ] at h1
    exact h1.symm
  have hsym : ∫ t in Set.Ioi (0 : ℝ), φ t = ∫ t in Set.Iic (0 : ℝ), φ t := by
    have h1 := integral_comp_neg_Ioi (c := (0 : ℝ)) (f := φ)
    simp only [neg_zero, φ_neg] at h1
    exact h1
  unfold Φ
  rw [hsym, integral_φ] at hsum
  linarith

private lemma Φ_tendsto_atTop : Tendsto Φ atTop (nhds 1) := by
  rw [← integral_φ]
  have hfn : Φ = fun x => ∫ t, (Set.Iic x).indicator φ t := funext Φ_eq_indicator
  rw [hfn]
  refine tendsto_integral_filter_of_dominated_convergence φ
    (Eventually.of_forall fun x =>
      (continuous_φ.aestronglyMeasurable.indicator measurableSet_Iic))
    (Eventually.of_forall fun x => Eventually.of_forall fun t => ?_)
    integrable_φ (Eventually.of_forall fun t => ?_)
  · by_cases ht : t ≤ x
    · simp only [Set.indicator, Set.mem_Iic, ht, ↓reduceIte, Real.norm_eq_abs,
        abs_of_nonneg (φ_nonneg t), le_refl]
    · simp only [Set.indicator, Set.mem_Iic, ht, ↓reduceIte, norm_zero, φ_nonneg t]
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop t] with x hx
    simp only [Set.indicator, Set.mem_Iic, hx, ↓reduceIte]

private lemma Φ_tendsto_atBot : Tendsto Φ atBot (nhds 0) := by
  have hfn : Φ = fun x => ∫ t, (Set.Iic x).indicator φ t := funext Φ_eq_indicator
  rw [hfn, show (0 : ℝ) = ∫ _ : ℝ, (0 : ℝ) by simp]
  refine tendsto_integral_filter_of_dominated_convergence φ
    (Eventually.of_forall fun x =>
      (continuous_φ.aestronglyMeasurable.indicator measurableSet_Iic))
    (Eventually.of_forall fun x => Eventually.of_forall fun t => ?_)
    integrable_φ (Eventually.of_forall fun t => ?_)
  · by_cases ht : t ≤ x
    · simp only [Set.indicator, Set.mem_Iic, ht, ↓reduceIte, Real.norm_eq_abs,
        abs_of_nonneg (φ_nonneg t), le_refl]
    · simp only [Set.indicator, Set.mem_Iic, ht, ↓reduceIte, norm_zero, φ_nonneg t]
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_lt_atBot t] with x hx
    simp only [Set.indicator, Set.mem_Iic, not_le.mpr hx, ↓reduceIte]

private lemma Φ_pos (x : ℝ) : 0 < Φ x := by
  have hlt : Φ (x - 1) < Φ x := Φ_strictMono (by linarith)
  have h0' : 0 ≤ Φ (x - 1) :=
    le_of_tendsto Φ_tendsto_atBot ((eventually_le_atBot (x - 1)).mono fun _ hy => Φ_strictMono.monotone hy)
  linarith

private lemma Φ_lt_one (x : ℝ) : Φ x < 1 := by
  have hlt : Φ x < Φ (x + 1) := Φ_strictMono (by linarith)
  have h1 : Φ (x + 1) ≤ 1 :=
    ge_of_tendsto Φ_tendsto_atTop ((eventually_ge_atTop (x + 1)).mono fun _ hy => Φ_strictMono.monotone hy)
  linarith

private lemma Φ_mem_Ioo (x : ℝ) : Φ x ∈ Set.Ioo 0 1 := ⟨Φ_pos x, Φ_lt_one x⟩

private lemma Φ_surj_Ioo {p : ℝ} (hp : p ∈ Set.Ioo 0 1) : ∃ x : ℝ, Φ x = p := by
  obtain ⟨a, ha⟩ := (Φ_tendsto_atBot.eventually (gt_mem_nhds hp.1)).exists
  obtain ⟨b, hb⟩ := (Φ_tendsto_atTop.eventually (lt_mem_nhds hp.2)).exists
  have hab : a ≤ b := le_of_lt (Φ_strictMono.lt_iff_lt.mp (lt_trans ha hb))
  have hmem : p ∈ Set.Icc (Φ a) (Φ b) := ⟨le_of_lt ha, le_of_lt hb⟩
  obtain ⟨x, _, hx⟩ := intermediate_value_Icc hab continuous_Φ.continuousOn hmem
  exact ⟨x, hx⟩

private noncomputable def Φinv (p : ℝ) : ℝ :=
  if hp : p ∈ Set.Ioo 0 1 then Classical.choose (Φ_surj_Ioo hp) else 0

private lemma Φ_Φinv {p : ℝ} (hp : p ∈ Set.Ioo 0 1) : Φ (Φinv p) = p := by
  simp only [Φinv, dif_pos hp]
  exact Classical.choose_spec (Φ_surj_Ioo hp)

private lemma Φinv_Φ (x : ℝ) : Φinv (Φ x) = x :=
  Φ_strictMono.injective (Φ_Φinv (Φ_mem_Ioo x))

private lemma Φinv_strictMonoOn : StrictMonoOn Φinv (Set.Ioo 0 1) := by
  intro p hp q hq hpq
  by_contra hle
  push Not at hle
  have := Φ_strictMono.monotone hle
  rw [Φ_Φinv hp, Φ_Φinv hq] at this
  linarith

private lemma Φinv_monoOn : MonotoneOn Φinv (Set.Ioo 0 1) :=
  Φinv_strictMonoOn.monotoneOn

private lemma Φinv_half : Φinv (1 / 2) = 0 := by
  rw [← Φ_zero, Φinv_Φ]

private lemma continuousOn_Φinv : ContinuousOn Φinv (Set.Ioo 0 1) := by
  intro p hp
  refine continuousWithinAt_iff_continuousAt (isOpen_Ioo.mem_nhds hp) |>.mpr ?_
  rw [Metric.continuousAt_iff]
  intro ε hε
  set x := Φinv p
  have hx1 : Φ (x - ε / 2) < p := by rw [← Φ_Φinv hp]; exact Φ_strictMono (by linarith)
  have hx2 : p < Φ (x + ε / 2) := by rw [← Φ_Φinv hp]; exact Φ_strictMono (by linarith)
  refine ⟨min (p - Φ (x - ε / 2)) (Φ (x + ε / 2) - p), by positivity, fun q hq => ?_⟩
  rw [Real.dist_eq] at hq ⊢
  have hq1 : Φ (x - ε / 2) < q := by linarith [(abs_lt.mp hq).1, min_le_left (p - Φ (x - ε / 2)) (Φ (x + ε / 2) - p)]
  have hq2 : q < Φ (x + ε / 2) := by linarith [(abs_lt.mp hq).2, min_le_right (p - Φ (x - ε / 2)) (Φ (x + ε / 2) - p)]
  have hq_mem : q ∈ Set.Ioo 0 1 := ⟨lt_trans (Φ_pos _) hq1, lt_trans hq2 (Φ_lt_one _)⟩
  have h1 : x - ε / 2 < Φinv q := by
    rw [← Φinv_Φ (x - ε / 2)]
    exact Φinv_strictMonoOn (Φ_mem_Ioo _) hq_mem hq1
  have h2 : Φinv q < x + ε / 2 := by
    rw [← Φinv_Φ (x + ε / 2)]
    exact Φinv_strictMonoOn hq_mem (Φ_mem_Ioo _) hq2
  rw [abs_lt]
  constructor <;> linarith

private lemma hasDerivAt_Φinv {p : ℝ} (hp : p ∈ Set.Ioo 0 1) :
    HasDerivAt Φinv (φ (Φinv p))⁻¹ p := by
  have hcont : ContinuousAt Φinv p :=
    (continuousOn_Φinv p hp).continuousAt (isOpen_Ioo.mem_nhds hp)
  have hinv : ∀ᶠ q in 𝓝 p, Φ (Φinv q) = q :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hp) fun q hq => Φ_Φinv hq
  have hΦ : HasDerivAt Φ (φ (Φinv p)) (Φinv p) := hasDerivAt_Φ (Φinv p)
  exact hΦ.of_local_left_inverse hcont (ne_of_gt (φ_pos _)) hinv

/-- Supporting line inequality for the concave Gaussian isoperimetric profile `I(p) = φ(Φ⁻¹(p))`. -/
private lemma isoperimetric_support {p p₀ : ℝ} (hp : p ∈ Set.Ioo 0 1) (hp₀ : p₀ ∈ Set.Ioo 0 1) :
    φ (Φinv p) ≤ φ (Φinv p₀) + (-Φinv p₀) * (p - p₀) := by
  let g : ℝ → ℝ := fun q => φ (Φinv q)
  have hderiv : ∀ q ∈ Set.Ioo 0 1, HasDerivAt g (-Φinv q) q := by
    intro q hq
    have h1 := (hasDerivAt_φ (Φinv q)).comp q (hasDerivAt_Φinv hq)
    have heq : -Φinv q * φ (Φinv q) * (φ (Φinv q))⁻¹ = -Φinv q := by
      rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt (φ_pos (Φinv q))), mul_one]
    rwa [heq] at h1
  rcases lt_trichotomy p p₀ with hlt | rfl | hgt
  · have hsub : Set.Icc p p₀ ⊆ Set.Ioo 0 1 := fun q hq => ⟨lt_of_lt_of_le hp.1 hq.1, lt_of_le_of_lt hq.2 hp₀.2⟩
    obtain ⟨c, hc, hmv⟩ := exists_hasDerivAt_eq_slope g (fun q => -Φinv q) hlt
      (fun q hq => (hderiv q (hsub hq)).continuousAt.continuousWithinAt)
      (fun q hq => hderiv q (hsub ⟨le_of_lt hq.1, le_of_lt hq.2⟩))
    have hc_le : Φinv c ≤ Φinv p₀ := Φinv_monoOn (hsub ⟨le_of_lt hc.1, le_of_lt hc.2⟩) hp₀ (le_of_lt hc.2)
    have hslope : g p₀ - g p = (-Φinv c) * (p₀ - p) := by
      have hne : p₀ - p ≠ 0 := by linarith
      rw [hmv, div_mul_cancel₀ _ hne]
    nlinarith
  · simp
  · have hsub : Set.Icc p₀ p ⊆ Set.Ioo 0 1 := fun q hq => ⟨lt_of_lt_of_le hp₀.1 hq.1, lt_of_le_of_lt hq.2 hp.2⟩
    obtain ⟨c, hc, hmv⟩ := exists_hasDerivAt_eq_slope g (fun q => -Φinv q) hgt
      (fun q hq => (hderiv q (hsub hq)).continuousAt.continuousWithinAt)
      (fun q hq => hderiv q (hsub ⟨le_of_lt hq.1, le_of_lt hq.2⟩))
    have hc_ge : Φinv p₀ ≤ Φinv c := Φinv_monoOn hp₀ (hsub ⟨le_of_lt hc.1, le_of_lt hc.2⟩) (le_of_lt hc.1)
    have hslope : g p - g p₀ = (-Φinv c) * (p - p₀) := by
      have hne : p - p₀ ≠ 0 := by linarith
      rw [hmv, div_mul_cancel₀ _ hne]
    nlinarith

/-- For any probability measure `ν` and measurable `X`, `c ↦ Φ⁻¹(∫ Φ(X + c) dν)` is `1`-Lipschitz. -/
private lemma Φinv_integral_add_le {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] {X : α → ℝ} (hX : Measurable X) {c : ℝ} (hc : 0 ≤ c) :
    Φinv (∫ a, Φ (X a + c) ∂ν) ≤ Φinv (∫ a, Φ (X a) ∂ν) + c := by
  let F : ℝ → ℝ := fun r => ∫ a, Φ (X a + r) ∂ν
  have hF_mem : ∀ r : ℝ, F r ∈ Set.Ioo 0 1 := by
    intro r
    have hint : Integrable (fun a => Φ (X a + r)) ν :=
      Integrable.of_bound (continuous_Φ.measurable.comp (hX.add measurable_const)).aestronglyMeasurable
        1 (Eventually.of_forall fun a => by rw [Real.norm_eq_abs, abs_of_pos (Φ_pos _)]; exact le_of_lt (Φ_lt_one _))
    constructor
    · refine (integral_pos_iff_support_of_nonneg_ae
        (Eventually.of_forall fun a => le_of_lt (Φ_pos _)) hint).mpr ?_
      have hsupp : Function.support (fun a => Φ (X a + r)) = Set.univ := by
        ext a; simp [ne_of_gt (Φ_pos (X a + r))]
      rw [hsupp]; simp
    · have hsub : 0 < ∫ a, (1 - Φ (X a + r)) ∂ν := by
        have hint2 : Integrable (fun a => 1 - Φ (X a + r)) ν := (integrable_const 1).sub hint
        refine (integral_pos_iff_support_of_nonneg_ae
          (Eventually.of_forall fun a => sub_nonneg.mpr (le_of_lt (Φ_lt_one (X a + r)))) hint2).mpr ?_
        have hsupp : Function.support (fun a => 1 - Φ (X a + r)) = Set.univ := by
          ext a; simp [sub_ne_zero.mpr (ne_of_gt (Φ_lt_one (X a + r)))]
        rw [hsupp]; simp
      rw [integral_sub (integrable_const 1) hint, integral_const] at hsub
      simp only [probReal_univ, one_smul] at hsub
      linarith
  have hF_deriv : ∀ r : ℝ, HasDerivAt F (∫ a, φ (X a + r) ∂ν) r := by
    intro r
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun s a => Φ (X a + s)) (F' := fun s a => φ (X a + s))
      (bound := fun _ => (1 : ℝ)) (s := Set.univ) Filter.univ_mem
      (Eventually.of_forall fun s =>
        (continuous_Φ.measurable.comp (hX.add measurable_const)).aestronglyMeasurable)
      (Integrable.of_bound (continuous_Φ.measurable.comp (hX.add measurable_const)).aestronglyMeasurable
        1 (Eventually.of_forall fun a => by rw [Real.norm_eq_abs, abs_of_pos (Φ_pos _)]; exact le_of_lt (Φ_lt_one _)))
      (continuous_φ.measurable.comp (hX.add measurable_const)).aestronglyMeasurable
      (Eventually.of_forall fun a s _ => by rw [Real.norm_eq_abs, abs_of_pos (φ_pos _)]; exact φ_le_one _)
      (integrable_const 1)
      (Eventually.of_forall fun a s _ => by
        simpa [Function.comp_def] using (hasDerivAt_Φ (X a + s)).comp s ((hasDerivAt_id s).const_add (X a)))).2
  let G : ℝ → ℝ := fun r => Φinv (F r)
  have hG_deriv : ∀ r : ℝ, HasDerivAt G ((∫ a, φ (X a + r) ∂ν) * (φ (G r))⁻¹) r := by
    intro r
    have h1 := (hasDerivAt_Φinv (hF_mem r)).comp r (hF_deriv r)
    rwa [mul_comm] at h1
  have hG_deriv_le : ∀ r : ℝ, (∫ a, φ (X a + r) ∂ν) * (φ (G r))⁻¹ ≤ 1 := by
    intro r
    have hpt : ∀ a, φ (X a + r) ≤ φ (G r) + (-G r) * (Φ (X a + r) - F r) := by
      intro a
      have := isoperimetric_support (Φ_mem_Ioo (X a + r)) (hF_mem r)
      simpa [G, Φinv_Φ] using this
    have hint1 : Integrable (fun a => φ (X a + r)) ν :=
      Integrable.of_bound (continuous_φ.measurable.comp (hX.add measurable_const)).aestronglyMeasurable
        1 (Eventually.of_forall fun a => by rw [Real.norm_eq_abs, abs_of_pos (φ_pos _)]; exact φ_le_one _)
    have hintΦ : Integrable (fun a => Φ (X a + r)) ν :=
      Integrable.of_bound (continuous_Φ.measurable.comp (hX.add measurable_const)).aestronglyMeasurable
        1 (Eventually.of_forall fun a => by rw [Real.norm_eq_abs, abs_of_pos (Φ_pos _)]; exact le_of_lt (Φ_lt_one _))
    have hint_sub : Integrable (fun a => Φ (X a + r) - F r) ν := hintΦ.sub (integrable_const (F r))
    have hint2 : Integrable (fun a => φ (G r) + (-G r) * (Φ (X a + r) - F r)) ν :=
      (integrable_const _).add (hint_sub.const_mul _)
    have hle := integral_mono hint1 hint2 hpt
    have hrhs : ∫ a, (φ (G r) + (-G r) * (Φ (X a + r) - F r)) ∂ν = φ (G r) := by
      rw [integral_add (integrable_const (φ (G r))) (hint_sub.const_mul (-G r)),
        integral_const_mul, integral_sub hintΦ (integrable_const (F r)), integral_const, integral_const]
      simp [F]
    rw [hrhs] at hle
    have hpos : 0 < φ (G r) := φ_pos (G r)
    rw [mul_inv_le_iff₀ hpos, one_mul]
    exact hle
  rcases eq_or_lt_of_le hc with rfl | hpos
  · simp [G, F]
  · obtain ⟨r, _, hmv⟩ := exists_hasDerivAt_eq_slope G (fun s => (∫ a, φ (X a + s) ∂ν) * (φ (G s))⁻¹) hpos
      (fun s _ => (hG_deriv s).continuousAt.continuousWithinAt)
      (fun s _ => hG_deriv s)
    have hle1 := hG_deriv_le r
    rw [hmv, sub_zero, div_le_one hpos] at hle1
    simpa [G, F] using show G c ≤ G 0 + c by linarith

/-! ### Part 2: Product Gaussian measure `γ`, heat kernel `K`, and heat semigroup `H` -/

private noncomputable def γ (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => gaussianReal 0 1)

private instance (n : ℕ) : IsProbabilityMeasure (γ n) := by
  unfold γ; infer_instance

/-- 1D heat kernel `K₁ t a b = (2πt)^{-1/2} exp(-(b - a)² / (2t))`. -/
private noncomputable def K₁ (t a b : ℝ) : ℝ :=
  (√(2 * Real.pi * t))⁻¹ * Real.exp (-(b - a) ^ 2 / (2 * t))

private noncomputable def K₁_da (t a b : ℝ) : ℝ :=
  ((b - a) / t) * K₁ t a b

private noncomputable def K₁_daa (t a b : ℝ) : ℝ :=
  (((b - a) / t) ^ 2 - 1 / t) * K₁ t a b

private noncomputable def K₁_dt (t a b : ℝ) : ℝ :=
  (1 / 2) * K₁_daa t a b

private lemma K₁_pos {t : ℝ} (ht : 0 < t) (a b : ℝ) : 0 < K₁ t a b := by
  unfold K₁; positivity

private lemma K₁_eq_gaussianPDFReal {t : ℝ} (ht : 0 < t) (a b : ℝ) :
    K₁ t a b = gaussianPDFReal a (Real.toNNReal t) b := by
  simp only [K₁, gaussianPDFReal_def, Real.coe_toNNReal t (le_of_lt ht)]

private lemma hasDerivAt_K₁_a {t : ℝ} (ht : 0 < t) (a b : ℝ) :
    HasDerivAt (fun s => K₁ t s b) (K₁_da t a b) a := by
  unfold K₁
  have h1 : HasDerivAt (fun s : ℝ => -(b - s) ^ 2 / (2 * t)) ((b - a) / t) a := by
    have hsub : HasDerivAt (fun s : ℝ => b - s) (-1) a := by
      simpa using (hasDerivAt_id a).const_sub b
    have hsq := ((hsub.pow 2).neg).div_const (2 * t)
    exact hsq.congr_deriv (by norm_num; field_simp [ne_of_gt ht])
  have h2 := (h1.exp).const_mul (√(2 * Real.pi * t))⁻¹
  exact h2.congr_deriv (by simp only [K₁_da, K₁]; ring)

private lemma hasDerivAt_K₁_da {t : ℝ} (ht : 0 < t) (a b : ℝ) :
    HasDerivAt (fun s => K₁_da t s b) (K₁_daa t a b) a := by
  unfold K₁_da
  have h1 : HasDerivAt (fun s : ℝ => (b - s) / t) (-1 / t) a := by
    have hsub : HasDerivAt (fun s : ℝ => b - s) (-1) a := by
      simpa using (hasDerivAt_id a).const_sub b
    exact hsub.div_const t
  have h2 := h1.mul (hasDerivAt_K₁_a ht a b)
  exact h2.congr_deriv (by simp only [K₁_daa, K₁_da]; ring)

private lemma hasDerivAt_K₁_t {t : ℝ} (ht : 0 < t) (a b : ℝ) :
    HasDerivAt (fun s => K₁ s a b) (K₁_dt t a b) t := by
  unfold K₁
  have h2pt : 0 < 2 * Real.pi * t := by positivity
  have hlin : HasDerivAt (fun s : ℝ => 2 * Real.pi * s) (2 * Real.pi) t := by
    simpa using (hasDerivAt_id t).const_mul (2 * Real.pi)
  have hsqrt : HasDerivAt (fun s : ℝ => √(2 * Real.pi * s)) (2 * Real.pi / (2 * √(2 * Real.pi * t))) t :=
    hlin.sqrt (ne_of_gt h2pt)
  have hinv : HasDerivAt (fun s : ℝ => (√(2 * Real.pi * s))⁻¹)
      (-(2 * Real.pi / (2 * √(2 * Real.pi * t))) / (√(2 * Real.pi * t)) ^ 2) t :=
    hsqrt.inv (ne_of_gt (Real.sqrt_pos.mpr h2pt))
  have hexp_arg : HasDerivAt (fun s : ℝ => -(b - a) ^ 2 / (2 * s))
      ((b - a) ^ 2 / (2 * t ^ 2)) t := by
    have h2s : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by simpa using (hasDerivAt_id t).const_mul 2
    have hdiv := (hasDerivAt_const t (-(b - a) ^ 2)).div h2s (by positivity)
    exact hdiv.congr_deriv (by field_simp [ne_of_gt ht]; ring)
  have hprod := hinv.mul hexp_arg.exp
  refine hprod.congr_deriv ?_
  simp only [K₁_dt, K₁_daa, K₁]
  have hsq : √(2 * Real.pi * t) ^ 2 = 2 * Real.pi * t := Real.sq_sqrt (le_of_lt h2pt)
  have hsq_ne : √(2 * Real.pi * t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h2pt)
  rw [hsq]
  field_simp [ne_of_gt ht, ne_of_gt Real.pi_pos, hsq_ne]
  ring

/-- Elementary Gaussian domination: `r^k * exp(-r² / (8 t₀)) ≤ C * exp(-r² / (16 t₀))`. -/
private lemma exp_poly_bound {t₀ r : ℝ} (ht₀ : 0 < t₀) (hr : 0 ≤ r) :
    Real.exp (-r ^ 2 / (8 * t₀)) ≤ Real.exp (-r ^ 2 / (16 * t₀)) ∧
    r * Real.exp (-r ^ 2 / (8 * t₀)) ≤ (1 + 16 * t₀) * Real.exp (-r ^ 2 / (16 * t₀)) ∧
    r ^ 2 * Real.exp (-r ^ 2 / (8 * t₀)) ≤ (16 * t₀) * Real.exp (-r ^ 2 / (16 * t₀)) := by
  have hu : 0 ≤ r ^ 2 / (16 * t₀) := by positivity
  have hexp_u : r ^ 2 / (16 * t₀) ≤ Real.exp (r ^ 2 / (16 * t₀)) := by
    linarith [Real.add_one_le_exp (r ^ 2 / (16 * t₀))]
  have hsplit : Real.exp (-r ^ 2 / (8 * t₀)) =
      Real.exp (-r ^ 2 / (16 * t₀)) * Real.exp (-(r ^ 2 / (16 * t₀))) := by
    rw [← Real.exp_add]; congr 1; ring
  have hle1 : Real.exp (-(r ^ 2 / (16 * t₀))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have h2 : r ^ 2 * Real.exp (-(r ^ 2 / (16 * t₀))) ≤ 16 * t₀ := by
    rw [Real.exp_neg]
    have hpos : 0 < Real.exp (r ^ 2 / (16 * t₀)) := Real.exp_pos _
    have hmul : r ^ 2 ≤ (16 * t₀) * Real.exp (r ^ 2 / (16 * t₀)) := by
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < 16 * t₀)).mp hexp_u
      linarith
    calc r ^ 2 * (Real.exp (r ^ 2 / (16 * t₀)))⁻¹
        = r ^ 2 / Real.exp (r ^ 2 / (16 * t₀)) := div_eq_mul_inv _ _
      _ ≤ 16 * t₀ := (div_le_iff₀ hpos).mpr (by linarith)
  have h1 : r * Real.exp (-(r ^ 2 / (16 * t₀))) ≤ 1 + 16 * t₀ := by
    by_cases hr1 : r ≤ 1
    · nlinarith [Real.exp_pos (-(r ^ 2 / (16 * t₀)))]
    · push Not at hr1
      have hrr : r ≤ r ^ 2 := by nlinarith
      nlinarith [Real.exp_pos (-(r ^ 2 / (16 * t₀)))]
  refine ⟨?_, ?_, ?_⟩
  · rw [hsplit]; nlinarith [Real.exp_pos (-r ^ 2 / (16 * t₀))]
  · rw [hsplit]; nlinarith [Real.exp_pos (-r ^ 2 / (16 * t₀))]
  · rw [hsplit]; nlinarith [Real.exp_pos (-r ^ 2 / (16 * t₀))]

/-- Uniform Gaussian envelope for `K₁`, `K₁_da`, `K₁_daa`, `K₁_dt` near `(t₀, a₀)` with `t₀ > 0`. -/
private lemma K₁_local_bounds {t₀ a₀ : ℝ} (ht₀ : 0 < t₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Set.Ioo (t₀ / 2) (2 * t₀), ∀ a ∈ Metric.ball a₀ 1, ∀ b : ℝ,
      |K₁ t a b| ≤ C * Real.exp (-(b - a₀) ^ 2 / (16 * t₀)) ∧
      |K₁_da t a b| ≤ C * Real.exp (-(b - a₀) ^ 2 / (16 * t₀)) ∧
      |K₁_daa t a b| ≤ C * Real.exp (-(b - a₀) ^ 2 / (16 * t₀)) ∧
      |K₁_dt t a b| ≤ C * Real.exp (-(b - a₀) ^ 2 / (16 * t₀)) := by
  let M₀ : ℝ := (√(Real.pi * t₀))⁻¹ * Real.exp (1 / (4 * t₀))
  let B0 : ℝ := M₀
  let B1 : ℝ := (2 / t₀) * M₀ * (1 + (1 + 16 * t₀))
  let B2 : ℝ := M₀ * ((4 / t₀ ^ 2) * (2 + 2 * (16 * t₀)) + 2 / t₀)
  let C : ℝ := max (max B0 B1) B2 + 1
  have hM₀_pos : 0 < M₀ := by positivity
  refine ⟨C, by positivity, fun t ht a ha b => ?_⟩
  have ht_pos : 0 < t := by linarith [ht.1]
  have ha_lt : |a - a₀| < 1 := by simpa [Metric.mem_ball, Real.dist_eq] using ha
  have ha_sq : (a - a₀) ^ 2 ≤ 1 := by nlinarith [abs_lt.mp ha_lt]
  have htri : (b - a₀) ^ 2 ≤ 2 * (b - a) ^ 2 + 2 * (a - a₀) ^ 2 := by nlinarith [sq_nonneg ((b - a) - (a - a₀))]
  have hexp_le : Real.exp (-(b - a) ^ 2 / (2 * t)) ≤
      Real.exp (1 / (4 * t₀)) * Real.exp (-(b - a₀) ^ 2 / (8 * t₀)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : (b - a₀) ^ 2 / 2 - 1 ≤ (b - a) ^ 2 := by linarith
    have h2 : (b - a) ^ 2 / (2 * t) ≥ ((b - a₀) ^ 2 / 2 - 1) / (4 * t₀) := by
      have h4 : 2 * t ≤ 4 * t₀ := by linarith [ht.2]
      by_cases hnn : 0 ≤ (b - a₀) ^ 2 / 2 - 1
      · calc ((b - a₀) ^ 2 / 2 - 1) / (4 * t₀)
            ≤ ((b - a₀) ^ 2 / 2 - 1) / (2 * t) := div_le_div_of_nonneg_left hnn (by positivity) h4
          _ ≤ (b - a) ^ 2 / (2 * t) := div_le_div_of_nonneg_right h1 (by positivity)
      · push Not at hnn
        have : ((b - a₀) ^ 2 / 2 - 1) / (4 * t₀) < 0 := div_neg_of_neg_of_pos hnn (by positivity)
        have : 0 ≤ (b - a) ^ 2 / (2 * t) := by positivity
        linarith
    have hid : 1 / (4 * t₀) + -(b - a₀) ^ 2 / (8 * t₀) = -(((b - a₀) ^ 2 / 2 - 1) / (4 * t₀)) := by
      field_simp [ne_of_gt ht₀]; ring
    rw [hid, neg_div]
    linarith
  have hsqrt_le : (√(2 * Real.pi * t))⁻¹ ≤ (√(Real.pi * t₀))⁻¹ := by
    apply inv_anti₀ (Real.sqrt_pos.mpr (by positivity))
    exact Real.sqrt_le_sqrt (by nlinarith [ht.1, Real.pi_pos])
  have hK_le : K₁ t a b ≤ M₀ * Real.exp (-(b - a₀) ^ 2 / (8 * t₀)) := by
    unfold K₁
    have hpos1 := Real.exp_pos (-(b - a) ^ 2 / (2 * t))
    have hpos2 : 0 < (√(Real.pi * t₀))⁻¹ := by positivity
    calc (√(2 * Real.pi * t))⁻¹ * Real.exp (-(b - a) ^ 2 / (2 * t))
        ≤ (√(Real.pi * t₀))⁻¹ * Real.exp (-(b - a) ^ 2 / (2 * t)) :=
          mul_le_mul_of_nonneg_right hsqrt_le (le_of_lt hpos1)
      _ ≤ (√(Real.pi * t₀))⁻¹ * (Real.exp (1 / (4 * t₀)) * Real.exp (-(b - a₀) ^ 2 / (8 * t₀))) :=
          mul_le_mul_of_nonneg_left hexp_le (le_of_lt hpos2)
      _ = M₀ * Real.exp (-(b - a₀) ^ 2 / (8 * t₀)) := by dsimp [M₀]; ring
  set r := |b - a₀|
  have hr : 0 ≤ r := abs_nonneg _
  have hr_sq : r ^ 2 = (b - a₀) ^ 2 := sq_abs _
  have ⟨hb0, hb1, hb2⟩ := exp_poly_bound ht₀ hr
  rw [hr_sq] at hb0 hb1 hb2
  have hba : |b - a| ≤ r + 1 := by
    have : b - a = (b - a₀) - (a - a₀) := by ring
    rw [this]
    calc |(b - a₀) - (a - a₀)| ≤ |b - a₀| + |a - a₀| := abs_sub _ _
      _ ≤ r + 1 := by linarith
  have hba_sq : (b - a) ^ 2 ≤ 2 * (b - a₀) ^ 2 + 2 := by
    nlinarith [sq_nonneg ((b - a₀) + (a - a₀)), ha_sq]
  have ht_inv : t⁻¹ ≤ 2 / t₀ := by
    rw [inv_le_iff_one_le_mul₀ ht_pos]
    have : t₀ / 2 < t := ht.1
    calc (1 : ℝ) = (2 / t₀) * (t₀ / 2) := by field_simp [ne_of_gt ht₀]
      _ ≤ (2 / t₀) * t := mul_le_mul_of_nonneg_left (le_of_lt this) (by positivity)
  have hC0 : B0 ≤ C := by dsimp [C]; linarith [le_max_left B0 B1, le_max_left (max B0 B1) B2]
  have hC1 : B1 ≤ C := by dsimp [C]; linarith [le_max_right B0 B1, le_max_left (max B0 B1) B2]
  have hC2 : B2 ≤ C := by dsimp [C]; linarith [le_max_right (max B0 B1) B2]
  have hK_pos : 0 < K₁ t a b := K₁_pos ht_pos a b
  have hexp_pos := Real.exp_pos (-(b - a₀) ^ 2 / (16 * t₀))
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [abs_of_pos hK_pos]
    calc K₁ t a b ≤ B0 * Real.exp (-(b - a₀) ^ 2 / (8 * t₀)) := hK_le
      _ ≤ B0 * Real.exp (-(b - a₀) ^ 2 / (16 * t₀)) := mul_le_mul_of_nonneg_left hb0 (by positivity)
      _ ≤ C * Real.exp (-(b - a₀) ^ 2 / (16 * t₀)) := mul_le_mul_of_nonneg_right hC0 (le_of_lt hexp_pos)
  · unfold K₁_da
    rw [abs_mul, abs_div, abs_of_pos ht_pos, abs_of_pos hK_pos, div_eq_mul_inv]
    calc |b - a| * t⁻¹ * K₁ t a b
        ≤ (r + 1) * (2 / t₀) * (M₀ * Real.exp (-(b - a₀) ^ 2 / (8 * t₀))) := by
          gcongr
      _ = (2 / t₀) * M₀ * (r * Real.exp (-(b - a₀) ^ 2 / (8 * t₀)) + Real.exp (-(b - a₀) ^ 2 / (8 * t₀))) := by ring
      _ ≤ (2 / t₀) * M₀ * ((1 + 16 * t₀) * Real.exp (-(b - a₀) ^ 2 / (16 * t₀)) +
            Real.exp (-(b - a₀) ^ 2 / (16 * t₀))) := by
          gcongr
      _ = B1 * Real.exp (-(b - a₀) ^ 2 / (16 * t₀)) := by dsimp [B1]; ring
      _ ≤ C * Real.exp (-(b - a₀) ^ 2 / (16 * t₀)) := mul_le_mul_of_nonneg_right hC1 (le_of_lt hexp_pos)
  · unfold K₁_daa
    rw [abs_mul, abs_of_pos hK_pos]
    have hcoeff : |((b - a) / t) ^ 2 - 1 / t| ≤ (4 / t₀ ^ 2) * (2 * (b - a₀) ^ 2 + 2) + 2 / t₀ := by
      have h1 : |((b - a) / t) ^ 2 - 1 / t| ≤ ((b - a) / t) ^ 2 + 1 / t := by
        calc |((b - a) / t) ^ 2 - 1 / t| ≤ |((b - a) / t) ^ 2| + |1 / t| := abs_sub _ _
          _ = ((b - a) / t) ^ 2 + 1 / t := by rw [abs_of_nonneg (sq_nonneg _), abs_of_pos (by positivity)]
      have h2 : ((b - a) / t) ^ 2 ≤ (4 / t₀ ^ 2) * (2 * (b - a₀) ^ 2 + 2) := by
        rw [div_pow, div_eq_mul_inv]
        have ht2 : (t ^ 2)⁻¹ ≤ 4 / t₀ ^ 2 := by
          have : (t⁻¹) ^ 2 ≤ (2 / t₀) ^ 2 := pow_le_pow_left₀ (by positivity) ht_inv 2
          convert this using 1 <;> ring
        calc (b - a) ^ 2 * (t ^ 2)⁻¹ ≤ (2 * (b - a₀) ^ 2 + 2) * (4 / t₀ ^ 2) := by gcongr
          _ = (4 / t₀ ^ 2) * (2 * (b - a₀) ^ 2 + 2) := by ring
      have h3 : 1 / t ≤ 2 / t₀ := by simpa [one_div] using ht_inv
      linarith
    calc |((b - a) / t) ^ 2 - 1 / t| * K₁ t a b
        ≤ ((4 / t₀ ^ 2) * (2 * (b - a₀) ^ 2 + 2) + 2 / t₀) * (M₀ * Real.exp (-(b - a₀) ^ 2 / (8 * t₀))) := by
          gcongr
      _ = M₀ * ((4 / t₀ ^ 2) * (2 * ((b - a₀) ^ 2 * Real.exp (-(b - a₀) ^ 2 / (8 * t₀))) +
            2 * Real.exp (-(b - a₀) ^ 2 / (8 * t₀))) + (2 / t₀) * Real.exp (-(b - a₀) ^ 2 / (8 * t₀))) := by ring
      _ ≤ M₀ * ((4 / t₀ ^ 2) * (2 * ((16 * t₀) * Real.exp (-(b - a₀) ^ 2 / (16 * t₀))) +
            2 * Real.exp (-(b - a₀) ^ 2 / (16 * t₀))) + (2 / t₀) * Real.exp (-(b - a₀) ^ 2 / (16 * t₀))) := by
          gcongr
      _ = B2 * Real.exp (-(b - a₀) ^ 2 / (16 * t₀)) := by dsimp [B2]; ring
      _ ≤ C * Real.exp (-(b - a₀) ^ 2 / (16 * t₀)) := mul_le_mul_of_nonneg_right hC2 (le_of_lt hexp_pos)
  · unfold K₁_dt
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have hdaa : |K₁_daa t a b| ≤ C * Real.exp (-(b - a₀) ^ 2 / (16 * t₀)) := by
      unfold K₁_daa
      rw [abs_mul, abs_of_pos hK_pos]
      have hcoeff : |((b - a) / t) ^ 2 - 1 / t| ≤ (4 / t₀ ^ 2) * (2 * (b - a₀) ^ 2 + 2) + 2 / t₀ := by
        have h1 : |((b - a) / t) ^ 2 - 1 / t| ≤ ((b - a) / t) ^ 2 + 1 / t := by
          calc |((b - a) / t) ^ 2 - 1 / t| ≤ |((b - a) / t) ^ 2| + |1 / t| := abs_sub _ _
            _ = ((b - a) / t) ^ 2 + 1 / t := by rw [abs_of_nonneg (sq_nonneg _), abs_of_pos (by positivity)]
        have h2 : ((b - a) / t) ^ 2 ≤ (4 / t₀ ^ 2) * (2 * (b - a₀) ^ 2 + 2) := by
          rw [div_pow, div_eq_mul_inv]
          have ht2 : (t ^ 2)⁻¹ ≤ 4 / t₀ ^ 2 := by
            have : (t⁻¹) ^ 2 ≤ (2 / t₀) ^ 2 := pow_le_pow_left₀ (by positivity) ht_inv 2
            convert this using 1 <;> ring
          calc (b - a) ^ 2 * (t ^ 2)⁻¹ ≤ (2 * (b - a₀) ^ 2 + 2) * (4 / t₀ ^ 2) := by gcongr
            _ = (4 / t₀ ^ 2) * (2 * (b - a₀) ^ 2 + 2) := by ring
        have h3 : 1 / t ≤ 2 / t₀ := by simpa [one_div] using ht_inv
        linarith
      calc |((b - a) / t) ^ 2 - 1 / t| * K₁ t a b
          ≤ ((4 / t₀ ^ 2) * (2 * (b - a₀) ^ 2 + 2) + 2 / t₀) * (M₀ * Real.exp (-(b - a₀) ^ 2 / (8 * t₀))) := by
            gcongr
        _ = M₀ * ((4 / t₀ ^ 2) * (2 * ((b - a₀) ^ 2 * Real.exp (-(b - a₀) ^ 2 / (8 * t₀))) +
              2 * Real.exp (-(b - a₀) ^ 2 / (8 * t₀))) + (2 / t₀) * Real.exp (-(b - a₀) ^ 2 / (8 * t₀))) := by ring
        _ ≤ M₀ * ((4 / t₀ ^ 2) * (2 * ((16 * t₀) * Real.exp (-(b - a₀) ^ 2 / (16 * t₀))) +
              2 * Real.exp (-(b - a₀) ^ 2 / (16 * t₀))) + (2 / t₀) * Real.exp (-(b - a₀) ^ 2 / (16 * t₀))) := by
            gcongr
        _ = B2 * Real.exp (-(b - a₀) ^ 2 / (16 * t₀)) := by dsimp [B2]; ring
        _ ≤ C * Real.exp (-(b - a₀) ^ 2 / (16 * t₀)) := mul_le_mul_of_nonneg_right hC2 (le_of_lt hexp_pos)
    linarith [abs_nonneg (K₁_daa t a b)]

/-- Product of 1D integrable functions on `Fin n → ℝ` is integrable against `volume`. -/
private lemma integrable_fin_prod {n : ℕ} (f : Fin n → ℝ → ℝ) (hf : ∀ i, Integrable (f i) volume) :
    Integrable (fun y : Fin n → ℝ => ∏ i : Fin n, f i (y i)) volume := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    exact integrable_const 1
  | succ n ih =>
    have hmp := MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have hprod : Integrable (fun p : ℝ × (Fin n → ℝ) => f 0 p.1 * ∏ j : Fin n, f j.succ (p.2 j))
        (volume.prod volume) :=
      (hf 0).mul_prod (ih (fun j => f j.succ) (fun j => hf j.succ))
    have hcomp : Integrable
        ((fun p : ℝ × (Fin n → ℝ) => f 0 p.1 * ∏ j : Fin n, f j.succ (p.2 j)) ∘
          MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0) volume :=
      (hmp.integrable_comp_emb (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).measurableEmbedding).mpr hprod
    refine hcomp.congr (Eventually.of_forall fun y => ?_)
    change f 0 (y 0) * ∏ j : Fin n, f j.succ (Fin.removeNth 0 y j) = ∏ i : Fin (n + 1), f i (y i)
    rw [Fin.prod_univ_succ]
    rfl

/-- Product of `withDensity` measures on `Fin n → ℝ`. -/
private lemma pi_withDensity_eq {n : ℕ} (d : Fin n → ℝ → ℝ≥0∞)
    (hd : ∀ i, Measurable (d i))
    (hfin : ∀ i, IsProbabilityMeasure (volume.withDensity (d i))) :
    Measure.pi (fun i : Fin n => volume.withDensity (d i)) =
      volume.withDensity (fun y : Fin n → ℝ => ∏ i : Fin n, d i (y i)) := by
  haveI : ∀ i, IsProbabilityMeasure (volume.withDensity (d i)) := hfin
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  have hpi : ∀ (m : ℕ) (g : Fin m → ℝ → ℝ≥0∞) (hg : ∀ i, Measurable (g i))
      (t : Fin m → Set ℝ) (ht : ∀ i, MeasurableSet (t i)),
      ∫⁻ y in Set.univ.pi t, ∏ i : Fin m, g i (y i) ∂(volume : Measure (Fin m → ℝ)) =
        ∏ i : Fin m, ∫⁻ x in t i, g i x ∂volume := by
    intro m
    induction m with
    | zero =>
      intro g _ t _
      have hset : (Set.univ.pi t : Set (Fin 0 → ℝ)) = Set.univ := by ext y; simp
      rw [hset, setLIntegral_univ]
      simp only [Finset.univ_eq_empty, Finset.prod_empty, lintegral_const, one_mul]
      change (Measure.pi fun _ : Fin 0 => (volume : Measure ℝ)) Set.univ = 1
      rw [Measure.pi_univ]
      simp
    | succ m ihm =>
      intro g hg t ht
      have hmp := MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
      have himg : e ⁻¹' (t 0 ×ˢ Set.univ.pi (fun j : Fin m => t j.succ)) = Set.univ.pi t := by
        ext y
        simp only [Set.mem_preimage, Set.mem_prod, Set.mem_pi, Set.mem_univ, forall_true_left,
          e, MeasurableEquiv.piFinSuccAbove, Fin.forall_fin_succ]
        rfl
      have hstep : ∫⁻ y in Set.univ.pi t,
          ∏ i : Fin (m + 1), g i (y i) ∂volume =
          ∫⁻ p in t 0 ×ˢ Set.univ.pi (fun j : Fin m => t j.succ),
            g 0 p.1 * ∏ j : Fin m, g j.succ (p.2 j) ∂(volume.prod volume) := by
        rw [← himg]
        have h1 := hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding
          (f := fun p : ℝ × (Fin m → ℝ) => g 0 p.1 * ∏ j : Fin m, g j.succ (p.2 j))
          (s := t 0 ×ˢ Set.univ.pi (fun j : Fin m => t j.succ))
        rw [← Measure.volume_eq_prod, ← h1]
        refine setLIntegral_congr_fun (by rw [himg]; exact MeasurableSet.univ_pi ht) fun y _ => ?_
        rw [Fin.prod_univ_succ]
        rfl
      rw [hstep, ← Measure.prod_restrict]
      rw [lintegral_prod_mul (f := g 0) (g := fun y : Fin m → ℝ => ∏ j : Fin m, g j.succ (y j))
        (hg 0).aemeasurable
        (Finset.measurable_prod Finset.univ fun (j : Fin m) _ =>
          (hg j.succ).comp (measurable_pi_apply j)).aemeasurable]
      rw [ihm (fun j => g j.succ) (fun j => hg j.succ) (fun j => t j.succ) (fun j => ht j.succ),
        Fin.prod_univ_succ]
  rw [hpi n d hd s hs]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i)]

private noncomputable def K {n : ℕ} (t : ℝ) (x y : Fin n → ℝ) : ℝ :=
  ∏ i : Fin n, K₁ t (x i) (y i)

private noncomputable def H {n : ℕ} (t : ℝ) (g : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  if t ≤ 0 then g x else ∫ z, g (x + √t • z) ∂(γ n)

private lemma H_zero {n : ℕ} (g : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : H 0 g x = g x := by
  simp [H]

private lemma H_pos_eq_integral_K {n : ℕ} {t : ℝ} (ht : 0 < t) {g : (Fin n → ℝ) → ℝ}
    (hg_meas : Measurable g) (x : Fin n → ℝ) :
    H t g x = ∫ y, g y * K t x y ∂volume := by
  have hnot : ¬ t ≤ 0 := not_le.mpr ht
  simp only [H, if_neg hnot]
  let φ_aff : (Fin n → ℝ) → (Fin n → ℝ) := fun z i => x i + √t * z i
  have hφ_eq : (fun z => g (x + √t • z)) = fun z => g (φ_aff z) :=
    funext fun z => congrArg g (by ext i; simp [φ_aff])
  rw [hφ_eq]
  have hmap : Measure.map φ_aff (γ n) =
      Measure.pi (fun i : Fin n => gaussianReal (x i) (Real.toNNReal t)) := by
    have h1 : φ_aff = fun z i => (fun s => x i + √t * s) (z i) := rfl
    rw [h1, γ, Measure.pi_map_pi (f := fun i s => x i + √t * s)
      (fun i => (continuous_const.add (continuous_const.mul continuous_id)).measurable.aemeasurable)]
    congr 1; funext i
    have hcomp : (fun s : ℝ => x i + √t * s) = (fun s => x i + s) ∘ (fun s => √t * s) := rfl
    rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
      gaussianReal_map_const_mul, gaussianReal_map_const_add]
    congr 1
    · ring
    · ext; simp [Real.sq_sqrt (le_of_lt ht), Real.coe_toNNReal t (le_of_lt ht)]
  have hwd : Measure.pi (fun i : Fin n => gaussianReal (x i) (Real.toNNReal t)) =
      volume.withDensity (fun y => ∏ i : Fin n, gaussianPDF (x i) (Real.toNNReal t) (y i)) := by
    have hne : Real.toNNReal t ≠ 0 := by
      intro h0
      have := congrArg (fun v : ℝ≥0 => (v : ℝ)) h0
      simp [Real.coe_toNNReal t (le_of_lt ht)] at this
      linarith
    have h_eq : (fun i : Fin n => gaussianReal (x i) (Real.toNNReal t)) =
        fun i : Fin n => volume.withDensity (gaussianPDF (x i) (Real.toNNReal t)) := by
      funext i; exact gaussianReal_of_var_ne_zero (x i) hne
    rw [h_eq]
    refine pi_withDensity_eq _ (fun i => measurable_gaussianPDF _ _) fun i => ?_
    rw [← gaussianReal_of_var_ne_zero (x i) hne]
    infer_instance
  have hInt_map : ∫ z, g (φ_aff z) ∂(γ n) = ∫ y, g y ∂(Measure.map φ_aff (γ n)) := by
    symm
    exact integral_map (Measurable.aemeasurable (measurable_pi_lambda _ fun i => by fun_prop))
      hg_meas.aestronglyMeasurable
  rw [hInt_map, hmap, hwd, integral_withDensity_eq_integral_toReal_smul]
  · refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    rw [ENNReal.toReal_prod, smul_eq_mul, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [toReal_gaussianPDF, K₁_eq_gaussianPDFReal ht]
  · exact Finset.measurable_prod _ fun i _ => (measurable_gaussianPDF _ _).comp (measurable_pi_apply i)
  · exact Eventually.of_forall fun y => ENNReal.prod_lt_top fun i _ => gaussianPDF_lt_top

/-! ### Part 3: Derivatives of `H`, Borell's PDE, and functional Ehrhard inequality -/

private noncomputable def K_dx {n : ℕ} (t : ℝ) (x y : Fin n → ℝ) (i : Fin n) : ℝ :=
  K₁_da t (x i) (y i) * ∏ j ∈ Finset.univ.erase i, K₁ t (x j) (y j)

private noncomputable def K_dxx {n : ℕ} (t : ℝ) (x y : Fin n → ℝ) (i : Fin n) : ℝ :=
  K₁_daa t (x i) (y i) * ∏ j ∈ Finset.univ.erase i, K₁ t (x j) (y j)

private noncomputable def K_dt {n : ℕ} (t : ℝ) (x y : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, K₁_dt t (x i) (y i) * ∏ j ∈ Finset.univ.erase i, K₁ t (x j) (y j)

private lemma K_dt_eq_half_sum_dxx {n : ℕ} (t : ℝ) (x y : Fin n → ℝ) :
    K_dt t x y = (1 / 2) * ∑ i : Fin n, K_dxx t x y i := by
  simp only [K_dt, K_dxx, K₁_dt, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

private lemma integrable_exp_shift_sq (t₀ a₀ : ℝ) (ht₀ : 0 < t₀) :
    Integrable (fun b : ℝ => Real.exp (-(b - a₀) ^ 2 / (16 * t₀))) volume := by
  have hv : Real.toNNReal (8 * t₀) ≠ 0 := by
    intro h0
    have := congrArg (fun v : ℝ≥0 => (v : ℝ)) h0
    simp [Real.coe_toNNReal (8 * t₀) (by positivity)] at this
    linarith
  have h1 := integrable_gaussianPDFReal a₀ (Real.toNNReal (8 * t₀))
  have hmul := h1.const_mul (√(2 * Real.pi * (8 * t₀)))
  refine hmul.congr (Eventually.of_forall fun b => ?_)
  simp only [gaussianPDFReal_def, Real.coe_toNNReal (8 * t₀) (by positivity)]
  have hpos : √(2 * Real.pi * (8 * t₀)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  field_simp [hpos]
  congr 1; ring

private lemma H_derivs_and_heat_eq {n : ℕ} {g : (Fin n → ℝ) → ℝ}
    (hg_meas : Measurable g) (hg_bdd : ∀ y, |g y| ≤ 1)
    {t₀ : ℝ} (ht₀ : 0 < t₀) (x₀ : Fin n → ℝ) :
    HasDerivAt (fun t => H t g x₀) (∫ y, g y * K_dt t₀ x₀ y ∂volume) t₀ ∧
    (∀ i : Fin n,
      HasDerivAt (fun s => H t₀ g (Function.update x₀ i s))
        (∫ y, g y * K_dx t₀ x₀ y i ∂volume) (x₀ i) ∧
      HasDerivAt (fun s => ∫ y, g y * K_dx t₀ (Function.update x₀ i s) y i ∂volume)
        (∫ y, g y * K_dxx t₀ x₀ y i ∂volume) (x₀ i)) ∧
    (∫ y, g y * K_dt t₀ x₀ y ∂volume) =
      (1 / 2) * ∑ i : Fin n, ∫ y, g y * K_dxx t₀ x₀ y i ∂volume := by
  -- Choose uniform envelope constant `C` across all coordinates `i : Fin n`
  choose Ci hCi_pos hCi using fun i : Fin n => K₁_local_bounds (a₀ := x₀ i) ht₀
  let M : ℝ := 1 + ∑ i : Fin n, Ci i
  have hCi_le : ∀ i : Fin n, Ci i ≤ M := fun i => by
    have hle := Finset.single_le_sum (fun j _ => le_of_lt (hCi_pos j)) (Finset.mem_univ i)
    dsimp [M]; linarith
  have hM_pos : 0 < M := by
    have hnn : 0 ≤ ∑ i : Fin n, Ci i := Finset.sum_nonneg fun j _ => le_of_lt (hCi_pos j)
    dsimp [M]; linarith
  let env : (Fin n → ℝ) → ℝ := fun y => ∏ i : Fin n, Real.exp (-(y i - x₀ i) ^ 2 / (16 * t₀))
  have henv_int : Integrable env volume :=
    integrable_fin_prod (fun i b => Real.exp (-(b - x₀ i) ^ 2 / (16 * t₀)))
      fun i => integrable_exp_shift_sq t₀ (x₀ i) ht₀
  have hK1_M : ∀ (i : Fin n) (t : ℝ), t ∈ Set.Ioo (t₀ / 2) (2 * t₀) →
      ∀ a ∈ Metric.ball (x₀ i) 1, ∀ b : ℝ,
        |K₁ t a b| ≤ M * Real.exp (-(b - x₀ i) ^ 2 / (16 * t₀)) ∧
        |K₁_da t a b| ≤ M * Real.exp (-(b - x₀ i) ^ 2 / (16 * t₀)) ∧
        |K₁_daa t a b| ≤ M * Real.exp (-(b - x₀ i) ^ 2 / (16 * t₀)) ∧
        |K₁_dt t a b| ≤ M * Real.exp (-(b - x₀ i) ^ 2 / (16 * t₀)) := by
    intro i t ht a ha b
    have ⟨h1, h2, h3, h4⟩ := hCi i t ht a ha b
    have hexp_nn : 0 ≤ Real.exp (-(b - x₀ i) ^ 2 / (16 * t₀)) := le_of_lt (Real.exp_pos _)
    have hle := mul_le_mul_of_nonneg_right (hCi_le i) hexp_nn
    exact ⟨h1.trans hle, h2.trans hle, h3.trans hle, h4.trans hle⟩
  have hIoo_mem : Set.Ioo (t₀ / 2) (2 * t₀) ∈ 𝓝 t₀ :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have ht₀_mem : t₀ ∈ Set.Ioo (t₀ / 2) (2 * t₀) := ⟨by linarith, by linarith⟩
  have hmeas_K₁ : ∀ (t : ℝ) (a : ℝ), Measurable (fun b => K₁ t a b) := fun t a => by
    unfold K₁; fun_prop
  have hmeas_K₁_da : ∀ (t : ℝ) (a : ℝ), Measurable (fun b => K₁_da t a b) := fun t a => by
    unfold K₁_da K₁; fun_prop
  have hmeas_K₁_daa : ∀ (t : ℝ) (a : ℝ), Measurable (fun b => K₁_daa t a b) := fun t a => by
    unfold K₁_daa K₁; fun_prop
  have hmeas_K₁_dt : ∀ (t : ℝ) (a : ℝ), Measurable (fun b => K₁_dt t a b) := fun t a => by
    unfold K₁_dt K₁_daa K₁; fun_prop
  -- Bound for `g y * K t x₀ y`
  have hint_gK : ∀ t ∈ Set.Ioo (t₀ / 2) (2 * t₀),
      Integrable (fun y => g y * K t x₀ y) volume := by
    intro t ht
    have hmeas : Measurable (fun y => g y * K t x₀ y) :=
      hg_meas.mul (Finset.measurable_prod _ fun i _ => (hmeas_K₁ t (x₀ i)).comp (measurable_pi_apply i))
    refine (henv_int.const_mul (M ^ n)).mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have hK_le : |K t x₀ y| ≤ M ^ n * env y := by
      unfold K env
      rw [Finset.abs_prod]
      calc ∏ i : Fin n, |K₁ t (x₀ i) (y i)|
          ≤ ∏ i : Fin n, (M * Real.exp (-(y i - x₀ i) ^ 2 / (16 * t₀))) :=
            Finset.prod_le_prod (fun i _ => abs_nonneg _)
              fun i _ => (hK1_M i t ht (x₀ i) (Metric.mem_ball_self zero_lt_one) (y i)).1
        _ = M ^ n * ∏ i : Fin n, Real.exp (-(y i - x₀ i) ^ 2 / (16 * t₀)) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hMnn : 0 ≤ M ^ n * env y := mul_nonneg (by positivity) (Finset.prod_nonneg fun i _ => le_of_lt (Real.exp_pos _))
    calc |g y| * |K t x₀ y| ≤ 1 * (M ^ n * env y) := mul_le_mul (hg_bdd y) hK_le (abs_nonneg _) zero_le_one
      _ = M ^ n * env y := one_mul _
  -- Bound for `g y * K_dxx t₀ x₀ y i`
  have hint_gKdxx : ∀ i : Fin n, Integrable (fun y => g y * K_dxx t₀ x₀ y i) volume := by
    intro i
    have hmeas : Measurable (fun y => g y * K_dxx t₀ x₀ y i) :=
      hg_meas.mul (((hmeas_K₁_daa t₀ (x₀ i)).comp (measurable_pi_apply i)).mul
        (Finset.measurable_prod _ fun j _ => (hmeas_K₁ t₀ (x₀ j)).comp (measurable_pi_apply j)))
    refine (henv_int.const_mul (M ^ n)).mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have hprod_le : |K_dxx t₀ x₀ y i| ≤ M ^ n * env y := by
      unfold K_dxx env
      rw [abs_mul, Finset.abs_prod]
      have h1 := (hK1_M i t₀ ht₀_mem (x₀ i) (Metric.mem_ball_self zero_lt_one) (y i)).2.2.1
      have h2 : ∏ j ∈ Finset.univ.erase i, |K₁ t₀ (x₀ j) (y j)| ≤
          ∏ j ∈ Finset.univ.erase i, (M * Real.exp (-(y j - x₀ j) ^ 2 / (16 * t₀))) :=
        Finset.prod_le_prod (fun j _ => abs_nonneg _)
          fun j _ => (hK1_M j t₀ ht₀_mem (x₀ j) (Metric.mem_ball_self zero_lt_one) (y j)).1
      calc |K₁_daa t₀ (x₀ i) (y i)| * ∏ j ∈ Finset.univ.erase i, |K₁ t₀ (x₀ j) (y j)|
          ≤ (M * Real.exp (-(y i - x₀ i) ^ 2 / (16 * t₀))) *
              ∏ j ∈ Finset.univ.erase i, (M * Real.exp (-(y j - x₀ j) ^ 2 / (16 * t₀))) :=
            mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => abs_nonneg _) (by positivity)
        _ = ∏ j : Fin n, (M * Real.exp (-(y j - x₀ j) ^ 2 / (16 * t₀))) :=
            Finset.mul_prod_erase Finset.univ (fun j => M * Real.exp (-(y j - x₀ j) ^ 2 / (16 * t₀))) (Finset.mem_univ i)
        _ = M ^ n * ∏ j : Fin n, Real.exp (-(y j - x₀ j) ^ 2 / (16 * t₀)) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc |g y| * |K_dxx t₀ x₀ y i| ≤ 1 * (M ^ n * env y) := mul_le_mul (hg_bdd y) hprod_le (abs_nonneg _) zero_le_one
      _ = M ^ n * env y := one_mul _
  -- 1. Time derivative of `H t g x₀` at `t₀`
  have hdt : HasDerivAt (fun t => H t g x₀) (∫ y, g y * K_dt t₀ x₀ y ∂volume) t₀ := by
    have heq : (fun t => H t g x₀) =ᶠ[𝓝 t₀] (fun t => ∫ y, g y * K t x₀ y ∂volume) := by
      filter_upwards [hIoo_mem] with t ht
      exact H_pos_eq_integral_K (by linarith [ht.1]) hg_meas x₀
    rw [heq.hasDerivAt_iff]
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun t y => g y * K t x₀ y) (F' := fun t y => g y * K_dt t x₀ y)
      (bound := fun y => ((n : ℝ) * M ^ n) * env y) hIoo_mem
      (Eventually.of_forall fun t =>
        (hg_meas.mul (Finset.measurable_prod _ fun i _ => (hmeas_K₁ t (x₀ i)).comp (measurable_pi_apply i))).aestronglyMeasurable)
      (hint_gK t₀ ht₀_mem)
      (hg_meas.mul (Finset.measurable_sum _ fun i _ =>
        ((hmeas_K₁_dt t₀ (x₀ i)).comp (measurable_pi_apply i)).mul
          (Finset.measurable_prod _ fun j _ => (hmeas_K₁ t₀ (x₀ j)).comp (measurable_pi_apply j)))).aestronglyMeasurable
      (Eventually.of_forall fun y t ht => ?_)
      (henv_int.const_mul ((n : ℝ) * M ^ n))
      (Eventually.of_forall fun y t ht => ?_)).2
    · rw [Real.norm_eq_abs, abs_mul]
      have hKdt : |K_dt t x₀ y| ≤ (n : ℝ) * M ^ n * env y := by
        unfold K_dt env
        calc |∑ i : Fin n, K₁_dt t (x₀ i) (y i) * ∏ j ∈ Finset.univ.erase i, K₁ t (x₀ j) (y j)|
            ≤ ∑ i : Fin n, |K₁_dt t (x₀ i) (y i) * ∏ j ∈ Finset.univ.erase i, K₁ t (x₀ j) (y j)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : Fin n, (M ^ n * ∏ j : Fin n, Real.exp (-(y j - x₀ j) ^ 2 / (16 * t₀))) := by
              refine Finset.sum_le_sum fun i _ => ?_
              rw [abs_mul, Finset.abs_prod]
              have h1 := (hK1_M i t ht (x₀ i) (Metric.mem_ball_self zero_lt_one) (y i)).2.2.2
              have h2 : ∏ j ∈ Finset.univ.erase i, |K₁ t (x₀ j) (y j)| ≤
                  ∏ j ∈ Finset.univ.erase i, (M * Real.exp (-(y j - x₀ j) ^ 2 / (16 * t₀))) :=
                Finset.prod_le_prod (fun j _ => abs_nonneg _)
                  fun j _ => (hK1_M j t ht (x₀ j) (Metric.mem_ball_self zero_lt_one) (y j)).1
              calc |K₁_dt t (x₀ i) (y i)| * ∏ j ∈ Finset.univ.erase i, |K₁ t (x₀ j) (y j)|
                  ≤ (M * Real.exp (-(y i - x₀ i) ^ 2 / (16 * t₀))) *
                      ∏ j ∈ Finset.univ.erase i, (M * Real.exp (-(y j - x₀ j) ^ 2 / (16 * t₀))) :=
                    mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => abs_nonneg _) (by positivity)
                _ = ∏ j : Fin n, (M * Real.exp (-(y j - x₀ j) ^ 2 / (16 * t₀))) :=
                    Finset.mul_prod_erase Finset.univ (fun j => M * Real.exp (-(y j - x₀ j) ^ 2 / (16 * t₀))) (Finset.mem_univ i)
                _ = M ^ n * ∏ j : Fin n, Real.exp (-(y j - x₀ j) ^ 2 / (16 * t₀)) := by
                    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          _ = (n : ℝ) * M ^ n * ∏ j : Fin n, Real.exp (-(y j - x₀ j) ^ 2 / (16 * t₀)) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      calc |g y| * |K_dt t x₀ y| ≤ 1 * ((n : ℝ) * M ^ n * env y) := mul_le_mul (hg_bdd y) hKdt (abs_nonneg _) zero_le_one
        _ = (n : ℝ) * M ^ n * env y := one_mul _
    · have hprod : HasDerivAt (fun s => K s x₀ y) (K_dt t x₀ y) t := by
        have ht_pos : 0 < t := by linarith [ht.1]
        have h1 := HasDerivAt.finset_prod (u := Finset.univ)
          (f := fun i s => K₁ s (x₀ i) (y i))
          (f' := fun i => K₁_dt t (x₀ i) (y i))
          (x := t) (fun i _ => hasDerivAt_K₁_t ht_pos (x₀ i) (y i))
        have hfun : (∏ i ∈ Finset.univ, fun s => K₁ s (x₀ i) (y i)) = fun s => K s x₀ y := by
          ext s; simp [K, Finset.prod_apply]
        rw [hfun] at h1
        exact h1.congr_deriv (by
          unfold K_dt
          refine Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, mul_comm])
      exact hprod.const_mul (g y)
  -- 2. First and second spatial derivatives in coordinate `i`
  have hdx : ∀ i : Fin n,
      HasDerivAt (fun s => H t₀ g (Function.update x₀ i s))
        (∫ y, g y * K_dx t₀ x₀ y i ∂volume) (x₀ i) ∧
      HasDerivAt (fun s => ∫ y, g y * K_dx t₀ (Function.update x₀ i s) y i ∂volume)
        (∫ y, g y * K_dxx t₀ x₀ y i ∂volume) (x₀ i) := by
    intro i
    have hball : Metric.ball (x₀ i) 1 ∈ 𝓝 (x₀ i) := Metric.ball_mem_nhds _ zero_lt_one
    have hK_upd : ∀ s y, K t₀ (Function.update x₀ i s) y =
        K₁ t₀ s (y i) * ∏ j ∈ Finset.univ.erase i, K₁ t₀ (x₀ j) (y j) := by
      intro s y
      unfold K
      rw [← Finset.mul_prod_erase Finset.univ (fun j => K₁ t₀ (Function.update x₀ i s j) (y j)) (Finset.mem_univ i)]
      simp only [Function.update_self]
      congr 1
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    have hKdx_upd : ∀ s y, K_dx t₀ (Function.update x₀ i s) y i =
        K₁_da t₀ s (y i) * ∏ j ∈ Finset.univ.erase i, K₁ t₀ (x₀ j) (y j) := by
      intro s y
      unfold K_dx
      simp only [Function.update_self]
      congr 1
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    have hdx1 : HasDerivAt (fun s => H t₀ g (Function.update x₀ i s))
        (∫ y, g y * K_dx t₀ x₀ y i ∂volume) (x₀ i) := by
      have hfun : (fun s => H t₀ g (Function.update x₀ i s)) =
          fun s => ∫ y, g y * K t₀ (Function.update x₀ i s) y ∂volume :=
        funext fun s => H_pos_eq_integral_K ht₀ hg_meas _
      rw [hfun]
      have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (F := fun s y => g y * K t₀ (Function.update x₀ i s) y)
        (F' := fun s y => g y * K_dx t₀ (Function.update x₀ i s) y i)
        (bound := fun y => M ^ n * env y) hball
        (Eventually.of_forall fun s =>
          (hg_meas.mul (Finset.measurable_prod _ fun j _ =>
            (hmeas_K₁ t₀ (Function.update x₀ i s j)).comp (measurable_pi_apply j))).aestronglyMeasurable)
        (by simpa [Function.update_eq_self] using hint_gK t₀ ht₀_mem)
        (by
          have hmeas' : Measurable (fun y => g y * K_dx t₀ (Function.update x₀ i (x₀ i)) y i) := by
            simp only [Function.update_eq_self, K_dx]
            exact hg_meas.mul (((hmeas_K₁_da t₀ (x₀ i)).comp (measurable_pi_apply i)).mul
              (Finset.measurable_prod (Finset.univ.erase i) fun j _ => (hmeas_K₁ t₀ (x₀ j)).comp (measurable_pi_apply j)))
          exact hmeas'.aestronglyMeasurable)
        (Eventually.of_forall fun y s hs => ?_)
        (henv_int.const_mul (M ^ n))
        (Eventually.of_forall fun y s hs => ?_)
      · simpa [Function.update_eq_self] using hres.2
      · rw [Real.norm_eq_abs, abs_mul, hKdx_upd, abs_mul, Finset.abs_prod]
        have h1 := (hK1_M i t₀ ht₀_mem s hs (y i)).2.1
        have h2 : ∏ j ∈ Finset.univ.erase i, |K₁ t₀ (x₀ j) (y j)| ≤
            ∏ j ∈ Finset.univ.erase i, (M * Real.exp (-(y j - x₀ j) ^ 2 / (16 * t₀))) :=
          Finset.prod_le_prod (fun j _ => abs_nonneg _)
            fun j _ => (hK1_M j t₀ ht₀_mem (x₀ j) (Metric.mem_ball_self zero_lt_one) (y j)).1
        have hprod : |K₁_da t₀ s (y i)| * ∏ j ∈ Finset.univ.erase i, |K₁ t₀ (x₀ j) (y j)| ≤ M ^ n * env y := by
          calc |K₁_da t₀ s (y i)| * ∏ j ∈ Finset.univ.erase i, |K₁ t₀ (x₀ j) (y j)|
              ≤ (M * Real.exp (-(y i - x₀ i) ^ 2 / (16 * t₀))) *
                  ∏ j ∈ Finset.univ.erase i, (M * Real.exp (-(y j - x₀ j) ^ 2 / (16 * t₀))) :=
                mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => abs_nonneg _) (by positivity)
            _ = ∏ j : Fin n, (M * Real.exp (-(y j - x₀ j) ^ 2 / (16 * t₀))) :=
                Finset.mul_prod_erase Finset.univ (fun j => M * Real.exp (-(y j - x₀ j) ^ 2 / (16 * t₀))) (Finset.mem_univ i)
            _ = M ^ n * env y := by
                unfold env; rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        calc |g y| * (|K₁_da t₀ s (y i)| * ∏ j ∈ Finset.univ.erase i, |K₁ t₀ (x₀ j) (y j)|)
            ≤ 1 * (M ^ n * env y) := mul_le_mul (hg_bdd y) hprod (by positivity) zero_le_one
          _ = M ^ n * env y := one_mul _
      · have hfn : (fun s' => g y * K t₀ (Function.update x₀ i s') y) =
            fun s' => g y * (K₁ t₀ s' (y i) * ∏ j ∈ Finset.univ.erase i, K₁ t₀ (x₀ j) (y j)) :=
          funext fun s' => by rw [hK_upd]
        rw [hfn, hKdx_upd]
        exact ((hasDerivAt_K₁_a ht₀ s (y i)).mul_const _).const_mul (g y)
    have hint_gKdx : Integrable (fun y => g y * K_dx t₀ x₀ y i) volume := by
      have hmeas : Measurable (fun y => g y * K_dx t₀ x₀ y i) :=
        hg_meas.mul (((hmeas_K₁_da t₀ (x₀ i)).comp (measurable_pi_apply i)).mul
          (Finset.measurable_prod (Finset.univ.erase i) fun j _ => (hmeas_K₁ t₀ (x₀ j)).comp (measurable_pi_apply j)))
      refine (henv_int.const_mul (M ^ n)).mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h1 := (hK1_M i t₀ ht₀_mem (x₀ i) (Metric.mem_ball_self zero_lt_one) (y i)).2.1
      have h2 : ∏ j ∈ Finset.univ.erase i, |K₁ t₀ (x₀ j) (y j)| ≤
          ∏ j ∈ Finset.univ.erase i, (M * Real.exp (-(y j - x₀ j) ^ 2 / (16 * t₀))) :=
        Finset.prod_le_prod (fun j _ => abs_nonneg _)
          fun j _ => (hK1_M j t₀ ht₀_mem (x₀ j) (Metric.mem_ball_self zero_lt_one) (y j)).1
      have hprod : |K_dx t₀ x₀ y i| ≤ M ^ n * env y := by
        unfold K_dx env
        rw [abs_mul, Finset.abs_prod]
        calc |K₁_da t₀ (x₀ i) (y i)| * ∏ j ∈ Finset.univ.erase i, |K₁ t₀ (x₀ j) (y j)|
            ≤ (M * Real.exp (-(y i - x₀ i) ^ 2 / (16 * t₀))) *
                ∏ j ∈ Finset.univ.erase i, (M * Real.exp (-(y j - x₀ j) ^ 2 / (16 * t₀))) :=
              mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => abs_nonneg _) (by positivity)
          _ = ∏ j : Fin n, (M * Real.exp (-(y j - x₀ j) ^ 2 / (16 * t₀))) :=
              Finset.mul_prod_erase Finset.univ (fun j => M * Real.exp (-(y j - x₀ j) ^ 2 / (16 * t₀))) (Finset.mem_univ i)
          _ = M ^ n * ∏ j : Fin n, Real.exp (-(y j - x₀ j) ^ 2 / (16 * t₀)) := by
              rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      calc |g y| * |K_dx t₀ x₀ y i| ≤ 1 * (M ^ n * env y) := mul_le_mul (hg_bdd y) hprod (abs_nonneg _) zero_le_one
        _ = M ^ n * env y := one_mul _
    have hdx2 : HasDerivAt (fun s => ∫ y, g y * K_dx t₀ (Function.update x₀ i s) y i ∂volume)
        (∫ y, g y * K_dxx t₀ x₀ y i ∂volume) (x₀ i) := by
      have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (F := fun s y => g y * K_dx t₀ (Function.update x₀ i s) y i)
        (F' := fun s y => g y * K_dxx t₀ (Function.update x₀ i s) y i)
        (bound := fun y => M ^ n * env y) hball
        (Eventually.of_forall fun s => by
          have hmeas' : Measurable (fun y => g y * K_dx t₀ (Function.update x₀ i s) y i) := by
            simp_rw [hKdx_upd]
            exact hg_meas.mul (((hmeas_K₁_da t₀ s).comp (measurable_pi_apply i)).mul
              (Finset.measurable_prod (Finset.univ.erase i) fun j _ => (hmeas_K₁ t₀ (x₀ j)).comp (measurable_pi_apply j)))
          exact hmeas'.aestronglyMeasurable)
        (by simpa [Function.update_eq_self] using hint_gKdx)
        (by
          have hmeas' : Measurable (fun y => g y * K_dxx t₀ (Function.update x₀ i (x₀ i)) y i) := by
            simp only [Function.update_eq_self, K_dxx]
            exact hg_meas.mul (((hmeas_K₁_daa t₀ (x₀ i)).comp (measurable_pi_apply i)).mul
              (Finset.measurable_prod (Finset.univ.erase i) fun j _ => (hmeas_K₁ t₀ (x₀ j)).comp (measurable_pi_apply j)))
          exact hmeas'.aestronglyMeasurable)
        (Eventually.of_forall fun y s hs => ?_)
        (henv_int.const_mul (M ^ n))
        (Eventually.of_forall fun y s hs => ?_)
      · simpa [Function.update_eq_self] using hres.2
      · rw [Real.norm_eq_abs, abs_mul]
        have h1 := (hK1_M i t₀ ht₀_mem s hs (y i)).2.2.1
        have h2 : ∏ j ∈ Finset.univ.erase i, |K₁ t₀ (x₀ j) (y j)| ≤
            ∏ j ∈ Finset.univ.erase i, (M * Real.exp (-(y j - x₀ j) ^ 2 / (16 * t₀))) :=
          Finset.prod_le_prod (fun j _ => abs_nonneg _)
            fun j _ => (hK1_M j t₀ ht₀_mem (x₀ j) (Metric.mem_ball_self zero_lt_one) (y j)).1
        have hprod : |K_dxx t₀ (Function.update x₀ i s) y i| ≤ M ^ n * env y := by
          have heq : K_dxx t₀ (Function.update x₀ i s) y i =
              K₁_daa t₀ s (y i) * ∏ j ∈ Finset.univ.erase i, K₁ t₀ (x₀ j) (y j) := by
            unfold K_dxx; simp only [Function.update_self]; congr 1
            exact Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
          rw [heq, abs_mul, Finset.abs_prod]
          calc |K₁_daa t₀ s (y i)| * ∏ j ∈ Finset.univ.erase i, |K₁ t₀ (x₀ j) (y j)|
              ≤ (M * Real.exp (-(y i - x₀ i) ^ 2 / (16 * t₀))) *
                  ∏ j ∈ Finset.univ.erase i, (M * Real.exp (-(y j - x₀ j) ^ 2 / (16 * t₀))) :=
                mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => abs_nonneg _) (by positivity)
            _ = ∏ j : Fin n, (M * Real.exp (-(y j - x₀ j) ^ 2 / (16 * t₀))) :=
                Finset.mul_prod_erase Finset.univ (fun j => M * Real.exp (-(y j - x₀ j) ^ 2 / (16 * t₀))) (Finset.mem_univ i)
            _ = M ^ n * env y := by
                unfold env; rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        calc |g y| * |K_dxx t₀ (Function.update x₀ i s) y i| ≤ 1 * (M ^ n * env y) :=
              mul_le_mul (hg_bdd y) hprod (abs_nonneg _) zero_le_one
          _ = M ^ n * env y := one_mul _
      · have hfn : (fun s' => g y * K_dx t₀ (Function.update x₀ i s') y i) =
            fun s' => g y * (K₁_da t₀ s' (y i) * ∏ j ∈ Finset.univ.erase i, K₁ t₀ (x₀ j) (y j)) :=
          funext fun s' => by rw [hKdx_upd]
        have heq : K_dxx t₀ (Function.update x₀ i s) y i =
            K₁_daa t₀ s (y i) * ∏ j ∈ Finset.univ.erase i, K₁ t₀ (x₀ j) (y j) := by
          unfold K_dxx; simp only [Function.update_self]; congr 1
          exact Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
        rw [hfn, heq]
        exact ((hasDerivAt_K₁_da ht₀ s (y i)).mul_const _).const_mul (g y)
    exact ⟨hdx1, hdx2⟩
  -- 3. Heat equation identity
  have hheat : (∫ y, g y * K_dt t₀ x₀ y ∂volume) =
      (1 / 2) * ∑ i : Fin n, ∫ y, g y * K_dxx t₀ x₀ y i ∂volume := by
    rw [← integral_finset_sum Finset.univ (fun i _ => hint_gKdxx i), ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    rw [K_dt_eq_half_sum_dxx, ← mul_assoc, mul_comm (g y) (1 / 2), mul_assoc, Finset.mul_sum]
  exact ⟨hdt, hdx, hheat⟩

/-! ### Part 3b: Borell's PDE and the functional Ehrhard inequality -/

private lemma second_deriv_nonneg_of_isLocalMin {f f' : ℝ → ℝ} {x₀ f'' : ℝ}
    (hmin : IsLocalMin f x₀) (hf' : ∀ᶠ x in 𝓝 x₀, HasDerivAt f (f' x) x)
    (hf'' : HasDerivAt f' f'' x₀) : 0 ≤ f'' := by
  have hf'0 : f' x₀ = 0 := hmin.hasDerivAt_eq_zero hf'.self_of_nhds
  by_contra hneg
  push Not at hneg
  have hslope : Tendsto (fun h => (f' (x₀ + h) - f' x₀) / h) (𝓝[>] 0) (nhds f'') := by
    have h1 := hasDerivAt_iff_tendsto_slope.mp hf''
    have h2 : Tendsto (fun h : ℝ => x₀ + h) (𝓝[>] 0) (𝓝[≠] x₀) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨by simpa using ((continuous_add_left x₀).continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with h hh
      change x₀ + h ≠ x₀
      intro heq
      linarith [Set.mem_Ioi.mp hh]
    refine (h1.comp h2).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    simp [slope_def_field, smul_eq_mul, div_eq_inv_mul]
  have hlt_ev : ∀ᶠ h in 𝓝[>] (0 : ℝ), f' (x₀ + h) < 0 := by
    filter_upwards [hslope.eventually (gt_mem_nhds hneg), self_mem_nhdsWithin] with h h1 hpos
    rw [hf'0, sub_zero] at h1
    have hpos' : 0 < h := Set.mem_Ioi.mp hpos
    have : f' (x₀ + h) < 0 * h := (div_lt_iff₀ hpos').mp h1
    linarith
  rcases Metric.eventually_nhds_iff.mp (hf'.and hmin) with ⟨δ₁, hδ₁, h1⟩
  rcases eventually_nhdsWithin_iff.mp hlt_ev with h2
  rcases Metric.eventually_nhds_iff.mp h2 with ⟨δ₂, hδ₂, h2'⟩
  let δ := min δ₁ δ₂ / 2
  have hδ : 0 < δ := by positivity
  have hsub : ∀ x ∈ Set.Icc x₀ (x₀ + δ), HasDerivAt f (f' x) x := by
    intro x hx
    refine (h1 ?_).1
    rw [Real.dist_eq, abs_of_nonneg (by linarith [hx.1])]
    have : δ < δ₁ := by dsimp [δ]; linarith [min_le_left δ₁ δ₂]
    linarith [hx.2]
  obtain ⟨c, hc, hmv⟩ := exists_hasDerivAt_eq_slope f f' (show x₀ < x₀ + δ by linarith)
    (fun x hx => (hsub x hx).continuousAt.continuousWithinAt)
    (fun x hx => hsub x ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
  have hfc_neg : f' c < 0 := by
    have hmem : c - x₀ ∈ Set.Ioi (0 : ℝ) := by simp; linarith [hc.1]
    have hdist : dist (c - x₀) 0 < δ₂ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith [hc.1])]
      have : δ < δ₂ := by dsimp [δ]; linarith [min_le_right δ₁ δ₂]
      linarith [hc.2]
    simpa [add_sub_cancel] using h2' hdist hmem
  have hfle : f x₀ ≤ f (x₀ + δ) := by
    refine (h1 ?_).2
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hδ]
    dsimp [δ]; linarith [min_le_left δ₁ δ₂]
  have hnn : 0 ≤ (f (x₀ + δ) - f x₀) / ((x₀ + δ) - x₀) :=
    div_nonneg (by linarith) (by linarith)
  linarith

private lemma deriv_le_zero_of_isMinOn_Icc {f : ℝ → ℝ} {t₀ d : ℝ}
    (ht₀ : 0 < t₀) (ht₁ : t₀ ≤ 1)
    (hmin : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t₀ ≤ f t) (hd : HasDerivAt f d t₀) : d ≤ 0 := by
  have hslope := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
    (nhdsWithin_mono t₀ (fun t ht => ne_of_lt (Set.mem_Iio.mp ht)))
  refine le_of_tendsto hslope ?_
  filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds (show t₀ / 2 < t₀ by linarith) (show t₀ < t₀ + 1 by linarith)),
    self_mem_nhdsWithin] with t ht1 ht2
  have ht_lt : t < t₀ := Set.mem_Iio.mp ht2
  have ht_mem : t ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [ht1.1], by linarith⟩
  have hge : f t₀ ≤ f t := hmin t ht_mem
  rw [slope_def_field]
  exact div_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)

private noncomputable def U {n : ℕ} (u₀ : (Fin n → ℝ) → ℝ) (t : ℝ) (x : Fin n → ℝ) : ℝ :=
  Φinv (H t (Φ ∘ u₀) x)

private lemma H_Phi_mem_Ioo {n : ℕ} {u₀ : (Fin n → ℝ) → ℝ} (hu₀ : Continuous u₀)
    (t : ℝ) (x : Fin n → ℝ) : H t (Φ ∘ u₀) x ∈ Set.Ioo 0 1 := by
  by_cases ht : t ≤ 0
  · simp only [H, if_pos ht, Function.comp_apply]
    exact Φ_mem_Ioo (u₀ x)
  · simp only [H, if_neg ht, Function.comp_apply]
    have hmeas : Measurable (fun z : Fin n → ℝ => Φ (u₀ (x + √t • z))) := by
      have hc : Continuous (fun z : Fin n → ℝ => Φ (u₀ (x + √t • z))) :=
        continuous_Φ.comp (hu₀.comp (by fun_prop))
      exact hc.measurable
    have hint : Integrable (fun z => Φ (u₀ (x + √t • z))) (γ n) :=
      Integrable.of_bound hmeas.aestronglyMeasurable 1
        (Eventually.of_forall fun z => by rw [Real.norm_eq_abs, abs_of_pos (Φ_pos _)]; exact le_of_lt (Φ_lt_one _))
    constructor
    · refine (integral_pos_iff_support_of_nonneg_ae
        (Eventually.of_forall fun z => le_of_lt (Φ_pos _)) hint).mpr ?_
      have hsupp : Function.support (fun z => Φ (u₀ (x + √t • z))) = Set.univ := by
        ext z; simp [ne_of_gt (Φ_pos _)]
      rw [hsupp]; simp
    · have hint2 : Integrable (fun z => 1 - Φ (u₀ (x + √t • z))) (γ n) := (integrable_const 1).sub hint
      have hpos : 0 < ∫ z, (1 - Φ (u₀ (x + √t • z))) ∂(γ n) := by
        refine (integral_pos_iff_support_of_nonneg_ae
          (Eventually.of_forall fun z => sub_nonneg.mpr (le_of_lt (Φ_lt_one (u₀ (x + √t • z))))) hint2).mpr ?_
        have hsupp : Function.support (fun z => 1 - Φ (u₀ (x + √t • z))) = Set.univ := by
          ext z; simp [sub_ne_zero.mpr (ne_of_gt (Φ_lt_one (u₀ (x + √t • z))))]
        rw [hsupp]; simp
      rw [integral_sub (integrable_const 1) hint, integral_const] at hpos
      simp only [smul_eq_mul, probReal_univ, mul_one] at hpos
      linarith

private lemma H_Phi_continuousOn {n : ℕ} {u₀ : (Fin n → ℝ) → ℝ} (hu₀ : Continuous u₀) :
    ContinuousOn (fun p : ℝ × (Fin n → ℝ) => H p.1 (Φ ∘ u₀) p.2) (Set.Ici 0 ×ˢ Set.univ) := by
  intro p₀ hp₀
  have heq : ∀ p ∈ Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set (Fin n → ℝ)),
      H p.1 (Φ ∘ u₀) p.2 = ∫ z, Φ (u₀ (p.2 + √p.1 • z)) ∂(γ n) := by
    intro p hp
    by_cases ht : p.1 ≤ 0
    · have h0 : p.1 = 0 := le_antisymm ht hp.1
      simp [H, h0]
    · simp [H, if_neg ht]
  refine ContinuousWithinAt.congr ?_ (fun p hp => heq p hp) (heq p₀ hp₀)
  refine continuousWithinAt_of_dominated (bound := fun _ => (1 : ℝ)) ?_ ?_ (integrable_const 1) ?_
  · refine Eventually.of_forall fun p => by
      have hc : Continuous (fun z : Fin n → ℝ => Φ (u₀ (p.2 + √p.1 • z))) :=
        continuous_Φ.comp (hu₀.comp (by fun_prop))
      exact hc.aestronglyMeasurable
  · refine Eventually.of_forall fun p => Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Φ_pos _)]
    exact le_of_lt (Φ_lt_one _)
  · refine Eventually.of_forall fun z => ?_
    have hc : Continuous (fun p : ℝ × (Fin n → ℝ) => Φ (u₀ (p.2 + √p.1 • z))) :=
      continuous_Φ.comp (hu₀.comp (continuous_snd.add ((Real.continuous_sqrt.comp continuous_fst).smul continuous_const)))
    exact hc.continuousWithinAt

private lemma U_continuousOn {n : ℕ} {u₀ : (Fin n → ℝ) → ℝ} (hu₀ : Continuous u₀) :
    ContinuousOn (fun p : ℝ × (Fin n → ℝ) => U u₀ p.1 p.2) (Set.Ici 0 ×ˢ Set.univ) := by
  intro p₀ hp₀
  have h1 := H_Phi_continuousOn hu₀ p₀ hp₀
  have h2 := (continuousOn_Φinv (H p₀.1 (Φ ∘ u₀) p₀.2) (H_Phi_mem_Ioo hu₀ p₀.1 p₀.2)).continuousAt
    (isOpen_Ioo.mem_nhds (H_Phi_mem_Ioo hu₀ p₀.1 p₀.2))
  exact ContinuousAt.comp_continuousWithinAt (g := Φinv)
    (f := fun p : ℝ × (Fin n → ℝ) => H p.1 (Φ ∘ u₀) p.2) h2 h1

private lemma U_lip {n : ℕ} {u₀ : (Fin n → ℝ) → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hu₀_lip : ∀ x y : Fin n → ℝ, |u₀ x - u₀ y| ≤ L * ∑ i : Fin n, |x i - y i|)
    (hu₀_cont : Continuous u₀) (t : ℝ) (ht : 0 ≤ t) (x y : Fin n → ℝ) :
    |U u₀ t x - U u₀ t y| ≤ L * ∑ i : Fin n, |x i - y i| := by
  have hone : ∀ a b : Fin n → ℝ, U u₀ t a ≤ U u₀ t b + L * ∑ i : Fin n, |a i - b i| := by
    intro a b
    set d := L * ∑ i : Fin n, |a i - b i|
    have hd : 0 ≤ d := mul_nonneg hL (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    by_cases ht0 : t ≤ 0
    · simp only [U, H, if_pos ht0, Function.comp_apply, Φinv_Φ]
      linarith [(abs_le.mp (hu₀_lip a b)).2]
    · simp only [U, H, if_neg ht0, Function.comp_apply]
      have hmeas_a : Measurable (fun z : Fin n → ℝ => u₀ (a + √t • z)) := by
        have hc : Continuous (fun z : Fin n → ℝ => u₀ (a + √t • z)) := by fun_prop
        exact hc.measurable
      have hmeas_b : Measurable (fun z : Fin n → ℝ => u₀ (b + √t • z)) := by
        have hc : Continuous (fun z : Fin n → ℝ => u₀ (b + √t • z)) := by fun_prop
        exact hc.measurable
      have hint_a : Integrable (fun z => Φ (u₀ (a + √t • z))) (γ n) :=
        Integrable.of_bound (continuous_Φ.measurable.comp hmeas_a).aestronglyMeasurable 1
          (Eventually.of_forall fun z => by rw [Real.norm_eq_abs, abs_of_pos (Φ_pos _)]; exact le_of_lt (Φ_lt_one _))
      have hint_bd : Integrable (fun z => Φ (u₀ (b + √t • z) + d)) (γ n) :=
        Integrable.of_bound (continuous_Φ.measurable.comp (hmeas_b.add measurable_const)).aestronglyMeasurable 1
          (Eventually.of_forall fun z => by rw [Real.norm_eq_abs, abs_of_pos (Φ_pos _)]; exact le_of_lt (Φ_lt_one _))
      have hle_int : ∫ z, Φ (u₀ (a + √t • z)) ∂(γ n) ≤ ∫ z, Φ (u₀ (b + √t • z) + d) ∂(γ n) := by
        refine integral_mono hint_a hint_bd fun z => Φ_strictMono.monotone ?_
        have hdiff := hu₀_lip (a + √t • z) (b + √t • z)
        have hsum_eq : ∑ i : Fin n, |(a + √t • z) i - (b + √t • z) i| = ∑ i : Fin n, |a i - b i| :=
          Finset.sum_congr rfl fun i _ => by simp [add_sub_add_right_eq_sub]
        rw [hsum_eq] at hdiff
        linarith [(abs_le.mp hdiff).2]
      have hmem1 : (∫ z, Φ (u₀ (a + √t • z)) ∂(γ n)) ∈ Set.Ioo 0 1 := by
        simpa [H, if_neg ht0] using H_Phi_mem_Ioo hu₀_cont t a
      have hmem2 : (∫ z, Φ (u₀ (b + √t • z) + d) ∂(γ n)) ∈ Set.Ioo 0 1 := by
        have h1 : (∫ z, Φ (u₀ (b + √t • z)) ∂(γ n)) ∈ Set.Ioo 0 1 := by
          simpa [H, if_neg ht0] using H_Phi_mem_Ioo hu₀_cont t b
        constructor
        · exact lt_of_lt_of_le h1.1 (integral_mono
            (Integrable.of_bound (continuous_Φ.measurable.comp hmeas_b).aestronglyMeasurable 1
              (Eventually.of_forall fun z => by rw [Real.norm_eq_abs, abs_of_pos (Φ_pos _)]; exact le_of_lt (Φ_lt_one _)))
            hint_bd fun z => Φ_strictMono.monotone (by linarith))
        · have hint2 : Integrable (fun z => 1 - Φ (u₀ (b + √t • z) + d)) (γ n) := (integrable_const 1).sub hint_bd
          have hpos : 0 < ∫ z, (1 - Φ (u₀ (b + √t • z) + d)) ∂(γ n) := by
            refine (integral_pos_iff_support_of_nonneg_ae
              (Eventually.of_forall fun z => sub_nonneg.mpr (le_of_lt (Φ_lt_one (u₀ (b + √t • z) + d)))) hint2).mpr ?_
            have hsupp : Function.support (fun z => 1 - Φ (u₀ (b + √t • z) + d)) = Set.univ := by
              ext z; simp [sub_ne_zero.mpr (ne_of_gt (Φ_lt_one (u₀ (b + √t • z) + d)))]
            rw [hsupp]; simp
          rw [integral_sub (integrable_const 1) hint_bd, integral_const] at hpos
          simp only [smul_eq_mul, probReal_univ, mul_one] at hpos
          linarith
      calc Φinv (∫ z, Φ (u₀ (a + √t • z)) ∂(γ n))
          ≤ Φinv (∫ z, Φ (u₀ (b + √t • z) + d) ∂(γ n)) := Φinv_monoOn hmem1 hmem2 hle_int
        _ ≤ Φinv (∫ z, Φ (u₀ (b + √t • z)) ∂(γ n)) + d := Φinv_integral_add_le (γ n) hmeas_b hd
  rw [abs_le]
  have hsym : ∑ i : Fin n, |y i - x i| = ∑ i : Fin n, |x i - y i| :=
    Finset.sum_congr rfl fun i _ => abs_sub_comm _ _
  constructor
  · have := hone y x; rw [hsym] at this; linarith
  · linarith [hone x y]

/-- Borell's PDE for `U u₀ t x = Φ⁻¹(H t (Φ ∘ u₀) x)` and uniform `L`-bound on partial derivatives. -/
private lemma U_PDE {n : ℕ} {u₀ : (Fin n → ℝ) → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hu₀_lip : ∀ x y : Fin n → ℝ, |u₀ x - u₀ y| ≤ L * ∑ i : Fin n, |x i - y i|)
    (hu₀_cont : Continuous u₀) {t₀ : ℝ} (ht₀ : 0 < t₀) (x₀ : Fin n → ℝ) :
    ∃ (ut : ℝ) (ux uxx : Fin n → ℝ),
      HasDerivAt (fun t => U u₀ t x₀) ut t₀ ∧
      (∀ i : Fin n,
        HasDerivAt (fun s => U u₀ t₀ (Function.update x₀ i s)) (ux i) (x₀ i) ∧
        (∃ ux_fn : ℝ → ℝ,
          (∀ᶠ s in 𝓝 (x₀ i), HasDerivAt (fun r => U u₀ t₀ (Function.update x₀ i r)) (ux_fn s) s) ∧
          HasDerivAt ux_fn (uxx i) (x₀ i)) ∧
        |ux i| ≤ L) ∧
      ut = (1 / 2) * ∑ i : Fin n, (uxx i - U u₀ t₀ x₀ * (ux i) ^ 2) := by
  let g := Φ ∘ u₀
  have hg_meas : Measurable g := (continuous_Φ.comp hu₀_cont).measurable
  have hg_bdd : ∀ y, |g y| ≤ 1 := fun y => by
    dsimp only [g, Function.comp_apply]
    rw [abs_of_pos (Φ_pos _)]; exact le_of_lt (Φ_lt_one _)
  have ⟨hFt, hFx, hheat⟩ := H_derivs_and_heat_eq hg_meas hg_bdd ht₀ x₀
  set F₀ := H t₀ g x₀
  set u := U u₀ t₀ x₀
  have hF₀_mem : F₀ ∈ Set.Ioo 0 1 := H_Phi_mem_Ioo hu₀_cont t₀ x₀
  have hφ_pos : 0 < φ u := φ_pos u
  have hφ_ne : φ u ≠ 0 := ne_of_gt hφ_pos
  set Ft := ∫ y, g y * K_dt t₀ x₀ y ∂volume
  let Fx : Fin n → ℝ := fun i => ∫ y, g y * K_dx t₀ x₀ y i ∂volume
  let Fxx : Fin n → ℝ := fun i => ∫ y, g y * K_dxx t₀ x₀ y i ∂volume
  let ut : ℝ := Ft * (φ u)⁻¹
  let ux : Fin n → ℝ := fun i => Fx i * (φ u)⁻¹
  let uxx : Fin n → ℝ := fun i => (Fxx i + u * (Fx i) ^ 2 * (φ u)⁻¹) * (φ u)⁻¹
  refine ⟨ut, ux, uxx, ?_, ?_, ?_⟩
  · -- Time derivative via chain rule
    change HasDerivAt (fun t => Φinv (H t g x₀)) ut t₀
    refine ((hasDerivAt_Φinv hF₀_mem).comp t₀ hFt).congr_deriv ?_
    dsimp [ut, u, U, F₀, g]; ring
  · intro i
    have hux_deriv : HasDerivAt (fun s => U u₀ t₀ (Function.update x₀ i s)) (ux i) (x₀ i) := by
      change HasDerivAt (fun s => Φinv (H t₀ g (Function.update x₀ i s))) (ux i) (x₀ i)
      have hFx_i : HasDerivAt (fun s => H t₀ g (Function.update x₀ i s)) (Fx i) (x₀ i) := (hFx i).1
      have hF0_eq : H t₀ g (Function.update x₀ i (x₀ i)) = F₀ := by simp [F₀]
      have hΦd : HasDerivAt Φinv (φ (Φinv F₀))⁻¹ (H t₀ g (Function.update x₀ i (x₀ i))) := by
        rw [hF0_eq]; exact hasDerivAt_Φinv hF₀_mem
      refine (hΦd.comp (x₀ i) hFx_i).congr_deriv ?_
      dsimp [ux, Fx, u, U, F₀, g]; ring
    -- Local first derivative function `ux_fn s = Fx_fn s * (φ (U u₀ t₀ (upd x₀ i s)))⁻¹`
    let Fx_fn : ℝ → ℝ := fun s => ∫ y, g y * K_dx t₀ (Function.update x₀ i s) y i ∂volume
    let U_fn : ℝ → ℝ := fun s => U u₀ t₀ (Function.update x₀ i s)
    let ux_fn : ℝ → ℝ := fun s => Fx_fn s * (φ (U_fn s))⁻¹
    have hux_ev : ∀ᶠ s in 𝓝 (x₀ i), HasDerivAt (fun r => U u₀ t₀ (Function.update x₀ i r)) (ux_fn s) s := by
      refine Eventually.of_forall fun s => ?_
      have hs_mem := H_Phi_mem_Ioo hu₀_cont t₀ (Function.update x₀ i s)
      have hFxs := (H_derivs_and_heat_eq hg_meas hg_bdd ht₀ (Function.update x₀ i s)).2.1 i |>.1
      have hupd : (fun r => H t₀ g (Function.update (Function.update x₀ i s) i r)) =
          fun r => H t₀ g (Function.update x₀ i r) := by
        ext r; simp [Function.update_idem]
      rw [hupd, Function.update_self] at hFxs
      change HasDerivAt (fun r => Φinv (H t₀ g (Function.update x₀ i r))) (ux_fn s) s
      have hs_eq : H t₀ g (Function.update x₀ i s) = H t₀ (Φ ∘ u₀) (Function.update x₀ i s) := rfl
      refine ((hasDerivAt_Φinv hs_mem).comp s hFxs).congr_deriv ?_
      dsimp [ux_fn, Fx_fn, U_fn, U, g]; ring
    have hux_d2 : HasDerivAt ux_fn (uxx i) (x₀ i) := by
      have h1 : HasDerivAt Fx_fn (Fxx i) (x₀ i) := (hFx i).2
      have hU0 : U_fn (x₀ i) = u := by simp [U_fn, Function.update_eq_self, u]
      have h2 : HasDerivAt (fun s => φ (U_fn s)) ((-u * φ u) * ux i) (x₀ i) := by
        have hφ_at : HasDerivAt φ (-u * φ u) (U_fn (x₀ i)) := by rw [hU0]; exact hasDerivAt_φ u
        exact hφ_at.comp (x₀ i) hux_deriv
      have h3 : HasDerivAt (fun s => (φ (U_fn s))⁻¹) (-((-u * φ u) * ux i) / (φ u) ^ 2) (x₀ i) := by
        have hne : φ (U_fn (x₀ i)) ≠ 0 := by rw [hU0]; exact hφ_ne
        refine (h2.inv hne).congr_deriv ?_
        rw [hU0]
      have h4 := h1.mul h3
      have hFx0 : Fx_fn (x₀ i) = Fx i := by simp [Fx_fn, Function.update_eq_self, Fx]
      refine h4.congr_deriv ?_
      rw [hFx0, hU0]
      dsimp [uxx, ux]
      field_simp [hφ_ne]
    have hux_le : |ux i| ≤ L := by
      have hslope := hasDerivAt_iff_tendsto_slope.mp hux_deriv
      have hslope_abs : Tendsto (fun s => |slope (fun r => U u₀ t₀ (Function.update x₀ i r)) (x₀ i) s|)
          (𝓝[≠] (x₀ i)) (nhds |ux i|) :=
        (continuous_abs.tendsto _).comp hslope
      refine le_of_tendsto hslope_abs ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hne : s - x₀ i ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hs)
      rw [slope_def_field, abs_div]
      have hlip := U_lip hL hu₀_lip hu₀_cont t₀ (le_of_lt ht₀) (Function.update x₀ i s) x₀
      have hsum : ∑ j : Fin n, |Function.update x₀ i s j - x₀ j| = |s - x₀ i| := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hji; simp [Function.update_of_ne hji]
        · intro hi; exact absurd (Finset.mem_univ i) hi
      rw [hsum] at hlip
      exact (div_le_iff₀ (abs_pos.mpr hne)).mpr (by simpa [Function.update_eq_self] using hlip)
    exact ⟨hux_deriv, ⟨ux_fn, hux_ev, hux_d2⟩, hux_le⟩
  · -- Borell's PDE: ut = (1/2) ∑ (uxx i - u * (ux i)^2)
    dsimp [ut, uxx, ux]
    rw [hheat]
    have hterm : ∀ i : Fin n,
        (Fxx i + u * (Fx i) ^ 2 * (φ u)⁻¹) * (φ u)⁻¹ - u * (Fx i * (φ u)⁻¹) ^ 2 =
          Fxx i * (φ u)⁻¹ := fun i => by field_simp [hφ_ne]; ring
    simp_rw [hterm]
    rw [← Finset.sum_mul]
    ring

set_option maxHeartbeats 800000 in
/-- Functional Ehrhard inequality for globally `ℓ¹`-Lipschitz functions. -/
private lemma functional_ehrhard {n : ℕ} {u₀ v₀ w₀ : (Fin n → ℝ) → ℝ} {L lam : ℝ}
    (hL : 0 ≤ L) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hu₀_lip : ∀ x y, |u₀ x - u₀ y| ≤ L * ∑ i : Fin n, |x i - y i|)
    (hv₀_lip : ∀ x y, |v₀ x - v₀ y| ≤ L * ∑ i : Fin n, |x i - y i|)
    (hw₀_lip : ∀ x y, |w₀ x - w₀ y| ≤ L * ∑ i : Fin n, |x i - y i|)
    (hineq : ∀ x y : Fin n → ℝ, lam * u₀ x + (1 - lam) * v₀ y ≤ w₀ (lam • x + (1 - lam) • y)) :
    lam * Φinv (∫ x, Φ (u₀ x) ∂(γ n)) + (1 - lam) * Φinv (∫ y, Φ (v₀ y) ∂(γ n)) ≤
      Φinv (∫ z, Φ (w₀ z) ∂(γ n)) := by
  have hu₀_cont : Continuous u₀ := by
    refine continuous_iff_continuousAt.mpr fun x => Metric.continuousAt_iff.mpr fun ε hε => ?_
    refine ⟨ε / (L * n + 1), by positivity, fun y hy => ?_⟩
    rw [Real.dist_eq]
    have hsum : ∑ i : Fin n, |y i - x i| ≤ (n : ℝ) * dist y x := by
      calc ∑ i : Fin n, |y i - x i|
          ≤ ∑ _i : Fin n, dist y x := Finset.sum_le_sum fun i _ => by
            simpa [Real.dist_eq] using dist_le_pi_dist y x i
        _ = (n : ℝ) * dist y x := by simp
    have h1 := hu₀_lip y x
    have h2 : L * ((n : ℝ) * dist y x) < ε := by
      have hpos : 0 < L * n + 1 := by positivity
      calc L * ((n : ℝ) * dist y x) ≤ (L * n + 1) * dist y x := by nlinarith [dist_nonneg (x := y) (y := x)]
        _ < (L * n + 1) * (ε / (L * n + 1)) := mul_lt_mul_of_pos_left hy hpos
        _ = ε := mul_div_cancel₀ ε (ne_of_gt hpos)
    linarith [mul_le_mul_of_nonneg_left hsum hL]
  have hv₀_cont : Continuous v₀ := by
    refine continuous_iff_continuousAt.mpr fun x => Metric.continuousAt_iff.mpr fun ε hε => ?_
    refine ⟨ε / (L * n + 1), by positivity, fun y hy => ?_⟩
    rw [Real.dist_eq]
    have hsum : ∑ i : Fin n, |y i - x i| ≤ (n : ℝ) * dist y x := by
      calc ∑ i : Fin n, |y i - x i|
          ≤ ∑ _i : Fin n, dist y x := Finset.sum_le_sum fun i _ => by
            simpa [Real.dist_eq] using dist_le_pi_dist y x i
        _ = (n : ℝ) * dist y x := by simp
    have h1 := hv₀_lip y x
    have h2 : L * ((n : ℝ) * dist y x) < ε := by
      have hpos : 0 < L * n + 1 := by positivity
      calc L * ((n : ℝ) * dist y x) ≤ (L * n + 1) * dist y x := by nlinarith [dist_nonneg (x := y) (y := x)]
        _ < (L * n + 1) * (ε / (L * n + 1)) := mul_lt_mul_of_pos_left hy hpos
        _ = ε := mul_div_cancel₀ ε (ne_of_gt hpos)
    linarith [mul_le_mul_of_nonneg_left hsum hL]
  have hw₀_cont : Continuous w₀ := by
    refine continuous_iff_continuousAt.mpr fun x => Metric.continuousAt_iff.mpr fun ε hε => ?_
    refine ⟨ε / (L * n + 1), by positivity, fun y hy => ?_⟩
    rw [Real.dist_eq]
    have hsum : ∑ i : Fin n, |y i - x i| ≤ (n : ℝ) * dist y x := by
      calc ∑ i : Fin n, |y i - x i|
          ≤ ∑ _i : Fin n, dist y x := Finset.sum_le_sum fun i _ => by
            simpa [Real.dist_eq] using dist_le_pi_dist y x i
        _ = (n : ℝ) * dist y x := by simp
    have h1 := hw₀_lip y x
    have h2 : L * ((n : ℝ) * dist y x) < ε := by
      have hpos : 0 < L * n + 1 := by positivity
      calc L * ((n : ℝ) * dist y x) ≤ (L * n + 1) * dist y x := by nlinarith [dist_nonneg (x := y) (y := x)]
        _ < (L * n + 1) * (ε / (L * n + 1)) := mul_lt_mul_of_pos_left hy hpos
        _ = ε := mul_div_cancel₀ ε (ne_of_gt hpos)
    linarith [mul_le_mul_of_nonneg_left hsum hL]
  -- Uniform bound `A` on `|U u₀ t 0|, |U v₀ t 0|, |U w₀ t 0|` for `t ∈ [0, 1]`
  have hcomp_Icc : IsCompact (Set.Icc (0 : ℝ) 1) := isCompact_Icc
  have hU0_cont : ContinuousOn (fun t => U u₀ t 0) (Set.Icc 0 1) :=
    (U_continuousOn hu₀_cont).comp (continuous_id.prodMk continuous_const).continuousOn
      fun t ht => ⟨ht.1, Set.mem_univ _⟩
  have hV0_cont : ContinuousOn (fun t => U v₀ t 0) (Set.Icc 0 1) :=
    (U_continuousOn hv₀_cont).comp (continuous_id.prodMk continuous_const).continuousOn
      fun t ht => ⟨ht.1, Set.mem_univ _⟩
  have hW0_cont : ContinuousOn (fun t => U w₀ t 0) (Set.Icc 0 1) :=
    (U_continuousOn hw₀_cont).comp (continuous_id.prodMk continuous_const).continuousOn
      fun t ht => ⟨ht.1, Set.mem_univ _⟩
  obtain ⟨Au, hAu⟩ := hcomp_Icc.exists_bound_of_continuousOn hU0_cont
  obtain ⟨Av, hAv⟩ := hcomp_Icc.exists_bound_of_continuousOn hV0_cont
  obtain ⟨Aw, hAw⟩ := hcomp_Icc.exists_bound_of_continuousOn hW0_cont
  let A : ℝ := max (max (|Au| + 1) (|Av| + 1)) (|Aw| + 1)
  have hA_pos : 0 < A := by dsimp [A]; positivity
  have hU_bdd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x : Fin n → ℝ,
      |U u₀ t x| ≤ A + L * ∑ i : Fin n, |x i| := by
    intro t ht x
    have h1 := U_lip hL hu₀_lip hu₀_cont t ht.1 x 0
    have h2 : |U u₀ t 0| ≤ A := by
      have h0 := hAu t ht; rw [Real.norm_eq_abs] at h0
      dsimp [A]; linarith [le_abs_self Au, le_max_left (|Au| + 1) (|Av| + 1),
        le_max_left (max (|Au| + 1) (|Av| + 1)) (|Aw| + 1)]
    have h3 : |U u₀ t x| - |U u₀ t 0| ≤ |U u₀ t x - U u₀ t 0| := abs_sub_abs_le_abs_sub _ _
    simp only [Pi.zero_apply, sub_zero] at h1
    linarith
  have hV_bdd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y : Fin n → ℝ,
      |U v₀ t y| ≤ A + L * ∑ i : Fin n, |y i| := by
    intro t ht y
    have h1 := U_lip hL hv₀_lip hv₀_cont t ht.1 y 0
    have h2 : |U v₀ t 0| ≤ A := by
      have h0 := hAv t ht; rw [Real.norm_eq_abs] at h0
      dsimp [A]; linarith [le_abs_self Av, le_max_right (|Au| + 1) (|Av| + 1),
        le_max_left (max (|Au| + 1) (|Av| + 1)) (|Aw| + 1)]
    have h3 : |U v₀ t y| - |U v₀ t 0| ≤ |U v₀ t y - U v₀ t 0| := abs_sub_abs_le_abs_sub _ _
    simp only [Pi.zero_apply, sub_zero] at h1
    linarith
  have hW_bdd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z : Fin n → ℝ,
      |U w₀ t z| ≤ A + L * ∑ i : Fin n, |z i| := by
    intro t ht z
    have h1 := U_lip hL hw₀_lip hw₀_cont t ht.1 z 0
    have h2 : |U w₀ t 0| ≤ A := by
      have h0 := hAw t ht; rw [Real.norm_eq_abs] at h0
      dsimp [A]; linarith [le_abs_self Aw, le_max_right (max (|Au| + 1) (|Av| + 1)) (|Aw| + 1)]
    have h3 : |U w₀ t z| - |U w₀ t 0| ≤ |U w₀ t z - U w₀ t 0| := abs_sub_abs_le_abs_sub _ _
    simp only [Pi.zero_apply, sub_zero] at h1
    linarith
  -- Show `C(1, 0, 0) ≥ 0` by proving `W_ε(1, 0, 0) > 0` for every `ε > 0`
  suffices hpos_eps : ∀ ε : ℝ, 0 < ε →
      0 < U w₀ 1 0 - lam * U u₀ 1 0 - (1 - lam) * U v₀ 1 0 + ε * Real.exp ((2 * (n : ℝ) + 4 * L * (A * ((n : ℝ) + 1) + L * (n : ℝ)) + 1) * 1) by
    have h1 : U w₀ 1 0 = Φinv (∫ z, Φ (w₀ z) ∂(γ n)) := by
      simp [U, H, show ¬ (1 : ℝ) ≤ 0 by norm_num]
    have h2 : U u₀ 1 0 = Φinv (∫ x, Φ (u₀ x) ∂(γ n)) := by
      simp [U, H, show ¬ (1 : ℝ) ≤ 0 by norm_num]
    have h3 : U v₀ 1 0 = Φinv (∫ y, Φ (v₀ y) ∂(γ n)) := by
      simp [U, H, show ¬ (1 : ℝ) ≤ 0 by norm_num]
    rw [← h1, ← h2, ← h3]
    by_contra hlt
    push Not at hlt
    set gap := lam * U u₀ 1 0 + (1 - lam) * U v₀ 1 0 - U w₀ 1 0
    have hgap : 0 < gap := by linarith
    let M : ℝ := 2 * (n : ℝ) + 4 * L * (A * ((n : ℝ) + 1) + L * (n : ℝ)) + 1
    let ε := gap / (2 * Real.exp (M * 1))
    have hε : 0 < ε := by positivity
    have h := hpos_eps ε hε
    have heq : ε * Real.exp (M * 1) = gap / 2 := by
      dsimp [ε]; field_simp [ne_of_gt (Real.exp_pos (M * 1))]
    rw [heq] at h
    linarith
  intro ε hε
  let M : ℝ := 2 * (n : ℝ) + 4 * L * (A * ((n : ℝ) + 1) + L * (n : ℝ)) + 1
  have hM_pos : 0 < M := by positivity
  let ψ : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ :=
    fun t x y => ε * Real.exp (M * t) * (1 + ∑ i : Fin n, (x i) ^ 2 + ∑ i : Fin n, (y i) ^ 2)
  let W : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ :=
    fun t x y => U w₀ t (lam • x + (1 - lam) • y) - lam * U u₀ t x - (1 - lam) * U v₀ t y + ψ t x y
  suffices hall_pos : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x y : Fin n → ℝ, 0 < W t x y by
    have := hall_pos 1 ⟨zero_le_one, le_refl 1⟩ 0 0
    simpa [W, ψ] using this
  -- Coercivity: outside a big box `R`, `W t x y ≥ W 0 0 0 + 1`
  let W0 : ℝ := W 0 0 0
  let B_const : ℝ := 2 * A + |W0| + 1 + 8 * (n : ℝ) * L ^ 2 / ε
  let R : ℝ := max 1 (2 * B_const / ε + 1)
  have hR_pos : 0 < R := by dsimp [R]; positivity
  have hcoerc : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x y : Fin n → ℝ,
      R < max (‖x‖) (‖y‖) → W0 + 1 ≤ W t x y := by
    intro t ht x y hgt
    have hexp1 : 1 ≤ Real.exp (M * t) := Real.one_le_exp (mul_nonneg (le_of_lt hM_pos) ht.1)
    have hSz : ∑ i : Fin n, |(lam • x + (1 - lam) • y) i| ≤ ∑ i : Fin n, |x i| + ∑ i : Fin n, |y i| := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      calc |lam * x i + (1 - lam) * y i| ≤ |lam * x i| + |(1 - lam) * y i| := abs_add_le _ _
        _ = lam * |x i| + (1 - lam) * |y i| := by
            rw [abs_mul, abs_mul, abs_of_pos hlam0, abs_of_pos (a := 1 - lam) (by linarith)]
        _ ≤ |x i| + |y i| := by nlinarith [abs_nonneg (x i), abs_nonneg (y i)]
    have hC_ge : -(2 * A + 2 * L * (∑ i : Fin n, |x i| + ∑ i : Fin n, |y i|)) ≤
        U w₀ t (lam • x + (1 - lam) • y) - lam * U u₀ t x - (1 - lam) * U v₀ t y := by
      have h1 := (abs_le.mp (hW_bdd t ht (lam • x + (1 - lam) • y))).1
      have h2 := (abs_le.mp (hU_bdd t ht x)).2
      have h3 := (abs_le.mp (hV_bdd t ht y)).2
      have hLsz : L * ∑ i : Fin n, |(lam • x + (1 - lam) • y) i| ≤
          L * (∑ i : Fin n, |x i| + ∑ i : Fin n, |y i|) := mul_le_mul_of_nonneg_left hSz hL
      have h2' : lam * U u₀ t x ≤ lam * (A + L * ∑ i : Fin n, |x i|) :=
        mul_le_mul_of_nonneg_left h2 (le_of_lt hlam0)
      have h3' : (1 - lam) * U v₀ t y ≤ (1 - lam) * (A + L * ∑ i : Fin n, |y i|) :=
        mul_le_mul_of_nonneg_left h3 (by linarith)
      have hSx_nn : 0 ≤ L * ∑ i : Fin n, |x i| := mul_nonneg hL (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      have hSy_nn : 0 ≤ L * ∑ i : Fin n, |y i| := mul_nonneg hL (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      nlinarith
    have hyoung : ∀ r : ℝ, 2 * L * |r| ≤ 4 * L ^ 2 / ε + (ε / 2) * r ^ 2 := by
      intro r
      have hsq : 0 ≤ (2 * L - (ε / 2) * |r|) ^ 2 := sq_nonneg _
      have h1 : 2 * L * |r| * ε ≤ 4 * L ^ 2 + (ε ^ 2 / 4) * |r| ^ 2 := by nlinarith
      have h2 : (ε ^ 2 / 4) * |r| ^ 2 ≤ (ε ^ 2 / 2) * r ^ 2 := by rw [sq_abs]; nlinarith [sq_nonneg r, sq_nonneg ε]
      have h3 : 2 * L * |r| * ε ≤ 4 * L ^ 2 + (ε ^ 2 / 2) * r ^ 2 := by linarith
      have h4 : (2 * L * |r| * ε) / ε ≤ (4 * L ^ 2 + (ε ^ 2 / 2) * r ^ 2) / ε :=
        div_le_div_of_nonneg_right h3 (le_of_lt hε)
      have hne : ε ≠ 0 := ne_of_gt hε
      calc 2 * L * |r| = (2 * L * |r| * ε) / ε := by field_simp [hne]
        _ ≤ (4 * L ^ 2 + (ε ^ 2 / 2) * r ^ 2) / ε := h4
        _ = 4 * L ^ 2 / ε + (ε / 2) * r ^ 2 := by field_simp [hne]
    set Q := ∑ i : Fin n, (x i) ^ 2 + ∑ i : Fin n, (y i) ^ 2
    have hlin_Q : 2 * L * (∑ i : Fin n, |x i| + ∑ i : Fin n, |y i|) ≤
        8 * (n : ℝ) * L ^ 2 / ε + (ε / 2) * Q := by
      have hx_b : 2 * L * ∑ i : Fin n, |x i| ≤ 4 * (n : ℝ) * L ^ 2 / ε + (ε / 2) * ∑ i : Fin n, (x i) ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum]
        calc ∑ i : Fin n, 2 * L * |x i|
            ≤ ∑ i : Fin n, (4 * L ^ 2 / ε + (ε / 2) * (x i) ^ 2) := Finset.sum_le_sum fun i _ => hyoung (x i)
          _ = 4 * (n : ℝ) * L ^ 2 / ε + ∑ i : Fin n, (ε / 2) * (x i) ^ 2 := by
              rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      have hy_b : 2 * L * ∑ i : Fin n, |y i| ≤ 4 * (n : ℝ) * L ^ 2 / ε + (ε / 2) * ∑ i : Fin n, (y i) ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum]
        calc ∑ i : Fin n, 2 * L * |y i|
            ≤ ∑ i : Fin n, (4 * L ^ 2 / ε + (ε / 2) * (y i) ^ 2) := Finset.sum_le_sum fun i _ => hyoung (y i)
          _ = 4 * (n : ℝ) * L ^ 2 / ε + ∑ i : Fin n, (ε / 2) * (y i) ^ 2 := by
              rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      have hdist1 : 2 * L * (∑ i : Fin n, |x i| + ∑ i : Fin n, |y i|) =
          2 * L * ∑ i : Fin n, |x i| + 2 * L * ∑ i : Fin n, |y i| := by ring
      have hdist2 : (ε / 2) * (∑ i : Fin n, (x i) ^ 2 + ∑ i : Fin n, (y i) ^ 2) =
          (ε / 2) * ∑ i : Fin n, (x i) ^ 2 + (ε / 2) * ∑ i : Fin n, (y i) ^ 2 := by ring
      have h8 : 4 * (n : ℝ) * L ^ 2 / ε + 4 * (n : ℝ) * L ^ 2 / ε = 8 * (n : ℝ) * L ^ 2 / ε := by ring
      dsimp [Q]; linarith
    have hsum_sq_ge : R ^ 2 ≤ Q := by
      rcases lt_max_iff.mp hgt with hxR | hyR
      · obtain ⟨i, hi⟩ : ∃ i : Fin n, R < |x i| := by
          by_contra hall; push Not at hall
          have : ‖x‖ ≤ R := (pi_norm_le_iff_of_nonneg (le_of_lt hR_pos)).mpr fun i => by
            simpa [Real.norm_eq_abs] using hall i
          linarith
        have h1 : (x i) ^ 2 ≤ ∑ j : Fin n, (x j) ^ 2 :=
          Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
        have h2 : 0 ≤ ∑ j : Fin n, (y j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg (y j)
        dsimp [Q]; nlinarith [sq_abs (x i)]
      · obtain ⟨i, hi⟩ : ∃ i : Fin n, R < |y i| := by
          by_contra hall; push Not at hall
          have : ‖y‖ ≤ R := (pi_norm_le_iff_of_nonneg (le_of_lt hR_pos)).mpr fun i => by
            simpa [Real.norm_eq_abs] using hall i
          linarith
        have h1 : (y i) ^ 2 ≤ ∑ j : Fin n, (y j) ^ 2 :=
          Finset.single_le_sum (fun j _ => sq_nonneg (y j)) (Finset.mem_univ i)
        have h2 : 0 ≤ ∑ j : Fin n, (x j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg (x j)
        dsimp [Q]; nlinarith [sq_abs (y i)]
    have hQ_ge_R : R ≤ Q := by nlinarith [le_max_left (1 : ℝ) (2 * B_const / ε + 1)]
    have hψ_ge : ε * (1 + Q) ≤ ψ t x y := by
      dsimp [ψ, Q]
      have hnn : 0 ≤ 1 + (∑ i : Fin n, (x i) ^ 2 + ∑ i : Fin n, (y i) ^ 2) := by
        have h1 : 0 ≤ ∑ i : Fin n, (x i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
        have h2 : 0 ≤ ∑ i : Fin n, (y i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
        linarith
      calc ε * (1 + (∑ i : Fin n, (x i) ^ 2 + ∑ i : Fin n, (y i) ^ 2))
          = ε * 1 * (1 + (∑ i : Fin n, (x i) ^ 2 + ∑ i : Fin n, (y i) ^ 2)) := by ring
        _ ≤ ε * Real.exp (M * t) * (1 + (∑ i : Fin n, (x i) ^ 2 + ∑ i : Fin n, (y i) ^ 2)) := by gcongr
        _ = ε * Real.exp (M * t) * (1 + ∑ i : Fin n, (x i) ^ 2 + ∑ i : Fin n, (y i) ^ 2) := by ring
    have hR1 : 2 * B_const / ε + 1 ≤ R := le_max_right _ _
    have hεQ : B_const ≤ (ε / 2) * Q := by
      have h1 : 2 * B_const / ε ≤ Q := by linarith
      have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ ε / 2 by positivity)
      have hne : ε ≠ 0 := ne_of_gt hε
      have hsimp : (ε / 2) * (2 * B_const / ε) = B_const := by field_simp [hne]
      linarith
    have hW0_le : W0 ≤ |W0| := le_abs_self W0
    dsimp [W, B_const] at *
    linarith
  -- Find global minimum of `W` on `[0, 1] × (Fin n → ℝ) × (Fin n → ℝ)` via compact box `S`
  let box : Set (Fin n → ℝ) := Metric.closedBall 0 R
  let S : Set (ℝ × (Fin n → ℝ) × (Fin n → ℝ)) := Set.Icc 0 1 ×ˢ (box ×ˢ box)
  have hS_comp : IsCompact S := isCompact_Icc.prod ((isCompact_closedBall 0 R).prod (isCompact_closedBall 0 R))
  have hS_ne : S.Nonempty := ⟨(0, 0, 0), ⟨⟨le_refl 0, zero_le_one⟩,
    ⟨Metric.mem_closedBall_self (le_of_lt hR_pos), Metric.mem_closedBall_self (le_of_lt hR_pos)⟩⟩⟩
  have hW_cont : ContinuousOn (fun p : ℝ × (Fin n → ℝ) × (Fin n → ℝ) => W p.1 p.2.1 p.2.2) S := by
    have hU1 : ContinuousOn (fun p : ℝ × (Fin n → ℝ) × (Fin n → ℝ) => U w₀ p.1 (lam • p.2.1 + (1 - lam) • p.2.2)) S :=
      ContinuousOn.comp
        (g := fun q : ℝ × (Fin n → ℝ) => U w₀ q.1 q.2)
        (f := fun p : ℝ × (Fin n → ℝ) × (Fin n → ℝ) => (p.1, lam • p.2.1 + (1 - lam) • p.2.2))
        (U_continuousOn hw₀_cont) (by fun_prop) (fun p hp => ⟨hp.1.1, Set.mem_univ _⟩)
    have hU2 : ContinuousOn (fun p : ℝ × (Fin n → ℝ) × (Fin n → ℝ) => U u₀ p.1 p.2.1) S :=
      ContinuousOn.comp
        (g := fun q : ℝ × (Fin n → ℝ) => U u₀ q.1 q.2)
        (f := fun p : ℝ × (Fin n → ℝ) × (Fin n → ℝ) => (p.1, p.2.1))
        (U_continuousOn hu₀_cont) (by fun_prop) (fun p hp => ⟨hp.1.1, Set.mem_univ _⟩)
    have hU3 : ContinuousOn (fun p : ℝ × (Fin n → ℝ) × (Fin n → ℝ) => U v₀ p.1 p.2.2) S :=
      ContinuousOn.comp
        (g := fun q : ℝ × (Fin n → ℝ) => U v₀ q.1 q.2)
        (f := fun p : ℝ × (Fin n → ℝ) × (Fin n → ℝ) => (p.1, p.2.2))
        (U_continuousOn hv₀_cont) (by fun_prop) (fun p hp => ⟨hp.1.1, Set.mem_univ _⟩)
    have hψ_cont : Continuous (fun p : ℝ × (Fin n → ℝ) × (Fin n → ℝ) => ψ p.1 p.2.1 p.2.2) := by
      unfold ψ; fun_prop
    exact ((hU1.sub (continuousOn_const.mul hU2)).sub (continuousOn_const.mul hU3)).add hψ_cont.continuousOn
  obtain ⟨⟨tstar, xstar, ystar⟩, hmem_S, hmin_S⟩ := hS_comp.exists_isMinOn hS_ne hW_cont
  have hmin_global : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x y : Fin n → ℝ, W tstar xstar ystar ≤ W t x y := by
    intro t ht x y
    by_cases hbox : max ‖x‖ ‖y‖ ≤ R
    · have hmem : (t, x, y) ∈ S := ⟨ht, ⟨by simpa [box, Metric.mem_closedBall, dist_zero_right] using le_trans (le_max_left _ _) hbox,
        by simpa [box, Metric.mem_closedBall, dist_zero_right] using le_trans (le_max_right _ _) hbox⟩⟩
      exact hmin_S hmem
    · push Not at hbox
      have h0_mem : ((0 : ℝ), (0 : Fin n → ℝ), (0 : Fin n → ℝ)) ∈ S :=
        ⟨⟨le_refl 0, zero_le_one⟩, ⟨Metric.mem_closedBall_self (le_of_lt hR_pos),
          Metric.mem_closedBall_self (le_of_lt hR_pos)⟩⟩
      have h0 : W tstar xstar ystar ≤ W0 := hmin_S h0_mem
      linarith [hcoerc t ht x y hbox]
  -- Show `0 < W tstar xstar ystar`
  suffices hmin_pos : 0 < W tstar xstar ystar by
    intro t ht x y; exact lt_of_lt_of_le hmin_pos (hmin_global t ht x y)
  by_contra hle0
  push Not at hle0
  -- Must have `tstar > 0` since `W 0 x y ≥ ε > 0`
  have ht_pos : 0 < tstar := by
    by_contra h0
    have ht0 : tstar = 0 := le_antisymm (not_lt.mp h0) hmem_S.1.1
    subst ht0
    have hC0 : 0 ≤ U w₀ 0 (lam • xstar + (1 - lam) • ystar) - lam * U u₀ 0 xstar - (1 - lam) * U v₀ 0 ystar := by
      simp only [U, H_zero, Function.comp_apply, Φinv_Φ]
      linarith [hineq xstar ystar]
    have hψ0 : ε ≤ ψ 0 xstar ystar := by
      dsimp [ψ]
      have h1 : 0 ≤ ∑ i : Fin n, (xstar i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      have h2 : 0 ≤ ∑ i : Fin n, (ystar i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      rw [mul_zero, Real.exp_zero, mul_one]; nlinarith
    dsimp [W] at hle0
    linarith
  -- Apply Borell's PDE at `(tstar, xstar, ystar)`
  set zstar := lam • xstar + (1 - lam) • ystar
  obtain ⟨ut, ux, uxx, hUt, hUx, hUPDE⟩ := U_PDE hL hu₀_lip hu₀_cont ht_pos xstar
  obtain ⟨vt, vx, vxx, hVt, hVx, hVPDE⟩ := U_PDE hL hv₀_lip hv₀_cont ht_pos ystar
  obtain ⟨wt, wx, wxx, hWt, hWx, hWPDE⟩ := U_PDE hL hw₀_lip hw₀_cont ht_pos zstar
  -- Time derivative `∂_t W ≤ 0` at `tstar`
  have hψt : HasDerivAt (fun t => ψ t xstar ystar) (M * ψ tstar xstar ystar) tstar := by
    have h1 : HasDerivAt (fun t => Real.exp (M * t)) (Real.exp (M * tstar) * M) tstar := by
      simpa using ((hasDerivAt_id tstar).const_mul M).exp
    have h2 := (h1.const_mul ε).mul_const (1 + ∑ i : Fin n, (xstar i) ^ 2 + ∑ i : Fin n, (ystar i) ^ 2)
    refine h2.congr_deriv ?_
    dsimp [ψ]; ring
  have hWt_deriv : HasDerivAt (fun t => W t xstar ystar) (wt - lam * ut - (1 - lam) * vt + M * ψ tstar xstar ystar) tstar :=
    ((hWt.sub (hUt.const_mul lam)).sub (hVt.const_mul (1 - lam))).add hψt
  have hWt_le0 : wt - lam * ut - (1 - lam) * vt + M * ψ tstar xstar ystar ≤ 0 :=
    deriv_le_zero_of_isMinOn_Icc ht_pos hmem_S.1.2 (fun t ht => hmin_global t ht xstar ystar) hWt_deriv
  -- Spatial first and second optimality conditions for each coordinate `i`
  have hcoord : ∀ i : Fin n,
      lam * (wx i - ux i) + 2 * ε * Real.exp (M * tstar) * xstar i = 0 ∧
      (1 - lam) * (wx i - vx i) + 2 * ε * Real.exp (M * tstar) * ystar i = 0 ∧
      0 ≤ wxx i - lam * uxx i - (1 - lam) * vxx i + 4 * ε * Real.exp (M * tstar) := by
    intro i
    -- 1. First derivative w.r.t. `x_i` vanishes
    have hfx_min : IsLocalMin (fun s => W tstar (Function.update xstar i s) ystar) (xstar i) :=
      Filter.Eventually.of_forall fun s => by
        simpa [Function.update_eq_self] using hmin_global tstar hmem_S.1 (Function.update xstar i s) ystar
    have hzx : ∀ s, lam • Function.update xstar i s + (1 - lam) • ystar =
        Function.update zstar i (lam * s + (1 - lam) * ystar i) := by
      intro s; ext j
      by_cases hj : j = i
      · subst hj; simp [zstar]
      · simp [zstar, Function.update_of_ne hj]
    have hW_dx : HasDerivAt (fun s => W tstar (Function.update xstar i s) ystar)
        (lam * (wx i - ux i) + 2 * ε * Real.exp (M * tstar) * xstar i) (xstar i) := by
      have hw_s : HasDerivAt (fun s => U w₀ tstar (lam • Function.update xstar i s + (1 - lam) • ystar)) (wx i * lam) (xstar i) := by
        simp_rw [hzx]
        have hlin : HasDerivAt (fun s => lam * s + (1 - lam) * ystar i) lam (xstar i) := by
          simpa using ((hasDerivAt_id (xstar i)).const_mul lam).add_const ((1 - lam) * ystar i)
        have hzi : lam * xstar i + (1 - lam) * ystar i = zstar i := by simp [zstar]
        have hW_at : HasDerivAt (fun r => U w₀ tstar (Function.update zstar i r)) (wx i)
            (lam * xstar i + (1 - lam) * ystar i) := by rw [hzi]; exact (hWx i).1
        have hcomp := hW_at.comp (xstar i) hlin
        exact hcomp
      have hψ_s : HasDerivAt (fun s => ψ tstar (Function.update xstar i s) ystar)
          (2 * ε * Real.exp (M * tstar) * xstar i) (xstar i) := by
        have hsum_upd : ∀ s, ∑ j : Fin n, (Function.update xstar i s j) ^ 2 =
            s ^ 2 + ∑ j ∈ Finset.univ.erase i, (xstar j) ^ 2 := by
          intro s
          rw [← Finset.add_sum_erase Finset.univ (fun j => (Function.update xstar i s j) ^ 2) (Finset.mem_univ i)]
          simp only [Function.update_self]
          congr 1
          exact Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
        have hfun : (fun s => ψ tstar (Function.update xstar i s) ystar) =
            fun s => ε * Real.exp (M * tstar) * (1 + (s ^ 2 + ∑ j ∈ Finset.univ.erase i, (xstar j) ^ 2) +
              ∑ j : Fin n, (ystar j) ^ 2) := funext fun s => by dsimp [ψ]; rw [hsum_upd]
        rw [hfun]
        have hd : HasDerivAt (fun s => 1 + (s ^ 2 + ∑ j ∈ Finset.univ.erase i, (xstar j) ^ 2) +
            ∑ j : Fin n, (ystar j) ^ 2) (2 * xstar i) (xstar i) := by
          refine ((((hasDerivAt_pow 2 (xstar i)).add_const _).const_add 1).add_const _).congr_deriv ?_
          norm_num
        refine (hd.const_mul (ε * Real.exp (M * tstar))).congr_deriv ?_; ring
      have hv_const : HasDerivAt (fun _ : ℝ => (1 - lam) * U v₀ tstar ystar) 0 (xstar i) := hasDerivAt_const _ _
      have hcomb := ((hw_s.sub ((hUx i).1.const_mul lam)).sub hv_const).add hψ_s
      refine hcomb.congr_deriv ?_; ring
    have hfx0 : lam * (wx i - ux i) + 2 * ε * Real.exp (M * tstar) * xstar i = 0 :=
      hfx_min.hasDerivAt_eq_zero hW_dx
    -- 2. First derivative w.r.t. `y_i` vanishes
    have hfy_min : IsLocalMin (fun s => W tstar xstar (Function.update ystar i s)) (ystar i) :=
      Filter.Eventually.of_forall fun s => by
        simpa [Function.update_eq_self] using hmin_global tstar hmem_S.1 xstar (Function.update ystar i s)
    have hzy : ∀ s, lam • xstar + (1 - lam) • Function.update ystar i s =
        Function.update zstar i (lam * xstar i + (1 - lam) * s) := by
      intro s; ext j
      by_cases hj : j = i
      · subst hj; simp [zstar]
      · simp [zstar, Function.update_of_ne hj]
    have hW_dy : HasDerivAt (fun s => W tstar xstar (Function.update ystar i s))
        ((1 - lam) * (wx i - vx i) + 2 * ε * Real.exp (M * tstar) * ystar i) (ystar i) := by
      have hw_s : HasDerivAt (fun s => U w₀ tstar (lam • xstar + (1 - lam) • Function.update ystar i s)) (wx i * (1 - lam)) (ystar i) := by
        simp_rw [hzy]
        have hlin : HasDerivAt (fun s => lam * xstar i + (1 - lam) * s) (1 - lam) (ystar i) := by
          simpa using ((hasDerivAt_id (ystar i)).const_mul (1 - lam)).const_add (lam * xstar i)
        have hzi : lam * xstar i + (1 - lam) * ystar i = zstar i := by simp [zstar]
        have hW_at : HasDerivAt (fun r => U w₀ tstar (Function.update zstar i r)) (wx i)
            (lam * xstar i + (1 - lam) * ystar i) := by rw [hzi]; exact (hWx i).1
        have hcomp := hW_at.comp (ystar i) hlin
        exact hcomp
      have hψ_s : HasDerivAt (fun s => ψ tstar xstar (Function.update ystar i s))
          (2 * ε * Real.exp (M * tstar) * ystar i) (ystar i) := by
        have hsum_upd : ∀ s, ∑ j : Fin n, (Function.update ystar i s j) ^ 2 =
            s ^ 2 + ∑ j ∈ Finset.univ.erase i, (ystar j) ^ 2 := by
          intro s
          rw [← Finset.add_sum_erase Finset.univ (fun j => (Function.update ystar i s j) ^ 2) (Finset.mem_univ i)]
          simp only [Function.update_self]
          congr 1
          exact Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
        have hfun : (fun s => ψ tstar xstar (Function.update ystar i s)) =
            fun s => ε * Real.exp (M * tstar) * (1 + ∑ j : Fin n, (xstar j) ^ 2 +
              (s ^ 2 + ∑ j ∈ Finset.univ.erase i, (ystar j) ^ 2)) := funext fun s => by dsimp [ψ]; rw [hsum_upd]
        rw [hfun]
        have hd : HasDerivAt (fun s => 1 + ∑ j : Fin n, (xstar j) ^ 2 +
            (s ^ 2 + ∑ j ∈ Finset.univ.erase i, (ystar j) ^ 2)) (2 * ystar i) (ystar i) := by
          refine (((hasDerivAt_pow 2 (ystar i)).add_const _).const_add _).congr_deriv ?_
          norm_num
        refine (hd.const_mul (ε * Real.exp (M * tstar))).congr_deriv ?_; ring
      have hu_const : HasDerivAt (fun _ : ℝ => lam * U u₀ tstar xstar) 0 (ystar i) := hasDerivAt_const _ _
      have hcomb := ((hw_s.sub hu_const).sub ((hVx i).1.const_mul (1 - lam))).add hψ_s
      refine hcomb.congr_deriv ?_; ring
    have hfy0 : (1 - lam) * (wx i - vx i) + 2 * ε * Real.exp (M * tstar) * ystar i = 0 :=
      hfy_min.hasDerivAt_eq_zero hW_dy
    -- 3. Diagonal second derivative `d²/ds²|_{s=0} W(tstar, xstar + s e_i, ystar + s e_i) ≥ 0`
    let diag : ℝ → ℝ := fun s =>
      W tstar (Function.update xstar i (xstar i + s)) (Function.update ystar i (ystar i + s))
    have hdiag_min : IsLocalMin diag 0 :=
      Filter.Eventually.of_forall fun s => by
        simpa [diag, Function.update_eq_self] using
          hmin_global tstar hmem_S.1 (Function.update xstar i (xstar i + s)) (Function.update ystar i (ystar i + s))
    have hzd : ∀ s, lam • Function.update xstar i (xstar i + s) + (1 - lam) • Function.update ystar i (ystar i + s) =
        Function.update zstar i (zstar i + s) := by
      intro s; ext j
      by_cases hj : j = i
      · subst hj; simp only [zstar, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.update_self]; ring
      · simp [zstar, Function.update_of_ne hj]
    obtain ⟨ux_fn, hux_ev, hux_d2⟩ := (hUx i).2.1
    obtain ⟨vx_fn, hvx_ev, hvx_d2⟩ := (hVx i).2.1
    obtain ⟨wx_fn, hwx_ev, hwx_d2⟩ := (hWx i).2.1
    let diag' : ℝ → ℝ := fun s =>
      wx_fn (zstar i + s) - lam * ux_fn (xstar i + s) - (1 - lam) * vx_fn (ystar i + s) +
        ε * Real.exp (M * tstar) * (2 * (xstar i + s) + 2 * (ystar i + s))
    have hdiag_d1 : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt diag (diag' s) s := by
      have ht1 : Tendsto (fun s : ℝ => zstar i + s) (𝓝 0) (𝓝 (zstar i)) := by
        simpa using ((continuous_add_left (zstar i)).continuousAt (x := (0 : ℝ))).tendsto
      have ht2 : Tendsto (fun s : ℝ => xstar i + s) (𝓝 0) (𝓝 (xstar i)) := by
        simpa using ((continuous_add_left (xstar i)).continuousAt (x := (0 : ℝ))).tendsto
      have ht3 : Tendsto (fun s : ℝ => ystar i + s) (𝓝 0) (𝓝 (ystar i)) := by
        simpa using ((continuous_add_left (ystar i)).continuousAt (x := (0 : ℝ))).tendsto
      have h1 : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt (fun r => U w₀ tstar (Function.update zstar i r)) (wx_fn (zstar i + s)) (zstar i + s) :=
        ht1.eventually hwx_ev
      have h2 : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt (fun r => U u₀ tstar (Function.update xstar i r)) (ux_fn (xstar i + s)) (xstar i + s) :=
        ht2.eventually hux_ev
      have h3 : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt (fun r => U v₀ tstar (Function.update ystar i r)) (vx_fn (ystar i + s)) (ystar i + s) :=
        ht3.eventually hvx_ev
      filter_upwards [h1, h2, h3] with s hw_s hu_s hv_s
      have hfun : diag = fun r =>
          U w₀ tstar (Function.update zstar i (zstar i + r)) -
          lam * U u₀ tstar (Function.update xstar i (xstar i + r)) -
          (1 - lam) * U v₀ tstar (Function.update ystar i (ystar i + r)) +
          ψ tstar (Function.update xstar i (xstar i + r)) (Function.update ystar i (ystar i + r)) :=
        funext fun r => by simp only [diag, W, hzd]
      rw [hfun]
      have hdw : HasDerivAt (fun r => U w₀ tstar (Function.update zstar i (zstar i + r))) (wx_fn (zstar i + s)) s := by
        have h0 := hw_s.comp s ((hasDerivAt_id s).const_add (zstar i))
        exact h0.congr_deriv (by ring)
      have hdu : HasDerivAt (fun r => U u₀ tstar (Function.update xstar i (xstar i + r))) (ux_fn (xstar i + s)) s := by
        have h0 := hu_s.comp s ((hasDerivAt_id s).const_add (xstar i))
        exact h0.congr_deriv (by ring)
      have hdv : HasDerivAt (fun r => U v₀ tstar (Function.update ystar i (ystar i + r))) (vx_fn (ystar i + s)) s := by
        have h0 := hv_s.comp s ((hasDerivAt_id s).const_add (ystar i))
        exact h0.congr_deriv (by ring)
      have hdψ : HasDerivAt (fun r => ψ tstar (Function.update xstar i (xstar i + r)) (Function.update ystar i (ystar i + r)))
          (ε * Real.exp (M * tstar) * (2 * (xstar i + s) + 2 * (ystar i + s))) s := by
        have hx_upd : ∀ r, ∑ j : Fin n, (Function.update xstar i (xstar i + r) j) ^ 2 =
            (xstar i + r) ^ 2 + ∑ j ∈ Finset.univ.erase i, (xstar j) ^ 2 := by
          intro r
          rw [← Finset.add_sum_erase Finset.univ (fun j => (Function.update xstar i (xstar i + r) j) ^ 2) (Finset.mem_univ i)]
          simp only [Function.update_self]; congr 1
          exact Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
        have hy_upd : ∀ r, ∑ j : Fin n, (Function.update ystar i (ystar i + r) j) ^ 2 =
            (ystar i + r) ^ 2 + ∑ j ∈ Finset.univ.erase i, (ystar j) ^ 2 := by
          intro r
          rw [← Finset.add_sum_erase Finset.univ (fun j => (Function.update ystar i (ystar i + r) j) ^ 2) (Finset.mem_univ i)]
          simp only [Function.update_self]; congr 1
          exact Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
        have hψ_fun : (fun r => ψ tstar (Function.update xstar i (xstar i + r)) (Function.update ystar i (ystar i + r))) =
            fun r => ε * Real.exp (M * tstar) * (1 + ((xstar i + r) ^ 2 + ∑ j ∈ Finset.univ.erase i, (xstar j) ^ 2) +
              ((ystar i + r) ^ 2 + ∑ j ∈ Finset.univ.erase i, (ystar j) ^ 2)) :=
          funext fun r => by dsimp [ψ]; rw [hx_upd, hy_upd]
        rw [hψ_fun]
        have hx2 : HasDerivAt (fun r => (xstar i + r) ^ 2) (2 * (xstar i + s)) s :=
          (((hasDerivAt_id s).const_add (xstar i)).pow 2).congr_deriv (by norm_num)
        have hy2 : HasDerivAt (fun r => (ystar i + r) ^ 2) (2 * (ystar i + s)) s :=
          (((hasDerivAt_id s).const_add (ystar i)).pow 2).congr_deriv (by norm_num)
        have hsum_d := ((hx2.add_const (∑ j ∈ Finset.univ.erase i, (xstar j) ^ 2)).const_add 1).add
          (hy2.add_const (∑ j ∈ Finset.univ.erase i, (ystar j) ^ 2))
        exact hsum_d.const_mul (ε * Real.exp (M * tstar))
      exact ((hdw.sub (hdu.const_mul lam)).sub (hdv.const_mul (1 - lam))).add hdψ
    have hdiag_d2 : HasDerivAt diag' (wxx i - lam * uxx i - (1 - lam) * vxx i + 4 * ε * Real.exp (M * tstar)) 0 := by
      have h1 : HasDerivAt (fun s => wx_fn (zstar i + s)) (wxx i) 0 := by
        have hwx' : HasDerivAt wx_fn (wxx i) (zstar i + 0) := by simpa using hwx_d2
        exact (HasDerivAt.comp 0 hwx' ((hasDerivAt_id (0 : ℝ)).const_add (zstar i))).congr_deriv (by ring)
      have h2 : HasDerivAt (fun s => ux_fn (xstar i + s)) (uxx i) 0 := by
        have hux' : HasDerivAt ux_fn (uxx i) (xstar i + 0) := by simpa using hux_d2
        exact (HasDerivAt.comp 0 hux' ((hasDerivAt_id (0 : ℝ)).const_add (xstar i))).congr_deriv (by ring)
      have h3 : HasDerivAt (fun s => vx_fn (ystar i + s)) (vxx i) 0 := by
        have hvx' : HasDerivAt vx_fn (vxx i) (ystar i + 0) := by simpa using hvx_d2
        exact (HasDerivAt.comp 0 hvx' ((hasDerivAt_id (0 : ℝ)).const_add (ystar i))).congr_deriv (by ring)
      have h4 : HasDerivAt (fun s => ε * Real.exp (M * tstar) * (2 * (xstar i + s) + 2 * (ystar i + s)))
          (4 * ε * Real.exp (M * tstar)) 0 := by
        have hlin : HasDerivAt (fun s => 2 * (xstar i + s) + 2 * (ystar i + s)) 4 0 := by
          have ha : HasDerivAt (fun s => 2 * (xstar i + s)) 2 0 :=
            (((hasDerivAt_id (0 : ℝ)).const_add (xstar i)).const_mul 2).congr_deriv (by ring)
          have hb : HasDerivAt (fun s => 2 * (ystar i + s)) 2 0 :=
            (((hasDerivAt_id (0 : ℝ)).const_add (ystar i)).const_mul 2).congr_deriv (by ring)
          exact (ha.add hb).congr_deriv (by norm_num)
        exact (hlin.const_mul (ε * Real.exp (M * tstar))).congr_deriv (by ring)
      exact ((h1.sub (h2.const_mul lam)).sub (h3.const_mul (1 - lam))).add h4
    exact ⟨hfx0, hfy0, second_deriv_nonneg_of_isLocalMin hdiag_min hdiag_d1 hdiag_d2⟩
  -- Combine PDE + optimality conditions to derive contradiction `0 < ψ ≤ 0`!
  set Cval := U w₀ tstar zstar - lam * U u₀ tstar xstar - (1 - lam) * U v₀ tstar ystar
  have hC_neg : Cval ≤ 0 := by
    have hψ_pos : 0 < ψ tstar xstar ystar := by
      dsimp [ψ]
      have h1 : 0 ≤ ∑ i : Fin n, (xstar i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      have h2 : 0 ≤ ∑ i : Fin n, (ystar i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      positivity
    dsimp [W, Cval] at hle0 ⊢
    linarith
  have hLap : 0 ≤ ∑ i : Fin n, (wxx i - lam * uxx i - (1 - lam) * vxx i) + 4 * (n : ℝ) * ε * Real.exp (M * tstar) := by
    have h1 : 0 ≤ ∑ i : Fin n, (wxx i - lam * uxx i - (1 - lam) * vxx i + 4 * ε * Real.exp (M * tstar)) :=
      Finset.sum_nonneg fun i _ => (hcoord i).2.2
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    linarith
  have hnonlin_i : ∀ i : Fin n,
      lam * U u₀ tstar xstar * (ux i) ^ 2 + (1 - lam) * U v₀ tstar ystar * (vx i) ^ 2 - U w₀ tstar zstar * (wx i) ^ 2 ≥
        -4 * L * ε * Real.exp (M * tstar) * (|U u₀ tstar xstar| * |xstar i| + |U v₀ tstar ystar| * |ystar i|) := by
    intro i
    have hdiff_u : lam * (ux i - wx i) = 2 * ε * Real.exp (M * tstar) * xstar i := by linarith [(hcoord i).1]
    have hdiff_v : (1 - lam) * (vx i - wx i) = 2 * ε * Real.exp (M * tstar) * ystar i := by linarith [(hcoord i).2.1]
    have halg : lam * U u₀ tstar xstar * (ux i) ^ 2 + (1 - lam) * U v₀ tstar ystar * (vx i) ^ 2 - U w₀ tstar zstar * (wx i) ^ 2 =
        (-Cval) * (wx i) ^ 2 + U u₀ tstar xstar * (ux i + wx i) * (lam * (ux i - wx i)) +
          U v₀ tstar ystar * (vx i + wx i) * ((1 - lam) * (vx i - wx i)) := by
      dsimp [Cval]; ring
    rw [halg, hdiff_u, hdiff_v]
    have h1 : 0 ≤ (-Cval) * (wx i) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have hu_sum : |ux i + wx i| ≤ 2 * L :=
      (abs_add_le _ _).trans (by linarith [(hUx i).2.2, (hWx i).2.2])
    have hv_sum : |vx i + wx i| ≤ 2 * L :=
      (abs_add_le _ _).trans (by linarith [(hVx i).2.2, (hWx i).2.2])
    have h2 : |U u₀ tstar xstar * (ux i + wx i) * (2 * ε * Real.exp (M * tstar) * xstar i)| ≤
        4 * L * ε * Real.exp (M * tstar) * (|U u₀ tstar xstar| * |xstar i|) := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos hε, abs_of_pos (Real.exp_pos _)]
      have hnn : 0 ≤ |U u₀ tstar xstar| * (2 * ε * Real.exp (M * tstar) * |xstar i|) := by positivity
      calc |U u₀ tstar xstar| * |ux i + wx i| * (2 * ε * Real.exp (M * tstar) * |xstar i|)
          = |ux i + wx i| * (|U u₀ tstar xstar| * (2 * ε * Real.exp (M * tstar) * |xstar i|)) := by ring
        _ ≤ (2 * L) * (|U u₀ tstar xstar| * (2 * ε * Real.exp (M * tstar) * |xstar i|)) :=
            mul_le_mul_of_nonneg_right hu_sum hnn
        _ = 4 * L * ε * Real.exp (M * tstar) * (|U u₀ tstar xstar| * |xstar i|) := by ring
    have h3 : |U v₀ tstar ystar * (vx i + wx i) * (2 * ε * Real.exp (M * tstar) * ystar i)| ≤
        4 * L * ε * Real.exp (M * tstar) * (|U v₀ tstar ystar| * |ystar i|) := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos hε, abs_of_pos (Real.exp_pos _)]
      have hnn : 0 ≤ |U v₀ tstar ystar| * (2 * ε * Real.exp (M * tstar) * |ystar i|) := by positivity
      calc |U v₀ tstar ystar| * |vx i + wx i| * (2 * ε * Real.exp (M * tstar) * |ystar i|)
          = |vx i + wx i| * (|U v₀ tstar ystar| * (2 * ε * Real.exp (M * tstar) * |ystar i|)) := by ring
        _ ≤ (2 * L) * (|U v₀ tstar ystar| * (2 * ε * Real.exp (M * tstar) * |ystar i|)) :=
            mul_le_mul_of_nonneg_right hv_sum hnn
        _ = 4 * L * ε * Real.exp (M * tstar) * (|U v₀ tstar ystar| * |ystar i|) := by ring
    linarith [(abs_le.mp h2).1, (abs_le.mp h3).1]
  -- Sum the nonlinear bound over `i : Fin n`
  have hCS : ∀ a : Fin n → ℝ, (∑ i : Fin n, |a i|) ^ 2 ≤ (n : ℝ) * ∑ i : Fin n, (a i) ^ 2 := by
    intro a
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin n => |a i|)
    simpa [sq_abs] using h
  have hlin1 : ∀ a : Fin n → ℝ, ∑ i : Fin n, |a i| ≤ (n : ℝ) + ∑ i : Fin n, (a i) ^ 2 := by
    intro a
    have : ∀ i : Fin n, |a i| ≤ 1 + (a i) ^ 2 := fun i => by nlinarith [sq_abs (a i), sq_nonneg (|a i| - 1)]
    calc ∑ i : Fin n, |a i| ≤ ∑ _i : Fin n, (1 : ℝ) + ∑ i : Fin n, (a i) ^ 2 := by
          rw [← Finset.sum_add_distrib]; exact Finset.sum_le_sum fun i _ => this i
      _ = (n : ℝ) + ∑ i : Fin n, (a i) ^ 2 := by simp
  have hnonlin_sum : ∑ i : Fin n, (lam * U u₀ tstar xstar * (ux i) ^ 2 + (1 - lam) * U v₀ tstar ystar * (vx i) ^ 2 - U w₀ tstar zstar * (wx i) ^ 2) ≥
      -8 * L * (A * ((n : ℝ) + 1) + L * (n : ℝ)) * ψ tstar xstar ystar := by
    have h1 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hnonlin_i i
    have h2 : ∑ i : Fin n, (-4 * L * ε * Real.exp (M * tstar) * (|U u₀ tstar xstar| * |xstar i| + |U v₀ tstar ystar| * |ystar i|)) =
        -4 * L * ε * Real.exp (M * tstar) * (|U u₀ tstar xstar| * ∑ i : Fin n, |xstar i| + |U v₀ tstar ystar| * ∑ i : Fin n, |ystar i|) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [h2] at h1
    have hSx_nn : 0 ≤ ∑ i : Fin n, |xstar i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hSy_nn : 0 ≤ ∑ i : Fin n, |ystar i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hUx_b : |U u₀ tstar xstar| * ∑ i : Fin n, |xstar i| ≤
        (A * ((n : ℝ) + 1) + L * (n : ℝ)) * (1 + ∑ i : Fin n, (xstar i) ^ 2) := by
      have hb := hU_bdd tstar hmem_S.1 xstar
      have hsqx : 0 ≤ ∑ i : Fin n, (xstar i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      calc |U u₀ tstar xstar| * ∑ i : Fin n, |xstar i|
          ≤ (A + L * ∑ i : Fin n, |xstar i|) * ∑ i : Fin n, |xstar i| := mul_le_mul_of_nonneg_right hb hSx_nn
        _ = A * ∑ i : Fin n, |xstar i| + L * (∑ i : Fin n, |xstar i|) ^ 2 := by ring
        _ ≤ A * ((n : ℝ) + ∑ i : Fin n, (xstar i) ^ 2) + L * ((n : ℝ) * ∑ i : Fin n, (xstar i) ^ 2) := by
            nlinarith [hlin1 xstar, hCS xstar]
        _ ≤ (A * ((n : ℝ) + 1) + L * (n : ℝ)) * (1 + ∑ i : Fin n, (xstar i) ^ 2) := by
            have hA_nn : 0 ≤ A := le_of_lt hA_pos
            have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
            nlinarith [mul_nonneg hA_nn hsqx, mul_nonneg hL hnn, mul_nonneg hA_nn hnn,
              mul_nonneg (mul_nonneg hA_nn hnn) hsqx]
    have hVy_b : |U v₀ tstar ystar| * ∑ i : Fin n, |ystar i| ≤
        (A * ((n : ℝ) + 1) + L * (n : ℝ)) * (1 + ∑ i : Fin n, (ystar i) ^ 2) := by
      have hb := hV_bdd tstar hmem_S.1 ystar
      have hsqy : 0 ≤ ∑ i : Fin n, (ystar i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      calc |U v₀ tstar ystar| * ∑ i : Fin n, |ystar i|
          ≤ (A + L * ∑ i : Fin n, |ystar i|) * ∑ i : Fin n, |ystar i| := mul_le_mul_of_nonneg_right hb hSy_nn
        _ = A * ∑ i : Fin n, |ystar i| + L * (∑ i : Fin n, |ystar i|) ^ 2 := by ring
        _ ≤ A * ((n : ℝ) + ∑ i : Fin n, (ystar i) ^ 2) + L * ((n : ℝ) * ∑ i : Fin n, (ystar i) ^ 2) := by
            nlinarith [hlin1 ystar, hCS ystar]
        _ ≤ (A * ((n : ℝ) + 1) + L * (n : ℝ)) * (1 + ∑ i : Fin n, (ystar i) ^ 2) := by
            have hA_nn : 0 ≤ A := le_of_lt hA_pos
            have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
            nlinarith [mul_nonneg hA_nn hsqy, mul_nonneg hL hnn, mul_nonneg hA_nn hnn,
              mul_nonneg (mul_nonneg hA_nn hnn) hsqy]
    have hcomb_xy : |U u₀ tstar xstar| * ∑ i : Fin n, |xstar i| + |U v₀ tstar ystar| * ∑ i : Fin n, |ystar i| ≤
        2 * (A * ((n : ℝ) + 1) + L * (n : ℝ)) * (1 + ∑ i : Fin n, (xstar i) ^ 2 + ∑ i : Fin n, (ystar i) ^ 2) := by
      have hK_nn : 0 ≤ A * ((n : ℝ) + 1) + L * (n : ℝ) := by positivity
      have hsqx : 0 ≤ ∑ i : Fin n, (xstar i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hsqy : 0 ≤ ∑ i : Fin n, (ystar i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      nlinarith
    have hcoeff_nn : 0 ≤ 4 * L * ε * Real.exp (M * tstar) := by positivity
    -- Wait: notice `2 * 4 * L` = `8 * L`, and `wt - lam ut - (1-lam) vt` has factor `(1/2)` in front, so `(1/2) * 8 * L = 4 * L`!
    dsimp [ψ]
    nlinarith [mul_le_mul_of_nonneg_left hcomb_xy hcoeff_nn]
  -- Wait: rewrite `wt - lam * ut - (1 - lam) * vt` using the 3 PDEs
  have hpde_comb : wt - lam * ut - (1 - lam) * vt =
      (1 / 2) * ∑ i : Fin n, (wxx i - lam * uxx i - (1 - lam) * vxx i) +
      (1 / 2) * ∑ i : Fin n, (lam * U u₀ tstar xstar * (ux i) ^ 2 + (1 - lam) * U v₀ tstar ystar * (vx i) ^ 2 - U w₀ tstar zstar * (wx i) ^ 2) := by
    rw [hWPDE, hUPDE, hVPDE, ← mul_add, ← Finset.sum_add_distrib]
    have hmul1 : lam * ((1 / 2) * ∑ i : Fin n, (uxx i - U u₀ tstar xstar * (ux i) ^ 2)) =
        (1 / 2) * ∑ i : Fin n, (lam * (uxx i - U u₀ tstar xstar * (ux i) ^ 2)) := by
      rw [← mul_assoc, mul_comm lam (1 / 2), mul_assoc, Finset.mul_sum]
    have hmul2 : (1 - lam) * ((1 / 2) * ∑ i : Fin n, (vxx i - U v₀ tstar ystar * (vx i) ^ 2)) =
        (1 / 2) * ∑ i : Fin n, ((1 - lam) * (vxx i - U v₀ tstar ystar * (vx i) ^ 2)) := by
      rw [← mul_assoc, mul_comm (1 - lam) (1 / 2), mul_assoc, Finset.mul_sum]
    rw [hmul1, hmul2, ← mul_sub, ← mul_sub, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => by ring
  have hψ_pos : 0 < ψ tstar xstar ystar := by
    dsimp [ψ]
    have h1 : 0 ≤ ∑ i : Fin n, (xstar i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have h2 : 0 ≤ ∑ i : Fin n, (ystar i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    positivity
  have h4n : 2 * (n : ℝ) * ε * Real.exp (M * tstar) ≤ 2 * (n : ℝ) * ψ tstar xstar ystar := by
    dsimp [ψ]
    have h1 : 0 ≤ ∑ i : Fin n, (xstar i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have h2 : 0 ≤ ∑ i : Fin n, (ystar i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have h3 : (1 : ℝ) ≤ 1 + ∑ i : Fin n, (xstar i) ^ 2 + ∑ i : Fin n, (ystar i) ^ 2 := by linarith
    calc 2 * (n : ℝ) * ε * Real.exp (M * tstar)
        = 2 * (n : ℝ) * (ε * Real.exp (M * tstar) * 1) := by ring
      _ ≤ 2 * (n : ℝ) * (ε * Real.exp (M * tstar) *
            (1 + ∑ i : Fin n, (xstar i) ^ 2 + ∑ i : Fin n, (ystar i) ^ 2)) := by gcongr
  -- Notice `hnonlin_sum` gave `-8 * L * (...) * ψ` before `(1/2)`, so `(1/2)` makes `-4 * L * (...) * ψ`!
  -- Wait: in `hnonlin_sum`, the statement had `-4 * L`, let's make it `-8 * L` so `(1/2)` gives `-4 * L`!
  rw [hpde_comb] at hWt_le0
  dsimp [M] at hWt_le0
  linarith

/-! ### Part 4: Concavity of `s ↦ Φ⁻¹(γ_n {F₀ < s})` for `F₀(z) = (1/n) ∑ exp(σ z_i)` -/

private noncomputable def expTrunc (R r : ℝ) : ℝ :=
  if r ≤ R then Real.exp r else Real.exp R * (1 + (r - R))

private lemma expTrunc_convex (R : ℝ) : ConvexOn ℝ Set.univ (expTrunc R) := by
  have hd : ∀ r : ℝ, HasDerivAt (expTrunc R) (if r ≤ R then Real.exp r else Real.exp R) r := by
    intro r
    rcases lt_trichotomy r R with hlt | rfl | hgt
    · have heq : expTrunc R =ᶠ[𝓝 r] Real.exp := by
        filter_upwards [gt_mem_nhds hlt] with s hs
        simp [expTrunc, le_of_lt hs]
      rw [heq.hasDerivAt_iff, if_pos (le_of_lt hlt)]
      exact Real.hasDerivAt_exp r
    · rw [if_pos (le_refl r), hasDerivAt_iff_tendsto_slope]
      have hleft : Tendsto (slope (expTrunc r) r) (𝓝[<] r) (nhds (Real.exp r)) := by
        have h1 := (hasDerivAt_iff_tendsto_slope.mp (Real.hasDerivAt_exp r)).mono_left
          (nhdsWithin_mono r fun s hs => ne_of_lt (Set.mem_Iio.mp hs))
        refine h1.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with s hs
        simp [slope_def_field, expTrunc, le_of_lt (Set.mem_Iio.mp hs)]
      have hright : Tendsto (slope (expTrunc r) r) (𝓝[>] r) (nhds (Real.exp r)) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with s hs
        have hgt' : ¬ s ≤ r := not_le.mpr (Set.mem_Ioi.mp hs)
        have hne : s - r ≠ 0 := sub_ne_zero.mpr (ne_of_gt (Set.mem_Ioi.mp hs))
        simp only [slope_def_field, expTrunc, if_neg hgt', if_pos (le_refl r)]
        field_simp [hne]; ring
      rw [← nhdsLT_sup_nhdsGT]
      exact hleft.sup hright
    · have heq : expTrunc R =ᶠ[𝓝 r] (fun s => Real.exp R * (1 + (s - R))) := by
        filter_upwards [lt_mem_nhds hgt] with s hs
        simp [expTrunc, not_le.mpr hs]
      rw [heq.hasDerivAt_iff, if_neg (not_le.mpr hgt)]
      have h1 : HasDerivAt (fun s : ℝ => 1 + (s - R)) 1 r := by
        simpa using ((hasDerivAt_id r).sub_const R).const_add 1
      simpa using h1.const_mul (Real.exp R)
  have hmono : Monotone (fun r : ℝ => if r ≤ R then Real.exp r else Real.exp R) := by
    intro a b hab
    dsimp only
    split_ifs with ha hb hb
    · exact Real.exp_le_exp.mpr hab
    · exact Real.exp_le_exp.mpr ha
    · exfalso; linarith
    · exact le_refl _
  have hdiff : Differentiable ℝ (expTrunc R) := fun r => (hd r).differentiableAt
  have hderiv : deriv (expTrunc R) = fun r => if r ≤ R then Real.exp r else Real.exp R :=
    funext fun r => (hd r).deriv
  exact MonotoneOn.convexOn_of_deriv convex_univ hdiff.continuous.continuousOn
    hdiff.differentiableOn (by rw [hderiv]; exact hmono.monotoneOn _)

private lemma expTrunc_lip (R a b : ℝ) : |expTrunc R a - expTrunc R b| ≤ Real.exp R * |a - b| := by
  have hd : ∀ r : ℝ, HasDerivAt (expTrunc R) (if r ≤ R then Real.exp r else Real.exp R) r := by
    intro r
    rcases lt_trichotomy r R with hlt | rfl | hgt
    · have heq : expTrunc R =ᶠ[𝓝 r] Real.exp := by
        filter_upwards [gt_mem_nhds hlt] with s hs; simp [expTrunc, le_of_lt hs]
      rw [heq.hasDerivAt_iff, if_pos (le_of_lt hlt)]; exact Real.hasDerivAt_exp r
    · rw [if_pos (le_refl r), hasDerivAt_iff_tendsto_slope]
      have hleft : Tendsto (slope (expTrunc r) r) (𝓝[<] r) (nhds (Real.exp r)) := by
        have h1 := (hasDerivAt_iff_tendsto_slope.mp (Real.hasDerivAt_exp r)).mono_left
          (nhdsWithin_mono r fun s hs => ne_of_lt (Set.mem_Iio.mp hs))
        refine h1.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with s hs
        simp [slope_def_field, expTrunc, le_of_lt (Set.mem_Iio.mp hs)]
      have hright : Tendsto (slope (expTrunc r) r) (𝓝[>] r) (nhds (Real.exp r)) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with s hs
        have hgt' : ¬ s ≤ r := not_le.mpr (Set.mem_Ioi.mp hs)
        have hne : s - r ≠ 0 := sub_ne_zero.mpr (ne_of_gt (Set.mem_Ioi.mp hs))
        simp only [slope_def_field, expTrunc, if_neg hgt', if_pos (le_refl r)]
        field_simp [hne]; ring
      rw [← nhdsLT_sup_nhdsGT]; exact hleft.sup hright
    · have heq : expTrunc R =ᶠ[𝓝 r] (fun s => Real.exp R * (1 + (s - R))) := by
        filter_upwards [lt_mem_nhds hgt] with s hs; simp [expTrunc, not_le.mpr hs]
      rw [heq.hasDerivAt_iff, if_neg (not_le.mpr hgt)]
      have h1 : HasDerivAt (fun s : ℝ => 1 + (s - R)) 1 r := by
        simpa using ((hasDerivAt_id r).sub_const R).const_add 1
      simpa using h1.const_mul (Real.exp R)
  have hbdd : ∀ r : ℝ, ‖if r ≤ R then Real.exp r else Real.exp R‖ ≤ Real.exp R := by
    intro r; split_ifs with hr
    · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.mpr hr
    · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h1 := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r _ => (hd r).hasDerivWithinAt) (fun r _ => hbdd r) convex_univ (Set.mem_univ b) (Set.mem_univ a)
  simpa [Real.norm_eq_abs] using h1

private noncomputable def F₀ (n : ℕ) (σ : ℝ) (z : Fin n → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i : Fin n, Real.exp (σ * z i)

private lemma F₀_pos {n : ℕ} (hn : 0 < n) (σ : ℝ) (z : Fin n → ℝ) : 0 < F₀ n σ z := by
  unfold F₀
  have hsum : 0 < ∑ i : Fin n, Real.exp (σ * z i) :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
  positivity

private lemma F₀_continuous (n : ℕ) (σ : ℝ) : Continuous (F₀ n σ) := by
  unfold F₀; fun_prop

private lemma γ_F₀_eq_zero {n : ℕ} (hn : 0 < n) {σ : ℝ} (hσ : 0 < σ) (s : ℝ) :
    (γ n) {z | F₀ n σ z = s} = 0 := by
  -- Use Fubini on coordinate `0`: for fixed `z_1, ..., z_{n-1}`, `z_0 ↦ F₀ n σ z` is strictly increasing!
  let i0 : Fin n := ⟨0, hn⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
  have hmp := MeasureTheory.measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => gaussianReal 0 1) 0
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
  have hset_meas : MeasurableSet {z : Fin (m + 1) → ℝ | F₀ (m + 1) σ z = s} :=
    isClosed_eq (F₀_continuous (m + 1) σ) continuous_const |>.measurableSet
  have hpre : (γ (m + 1)) {z | F₀ (m + 1) σ z = s} =
      ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin m => gaussianReal 0 1))
        (e.symm ⁻¹' {z | F₀ (m + 1) σ z = s}) := by
    have h1 := hmp.measure_preimage_emb e.measurableEmbedding
      (s := e.symm ⁻¹' {z | F₀ (m + 1) σ z = s})
    have h2 : e ⁻¹' (e.symm ⁻¹' {z | F₀ (m + 1) σ z = s}) = {z | F₀ (m + 1) σ z = s} := by
      ext z; simp
    rw [h2] at h1
    exact h1
  rw [hpre, Measure.prod_apply_symm (e.symm.measurable hset_meas)]
  have hzero : ∀ y : Fin m → ℝ,
      (gaussianReal 0 1) {t : ℝ | e.symm (t, y) ∈ {z | F₀ (m + 1) σ z = s}} = 0 := by
    intro y
    have hsub : Set.Subsingleton {t : ℝ | e.symm (t, y) ∈ {z | F₀ (m + 1) σ z = s}} := by
      intro t₁ ht₁ t₂ ht₂
      have heq : F₀ (m + 1) σ (e.symm (t₁, y)) = F₀ (m + 1) σ (e.symm (t₂, y)) := by
        rw [ht₁, ht₂]
      simp only [F₀, Fin.sum_univ_succ] at heq
      have h1 : (e.symm (t₁, y)) 0 = t₁ := by simp [e, MeasurableEquiv.piFinSuccAbove]
      have h2 : (e.symm (t₂, y)) 0 = t₂ := by simp [e, MeasurableEquiv.piFinSuccAbove]
      have htail : ∀ j : Fin m, (e.symm (t₁, y)) j.succ = (e.symm (t₂, y)) j.succ := fun j => by
        simp [e, MeasurableEquiv.piFinSuccAbove]
      simp_rw [h1, h2, htail] at heq
      have hpos : (1 / ((m + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      have hexp : Real.exp (σ * t₁) = Real.exp (σ * t₂) := by
        have := mul_left_cancel₀ hpos heq
        linarith
      exact mul_left_cancel₀ (ne_of_gt hσ) (Real.exp_injective hexp)
    rcases hsub.eq_empty_or_singleton with h | ⟨a, h⟩
    · rw [h]; simp
    · rw [h, gaussianReal_of_var_ne_zero 0 one_ne_zero, withDensity_apply _ (measurableSet_singleton a)]
      exact setLIntegral_measure_zero {a} _ Real.volume_singleton
  simp only [Set.preimage_setOf_eq, Set.mem_setOf_eq] at hzero ⊢
  simp [hzero]

private lemma γ_F₀_lt_mem_Ioo {n : ℕ} (hn : 0 < n) {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) :
    (γ n).real {z | F₀ n σ z < s} ∈ Set.Ioo 0 1 := by
  have hmeas : MeasurableSet {z : Fin n → ℝ | F₀ n σ z < s} :=
    (isOpen_lt (F₀_continuous n σ) continuous_const).measurableSet
  have hmeas_gt : MeasurableSet {z : Fin n → ℝ | s < F₀ n σ z} :=
    (isOpen_lt continuous_const (F₀_continuous n σ)).measurableSet
  let c := Real.log s / σ
  have hsub1 : Set.univ.pi (fun _ : Fin n => Set.Iio c) ⊆ {z | F₀ n σ z < s} := by
    intro z hz
    unfold F₀
    have hsum : ∑ i : Fin n, Real.exp (σ * z i) < (n : ℝ) * s := by
      have hlt : ∀ i : Fin n, Real.exp (σ * z i) < s := fun i => by
        have hi : z i < c := hz i (Set.mem_univ i)
        have hmul : σ * z i < Real.log s := by
          dsimp [c] at hi
          have := mul_lt_mul_of_pos_left hi hσ
          rwa [mul_div_cancel₀ _ (ne_of_gt hσ)] at this
        calc Real.exp (σ * z i) < Real.exp (Real.log s) := Real.exp_lt_exp.mpr hmul
          _ = s := Real.exp_log hs
      calc ∑ i : Fin n, Real.exp (σ * z i)
          < ∑ _i : Fin n, s := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) fun i _ => hlt i
        _ = (n : ℝ) * s := by simp
    have hpos : (0 : ℝ) < (n : ℝ) := by positivity
    change (1 / (n : ℝ)) * ∑ i : Fin n, Real.exp (σ * z i) < s
    rw [one_div, inv_mul_lt_iff₀ hpos]
    exact hsum
  have hsub2 : Set.univ.pi (fun _ : Fin n => Set.Ioi c) ⊆ {z | s < F₀ n σ z} := by
    intro z hz
    unfold F₀
    have hsum : (n : ℝ) * s < ∑ i : Fin n, Real.exp (σ * z i) := by
      have hgt : ∀ i : Fin n, s < Real.exp (σ * z i) := fun i => by
        have hi : c < z i := hz i (Set.mem_univ i)
        have hmul : Real.log s < σ * z i := by
          dsimp [c] at hi
          have := mul_lt_mul_of_pos_left hi hσ
          rwa [mul_div_cancel₀ _ (ne_of_gt hσ)] at this
        calc s = Real.exp (Real.log s) := (Real.exp_log hs).symm
          _ < Real.exp (σ * z i) := Real.exp_lt_exp.mpr hmul
      calc (n : ℝ) * s = ∑ _i : Fin n, s := by simp
        _ < ∑ i : Fin n, Real.exp (σ * z i) :=
            Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) fun i _ => hgt i
    have hpos : (0 : ℝ) < (n : ℝ) := by positivity
    change s < (1 / (n : ℝ)) * ∑ i : Fin n, Real.exp (σ * z i)
    rw [one_div, lt_inv_mul_iff₀ hpos]
    exact hsum
  have hpos_Iio : 0 < gaussianReal 0 1 (Set.Iio c) := by
    rw [gaussianReal_of_var_ne_zero 0 one_ne_zero, withDensity_apply _ measurableSet_Iio]
    have hgt : 0 < ∫⁻ t in Set.Iio c, gaussianPDF 0 1 t ∂volume := by
      rw [lintegral_pos_iff_support (measurable_gaussianPDF 0 1)]
      have : Function.support (gaussianPDF 0 1) ∩ Set.Iio c = Set.Iio c := by
        ext t; simp [ne_of_gt (gaussianPDF_pos 0 one_ne_zero t)]
      rw [Measure.restrict_apply' measurableSet_Iio, this, Real.volume_Iio]
      simp
    exact hgt
  have hpos_Ioi : 0 < gaussianReal 0 1 (Set.Ioi c) := by
    rw [gaussianReal_of_var_ne_zero 0 one_ne_zero, withDensity_apply _ measurableSet_Ioi]
    have hgt : 0 < ∫⁻ t in Set.Ioi c, gaussianPDF 0 1 t ∂volume := by
      rw [lintegral_pos_iff_support (measurable_gaussianPDF 0 1)]
      have : Function.support (gaussianPDF 0 1) ∩ Set.Ioi c = Set.Ioi c := by
        ext t; simp [ne_of_gt (gaussianPDF_pos 0 one_ne_zero t)]
      rw [Measure.restrict_apply' measurableSet_Ioi, this, Real.volume_Ioi]
      simp
    exact hgt
  constructor
  · have h1 : 0 < (γ n) {z | F₀ n σ z < s} := by
      calc (0 : ℝ≥0∞) < ∏ _i : Fin n, gaussianReal 0 1 (Set.Iio c) :=
            pos_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun _ _ => hpos_Iio.ne')
        _ = (γ n) (Set.univ.pi fun _ => Set.Iio c) := by unfold γ; rw [Measure.pi_pi]
        _ ≤ (γ n) {z | F₀ n σ z < s} := measure_mono hsub1
    exact ENNReal.toReal_pos h1.ne' (measure_ne_top _ _)
  · have h2 : 0 < (γ n) {z | s < F₀ n σ z} := by
      calc (0 : ℝ≥0∞) < ∏ _i : Fin n, gaussianReal 0 1 (Set.Ioi c) :=
            pos_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun _ _ => hpos_Ioi.ne')
        _ = (γ n) (Set.univ.pi fun _ => Set.Ioi c) := by unfold γ; rw [Measure.pi_pi]
        _ ≤ (γ n) {z | s < F₀ n σ z} := measure_mono hsub2
    have hdisj : Disjoint {z | F₀ n σ z < s} {z | s < F₀ n σ z} :=
      Set.disjoint_left.mpr fun z h1 h2 => lt_asymm (show F₀ n σ z < s from h1) (show s < F₀ n σ z from h2)
    have hadd : (γ n).real {z | F₀ n σ z < s} + (γ n).real {z | s < F₀ n σ z} ≤ 1 := by
      rw [← measureReal_union hdisj hmeas_gt]
      exact measureReal_le_one
    have hpos2 : 0 < (γ n).real {z | s < F₀ n σ z} := ENNReal.toReal_pos h2.ne' (measure_ne_top _ _)
    linarith

/-- Concavity of `s ↦ Φ⁻¹(γ_n {F₀ < s})` on `(0, ∞)`. -/
private lemma concave_Φinv_F₀ {n : ℕ} (hn : 0 < n) {σ : ℝ} (hσ : 0 < σ) :
    ConcaveOn ℝ (Set.Ioi 0) (fun s => Φinv ((γ n).real {z | F₀ n σ z < s})) := by
  refine ⟨convex_Ioi 0, fun s₁ hs₁ s₂ hs₂ a b ha hb hab => ?_⟩
  rcases eq_or_lt_of_le ha with rfl | ha_pos
  · have hb1 : b = 1 := by linarith
    subst hb1; simp
  rcases eq_or_lt_of_le hb with rfl | hb_pos
  · have ha1 : a = 1 := by linarith
    subst ha1; simp
  have hb_eq : b = 1 - a := by linarith
  subst hb_eq
  have ha1 : a < 1 := by linarith
  set s₃ := a * s₁ + (1 - a) * s₂
  have hs₃ : 0 < s₃ := by dsimp [s₃]; nlinarith [Set.mem_Ioi.mp hs₁, Set.mem_Ioi.mp hs₂]
  -- Step 1: For fixed `β > 0` and `R > 0`, apply `functional_ehrhard` to `u₀(z) = β * (s_i - F_R(z))`
  have hstep_β : ∀ β : ℝ, 0 < β →
      a * Φinv (∫ z, Φ (β * (s₁ - F₀ n σ z)) ∂(γ n)) +
      (1 - a) * Φinv (∫ z, Φ (β * (s₂ - F₀ n σ z)) ∂(γ n)) ≤
      Φinv (∫ z, Φ (β * (s₃ - F₀ n σ z)) ∂(γ n)) := by
    intro β hβ
    have hR_ehr : ∀ R : ℕ,
        a * Φinv (∫ z, Φ (β * (s₁ - (1 / (n : ℝ)) * ∑ i : Fin n, expTrunc R (σ * z i))) ∂(γ n)) +
        (1 - a) * Φinv (∫ z, Φ (β * (s₂ - (1 / (n : ℝ)) * ∑ i : Fin n, expTrunc R (σ * z i))) ∂(γ n)) ≤
        Φinv (∫ z, Φ (β * (s₃ - (1 / (n : ℝ)) * ∑ i : Fin n, expTrunc R (σ * z i))) ∂(γ n)) := by
      intro R
      let FR : (Fin n → ℝ) → ℝ := fun z => (1 / (n : ℝ)) * ∑ i : Fin n, expTrunc R (σ * z i)
      let L : ℝ := β * σ * Real.exp R
      have hFR_lip : ∀ x y, |FR x - FR y| ≤ (σ * Real.exp R) * ∑ i : Fin n, |x i - y i| := by
        intro x y
        dsimp [FR]
        rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (n : ℝ)), ← Finset.sum_sub_distrib]
        have h1 : |∑ i : Fin n, (expTrunc R (σ * x i) - expTrunc R (σ * y i))| ≤
            ∑ i : Fin n, Real.exp R * (σ * |x i - y i|) := by
          calc |∑ i : Fin n, (expTrunc R (σ * x i) - expTrunc R (σ * y i))|
              ≤ ∑ i : Fin n, |expTrunc R (σ * x i) - expTrunc R (σ * y i)| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ i : Fin n, Real.exp R * |σ * x i - σ * y i| := Finset.sum_le_sum fun i _ => expTrunc_lip R _ _
            _ = ∑ i : Fin n, Real.exp R * (σ * |x i - y i|) := Finset.sum_congr rfl fun i _ => by
                rw [← mul_sub, abs_mul, abs_of_pos hσ]
        have h2 : ∑ i : Fin n, Real.exp R * (σ * |x i - y i|) = (σ * Real.exp R) * ∑ i : Fin n, |x i - y i| := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
        have h1n : (1 / (n : ℝ)) ≤ 1 := by
          rw [one_div]; exact inv_le_one_of_one_le₀ (by exact_mod_cast hn)
        have hnn : 0 ≤ (σ * Real.exp R) * ∑ i : Fin n, |x i - y i| :=
          mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
        calc (1 / (n : ℝ)) * |∑ i : Fin n, (expTrunc R (σ * x i) - expTrunc R (σ * y i))|
            ≤ 1 * |∑ i : Fin n, (expTrunc R (σ * x i) - expTrunc R (σ * y i))| :=
              mul_le_mul_of_nonneg_right h1n (abs_nonneg _)
          _ = |∑ i : Fin n, (expTrunc R (σ * x i) - expTrunc R (σ * y i))| := one_mul _
          _ ≤ (σ * Real.exp R) * ∑ i : Fin n, |x i - y i| := by linarith [h1, h2]
      have hlip : ∀ s x y, |β * (s - FR x) - β * (s - FR y)| ≤ L * ∑ i : Fin n, |x i - y i| := by
        intro s x y
        have : β * (s - FR x) - β * (s - FR y) = -(β * (FR x - FR y)) := by ring
        rw [this, abs_neg, abs_mul, abs_of_pos hβ]
        calc β * |FR x - FR y| ≤ β * ((σ * Real.exp R) * ∑ i : Fin n, |x i - y i|) :=
              mul_le_mul_of_nonneg_left (hFR_lip x y) (le_of_lt hβ)
          _ = L * ∑ i : Fin n, |x i - y i| := by dsimp [L]; ring
      have hconv_FR : ∀ x y, FR (a • x + (1 - a) • y) ≤ a * FR x + (1 - a) * FR y := by
        intro x y
        dsimp [FR]
        have hsum : ∑ i : Fin n, expTrunc R (σ * (a * x i + (1 - a) * y i)) ≤
            a * ∑ i : Fin n, expTrunc R (σ * x i) + (1 - a) * ∑ i : Fin n, expTrunc R (σ * y i) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_le_sum fun i _ => ?_
          have := (expTrunc_convex R).2 (Set.mem_univ (σ * x i)) (Set.mem_univ (σ * y i))
            (le_of_lt ha_pos) (show 0 ≤ 1 - a by linarith) (by ring)
          have heq : a * (σ * x i) + (1 - a) * (σ * y i) = σ * (a * x i + (1 - a) * y i) := by ring
          simpa [smul_eq_mul, heq] using this
        have h1n : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
        simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, mul_left_comm] using
          mul_le_mul_of_nonneg_left hsum h1n
      refine functional_ehrhard (L := L) (by positivity) ha_pos ha1 (hlip s₁) (hlip s₂) (hlip s₃) ?_
      intro x y
      have h1 : a * (s₁ - FR x) + (1 - a) * (s₂ - FR y) ≤ s₃ - FR (a • x + (1 - a) • y) := by
        dsimp [s₃]; linarith [hconv_FR x y]
      have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hβ)
      linarith
    -- Pass `R → ∞` by dominated convergence
    have htend : ∀ s : ℝ, Tendsto (fun R : ℕ =>
        Φinv (∫ z, Φ (β * (s - (1 / (n : ℝ)) * ∑ i : Fin n, expTrunc R (σ * z i))) ∂(γ n)))
        atTop (nhds (Φinv (∫ z, Φ (β * (s - F₀ n σ z)) ∂(γ n)))) := by
      intro s
      have hmem : (∫ z, Φ (β * (s - F₀ n σ z)) ∂(γ n)) ∈ Set.Ioo 0 1 := by
        have hcont : Continuous (fun z => β * (s - F₀ n σ z)) :=
          continuous_const.mul (continuous_const.sub (F₀_continuous n σ))
        simpa [H, show ¬ (1 : ℝ) ≤ 0 by norm_num] using H_Phi_mem_Ioo hcont 1 0
      have hint_tend : Tendsto (fun R : ℕ => ∫ z, Φ (β * (s - (1 / (n : ℝ)) * ∑ i : Fin n, expTrunc R (σ * z i))) ∂(γ n))
          atTop (nhds (∫ z, Φ (β * (s - F₀ n σ z)) ∂(γ n))) := by
        refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ (integrable_const 1) ?_ ?_
        · intro R
          have hcont_t : Continuous (expTrunc R) :=
            continuous_iff_continuousAt.mpr fun a => Metric.continuousAt_iff.mpr fun ε hε =>
              ⟨ε / (Real.exp R + 1), by positivity, fun b hb => by
                rw [Real.dist_eq] at hb ⊢
                have h1 := expTrunc_lip R b a
                have hpos : 0 < Real.exp R + 1 := by positivity
                calc |expTrunc R b - expTrunc R a| ≤ Real.exp R * |b - a| := h1
                  _ ≤ (Real.exp R + 1) * |b - a| := by nlinarith [abs_nonneg (b - a)]
                  _ < (Real.exp R + 1) * (ε / (Real.exp R + 1)) := mul_lt_mul_of_pos_left hb hpos
                  _ = ε := mul_div_cancel₀ ε (ne_of_gt hpos)⟩
          have hc : Continuous (fun z : Fin n → ℝ => Φ (β * (s - (1 / (n : ℝ)) * ∑ i : Fin n, expTrunc R (σ * z i)))) :=
            continuous_Φ.comp (continuous_const.mul (continuous_const.sub (continuous_const.mul
              (continuous_finset_sum _ fun i _ => hcont_t.comp (continuous_const.mul (continuous_apply i))))))
          exact hc.aestronglyMeasurable
        · intro R; exact Eventually.of_forall fun z => by rw [Real.norm_eq_abs, abs_of_pos (Φ_pos _)]; exact le_of_lt (Φ_lt_one _)
        · refine Eventually.of_forall fun z => ?_
          refine tendsto_const_nhds.congr' ?_
          obtain ⟨R₀, hR₀⟩ := exists_nat_gt (Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) fun i => σ * z i)
          filter_upwards [eventually_ge_atTop R₀] with R hR
          have hsum_eq : ∑ i : Fin n, expTrunc R (σ * z i) = ∑ i : Fin n, Real.exp (σ * z i) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            have hi : σ * z i ≤ (R : ℝ) := by
              have hle := Finset.le_sup' (f := fun j => σ * z j) (Finset.mem_univ i)
              have hRR : (R₀ : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
              linarith
            simp [expTrunc, hi]
          simp only [F₀, hsum_eq]
      exact ((continuousOn_Φinv _ hmem).continuousAt (isOpen_Ioo.mem_nhds hmem)).tendsto.comp hint_tend
    exact le_of_tendsto_of_tendsto (((htend s₁).const_mul a).add ((htend s₂).const_mul (1 - a))) (htend s₃)
      (Eventually.of_forall hR_ehr)
  -- Step 2: Pass `β → ∞` by dominated convergence (using `γ_F₀_eq_zero`)
  have htend_β : ∀ s : ℝ, 0 < s →
      Tendsto (fun β : ℕ => Φinv (∫ z, Φ ((β : ℝ) * (s - F₀ n σ z)) ∂(γ n)))
        atTop (nhds (Φinv ((γ n).real {z | F₀ n σ z < s}))) := by
    intro s hs
    have hmem := γ_F₀_lt_mem_Ioo hn hσ hs
    have hint_tend : Tendsto (fun β : ℕ => ∫ z, Φ ((β : ℝ) * (s - F₀ n σ z)) ∂(γ n))
        atTop (nhds ((γ n).real {z | F₀ n σ z < s})) := by
      have hmeas_lt : MeasurableSet {z : Fin n → ℝ | F₀ n σ z < s} :=
        (isOpen_lt (F₀_continuous n σ) continuous_const).measurableSet
      rw [← integral_indicator_one hmeas_lt]
      refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ (integrable_const 1) ?_ ?_
      · intro β
        exact (continuous_Φ.comp (continuous_const.mul (continuous_const.sub (F₀_continuous n σ)))).aestronglyMeasurable
      · intro β
        exact Eventually.of_forall fun z => by rw [Real.norm_eq_abs, abs_of_pos (Φ_pos _)]; exact le_of_lt (Φ_lt_one _)
      · have hae : ∀ᵐ z ∂(γ n), F₀ n σ z ≠ s := by
          rw [ae_iff]; simp only [not_not]; exact γ_F₀_eq_zero hn hσ s
        filter_upwards [hae] with z hz
        rcases lt_or_gt_of_ne hz with hlt | hgt
        · simp only [Set.indicator_of_mem (show z ∈ {z | F₀ n σ z < s} from hlt), Pi.one_apply]
          have hmul : Tendsto (fun β : ℕ => (β : ℝ) * (s - F₀ n σ z)) atTop atTop :=
            Tendsto.atTop_mul_const (by linarith) tendsto_natCast_atTop_atTop
          exact Φ_tendsto_atTop.comp hmul
        · simp only [Set.indicator_of_notMem (show z ∉ {z | F₀ n σ z < s} from not_lt.mpr (le_of_lt hgt))]
          have hmul : Tendsto (fun β : ℕ => (β : ℝ) * (s - F₀ n σ z)) atTop atBot :=
            Tendsto.atTop_mul_const_of_neg (by linarith) tendsto_natCast_atTop_atTop
          exact Φ_tendsto_atBot.comp hmul
    exact ((continuousOn_Φinv _ hmem).continuousAt (isOpen_Ioo.mem_nhds hmem)).tendsto.comp hint_tend
  have hev : ∀ᶠ β : ℕ in atTop,
      a * Φinv (∫ z, Φ ((β : ℝ) * (s₁ - F₀ n σ z)) ∂(γ n)) +
      (1 - a) * Φinv (∫ z, Φ ((β : ℝ) * (s₂ - F₀ n σ z)) ∂(γ n)) ≤
      Φinv (∫ z, Φ ((β : ℝ) * (s₃ - F₀ n σ z)) ∂(γ n)) := by
    filter_upwards [eventually_ge_atTop 1] with β hβ
    exact hstep_β (β : ℝ) (by positivity)
  simpa [smul_eq_mul, s₃] using le_of_tendsto_of_tendsto
    (((htend_β s₁ (Set.mem_Ioi.mp hs₁)).const_mul a).add
      ((htend_β s₂ (Set.mem_Ioi.mp hs₂)).const_mul (1 - a)))
    (htend_β s₃ hs₃) hev

/-! ### Part 5: Kwapień's strict inequality `γ_n {F₀ < E} > 1/2` via supporting line + layer-cake -/

private lemma integral_comp_add_left_Ioi (f : ℝ → ℝ) (a c : ℝ) :
    ∫ x in Set.Ioi a, f (c + x) = ∫ u in Set.Ioi (c + a), f u := by
  have hmp := measurePreserving_add_left (volume : Measure ℝ) c
  have hpre : (fun x : ℝ => c + x) ⁻¹' Set.Ioi (c + a) = Set.Ioi a := by
    ext x; simp [Set.mem_Ioi]
  rw [← hpre]
  exact hmp.setIntegral_preimage_emb (measurableEmbedding_addLeft c) f (Set.Ioi (c + a))

/-- Exact tail integral for shifted normal: `∫_{s > 0} (1 - Φ(a*(s - E))) ds > E` for `a > 0, E > 0`. -/
private lemma integral_tail_normal_gt {a E : ℝ} (ha : 0 < a) (hE : 0 < E) :
    E < ∫ s in Set.Ioi (0 : ℝ), (1 - Φ (a * (s - E))) := by
  -- Change of variable `u = a * (s - E)` maps `Ioi 0` to `Ioi (-a * E)`
  have hsub : ∫ s in Set.Ioi (0 : ℝ), (1 - Φ (a * (s - E))) =
      a⁻¹ * ∫ u in Set.Ioi (-(a * E)), (1 - Φ u) := by
    have h1 := MeasureTheory.integral_comp_mul_left_Ioi (fun u => 1 - Φ (-(a * E) + u)) (0 : ℝ) ha
    have h2 := integral_comp_add_left_Ioi (fun u => 1 - Φ u) (0 : ℝ) (-(a * E))
    have heq : (fun s => 1 - Φ (a * (s - E))) = fun s => 1 - Φ (-(a * E) + a * s) :=
      funext fun s => by ring_nf
    rw [heq, h1, mul_zero, smul_eq_mul, h2, add_zero]
  rw [hsub, ← mul_lt_mul_iff_right₀ ha]
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt ha), one_mul]
  -- Now prove `a * E < ∫ u in Ioi (-a*E), (1 - Φ u)` via Fubini on `{(u, t) : -a*E < u < t}`!
  set c := -(a * E)
  have hc : c < 0 := by dsimp [c]; nlinarith
  have h1mΦ : ∀ u : ℝ, 1 - Φ u = ∫ t in Set.Ioi u, φ t := by
    intro u
    have hsum : (∫ t in Set.Iic u, φ t) + (∫ t in Set.Ioi u, φ t) = ∫ t, φ t := by
      rw [← setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
        (integrable_φ.integrableOn) (integrable_φ.integrableOn),
        Set.Iic_union_Ioi, setIntegral_univ]
    rw [integral_φ] at hsum
    unfold Φ; linarith
  -- Use `Integrable.integral_eq_integral_meas_lt` on the positive part `max(Z - c, 0)` where `Z ~ N(0, 1)`!
  let Zpos : ℝ → ℝ := fun t => max (t - c) 0
  have hZpos_int : Integrable Zpos (gaussianReal 0 1) := by
    have hid : Integrable (fun t : ℝ => t) (gaussianReal 0 1) := (memLp_id_gaussianReal 1).integrable le_rfl
    have hsub_int : Integrable (fun t : ℝ => t - c) (gaussianReal 0 1) := hid.sub (integrable_const c)
    exact hsub_int.sup (integrable_const 0)
  have hlayer := hZpos_int.integral_eq_integral_meas_lt (Eventually.of_forall fun t => le_max_right _ _)
  have hmeas_eq : ∀ r : ℝ, 0 < r →
      (gaussianReal 0 1).real {t : ℝ | r < Zpos t} = 1 - Φ (c + r) := by
    intro r hr
    have hset : {t : ℝ | r < Zpos t} = Set.Ioi (c + r) := by
      ext t; simp only [Set.mem_setOf_eq, Set.mem_Ioi, Zpos, lt_max_iff]
      constructor
      · rintro (h | h) <;> linarith
      · intro h; left; linarith
    rw [hset, h1mΦ (c + r)]
    rw [Measure.real, gaussianReal_of_var_ne_zero 0 one_ne_zero, withDensity_apply _ measurableSet_Ioi]
    have h1 := integral_eq_lintegral_of_nonneg_ae (μ := volume.restrict (Set.Ioi (c + r)))
      (Eventually.of_forall fun t => φ_nonneg t) continuous_φ.aestronglyMeasurable
    rw [h1]; rfl
  have hrhs_eq : ∫ r in Set.Ioi (0 : ℝ), (gaussianReal 0 1).real {t : ℝ | r < Zpos t} =
      ∫ u in Set.Ioi c, (1 - Φ u) := by
    have h1 : ∫ r in Set.Ioi (0 : ℝ), (gaussianReal 0 1).real {t : ℝ | r < Zpos t} =
        ∫ r in Set.Ioi (0 : ℝ), (1 - Φ (c + r)) :=
      setIntegral_congr_fun measurableSet_Ioi fun r hr => hmeas_eq r hr
    rw [h1]
    have h2 := integral_comp_add_left_Ioi (fun u => 1 - Φ u) (0 : ℝ) c
    simpa using h2
  rw [← hrhs_eq, ← hlayer]
  -- Now compare `∫ max(t - c, 0) dN(0,1)` with `∫ (t - c) dN(0,1) = -c = a * E`!
  have hid : Integrable (fun t : ℝ => t) (gaussianReal 0 1) := (memLp_id_gaussianReal 1).integrable le_rfl
  have hsub_int : Integrable (fun t : ℝ => t - c) (gaussianReal 0 1) := hid.sub (integrable_const c)
  have hE_eq : ∫ t, (t - c) ∂(gaussianReal 0 1) = a * E := by
    rw [integral_sub hid (integrable_const c), integral_id_gaussianReal, integral_const]
    simp [c]
  rw [← hE_eq]
  have hdiff_int : Integrable (fun t => Zpos t - (t - c)) (gaussianReal 0 1) := hZpos_int.sub hsub_int
  have hdiff_pos : 0 < ∫ t, (Zpos t - (t - c)) ∂(gaussianReal 0 1) := by
    refine (integral_pos_iff_support_of_nonneg_ae
      (Eventually.of_forall fun t => by dsimp [Zpos]; linarith [le_max_left (t - c) 0]) hdiff_int).mpr ?_
    have hsub : Set.Iio c ⊆ Function.support (fun t => Zpos t - (t - c)) := by
      intro t ht
      have hlt : t - c < 0 := by linarith [Set.mem_Iio.mp ht]
      simp [Function.mem_support, Zpos, max_eq_right (le_of_lt hlt)]
      linarith
    have hpos_Iio : 0 < gaussianReal 0 1 (Set.Iio c) := by
      rw [gaussianReal_of_var_ne_zero 0 one_ne_zero, withDensity_apply _ measurableSet_Iio]
      rw [lintegral_pos_iff_support (measurable_gaussianPDF 0 1)]
      have : Function.support (gaussianPDF 0 1) ∩ Set.Iio c = Set.Iio c := by
        ext t; simp [ne_of_gt (gaussianPDF_pos 0 one_ne_zero t)]
      rw [Measure.restrict_apply' measurableSet_Iio, this, Real.volume_Iio]
      simp
    exact lt_of_lt_of_le hpos_Iio (measure_mono hsub)
  rw [integral_sub hZpos_int hsub_int] at hdiff_pos
  linarith

private lemma integrable_F₀ {n : ℕ} (σ : ℝ) : Integrable (F₀ n σ) (γ n) := by
  unfold F₀
  refine Integrable.const_mul ?_ _
  refine integrable_finset_sum Finset.univ fun i _ => ?_
  have hmp : MeasurePreserving (fun z : Fin n → ℝ => z i) (γ n) (gaussianReal 0 1) := by
    unfold γ; exact MeasureTheory.measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i
  have hint : Integrable (fun t : ℝ => Real.exp (σ * t)) (gaussianReal 0 1) :=
    integrable_exp_mul_gaussianReal (μ := 0) (v := 1) σ
  exact memLp_one_iff_integrable.mp ((memLp_one_iff_integrable.mpr hint).comp_measurePreserving hmp)

/-- Strict Kwapień inequality: `γ_n {F₀ < E} > 1/2` where `E = ∫ F₀ dγ_n`. -/
private lemma kwapien_strict {n : ℕ} (hn : 0 < n) {σ : ℝ} (hσ : 0 < σ) :
    1 / 2 < (γ n).real {z | F₀ n σ z < ∫ w, F₀ n σ w ∂(γ n)} := by
  set E := ∫ w, F₀ n σ w ∂(γ n)
  have hE_pos : 0 < E := by
    refine (integral_pos_iff_support_of_nonneg_ae
      (Eventually.of_forall fun z => le_of_lt (F₀_pos hn σ z)) (integrable_F₀ σ)).mpr ?_
    have hsupp : Function.support (F₀ n σ) = Set.univ := by
      ext z; simp [ne_of_gt (F₀_pos hn σ z)]
    rw [hsupp]; simp
  by_contra hle
  push Not at hle
  let G : ℝ → ℝ := fun s => Φinv ((γ n).real {z | F₀ n σ z < s})
  have hG_conc : ConcaveOn ℝ (Set.Ioi 0) G := concave_Φinv_F₀ hn hσ
  have hGE : G E ≤ 0 := by
    rw [← Φinv_half]
    exact Φinv_monoOn (γ_F₀_lt_mem_Ioo hn hσ hE_pos) (by norm_num) hle
  -- Supporting line of concave `G` at `E > 0`: pick `a = sInf { (G E - G s) / (E - s) | 0 < s < E }`
  -- Equivalently, by slope monotonicity of concave `G`, for `s < E < t`: `(G t - G E)/(t - E) ≤ (G E - G s)/(E - s)`.
  have hslope_le : ∀ s ∈ Set.Ioo (0 : ℝ) E, ∀ t ∈ Set.Ioi E,
      (G t - G E) / (t - E) ≤ (G E - G s) / (E - s) := by
    intro s hs t ht
    have hst : 0 < t - s := by linarith [hs.2, Set.mem_Ioi.mp ht]
    let lam := (t - E) / (t - s)
    have hlam0 : 0 ≤ lam := div_nonneg (by linarith [Set.mem_Ioi.mp ht]) (le_of_lt hst)
    have hlam1 : 0 ≤ 1 - lam := by
      have : lam ≤ 1 := (div_le_one hst).mpr (by linarith [hs.2])
      linarith
    have hcomb : lam * s + (1 - lam) * t = E := by
      dsimp [lam]; field_simp [ne_of_gt hst]; ring
    have hc := hG_conc.2 hs.1 (lt_trans hE_pos ht) hlam0 hlam1 (by ring)
    simp only [smul_eq_mul, hcomb] at hc
    have h1 : lam * (G E - G s) ≥ (1 - lam) * (G t - G E) := by linarith
    have h1mlam : 1 - lam = (E - s) / (t - s) := by dsimp [lam]; field_simp [ne_of_gt hst]; ring
    rw [h1mlam] at h1
    dsimp [lam] at h1
    have hmul : (t - E) * (G E - G s) ≥ (E - s) * (G t - G E) := by
      have := mul_le_mul_of_nonneg_right h1 (le_of_lt hst)
      rw [mul_right_comm, div_mul_cancel₀ _ (ne_of_gt hst),
        mul_right_comm, div_mul_cancel₀ _ (ne_of_gt hst)] at this
      exact this
    rw [div_le_div_iff₀ (by linarith [Set.mem_Ioi.mp ht]) (by linarith [hs.2])]
    linarith
  let S_left := (fun s => (G E - G s) / (E - s)) '' Set.Ioo (0 : ℝ) E
  have hS_ne : S_left.Nonempty := ⟨(G E - G (E / 2)) / (E - E / 2), E / 2, ⟨by linarith, by linarith⟩, rfl⟩
  have hS_bdd : BddBelow S_left := ⟨(G (E + 1) - G E) / ((E + 1) - E), by
    rintro _ ⟨s, hs, rfl⟩; exact hslope_le s hs (E + 1) (by simp)⟩
  let a := sInf S_left
  have hG_sup : ∀ s : ℝ, 0 < s → G s ≤ G E + a * (s - E) := by
    intro s hs
    rcases lt_trichotomy s E with hlt | rfl | hgt
    · have ha_le : a ≤ (G E - G s) / (E - s) := csInf_le hS_bdd ⟨s, ⟨hs, hlt⟩, rfl⟩
      have hpos : 0 < E - s := by linarith
      have := (le_div_iff₀ hpos).mp ha_le
      linarith
    · simp
    · have ha_ge : (G s - G E) / (s - E) ≤ a := le_csInf hS_ne fun y hy => by
        rcases hy with ⟨r, hr, rfl⟩; exact hslope_le r hr s hgt
      have hpos : 0 < s - E := by linarith
      have := (div_le_iff₀ hpos).mp ha_ge
      linarith
  -- Show `0 < a`: otherwise `G s ≤ 0` for all `s > 0`, so `γ_n {F₀ < s} ≤ 1/2` for all `s`, contradicting limit `1`!
  have ha_pos : 0 < a := by
    by_contra ha_le
    push Not at ha_le
    have hall : ∀ s : ℝ, E ≤ s → (γ n).real {z | F₀ n σ z < s} ≤ 1 / 2 := by
      intro s hs
      have h1 : G s ≤ 0 := by nlinarith [hG_sup s (lt_of_lt_of_le hE_pos hs)]
      have h2 := Φ_strictMono.monotone h1
      rw [Φ_Φinv (γ_F₀_lt_mem_Ioo hn hσ (lt_of_lt_of_le hE_pos hs)), Φ_zero] at h2
      exact h2
    -- For large `k : ℕ`, `γ_n {F₀ < k} → 1` by monotone convergence!
    have hlim : Tendsto (fun k : ℕ => (γ n).real {z | F₀ n σ z < (k : ℝ)}) atTop (nhds 1) := by
      have h1 : Tendsto (fun k : ℕ => (γ n) {z | F₀ n σ z < (k : ℝ)}) atTop (nhds ((γ n) Set.univ)) := by
        have hunion : (⋃ k : ℕ, {z : Fin n → ℝ | F₀ n σ z < (k : ℝ)}) = Set.univ := by
          ext z; simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
          exact exists_nat_gt (F₀ n σ z)
        rw [← hunion]
        exact tendsto_measure_iUnion_atTop fun k l hkl z hz =>
          lt_of_lt_of_le (show F₀ n σ z < (k : ℝ) from hz) (Nat.cast_le.mpr hkl)
      have h2 := (ENNReal.tendsto_toReal (by simp : (γ n) Set.univ ≠ ∞)).comp h1
      simpa [Measure.real, Function.comp_def] using h2
    have hle_half : (1 : ℝ) ≤ 1 / 2 := le_of_tendsto hlim (by
      obtain ⟨N, hN⟩ := exists_nat_ge E
      filter_upwards [eventually_ge_atTop N] with k hk
      exact hall (k : ℝ) (le_trans hN (by exact_mod_cast hk)))
    linarith
  -- Apply layer-cake formula to `F₀` and compare with `integral_tail_normal_gt`!
  have hlayer : E = ∫ s in Set.Ioi (0 : ℝ), (γ n).real {z | s < F₀ n σ z} :=
    (integrable_F₀ σ).integral_eq_integral_meas_lt (Eventually.of_forall fun z => le_of_lt (F₀_pos hn σ z))
  have hpt : ∀ s ∈ Set.Ioi (0 : ℝ), 1 - Φ (a * (s - E)) ≤ (γ n).real {z | s < F₀ n σ z} := by
    intro s hs
    have h1 : G s ≤ a * (s - E) := by linarith [hG_sup s hs]
    have h2 : (γ n).real {z | F₀ n σ z < s} ≤ Φ (a * (s - E)) := by
      have := Φ_strictMono.monotone h1
      rwa [Φ_Φinv (γ_F₀_lt_mem_Ioo hn hσ hs)] at this
    -- `{F₀ < s} ∪ {s < F₀}` has full measure since `γ_n {F₀ = s} = 0`!
    have hadd : (γ n).real {z | F₀ n σ z < s} + (γ n).real {z | s < F₀ n σ z} = 1 := by
      have hmeas_lt : MeasurableSet {z : Fin n → ℝ | F₀ n σ z < s} :=
        (isOpen_lt (F₀_continuous n σ) continuous_const).measurableSet
      have hmeas_gt : MeasurableSet {z : Fin n → ℝ | s < F₀ n σ z} :=
        (isOpen_lt continuous_const (F₀_continuous n σ)).measurableSet
      have hdisj : Disjoint {z : Fin n → ℝ | F₀ n σ z < s} {z | s < F₀ n σ z} :=
        Set.disjoint_left.mpr fun z h1 h2 => lt_asymm (show F₀ n σ z < s from h1) (show s < F₀ n σ z from h2)
      rw [← measureReal_union hdisj hmeas_gt]
      have hcompl : ({z : Fin n → ℝ | F₀ n σ z < s} ∪ {z | s < F₀ n σ z})ᶜ = {z | F₀ n σ z = s} := by
        ext z; simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or, not_lt]
        exact ⟨fun ⟨h1, h2⟩ => le_antisymm h2 h1, fun h => ⟨le_of_eq h.symm, le_of_eq h⟩⟩
      have hmeas_u : MeasurableSet ({z : Fin n → ℝ | F₀ n σ z < s} ∪ {z | s < F₀ n σ z}) :=
        hmeas_lt.union hmeas_gt
      have htot := measureReal_add_measureReal_compl (μ := γ n) hmeas_u
      simp only [hcompl, Measure.real, γ_F₀_eq_zero hn hσ s, ENNReal.toReal_zero, add_zero,
        measure_univ, ENNReal.toReal_one] at htot
      exact htot
    linarith
  have hint_lhs : IntegrableOn (fun s => 1 - Φ (a * (s - E))) (Set.Ioi 0) volume := by
    -- Integrable because `0 ≤ 1 - Φ(a*(s-E)) ≤ (γ n).real {s < F₀}` which is integrable on `Ioi 0`!
    have hint_rhs : IntegrableOn (fun s => (γ n).real {z | s < F₀ n σ z}) (Set.Ioi 0) volume := by
      -- Follows from `lintegral_eq_lintegral_meas_lt` being finite!
      have hkey := lintegral_eq_lintegral_meas_lt (γ n) (Eventually.of_forall fun z => le_of_lt (F₀_pos hn σ z))
        (F₀_continuous n σ).measurable.aemeasurable
      have hlt : ∫⁻ s in Set.Ioi (0 : ℝ), (γ n) {z | s < F₀ n σ z} ∂volume < ∞ := by
        rw [← hkey]; exact (integrable_F₀ σ).lintegral_lt_top
      have hmono : Antitone (fun s : ℝ => (γ n).real {z | s < F₀ n σ z}) := fun s t hst =>
        measureReal_mono (fun z hz => lt_of_le_of_lt hst hz)
      refine ⟨hmono.measurable.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun s => measureReal_nonneg)]
      refine lt_of_le_of_lt (lintegral_mono fun s => ?_) hlt
      rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    refine hint_rhs.mono' ((continuous_const.sub (continuous_Φ.comp
      (continuous_const.mul (continuous_id.sub continuous_const)))).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [Φ_lt_one (a * (s - E))])]
    exact hpt s hs
  have hint_rhs : IntegrableOn (fun s => (γ n).real {z | s < F₀ n σ z}) (Set.Ioi 0) volume := by
    have hkey := lintegral_eq_lintegral_meas_lt (γ n) (Eventually.of_forall fun z => le_of_lt (F₀_pos hn σ z))
      (F₀_continuous n σ).measurable.aemeasurable
    have hlt : ∫⁻ s in Set.Ioi (0 : ℝ), (γ n) {z | s < F₀ n σ z} ∂volume < ∞ := by
      rw [← hkey]; exact (integrable_F₀ σ).lintegral_lt_top
    have hmono : Antitone (fun s : ℝ => (γ n).real {z | s < F₀ n σ z}) := fun s t hst =>
      measureReal_mono (fun z hz => lt_of_le_of_lt hst hz)
    refine ⟨hmono.measurable.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun s => measureReal_nonneg)]
    refine lt_of_le_of_lt (lintegral_mono fun s => ?_) hlt
    rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hle_int : ∫ s in Set.Ioi (0 : ℝ), (1 - Φ (a * (s - E))) ≤
      ∫ s in Set.Ioi (0 : ℝ), (γ n).real {z | s < F₀ n σ z} :=
    setIntegral_mono_on hint_lhs hint_rhs measurableSet_Ioi hpt
  linarith [integral_tail_normal_gt ha_pos hE_pos]

/-! ### Part 6: Reduction from arbitrary probability space `(Ω, ℙ, x)` to `kwapien_strict` -/

theorem main_proof :
    ∀ (n : ℕ), 0 < n → ∀ (μ σ : ℝ), 0 < σ →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] (x : Fin n → Ω → ℝ),
        iIndepFun x ℙ → (∀ i, ∀ᵐ ω ∂(ℙ : Measure Ω), 0 < x i ω) →
        (∀ i, Measure.map (fun ω => Real.log (x i ω)) ℙ = gaussianReal μ (Real.toNNReal (σ ^ 2))) →
        ∀ m : ℝ,
          1 / 2 ≤ (ℙ : Measure Ω).real {ω | (1 / (n : ℝ)) * ∑ i, x i ω ≤ m} →
          1 / 2 ≤ (ℙ : Measure Ω).real {ω | m ≤ (1 / (n : ℝ)) * ∑ i, x i ω} →
          m < 𝔼[fun ω => (1 / (n : ℝ)) * ∑ i, x i ω] := by
  intro n hn μ σ hσ Ω _ _ x hindep hx_pos hx_law m hm_le hm_ge
  let Z : Fin n → Ω → ℝ := fun i ω => (Real.log (x i ω) - μ) / σ
  have hlog_aem : ∀ i, AEMeasurable (fun ω => Real.log (x i ω)) (ℙ : Measure Ω) := by
    intro i
    by_contra hnot
    have h0 : Measure.map (fun ω => Real.log (x i ω)) (ℙ : Measure Ω) = 0 := Measure.map_of_not_aemeasurable hnot
    rw [hx_law i] at h0
    exact IsProbabilityMeasure.ne_zero (gaussianReal μ (Real.toNNReal (σ ^ 2))) h0
  have hx_aem : ∀ i, AEMeasurable (x i) (ℙ : Measure Ω) := by
    intro i
    have h1 : AEMeasurable (fun ω => Real.exp (Real.log (x i ω))) (ℙ : Measure Ω) :=
      Real.continuous_exp.measurable.comp_aemeasurable (hlog_aem i)
    refine h1.congr ?_
    filter_upwards [hx_pos i] with ω hω
    exact Real.exp_log hω
  have hZ_aem : ∀ i, AEMeasurable (Z i) (ℙ : Measure Ω) := fun i =>
    (((hlog_aem i).sub_const μ).div_const σ)
  have hZ_law : ∀ i, Measure.map (Z i) (ℙ : Measure Ω) = gaussianReal 0 1 := by
    intro i
    have hcomp : Z i = (fun t => t / σ) ∘ (fun t => t - μ) ∘ (fun ω => Real.log (x i ω)) := rfl
    rw [hcomp, ← AEMeasurable.map_map_of_aemeasurable (by fun_prop) ((by fun_prop : Measurable (fun t : ℝ => t - μ)).comp_aemeasurable (hlog_aem i)),
      ← AEMeasurable.map_map_of_aemeasurable (by fun_prop) (hlog_aem i), hx_law i,
      gaussianReal_map_sub_const, sub_self, gaussianReal_map_div_const]
    congr 1
    · simp
    · ext
      simp only [NNReal.coe_div, Real.coe_toNNReal (σ ^ 2) (sq_nonneg σ), NNReal.coe_mk,
        NNReal.coe_one, div_self (ne_of_gt (sq_pos_of_pos hσ))]
  have hZ_indep : iIndepFun Z (ℙ : Measure Ω) := by
    have h1 := hindep.comp (fun _ : Fin n => fun t : ℝ => (Real.log t - μ) / σ)
      (fun _ => ((Real.measurable_log.sub measurable_const).div measurable_const))
    exact h1
  have hjoint : Measure.map (fun ω i => Z i ω) (ℙ : Measure Ω) = γ n := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map hZ_aem).mp hZ_indep]
    unfold γ; congr 1; funext i; exact hZ_law i
  -- Compare `y ω = (1/n) ∑ x i ω` with `exp μ * F₀ n σ (Z · ω)` a.e.
  have hae_eq : ∀ᵐ ω ∂(ℙ : Measure Ω),
      (1 / (n : ℝ)) * ∑ i : Fin n, x i ω = Real.exp μ * F₀ n σ (fun i => Z i ω) := by
    have hall_pos : ∀ᵐ ω ∂(ℙ : Measure Ω), ∀ i : Fin n, 0 < x i ω := ae_all_iff.mpr hx_pos
    filter_upwards [hall_pos] with ω hω
    unfold F₀
    conv_rhs => rw [← mul_assoc, mul_comm (Real.exp μ) (1 / (n : ℝ)), mul_assoc]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : σ * Z i ω = Real.log (x i ω) - μ := by
      dsimp [Z]; exact mul_div_cancel₀ _ (ne_of_gt hσ)
    rw [h1, ← Real.exp_add, add_sub_cancel, Real.exp_log (hω i)]
  have hZ_fun_aem : AEMeasurable (fun ω i => Z i ω) (ℙ : Measure Ω) :=
    aemeasurable_pi_lambda _ hZ_aem
  set E₀ := ∫ w, F₀ n σ w ∂(γ n)
  have hE_eq : 𝔼[fun ω => (1 / (n : ℝ)) * ∑ i, x i ω] = Real.exp μ * E₀ := by
    rw [integral_congr_ae hae_eq, integral_const_mul]
    congr 1
    have hmap_int := integral_map hZ_fun_aem (F₀_continuous n σ).aestronglyMeasurable
    rw [hjoint] at hmap_int
    exact hmap_int.symm
  rw [hE_eq]
  -- If `Real.exp μ * E₀ ≤ m`, then `{m ≤ y}` has measure `≤ γ_n {E₀ ≤ F₀} < 1/2`, contradicting `hm_ge`!
  by_contra hle
  push Not at hle
  have hstrict := kwapien_strict hn hσ
  have hmeas_lt : MeasurableSet {z : Fin n → ℝ | F₀ n σ z < E₀} :=
    (isOpen_lt (F₀_continuous n σ) continuous_const).measurableSet
  have hmeas_ge : MeasurableSet {z : Fin n → ℝ | E₀ ≤ F₀ n σ z} :=
    (isClosed_le continuous_const (F₀_continuous n σ)).measurableSet
  have hcompl : (γ n).real {z | E₀ ≤ F₀ n σ z} < 1 / 2 := by
    have hset : {z : Fin n → ℝ | E₀ ≤ F₀ n σ z} = {z | F₀ n σ z < E₀}ᶜ := by ext z; simp
    rw [hset]
    have htot := measureReal_add_measureReal_compl (μ := γ n) hmeas_lt
    rw [probReal_univ] at htot
    linarith
  have hsub_ae : (ℙ : Measure Ω) {ω | m ≤ (1 / (n : ℝ)) * ∑ i, x i ω} ≤
      (ℙ : Measure Ω) {ω | E₀ ≤ F₀ n σ (fun i => Z i ω)} := by
    refine measure_mono_ae ?_
    filter_upwards [hae_eq] with ω hω hmω
    change E₀ ≤ F₀ n σ (fun i => Z i ω)
    change m ≤ (1 / (n : ℝ)) * ∑ i, x i ω at hmω
    rw [hω] at hmω
    have : Real.exp μ * E₀ ≤ Real.exp μ * F₀ n σ (fun i => Z i ω) := le_trans hle hmω
    exact le_of_mul_le_mul_left this (Real.exp_pos μ)
  have hmap_ge : (ℙ : Measure Ω) {ω | E₀ ≤ F₀ n σ (fun i => Z i ω)} = (γ n) {z | E₀ ≤ F₀ n σ z} := by
    rw [← hjoint, Measure.map_apply_of_aemeasurable hZ_fun_aem hmeas_ge]; rfl
  have hreal_le : (ℙ : Measure Ω).real {ω | m ≤ (1 / (n : ℝ)) * ∑ i, x i ω} ≤
      (γ n).real {z | E₀ ≤ F₀ n σ z} := by
    rw [Measure.real, Measure.real, ← hmap_ge]
    exact ENNReal.toReal_mono (measure_ne_top _ _) hsub_ae
  linarith

end OMA.S_mo_271503_Proof

theorem OMA.solution : type_of% @OMA.S_mo_271503.main :=
  OMA.S_mo_271503_Proof.main_proof




