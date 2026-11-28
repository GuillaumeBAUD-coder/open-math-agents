import OMAStatements.S_mo_360993

/-! The first step represents the low-exponent kernel by dilates of the
compact kernel K(x) = ∫ from |x| to 1 of s(1-s)² ds, extended by zero.
The second step uses the positive stable Gaussian scale mixture and the
third-order Taylor lower bound for exp(y(1-t^(-2/a))) for t ≥ 1.
The final step is a scalar inequality from the digamma series. -/

namespace OMA.R_mo_360993_R1
open Real MeasureTheory Set Filter
open scoped FourierTransform Topology

def H1 : Prop :=
  ∀ a : ℝ, 0 < a → a ≤ 5/4 → ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧
    ∀ w : ℝ, (∫ x : ℝ, Real.cos (-2*Real.pi*x*w) * (Real.exp (- |x|^a) * (2 + |x|^a * Real.log (|x|^a)))) =
      ∫ t : ℝ, let z := |2*Real.pi*w*t|
               if z = 0 then (1/30 : ℝ)
               else 2*(z*(2+Real.cos z) - 3*Real.sin z)/z^5 ∂μ

def H2 : Prop :=
  ∀ a : ℝ, 5/4 ≤ a → a < 2 →
    let B := fun v : ℝ => 2 - Real.eulerMascheroniConstant*v +
      ∑' k : ℕ, v^2 / (((k : ℝ)+1)*((k : ℝ)+1+v))
    let cubic := fun r y : ℝ => B r + (B r - B (3*r))*y +
      (B r - 2*B (3*r) + B (5*r))*y^2/2 +
      (B r - 3*B (3*r) + 3*B (5*r) - B (7*r))*y^3/6
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      (∀ x : ℝ, Real.exp (- |x|^a) =
        ∫ v in Ioi (0 : ℝ), Real.exp (-v*x^2) ∂μ) ∧
      ∀ w : ℝ, (∫ v in Ioi (0 : ℝ),
        let y := (2*Real.pi*w)^2/(4*v)
        Real.sqrt (Real.pi/v) * Real.exp (-y) * cubic (1/a) y ∂μ) ≤
        ∫ x : ℝ, Real.cos (-2*Real.pi*x*w) * (Real.exp (- |x|^a) * (2 + |x|^a * Real.log (|x|^a)))

def H3 : Prop :=
  let B := fun v : ℝ => 2 - Real.eulerMascheroniConstant*v +
      ∑' k : ℕ, v^2 / (((k : ℝ)+1)*((k : ℝ)+1+v))
  let cubic := fun r y : ℝ => B r + (B r - B (3*r))*y +
      (B r - 2*B (3*r) + B (5*r))*y^2/2 +
      (B r - 3*B (3*r) + 3*B (5*r) - B (7*r))*y^3/6
  ∀ r y : ℝ, r ∈ Icc (1/2) (4/5) → 0 ≤ y → 0 ≤ cubic r y


theorem nonneg_of_derivative_on_three {f d : ℝ → ℝ} (hf : 0 ≤ f 0)
    (hd : ∀ x, HasDerivAt f (d x) x) (hs : ∀ x ∈ Icc 0 3, 0 ≤ d x) :
    ∀ x ∈ Icc 0 3, 0 ≤ f x := by
  have m := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) 3)
    (fun x _ => (hd x).continuousAt.continuousWithinAt)
    (fun x _ => (hd x).hasDerivWithinAt) (fun x hx => hs x (interior_subset hx))
  intro x hx
  exact hf.trans (m (by constructor <;> norm_num) hx hx.1)

theorem compact_numerator (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ x*(2+cos x) - 3*sin x := by
  by_cases h : x ≤ 3
  · apply nonneg_of_derivative_on_three (d := fun t => 2-2*cos t-t*sin t) (by norm_num) _ _ x ⟨hx,h⟩
    · intro t
      convert! ((hasDerivAt_id t).mul ((Real.hasDerivAt_cos t).const_add 2)).sub
        ((Real.hasDerivAt_sin t).const_mul 3) using 1
      dsimp
      ring
    apply nonneg_of_derivative_on_three (d := fun t => sin t-t*cos t) (by norm_num)
    · intro t
      convert! (((Real.hasDerivAt_cos t).const_mul 2).const_sub 2).sub
        ((hasDerivAt_id t).mul (Real.hasDerivAt_sin t)) using 1
      dsimp
      ring
    apply nonneg_of_derivative_on_three (d := fun t => t*sin t) (by norm_num)
    · intro t
      convert! (Real.hasDerivAt_sin t).sub ((hasDerivAt_id t).mul (Real.hasDerivAt_cos t))
        using 1
      dsimp
      ring
    · intro t ht
      exact mul_nonneg ht.1 (Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (ht.2.trans Real.pi_gt_three.le))
  · nlinarith [mul_nonneg hx (show 0 ≤ 1+cos x by linarith [Real.neg_one_le_cos x]), Real.sin_le_one x]


lemma cosine_reduction (hsign : ∀ (a w : ℝ), a ∈ Ioo 0 2 →
    0 ≤ ∫ x : ℝ, Real.cos (-2*Real.pi*x*w) * (Real.exp (- |x|^a) * (2 + |x|^a * Real.log (|x|^a)))) :
    type_of% @OMA.S_mo_360993.main := by
  let weight (a x : ℝ) := Real.exp (- |x| ^ a)
  let kernel (a x : ℝ) :=
    weight a x * (2 + |x| ^ a * Real.log (|x| ^ a))
  let integrand (w a x : ℝ) :=
    Real.cos (-2*Real.pi*x*w) * (weight a x / a^2)
  let slope (w a x : ℝ) :=
    (-(1/a^3)) * (Real.cos (-2*Real.pi*x*w) * kernel a x)
  have envelope_integrable {p b : ℝ} (hp : 0 < p) (hb : 0 < b) :
      Integrable (fun x : ℝ => Real.exp (-b * |x|^p)) := by
    have hi : IntegrableOn (fun x : ℝ => Real.exp (-b * |x|^p)) (Ioi 0) := by
      have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 0) (by norm_num) hp hb
      simp only [Real.rpow_zero, one_mul] at h
      exact h.congr_fun (fun x hx => by rw [abs_of_pos hx]) measurableSet_Ioi
    rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
      integrableOn_Ici_iff_integrableOn_Ioi]
    refine ⟨?_, hi⟩
    rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
        (Homeomorph.neg ℝ).measurableEmbedding]
    simpa only [Function.comp_def, abs_neg, neg_preimage, neg_Iio, neg_zero] using hi

  have weight_integrable {a : ℝ} (ha : 0 < a) : Integrable (weight a) := by
    change Integrable (fun x : ℝ => Real.exp (-|x|^a))
    simpa only [neg_one_mul] using (envelope_integrable ha (b := 1) one_pos)

  have log_factor_bound (u : ℝ) (hu : 0 < u) :
      |2 + u * Real.log u| ≤ 11 * Real.exp (u/2) := by
    have h₁ := Real.log_le_sub_one_of_pos hu
    have h₂ := Real.log_le_sub_one_of_pos (inv_pos.mpr hu)
    rw [Real.log_inv] at h₂
    have hmul := mul_le_mul_of_nonneg_left h₂ hu.le
    rw [mul_sub, mul_inv_cancel₀ hu.ne', mul_one] at hmul
    have he := Real.pow_div_factorial_le_exp (u/2) (by positivity) 2
    norm_num at he
    have hge : 1 ≤ Real.exp (u/2) := Real.one_le_exp (by positivity)
    apply abs_le.mpr
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left h₁ hu.le]

  have kernel_bound {p b x : ℝ} (hp : 0 < p) (hb : p ≤ b) (hx : x ≠ 0) :
      |kernel b x| ≤ 11 * Real.exp 1 * Real.exp (-(1/2) * |x| ^ p) := by
    have hx' : 0 < |x| := abs_pos.mpr hx
    set u := |x|^b
    have hu : 0 < u := Real.rpow_pos_of_pos hx' _
    have he : -(u/2) ≤ 1 + (-(1/2) * |x|^p) := by
      rcases le_total 1 |x| with h|h
      · have := Real.rpow_le_rpow_of_exponent_le h hb
        dsimp [u]; linarith
      · have := Real.rpow_le_one hx'.le h hp.le
        linarith
    change |Real.exp (-u) * (2 + u * Real.log u)| ≤ _
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-u) * (11 * Real.exp (u/2)) :=
        mul_le_mul_of_nonneg_left (log_factor_bound _ hu) (Real.exp_pos _).le
      _ = 11 * Real.exp (-(u/2)) := by
        rw [show -(u/2) = -u + u/2 by ring, Real.exp_add]; ring
      _ ≤ _ := by
        rw [mul_assoc, ← Real.exp_add]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by norm_num)

  have re_fourier (f : ℝ → ℝ) (hf : Integrable f) (w : ℝ) :
      (𝓕 (fun x : ℝ => (f x : ℂ)) w).re =
        ∫ x : ℝ, Real.cos (-2*Real.pi*x*w) * f x := by
    rw [Real.fourier_real_eq_integral_exp_smul, ← RCLike.re_to_complex, ← integral_re]
    · apply integral_congr_ae
      filter_upwards with x
      simp only [RCLike.re_to_complex, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero, Complex.exp_ofReal_mul_I_re]
    · simp only [smul_eq_mul]
      apply (hf.ofReal (𝕜 := ℂ)).bdd_mul (c := 1)
      · fun_prop
      · exact .of_forall (fun x => (Complex.norm_exp_ofReal_mul_I _).le)

  have integrand_diff {a x : ℝ} (w : ℝ) (ha : 0 < a) (hx : x ≠ 0) :
      HasDerivAt (fun b => integrand w b x) (slope w a x) a := by
    have h := (hasDerivAt_id a).const_rpow (abs_pos.mpr hx)
    have d := ((h.neg.exp).div ((hasDerivAt_id a).pow 2) (by positivity : a^2 ≠ 0)).const_mul
      (Real.cos (-2*Real.pi*x*w))
    convert! d using 1
    unfold slope kernel weight
    rw [Real.log_rpow (abs_pos.mpr hx)]
    dsimp
    field_simp
    ring

  have slope_bound {p b x : ℝ} (w : ℝ) (hp : 0 < p) (hb : p ≤ b) (hx : x ≠ 0) :
      ‖slope w b x‖ ≤ ((1/p^3)*(11*Real.exp 1)) * Real.exp (-(1/2)*|x|^p) := by
    have hb' := hp.trans_le hb
    have hc := Real.abs_cos_le_one (-2*Real.pi*x*w)
    have hi : 1/b^3 ≤ 1/p^3 := one_div_le_one_div_of_le (by positivity) (by gcongr)
    unfold slope
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 1/b^3), abs_mul]
    calc
      _ ≤ (1/p^3) * (1 * (11*Real.exp 1 * Real.exp (-(1/2)*|x|^p))) := by
        gcongr
        exact kernel_bound hp hb hx
      _ = _ := by ring

  have integral_diff {a : ℝ} (w : ℝ) (ha : 0 < a) :
      HasDerivAt (fun b => ∫ x : ℝ, integrand w b x) (∫ x : ℝ, slope w a x) a := by
    let p := a/2
    have hp : 0 < p := by dsimp [p]; positivity
    have hs : Ioi p ∈ 𝓝 a := Ioi_mem_nhds (by dsimp [p]; linarith)
    have hm (b : ℝ) : AEStronglyMeasurable (integrand w b) volume := by
      unfold integrand weight
      fun_prop
    have hmi : Integrable (integrand w a) := by
      exact ((weight_integrable ha).div_const (a^2)).bdd_mul (c := 1) (by fun_prop)
        (.of_forall (fun x => by simpa using Real.abs_cos_le_one (-2*Real.pi*x*w)))
    have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := integrand w)
      (F' := slope w) hs (.of_forall hm) hmi (by unfold slope kernel weight; fun_prop)
      (bound := fun x : ℝ => ((1/p^3)*(11*Real.exp 1)) * Real.exp (-(1/2)*|x|^p))
      (by
        filter_upwards [show ∀ᵐ x : ℝ, x ≠ 0 from volume.ae_ne 0] with x hx b hb
        exact slope_bound w hp (le_of_lt hb) hx)
      ((envelope_integrable hp (b := 1/2) (by norm_num)).const_mul _)
      (by
        filter_upwards [show ∀ᵐ x : ℝ, x ≠ 0 from volume.ae_ne 0] with x hx b hb
        exact integrand_diff w (hp.trans hb) hx)
    exact hd.2
  intro w
  have eqn {a : ℝ} (ha : 0 < a) :
      (𝓕 (fun x : ℝ => ((Real.exp (-(|x|^a))/a^2 : ℝ) : ℂ)) w).re =
      ∫ x : ℝ, integrand w a x :=
    re_fourier _ ((weight_integrable ha).div_const _) w
  have hmono : AntitoneOn (fun a => ∫ x : ℝ, integrand w a x) (Ioo 0 2) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioo _ _)
      (fun b hb => (integral_diff w hb.1).continuousAt.continuousWithinAt)
      (fun b hb => (integral_diff w (interior_subset hb).1).hasDerivWithinAt)
    intro b hb
    have ht := interior_subset hb
    rw [show (∫ x : ℝ, slope w b x) =
          (-(1/b^3)) * ∫ x : ℝ, Real.cos (-2*Real.pi*x*w) * kernel b x from
          integral_const_mul _ _]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (one_div_nonneg.mpr (pow_nonneg ht.1.le _))) (hsign b w ht)
  intro a ha b hb hab
  dsimp only
  rw [eqn ha.1, eqn hb.1]
  exact hmono ha hb hab

theorem main : H1 → H2 → H3 → type_of% @OMA.S_mo_360993.main := by
  intro hsmall hlarge hcubic
  apply cosine_reduction
  intro a w ha
  by_cases h : a ≤ 5/4
  · obtain ⟨μ, _, hμ⟩ := hsmall a ha.1 h
    rw [hμ w]
    apply integral_nonneg
    intro t
    dsimp only
    split_ifs with hz
    · norm_num
    · exact div_nonneg (mul_nonneg (by norm_num) (compact_numerator _ (abs_nonneg _)))
        (pow_nonneg (abs_nonneg _) _)
  · obtain ⟨μ, _, _, hμ⟩ := hlarge a (le_of_not_ge h) ha.2
    apply le_trans _ (hμ w)
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem (μ := μ) (measurableSet_Ioi (a := (0 : ℝ)))] with v hv
    have hv' : 0 < v := hv
    have hr : 1/a ∈ Icc (1/2 : ℝ) (4/5) := by
      constructor
      · exact one_div_le_one_div_of_le ha.1 ha.2.le
      · apply (div_le_iff₀ ha.1).2
        linarith
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)
      (hcubic (1/a) _ hr (div_nonneg (sq_nonneg _) (by positivity)))

end OMA.R_mo_360993_R1
