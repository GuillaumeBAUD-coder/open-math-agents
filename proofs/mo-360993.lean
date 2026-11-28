import OMAStatements.S_mo_360993

section
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
end

section
namespace Mo360993Small

def P (w v : ℝ) := (4430+v*(4750+v*(3000+v*(-1250)))) + w*(18540+v*(13500+v*(-4500))) + w^2*(23040) + w^3*(7680)
def Q (w v : ℝ) := (-1155+v*(-1395+v*(-975+v*(-1750+v*(625))))) + w*(-6740+v*(-7860+v*(-6200+v*(4500)))) + w^2*(-12640+v*(-8160+v*(10400))) + w^3*(-7680+v*(7680))

def seriesNum (v : ℝ) :=
  210*(v-1)*(v+1)^6 + 70*(v-1)^3*(v+1)^4 +
  42*(v-1)^5*(v+1)^2 + 30*(v-1)^7

def lowNum (w v : ℝ) := 105*(v+1)^7 * P w v + seriesNum v * Q w v
def highNum (w v : ℝ) := 2*v*lowNum w v + 105*(v-1)^9 * Q w v

set_option maxHeartbeats 2400000 in
theorem lowNum_nonneg (w v : ℝ) (hw : 0 ≤ w) (hv : 1 ≤ v) : 0 ≤ lowNum w v := by
  by_cases h₃ : v < 3
  · let t := (v-1)/(3-v)
    have ht : 0 ≤ t := div_nonneg (by linarith) (by linarith)
    have he : v = (1+3*t)/(1+t) := by
      apply (eq_div_iff (by positivity : (1+t : ℝ) ≠ 0)).2
      dsimp [t]
      field_simp [ne_of_gt (sub_pos.mpr h₃)]
      <;> ring
    rw [he]
    unfold lowNum P Q seriesNum
    field_simp
    ring_nf
    positivity
  by_cases h₄ : v < 4
  · let t := (v-3)/(4-v)
    have ht : 0 ≤ t := div_nonneg (by linarith) (by linarith)
    have he : v = (3+4*t)/(1+t) := by
      apply (eq_div_iff (by positivity : (1+t : ℝ) ≠ 0)).2
      dsimp [t]
      field_simp [ne_of_gt (sub_pos.mpr h₄)]
      <;> ring
    rw [he]
    unfold lowNum P Q seriesNum
    field_simp
    ring_nf
    positivity
  obtain ⟨t, ht, rfl⟩ := exists_nonneg_add_of_le (le_of_not_gt h₄)
  unfold lowNum P Q seriesNum
  ring_nf
  positivity

set_option maxHeartbeats 2400000 in
theorem highNum_nonneg (w v : ℝ) (hw : 0 ≤ w) (hv : 1 ≤ v) : 0 ≤ highNum w v := by
  by_cases h₃ : v < 3
  · let t := (v-1)/(3-v)
    have ht : 0 ≤ t := div_nonneg (by linarith) (by linarith)
    have he : v = (1+3*t)/(1+t) := by
      apply (eq_div_iff (by positivity : (1+t : ℝ) ≠ 0)).2
      dsimp [t]
      field_simp [ne_of_gt (sub_pos.mpr h₃)]
      <;> ring
    rw [he]
    unfold highNum lowNum P Q seriesNum
    field_simp
    ring_nf
    positivity
  by_cases h₄ : v < 4
  · let t := (v-3)/(4-v)
    have ht : 0 ≤ t := div_nonneg (by linarith) (by linarith)
    have he : v = (3+4*t)/(1+t) := by
      apply (eq_div_iff (by positivity : (1+t : ℝ) ≠ 0)).2
      dsimp [t]
      field_simp [ne_of_gt (sub_pos.mpr h₄)]
      <;> ring
    rw [he]
    unfold highNum lowNum P Q seriesNum
    field_simp
    ring_nf
    positivity
  obtain ⟨t, ht, rfl⟩ := exists_nonneg_add_of_le (le_of_not_gt h₄)
  unfold highNum lowNum P Q seriesNum
  ring_nf
  positivity

set_option maxHeartbeats 2400000 in
theorem log_polynomial_nonneg (w v : ℝ) (hw : 0 ≤ w) (hv : 0 < v) : 0 ≤ P w v + Q w v * Real.log v := by
  by_cases hv₁ : v < 1
  · have hl := Real.log_nonpos hv.le hv₁.le
    let t := (1-v)/v
    have ht : 0 ≤ t := div_nonneg (by linarith) hv.le
    have he : v = 1/(1+t) := by dsimp [t]; field_simp; ring
    have hp : 0 ≤ P w v := by
      rw [he]; unfold P; field_simp; ring_nf; positivity
    have hq : Q w v ≤ 0 := by
      rw [← neg_nonneg, he]; unfold Q; field_simp; ring_nf; positivity
    exact add_nonneg hp (mul_nonneg_of_nonpos_of_nonpos hq hl)
  have hv₁ : 1 ≤ v := le_of_not_gt hv₁
  let z := (v-1)/(v+1)
  have hz : 0 ≤ z := div_nonneg (by linarith) (by linarith)
  have hz' : z < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have he : (1+z)/(1-z) = v := by
    dsimp [z]
    field_simp
    ring
  have lo := Real.sum_range_le_log_div hz hz' 4
  have hi := Real.log_div_le_sum_range_add hz hz' 4
  rw [he] at lo hi
  norm_num [Finset.sum_range_succ] at lo hi
  have denom : 0 < 105*(v+1)^7 := by positivity
  have hd : 0 < 1-z^2 := by nlinarith
  have heq : seriesNum v / (105*(v+1)^7) = 2*(z + z^3/3 + z^5/5 + z^7/7) := by
    unfold seriesNum z
    field_simp
    ring
  have er : 2 * z^9 / (1-z^2) = (v-1)^9/(2*v*(v+1)^7) := by
    apply (div_eq_div_iff (ne_of_gt hd) (by positivity)).2
    dsimp [z]
    field_simp [hv.ne']
    <;> ring
  by_cases hq : 0 ≤ Q w v
  · have hl : seriesNum v / (105*(v+1)^7) ≤ Real.log v := by rw [heq]; linarith
    have h := lowNum_nonneg w v hw hv₁
    unfold lowNum at h
    have hp : 0 ≤ P w v + Q w v * (seriesNum v / (105*(v+1)^7)) := by
      field_simp
      linarith
    nlinarith only [hp, mul_nonneg hq (sub_nonneg.mpr hl)]
  · have hu : Real.log v ≤ seriesNum v / (105*(v+1)^7) + (v-1)^9/(2*v*(v+1)^7) := by
      rw [heq, ← er, mul_div_assoc]
      linarith
    have h := highNum_nonneg w v hw hv₁
    unfold highNum lowNum at h
    have hp : 0 ≤ P w v + Q w v * (seriesNum v / (105*(v+1)^7) + (v-1)^9/(2*v*(v+1)^7)) := by
      field_simp
      nlinarith only [h]
    nlinarith only [hp, mul_nonneg (neg_nonneg.mpr (le_of_not_ge hq)) (sub_nonneg.mpr hu)]

end Mo360993Small

namespace Mo360993Small
open Real Set Filter MeasureTheory
open scoped Topology

def poly0 (a v L : ℝ) := (2 : ℝ) + (1 : ℝ)*v^1*L

noncomputable def jet0 (a x : ℝ) := Real.exp (-x^a) / x^0 * poly0 a (x^a) (Real.log (x^a))

def poly1 (a v L : ℝ) := (1 : ℝ)*a^1*v^1 + (-1 : ℝ)*a^1*v^1*L + (1 : ℝ)*a^1*v^2*L

noncomputable def jet1 (a x : ℝ) := Real.exp (-x^a) / x^2 * poly1 a (x^a) (Real.log (x^a))

def poly2 (a v L : ℝ) := (2 : ℝ)*a^1*v^1 + (-2 : ℝ)*a^1*v^1*L + (2 : ℝ)*a^1*v^2*L + (1 : ℝ)*a^2*v^1*L + (-3 : ℝ)*a^2*v^2*L + (1 : ℝ)*a^2*v^3*L

noncomputable def jet2 (a x : ℝ) := Real.exp (-x^a) / x^3 * poly2 a (x^a) (Real.log (x^a))

def poly3 (a v L : ℝ) := (6 : ℝ)*a^1*v^1 + (-6 : ℝ)*a^1*v^1*L + (6 : ℝ)*a^1*v^2*L + (5 : ℝ)*a^2*v^1*L + (-15 : ℝ)*a^2*v^2*L + (5 : ℝ)*a^2*v^3*L + (-1 : ℝ)*a^3*v^1 + (-1 : ℝ)*a^3*v^1*L + (3 : ℝ)*a^3*v^2 + (7 : ℝ)*a^3*v^2*L + (-1 : ℝ)*a^3*v^3 + (-6 : ℝ)*a^3*v^3*L + (1 : ℝ)*a^3*v^4*L

noncomputable def jet3 (a x : ℝ) := Real.exp (-x^a) / x^4 * poly3 a (x^a) (Real.log (x^a))

def poly4 (a v L : ℝ) := (24 : ℝ)*a^1*v^1 + (-24 : ℝ)*a^1*v^1*L + (24 : ℝ)*a^1*v^2*L + (26 : ℝ)*a^2*v^1*L + (-78 : ℝ)*a^2*v^2*L + (26 : ℝ)*a^2*v^3*L + (-9 : ℝ)*a^3*v^1 + (-9 : ℝ)*a^3*v^1*L + (27 : ℝ)*a^3*v^2 + (63 : ℝ)*a^3*v^2*L + (-9 : ℝ)*a^3*v^3 + (-54 : ℝ)*a^3*v^3*L + (9 : ℝ)*a^3*v^4*L + (2 : ℝ)*a^4*v^1 + (1 : ℝ)*a^4*v^1*L + (-14 : ℝ)*a^4*v^2 + (-15 : ℝ)*a^4*v^2*L + (12 : ℝ)*a^4*v^3 + (25 : ℝ)*a^4*v^3*L + (-2 : ℝ)*a^4*v^4 + (-10 : ℝ)*a^4*v^4*L + (1 : ℝ)*a^4*v^5*L

noncomputable def jet4 (a x : ℝ) := Real.exp (-x^a) / x^5 * poly4 a (x^a) (Real.log (x^a))

set_option maxHeartbeats 2400000 in
theorem jet_vderiv (a : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => t^a) (a*x^a/x) x := by
  convert Real.hasDerivAt_rpow_const (p := a) (Or.inl hx.ne') using 1
  rw [Real.rpow_sub hx, Real.rpow_one]
  ring

set_option maxHeartbeats 2400000 in
theorem jet_logderiv (a : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => Real.log (t^a)) (a/x) x := by
  have hv := jet_vderiv a hx
  have hv' := Real.rpow_pos_of_pos hx a
  convert (hv.log hv'.ne') using 1
  field_simp

set_option maxHeartbeats 2400000 in
theorem jet0_deriv (a : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (jet0 a) (-x*jet1 a x) x := by
  have hv := jet_vderiv a hx
  have hl := jet_logderiv a hx
  have he := (hv.neg.exp).div ((hasDerivAt_id x).pow 0) (pow_ne_zero 0 hx.ne')
  have hd := he.mul ((hasDerivAt_const x (2 : ℝ)).add (((hasDerivAt_const x (1 : ℝ)).mul (hv.pow 1)).mul hl))
  unfold jet0 jet1 poly0 poly1
  convert! hd using 1
  simp only [Pi.neg_apply, Pi.pow_apply, Pi.add_apply, Pi.mul_apply, Pi.div_apply, id_eq]
  field_simp
  ring

set_option maxHeartbeats 2400000 in
theorem jet1_deriv (a : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (jet1 a) (-jet2 a x) x := by
  have hv := jet_vderiv a hx
  have hl := jet_logderiv a hx
  have he := (hv.neg.exp).div ((hasDerivAt_id x).pow 2) (pow_ne_zero 2 hx.ne')
  have hd := he.mul (((((hasDerivAt_const x (1 : ℝ)).mul (hasDerivAt_const x (a^1))).mul (hv.pow 1)).add ((((hasDerivAt_const x (-1 : ℝ)).mul (hasDerivAt_const x (a^1))).mul (hv.pow 1)).mul hl)).add ((((hasDerivAt_const x (1 : ℝ)).mul (hasDerivAt_const x (a^1))).mul (hv.pow 2)).mul hl))
  unfold jet1 jet2 poly1 poly2
  convert! hd using 1
  simp only [Pi.neg_apply, Pi.pow_apply, Pi.add_apply, Pi.mul_apply, Pi.div_apply, id_eq]
  field_simp
  ring

set_option maxHeartbeats 2400000 in
theorem jet2_deriv (a : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (jet2 a) (-jet3 a x) x := by
  have hv := jet_vderiv a hx
  have hl := jet_logderiv a hx
  have he := (hv.neg.exp).div ((hasDerivAt_id x).pow 3) (pow_ne_zero 3 hx.ne')
  have hd := he.mul ((((((((hasDerivAt_const x (2 : ℝ)).mul (hasDerivAt_const x (a^1))).mul (hv.pow 1)).add ((((hasDerivAt_const x (-2 : ℝ)).mul (hasDerivAt_const x (a^1))).mul (hv.pow 1)).mul hl)).add ((((hasDerivAt_const x (2 : ℝ)).mul (hasDerivAt_const x (a^1))).mul (hv.pow 2)).mul hl)).add ((((hasDerivAt_const x (1 : ℝ)).mul (hasDerivAt_const x (a^2))).mul (hv.pow 1)).mul hl)).add ((((hasDerivAt_const x (-3 : ℝ)).mul (hasDerivAt_const x (a^2))).mul (hv.pow 2)).mul hl)).add ((((hasDerivAt_const x (1 : ℝ)).mul (hasDerivAt_const x (a^2))).mul (hv.pow 3)).mul hl))
  unfold jet2 jet3 poly2 poly3
  convert! hd using 1
  simp only [Pi.neg_apply, Pi.pow_apply, Pi.add_apply, Pi.mul_apply, Pi.div_apply, id_eq]
  field_simp
  ring

set_option maxHeartbeats 2400000 in
theorem jet3_deriv (a : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (jet3 a) (-jet4 a x) x := by
  have hv := jet_vderiv a hx
  have hl := jet_logderiv a hx
  have he := (hv.neg.exp).div ((hasDerivAt_id x).pow 4) (pow_ne_zero 4 hx.ne')
  have hd := he.mul (((((((((((((((hasDerivAt_const x (6 : ℝ)).mul (hasDerivAt_const x (a^1))).mul (hv.pow 1)).add ((((hasDerivAt_const x (-6 : ℝ)).mul (hasDerivAt_const x (a^1))).mul (hv.pow 1)).mul hl)).add ((((hasDerivAt_const x (6 : ℝ)).mul (hasDerivAt_const x (a^1))).mul (hv.pow 2)).mul hl)).add ((((hasDerivAt_const x (5 : ℝ)).mul (hasDerivAt_const x (a^2))).mul (hv.pow 1)).mul hl)).add ((((hasDerivAt_const x (-15 : ℝ)).mul (hasDerivAt_const x (a^2))).mul (hv.pow 2)).mul hl)).add ((((hasDerivAt_const x (5 : ℝ)).mul (hasDerivAt_const x (a^2))).mul (hv.pow 3)).mul hl)).add (((hasDerivAt_const x (-1 : ℝ)).mul (hasDerivAt_const x (a^3))).mul (hv.pow 1))).add ((((hasDerivAt_const x (-1 : ℝ)).mul (hasDerivAt_const x (a^3))).mul (hv.pow 1)).mul hl)).add (((hasDerivAt_const x (3 : ℝ)).mul (hasDerivAt_const x (a^3))).mul (hv.pow 2))).add ((((hasDerivAt_const x (7 : ℝ)).mul (hasDerivAt_const x (a^3))).mul (hv.pow 2)).mul hl)).add (((hasDerivAt_const x (-1 : ℝ)).mul (hasDerivAt_const x (a^3))).mul (hv.pow 3))).add ((((hasDerivAt_const x (-6 : ℝ)).mul (hasDerivAt_const x (a^3))).mul (hv.pow 3)).mul hl)).add ((((hasDerivAt_const x (1 : ℝ)).mul (hasDerivAt_const x (a^3))).mul (hv.pow 4)).mul hl))
  unfold jet3 jet4 poly3 poly4
  convert! hd using 1
  simp only [Pi.neg_apply, Pi.pow_apply, Pi.add_apply, Pi.mul_apply, Pi.div_apply, id_eq]
  field_simp
  ring

end Mo360993Small

open Real Set Filter MeasureTheory
open scoped Topology
namespace Mo360993Small

set_option maxHeartbeats 2400000 in
theorem jet4_nonneg {a t : ℝ} (ha : 0 < a) (hab : a ≤ 5/4) (ht : 0 < t) :
    0 ≤ jet4 a t := by
  let w := 5/(4*a)-1
  let v := t^a
  have hv : 0 < v := Real.rpow_pos_of_pos ht a
  have hw : 0 ≤ w := by
    dsimp [w]; rw [sub_nonneg, le_div_iff₀ (by positivity)]; linarith
  have h := log_polynomial_nonneg w v hw hv
  have hpoly : poly4 a v (Real.log v) = (a^4/625)*v*(P w v + Q w v * Real.log v) := by
    unfold poly4 P Q w
    field_simp
    ring
  change 0 ≤ Real.exp (-v)/t^5 * poly4 a v (Real.log v)
  rw [hpoly]
  positivity

set_option maxHeartbeats 2400000 in
theorem exp_poly_limit (n : ℕ) :
    Tendsto (fun v : ℝ => v^n*Real.exp (-v)*Real.log v) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (n+1))
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with v hv
    exact mul_nonneg (mul_nonneg (pow_nonneg (by linarith) _) (Real.exp_pos _).le) (Real.log_nonneg hv)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with v hv
    have h := Real.log_le_self (by linarith : 0 ≤ v)
    rw [pow_succ]
    nlinarith only [mul_nonneg (mul_nonneg (pow_nonneg (by linarith : 0 ≤ v) n)
      (Real.exp_pos (-v)).le) (sub_nonneg.mpr h)]

set_option maxHeartbeats 2400000 in
theorem damped0_limit (a : ℝ) :
    Tendsto (fun v : ℝ => Real.exp (-v)*poly0 a v (Real.log v)) atTop (𝓝 0) := by
  have h0 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).const_mul ((2 : ℝ)*a^0)
  have h1 := (exp_poly_limit 1).const_mul ((1 : ℝ)*a^0)
  convert! (h0.add h1) using 1
  · funext v; unfold poly0; ring
  · ring

set_option maxHeartbeats 2400000 in
theorem damped1_limit (a : ℝ) :
    Tendsto (fun v : ℝ => Real.exp (-v)*poly1 a v (Real.log v)) atTop (𝓝 0) := by
  have h0 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul ((1 : ℝ)*a^1)
  have h1 := (exp_poly_limit 1).const_mul ((-1 : ℝ)*a^1)
  have h2 := (exp_poly_limit 2).const_mul ((1 : ℝ)*a^1)
  convert! ((h0.add h1).add h2) using 1
  · funext v; unfold poly1; ring
  · ring

set_option maxHeartbeats 2400000 in
theorem damped2_limit (a : ℝ) :
    Tendsto (fun v : ℝ => Real.exp (-v)*poly2 a v (Real.log v)) atTop (𝓝 0) := by
  have h0 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul ((2 : ℝ)*a^1)
  have h1 := (exp_poly_limit 1).const_mul ((-2 : ℝ)*a^1)
  have h2 := (exp_poly_limit 2).const_mul ((2 : ℝ)*a^1)
  have h3 := (exp_poly_limit 1).const_mul ((1 : ℝ)*a^2)
  have h4 := (exp_poly_limit 2).const_mul ((-3 : ℝ)*a^2)
  have h5 := (exp_poly_limit 3).const_mul ((1 : ℝ)*a^2)
  convert! (((((h0.add h1).add h2).add h3).add h4).add h5) using 1
  · funext v; unfold poly2; ring
  · ring

set_option maxHeartbeats 2400000 in
theorem damped3_limit (a : ℝ) :
    Tendsto (fun v : ℝ => Real.exp (-v)*poly3 a v (Real.log v)) atTop (𝓝 0) := by
  have h0 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul ((6 : ℝ)*a^1)
  have h1 := (exp_poly_limit 1).const_mul ((-6 : ℝ)*a^1)
  have h2 := (exp_poly_limit 2).const_mul ((6 : ℝ)*a^1)
  have h3 := (exp_poly_limit 1).const_mul ((5 : ℝ)*a^2)
  have h4 := (exp_poly_limit 2).const_mul ((-15 : ℝ)*a^2)
  have h5 := (exp_poly_limit 3).const_mul ((5 : ℝ)*a^2)
  have h6 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul ((-1 : ℝ)*a^3)
  have h7 := (exp_poly_limit 1).const_mul ((-1 : ℝ)*a^3)
  have h8 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).const_mul ((3 : ℝ)*a^3)
  have h9 := (exp_poly_limit 2).const_mul ((7 : ℝ)*a^3)
  have h10 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).const_mul ((-1 : ℝ)*a^3)
  have h11 := (exp_poly_limit 3).const_mul ((-6 : ℝ)*a^3)
  have h12 := (exp_poly_limit 4).const_mul ((1 : ℝ)*a^3)
  convert! ((((((((((((h0.add h1).add h2).add h3).add h4).add h5).add h6).add h7).add h8).add h9).add h10).add h11).add h12) using 1
  · funext v; unfold poly3; ring
  · ring


noncomputable def compactP (t x : ℝ) := (t^4-6*t^2*x^2+8*t*x^3-3*x^4)/12
noncomputable def compactD (t x : ℝ) := (4*t^3-12*t*x^2+8*x^3)/12
noncomputable def compactDD (t x : ℝ) := (12*t^2-12*x^2)/12

set_option maxHeartbeats 2400000 in
theorem compactP_pos {x t : ℝ} (hx : 0 ≤ x) (ht : x ≤ t) : 0 ≤ compactP t x := by
  have he : compactP t x = (t-x)^3*(t+3*x)/12 := by unfold compactP; ring
  rw [he]
  exact div_nonneg (mul_nonneg (pow_nonneg (sub_nonneg.mpr ht) _) (by linarith)) (by norm_num)

set_option maxHeartbeats 2400000 in
theorem compact_der (t x : ℝ) :
    HasDerivAt (fun t => compactP t x) (compactD t x) t ∧
    HasDerivAt (fun t => compactD t x) (compactDD t x) t ∧
    HasDerivAt (fun t => compactDD t x) (2*t) t := by
  have h := hasDerivAt_id t
  unfold compactP compactD compactDD
  refine ⟨?_, ?_, ?_⟩
  · convert! (((((h.pow 4).sub (((h.pow 2).const_mul 6).mul_const (x^2))).add
      ((h.const_mul 8).mul_const (x^3))).sub_const (3*x^4)).div_const 12) using 1 <;> dsimp <;> ring
  · convert! (((((h.pow 3).const_mul 4).sub ((h.const_mul 12).mul_const (x^2))).add_const (8*x^3)).div_const 12) using 1 <;> dsimp <;> ring
  · convert! ((((h.pow 2).const_mul 12).sub_const (12*x^2)).div_const 12) using 1 <;> dsimp <;> ring

noncomputable def primitive (a x t : ℝ) :=
  compactP t x * jet3 a t + compactD t x * jet2 a t + compactDD t x * jet1 a t + 2*jet0 a t

set_option maxHeartbeats 2400000 in
theorem primitive_der {t : ℝ} (a x : ℝ) (ht : 0 < t) :
    HasDerivAt (primitive a x) (-(compactP t x * jet4 a t)) t := by
  obtain ⟨h₀,h₁,h₂⟩ := compact_der t x
  have d := (((h₀.mul (jet3_deriv a ht)).add (h₁.mul (jet2_deriv a ht))).add
    (h₂.mul (jet1_deriv a ht))).add ((jet0_deriv a ht).const_mul 2)
  unfold primitive
  convert! d using 1
  try simp only [Pi.add_apply, Pi.mul_apply]
  ring

set_option maxHeartbeats 2400000 in
theorem primitive_limit {a : ℝ} (ha : 0 < a) (x : ℝ) : Tendsto (primitive a x) atTop (𝓝 0) := by
  have h := tendsto_rpow_atTop ha
  have hz : Tendsto (fun t : ℝ => x/t) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hP := (((((tendsto_const_nhds (x := (1 : ℝ))).sub ((hz.pow 2).const_mul 6)).add
    ((hz.pow 3).const_mul 8)).sub ((hz.pow 4).const_mul 3)).div_const 12)
  have hD := ((((tendsto_const_nhds (x := (4 : ℝ))).sub ((hz.pow 2).const_mul 12)).add
    ((hz.pow 3).const_mul 8)).div_const 12)
  have hDD := ((tendsto_const_nhds (x := (12 : ℝ))).sub ((hz.pow 2).const_mul 12)).div_const 12
  have H := (((hP.mul ((damped3_limit a).comp h)).add (hD.mul ((damped2_limit a).comp h))).add
    (hDD.mul ((damped1_limit a).comp h))).add (((damped0_limit a).comp h).const_mul 2)
  apply Tendsto.congr' _ (by simpa using H)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  try simp only [Function.comp_apply, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.div_apply, Pi.pow_apply]
  unfold primitive compactP compactD compactDD jet0 jet1 jet2 jet3
  field_simp <;> ring

set_option maxHeartbeats 2400000 in
theorem kernel_mixture {a x : ℝ} (ha : 0 < a) (hab : a ≤ 5/4) (hx : 0 < x) :
    IntegrableOn (fun t => compactP t x * jet4 a t) (Ioi x) ∧
    (∫ t in Ioi x, compactP t x * jet4 a t) = 2*jet0 a x := by
  have hd : ∀ t ∈ Ici x, HasDerivAt (fun t => -primitive a x t) (compactP t x * jet4 a t) t := by
    intro t ht
    convert! ((primitive_der a x (hx.trans_le ht)).neg) using 1
    ring
  have hs : ∀ t ∈ Ioi x, 0 ≤ compactP t x * jet4 a t :=
    fun t ht => mul_nonneg (compactP_pos hx.le (le_of_lt ht)) (jet4_nonneg ha hab (hx.trans ht))
  have hl : Tendsto (fun t => -primitive a x t) atTop (𝓝 0) := by simpa using (primitive_limit ha x).neg
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hs hl, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hd hs hl]
  unfold primitive compactP compactD compactDD
  ring
end Mo360993Small

namespace Mo360993Small
open Real Set Filter MeasureTheory

noncomputable def compactPoly (t x : ℝ) := (t^4-6*t^2*x^2+8*t*x^3-3*x^4)/12
noncomputable def cosineProfile (z : ℝ) :=
  if z = 0 then (1/30 : ℝ) else 2*(z*(2+Real.cos z)-3*Real.sin z)/z^5

noncomputable def sinePoly (t w x : ℝ) := (t^4/(12*w)+t^2/w^3-6/w^5)*x^0 + (-4*t/w^3)*x^1 + (-t^2/(2*w)+3/w^3)*x^2 + (2*t/(3*w))*x^3 + (-1/(4*w))*x^4

noncomputable def cosPoly (t w x : ℝ) := (-4*t/w^4)*x^0 + (-t^2/w^2+6/w^4)*x^1 + (2*t/w^2)*x^2 + (-1/w^2)*x^3

noncomputable def zeroPoly (t x : ℝ) := (t^4/12)*x^1 + (-t^2/6)*x^3 + (t/6)*x^4 + (-1/20)*x^5

set_option maxHeartbeats 2400000 in
theorem cosineProfile_even (z : ℝ) : cosineProfile |z| = cosineProfile z := by
  rcases le_total 0 z with hz|hz
  · rw [abs_of_nonneg hz]
  rw [abs_of_nonpos hz]
  unfold cosineProfile
  by_cases h : z = 0
  · simp [h]
  simp only [neg_eq_zero, h, ↓reduceIte, Real.cos_neg, Real.sin_neg]
  ring

set_option maxHeartbeats 2400000 in
theorem compact_cosine_integral (t w : ℝ) (ht : 0 < t) :
    (∫ x in (0 : ℝ)..t, Real.cos (w*x)*compactPoly t x) = t^5*cosineProfile |w*t| := by
  rw [cosineProfile_even]
  have hi : IntervalIntegrable (fun x : ℝ => Real.cos (w*x)*compactPoly t x) volume 0 t :=
    Continuous.intervalIntegrable (by unfold compactPoly; fun_prop) _ _
  by_cases hw : w = 0
  · subst w
    simp only [zero_mul, Real.cos_zero, one_mul, cosineProfile, if_true]
    have hd (x : ℝ) : HasDerivAt (zeroPoly t) (compactPoly t x) x := by
      unfold zeroPoly compactPoly
      convert! ((((((hasDerivAt_id x).pow 1).const_mul (t^4/12 : ℝ)).add (((hasDerivAt_id x).pow 3).const_mul (-t^2/6 : ℝ))).add (((hasDerivAt_id x).pow 4).const_mul (t/6 : ℝ))).add (((hasDerivAt_id x).pow 5).const_mul (-1/20 : ℝ))) using 1
      simp only [Pi.pow_apply, Pi.add_apply, Pi.mul_apply, id_eq]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
      (Continuous.intervalIntegrable (by unfold compactPoly; fun_prop) _ _)]
    unfold zeroPoly; ring
  have hd (x : ℝ) : HasDerivAt (fun y => Real.sin (w*y)*sinePoly t w y + Real.cos (w*y)*cosPoly t w y)
      (Real.cos (w*x)*compactPoly t x) x := by
    have hs := (((((((hasDerivAt_id x).pow 0).const_mul (t^4/(12*w)+t^2/w^3-6/w^5 : ℝ)).add (((hasDerivAt_id x).pow 1).const_mul (-4*t/w^3 : ℝ))).add (((hasDerivAt_id x).pow 2).const_mul (-t^2/(2*w)+3/w^3 : ℝ))).add (((hasDerivAt_id x).pow 3).const_mul (2*t/(3*w) : ℝ))).add (((hasDerivAt_id x).pow 4).const_mul (-1/(4*w) : ℝ)))
    have hc := ((((((hasDerivAt_id x).pow 0).const_mul (-4*t/w^4 : ℝ)).add (((hasDerivAt_id x).pow 1).const_mul (-t^2/w^2+6/w^4 : ℝ))).add (((hasDerivAt_id x).pow 2).const_mul (2*t/w^2 : ℝ))).add (((hasDerivAt_id x).pow 3).const_mul (-1/w^2 : ℝ)))
    have h := (hasDerivAt_id x).const_mul w
    unfold compactPoly sinePoly cosPoly
    convert! ((h.sin.mul hs).add (h.cos.mul hc)) using 1
    simp only [Pi.pow_apply, Pi.add_apply, Pi.mul_apply, Pi.neg_apply, id_eq]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) hi]
  unfold cosineProfile cosPoly sinePoly
  simp only [mul_zero, Real.sin_zero, zero_mul, Real.cos_zero, one_mul, if_neg (mul_ne_zero hw ht.ne')]
  field_simp
  ring
end Mo360993Small

namespace Mo360993Small
open Real Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable def triangle (a x t : ℝ) := if x < t then compactP t x * jet4 a t else 0

set_option maxHeartbeats 2400000 in
theorem triangle_meas (a : ℝ) : Measurable (fun p : ℝ × ℝ => triangle a p.1 p.2) := by
  unfold triangle jet4 compactP poly4
  exact Measurable.ite (measurableSet_lt measurable_fst measurable_snd) (by fun_prop) measurable_const

set_option maxHeartbeats 2400000 in
theorem triangle_integral {a x : ℝ} (ha : 0 < a) (hab : a ≤ 5/4) (hx : 0 < x) :
    IntegrableOn (triangle a x) (Ioi 0) ∧
    (∫ t in Ioi (0 : ℝ), triangle a x t) = 2*jet0 a x := by
  have h := kernel_mixture ha hab hx
  have he : triangle a x = (Ioi x).indicator (fun t => compactP t x * jet4 a t) := by
    funext t; rfl
  rw [he]
  simpa only [IntegrableOn, integrable_indicator_iff measurableSet_Ioi, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, Ioi_inter_Ioi, sup_eq_left.mpr hx.le] using h

set_option maxHeartbeats 2400000 in
theorem log_factor_bound (u : ℝ) (hu : 0 < u) :
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

set_option maxHeartbeats 2400000 in
theorem jet0_integrable {a : ℝ} (ha : 0 < a) : IntegrableOn (jet0 a) (Ioi 0) := by
  have he := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 0) (by norm_num) ha (b := 1/2) (by norm_num)
  simp only [Real.rpow_zero, one_mul] at he
  apply (he.const_mul 11).mono' (by unfold jet0 poly0; fun_prop)
  filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (0 : ℝ)))] with x hx
  let v := x^a
  have hv : 0 < v := Real.rpow_pos_of_pos hx a
  simp only [jet0, pow_zero, div_one, poly0, pow_one, one_mul, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-v)*(11*Real.exp (v/2)) :=
      mul_le_mul_of_nonneg_left (log_factor_bound v hv) (Real.exp_pos _).le
    _ = 11*Real.exp (-(1/2)*v) := by
      rw [show -(1/2)*v = -v+v/2 by ring, Real.exp_add]; ring

set_option maxHeartbeats 2400000 in
theorem triangle_swap {a : ℝ} (ha : 0 < a) (hab : a ≤ 5/4) :
    Integrable (fun p : ℝ × ℝ => triangle a p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  rw [integrable_prod_iff (triangle_meas a).aestronglyMeasurable]
  have hp := ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (0 : ℝ)))
  refine ⟨hp.mono (fun x hx => (triangle_integral ha hab hx).1), ?_⟩
  apply ((jet0_integrable ha).const_mul 2).congr
  filter_upwards [hp] with x hx
  rw [← (triangle_integral ha hab hx).2]
  apply integral_congr_ae
  filter_upwards [hp] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg]
  unfold triangle
  split_ifs with h
  · exact mul_nonneg (compactP_pos (le_of_lt hx) h.le) (jet4_nonneg ha hab ht)
  · rfl

set_option maxHeartbeats 2400000 in
theorem triangle_cosine (a w t : ℝ) (ht : 0 < t) :
    (∫ x in Ioi (0 : ℝ), Real.cos (w*x)*triangle a x t) =
      (t^5*jet4 a t)*cosineProfile |w*t| := by
  have he : (fun x => Real.cos (w*x)*triangle a x t) = (Iio t).indicator
      (fun x => (Real.cos (w*x)*compactPoly t x)*jet4 a t) := by
    funext x; by_cases hx : x < t <;> simp [triangle, Set.indicator, hx, compactP, compactPoly, mul_assoc]
  rw [he, integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
  have hi : Iio t ∩ Ioi (0 : ℝ) = Ioo 0 t := by ext x; exact and_comm
  rw [hi, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht.le,
    intervalIntegral.integral_mul_const, compact_cosine_integral t w ht]
  ring

set_option maxHeartbeats 2400000 in
theorem spectral_small {a : ℝ} (ha : 0 < a) (hab : a ≤ 5/4) :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧
      ∀ w : ℝ, (∫ x : ℝ, Real.cos (w*x)*jet0 a |x|) = ∫ t, cosineProfile |w*t| ∂μ := by
  let ν : Measure ℝ := volume.restrict (Ioi 0)
  let ρ (t : ℝ) := t^5*jet4 a t
  have hp : ∀ᵐ t ∂ν, 0 < t := ae_restrict_mem measurableSet_Ioi
  have hρpos : 0 ≤ᵐ[ν] ρ := hp.mono (fun t ht => mul_nonneg (pow_nonneg ht.le _) (jet4_nonneg ha hab ht))
  have hρmeas : Measurable ρ := by unfold ρ jet4 poly4; fun_prop
  have hij := triangle_swap ha hab
  have hρint : Integrable ρ ν := by
    apply (hij.integral_prod_right.const_mul 30).congr
    filter_upwards [hp] with t ht
    have he := triangle_cosine a 0 t ht
    simp only [zero_mul, Real.cos_zero, one_mul, abs_zero, cosineProfile, if_true] at he
    dsimp only [ρ]; rw [he]; ring
  refine ⟨ν.withDensity (fun t => ENNReal.ofReal (ρ t)), ⟨?_⟩, ?_⟩
  · rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact (lintegral_ofReal_le_lintegral_enorm _).trans_lt hρint.2
  intro w
  have he : (∫ x : ℝ, Real.cos (w*x)*jet0 a |x|) =
      2 * ∫ x in Ioi (0 : ℝ), Real.cos (w*x)*jet0 a x := by
    rw [← integral_comp_abs]
    apply integral_congr_ae
    filter_upwards with x
    rcases le_total 0 x with hx|hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, mul_neg, Real.cos_neg]
  have hs : Integrable (Function.uncurry (fun x t : ℝ => Real.cos (w*x)*triangle a x t)) (ν.prod ν) := by
    apply hij.bdd_mul (c := 1)
    · exact (by fun_prop : Measurable (fun p : ℝ × ℝ => Real.cos (w*p.1))).aestronglyMeasurable
    · exact .of_forall (fun p => by simpa using Real.abs_cos_le_one (w*p.1))
  rw [he, ← integral_const_mul, integral_withDensity_eq_integral_toReal_smul hρmeas.ennreal_ofReal
      (.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  calc
    _ = ∫ x, ∫ t, Real.cos (w*x)*triangle a x t ∂ν ∂ν := by
      apply integral_congr_ae
      filter_upwards [hp] with x hx
      rw [integral_const_mul, (triangle_integral ha hab hx).2]
      ring
    _ = _ := by
      rw [integral_integral_swap hs]
      apply integral_congr_ae
      filter_upwards [hp, hρpos] with t ht ht'
      rw [triangle_cosine a w t ht, ENNReal.toReal_ofReal ht', smul_eq_mul]

end Mo360993Small

theorem Mo360993Full.small : OMA.R_mo_360993_R1.H1 := by
  intro a ha hab
  obtain ⟨μ, hμ, h⟩ := Mo360993Small.spectral_small ha hab
  refine ⟨μ, hμ, ?_⟩
  intro w
  specialize h (-2*Real.pi*w)
  convert! h using 1
  · apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    have he : -2*Real.pi*x*w = -2*Real.pi*w*x := by ring
    rw [he]
    simp [Mo360993Small.jet0, Mo360993Small.poly0]
  · apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    have he : -2*Real.pi*w*t = -(2*Real.pi*w*t) := by ring
    simp [Mo360993Small.cosineProfile, he]
end

section
section
/-
The Bernstein-Widder representation below is adapted from work of the Tau Ceti contributors,
Copyright (c) 2026. Source revision afb1aacb3632d3236eee756ea1683290c07270a3:
https://github.com/TauCetiProject/TauCeti/tree/afb1aacb3632d3236eee756ea1683290c07270a3
This version collects the required results in one compilation unit and ports them to the
project's pinned Mathlib. The copula comparison follows those results. The license for the
Tau Ceti portions follows.
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "{}"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright {yyyy} {name of copyright owner}

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/

/- TauCeti.Analysis.Calculus.IteratedDerivWithin -/
noncomputable section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/



/-!
# Generic lemmas for iterated derivatives within sets

This file records calculus lemmas about `iteratedDerivWithin` that are independent of any
completely-monotone or Bernstein-function structure.

## Main declarations

* `TauCeti.ContDiffOn.hasDerivAt_iteratedDerivWithin`: differentiability of an
  `iteratedDerivWithin` on a neighbourhood inside a unique-differentiability set.
For the plain fundamental-theorem identity on a compact interval use Mathlib's
`intervalIntegral.integral_derivWithin_Icc_of_contDiffOn_Icc` together with
`iteratedDerivWithin_one`.
-/


open Set Filter
open scoped ContDiff Topology

namespace TauCeti

/-- At a point `x` in the interior of a unique-differentiability set `s` (`s ∈ 𝓝 x`),
the derivative of the `k`-th iterated derivative-within-`s` of a `C^(k+1)` function is the
`(k+1)`-th iterated derivative-within-`s`. -/
theorem ContDiffOn.hasDerivAt_iteratedDerivWithin
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {g : 𝕜 → E} {s : Set 𝕜} {k : ℕ} (hf : ContDiffOn 𝕜 ((k + 1 : ℕ) : WithTop ℕ∞) g s)
    (hs : UniqueDiffOn 𝕜 s) {x : 𝕜} (hx : s ∈ nhds x) :
    HasDerivAt (iteratedDerivWithin k g s) (iteratedDerivWithin (k + 1) g s x) x := by
  rw [iteratedDerivWithin_succ, derivWithin_of_mem_nhds hx]
  exact (hf.differentiableOn_iteratedDerivWithin
    (by exact_mod_cast Nat.lt_succ_self k) hs).hasDerivAt hx

end TauCeti
end

/- TauCeti.Analysis.CompletelyMonotone.Basic -/
noncomputable section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/







/-!
# Completely monotone functions

A function `f : ℝ → ℝ` is *completely monotone* if it is smooth on the closed half-line
`[0, ∞)` and its iterated derivatives there alternate in sign:
`(-1)ⁿ f⁽ⁿ⁾(t) ≥ 0` for every `n` and every `t ≥ 0`. Equivalently `f` is nonnegative,
nonincreasing, convex, and so on through every order. Bernstein's theorem identifies the
completely monotone functions on the *open* half-line `(0, ∞)` with the Laplace transforms of
positive measures on `[0, ∞)`. Demanding smoothness up to the boundary point `0`, as we do
here, is a genuine strengthening: it carves out the subclass whose representing measure has
every moment finite. (It thereby excludes some Laplace transforms of finite measures, such as
`t ↦ ∫₀^∞ e^{-x t} (1 + x)⁻² dx`, which is finite at `0` yet has `f'(0⁺) = -∞`.) The
prototypes `t ↦ e^{-x t}` (`x ≥ 0`) are the extreme rays out of which Bernstein's theorem
builds the general member.

The smoothness clause is essential and is not folded into the sign condition: an iterated
derivative defaults to a junk value where the function fails to be differentiable, so
without it a badly behaved `f` could satisfy `0 ≤ 0` vacuously. We phrase the sign condition
through `iteratedDerivWithin _ (Set.Ici 0)`, the derivative *within* the closed half-line,
which is the object that pairs cleanly with `ContDiffOn` (in particular at the boundary
point `0`); on the open half-line it agrees with the ordinary iterated derivative.

## Main declarations

* `TauCeti.IsCompletelyMonotone`: the predicate that `f` is smooth and sign-alternating on
  `[0, ∞)`.
* `TauCeti.IsCompletelyMonotone.congr`: complete monotonicity only depends on the values of the
  function on `[0, ∞)`.
* `TauCeti.IsCompletelyMonotone.nonneg`, `TauCeti.IsCompletelyMonotone.derivWithin_nonpos`,
  `TauCeti.IsCompletelyMonotone.antitoneOn`: a completely monotone function is nonnegative
  and nonincreasing on `[0, ∞)`.
* `TauCeti.IsCompletelyMonotoneOnIci.exists_nonneg_tendsto_atTop`,
  `TauCeti.IsCompletelyMonotoneOnIci.le_of_tendsto_atTop`: order-limit consequences of
  nonnegativity and monotonicity on `[0, ∞)`.
* `TauCeti.IsCompletelyMonotone.neg_one_pow_mul_iteratedDeriv_nonneg`: on the open half-line,
  the sign condition also holds for ordinary iterated derivatives.
* `TauCeti.IsCompletelyMonotone.add`, `TauCeti.IsCompletelyMonotone.sum`,
  `TauCeti.IsCompletelyMonotone.smul`: closure under addition, finite sums, and nonnegative
  scalar multiples.
* `TauCeti.IsCompletelyMonotoneOnIoi`: the open-half-line analogue, using ordinary iterated
  derivatives on `(0, ∞)`.
* `TauCeti.IsCompletelyMonotoneOnIci`: the closed-half-line predicate used by the
  finite-measure Hausdorff--Bernstein--Widder theorem: continuity on `[0, ∞)` plus complete
  monotonicity on `(0, ∞)`.
* `TauCeti.isCompletelyMonotone_const`: a nonnegative constant is completely monotone.
* `TauCeti.isCompletelyMonotone_exp_neg_mul`: the building block `t ↦ e^{-x t}` for `x ≥ 0`.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012).
-/


open Set Filter
open scoped ContDiff Topology

namespace TauCeti

/-- A function `f : ℝ → ℝ` is **completely monotone** if it is `C^∞` on the closed half-line
`[0, ∞)` and its iterated derivatives within `[0, ∞)` alternate in sign:
`0 ≤ (-1)ⁿ f⁽ⁿ⁾(t)` for every `n` and every `t ≥ 0`. The smoothness clause prevents the sign
condition from being satisfied vacuously by a junk iterated derivative. -/
def IsCompletelyMonotone (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ f (Ici 0) ∧
    ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → 0 ≤ (-1) ^ n * iteratedDerivWithin n f (Ici 0) t

/-- `IsCompletelyMonotone f` unfolds to its defining conjunction: `f` is `C^∞` on `[0, ∞)`
and its iterated derivatives within `[0, ∞)` alternate in sign. -/
lemma isCompletelyMonotone_iff {f : ℝ → ℝ} :
    IsCompletelyMonotone f ↔
      ContDiffOn ℝ ∞ f (Ici 0) ∧
        ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → 0 ≤ (-1) ^ n * iteratedDerivWithin n f (Ici 0) t :=
  Iff.rfl

/-- Completely monotone functions are exactly absolutely monotone functions after reflecting the
closed half-line through zero. -/
lemma isCompletelyMonotone_iff_absolutelyMonotoneOn_comp_neg {f : ℝ → ℝ} :
    IsCompletelyMonotone f ↔ AbsolutelyMonotoneOn (fun u => f (-u)) (Iic 0) := by
  rw [isCompletelyMonotone_iff,
    AbsolutelyMonotoneOn.iff_iteratedDerivWithin_nonneg (uniqueDiffOn_Iic 0)]
  constructor
  -- Reflect smoothness and the alternating-sign condition from `[0, ∞)` to `(-∞, 0]`.
  · rintro ⟨hcont, hsign⟩
    refine ⟨?_, fun n u hu => ?_⟩
    · have hpre : ((-ContinuousLinearMap.id ℝ ℝ) ⁻¹' Ici 0) = Iic 0 := by
        ext x
        simp
      rw [← hpre]
      simpa [Function.comp_def] using
        hcont.comp_continuousLinearMap (-ContinuousLinearMap.id ℝ ℝ)
    · rw [iteratedDerivWithin_comp_neg (n := n) (f := f) (s := Iic 0) u]
      have hset : (-Iic (0 : ℝ) : Set ℝ) = Ici 0 := by
        ext x
        simp
      rw [hset]
      simpa [smul_eq_mul] using hsign n (-u) (neg_nonneg.mpr hu)
  -- Reflect the absolutely-monotone data back to the original closed half-line.
  · rintro ⟨hcont, hsign⟩
    refine ⟨?_, fun n t ht => ?_⟩
    · have hpre : ((-ContinuousLinearMap.id ℝ ℝ) ⁻¹' Iic 0) = Ici 0 := by
        ext x
        simp
      rw [← hpre]
      simpa [Function.comp_def] using
        hcont.comp_continuousLinearMap (-ContinuousLinearMap.id ℝ ℝ)
    · have hsign' := hsign n (-t) (mem_Iic.mpr (neg_nonpos.mpr ht))
      rw [iteratedDerivWithin_comp_neg (n := n) (f := f) (s := Iic 0) (-t)] at hsign'
      have hset : (-Iic (0 : ℝ) : Set ℝ) = Ici 0 := by
        ext x
        simp
      rw [hset] at hsign'
      simpa [smul_eq_mul] using hsign'

namespace IsCompletelyMonotone

variable {f g : ℝ → ℝ}

/-- A completely monotone function is `C^∞` on `[0, ∞)`. -/
lemma contDiffOn (hf : IsCompletelyMonotone f) : ContDiffOn ℝ ∞ f (Ici 0) := hf.1

/-- The sign-alternation property of the iterated derivatives of a completely monotone
function: `0 ≤ (-1)ⁿ f⁽ⁿ⁾(t)` for every `n` and every `t ≥ 0`. -/
lemma neg_one_pow_mul_iteratedDerivWithin_nonneg (hf : IsCompletelyMonotone f) (n : ℕ) {t : ℝ}
    (ht : 0 ≤ t) : 0 ≤ (-1) ^ n * iteratedDerivWithin n f (Ici 0) t := hf.2 n t ht

/-- On the open half-line, the completely monotone sign condition can be read using ordinary
iterated derivatives instead of derivatives within `[0, ∞)`. -/
lemma neg_one_pow_mul_iteratedDeriv_nonneg (hf : IsCompletelyMonotone f) (n : ℕ) {t : ℝ}
    (ht : 0 < t) : 0 ≤ (-1) ^ n * iteratedDeriv n f t := by
  have hnhds : Ici (0 : ℝ) ∈ 𝓝 t :=
    mem_of_superset (isOpen_Ioi.mem_nhds ht) Ioi_subset_Ici_self
  have hcont : ContDiffAt ℝ (n : WithTop ℕ∞) f t :=
    (hf.contDiffOn.contDiffAt hnhds).of_le (by exact_mod_cast le_top)
  rw [← iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hcont
    (mem_Ici.mpr ht.le)]
  exact hf.neg_one_pow_mul_iteratedDerivWithin_nonneg n ht.le

/-- A completely monotone function is nonnegative on `[0, ∞)`. -/
lemma nonneg (hf : IsCompletelyMonotone f) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ f t := by
  simpa [iteratedDerivWithin_zero] using hf.neg_one_pow_mul_iteratedDerivWithin_nonneg 0 ht

/-- The derivative within `[0, ∞)` of a completely monotone function is nonpositive: it is
nonincreasing. -/
lemma derivWithin_nonpos (hf : IsCompletelyMonotone f) {t : ℝ} (ht : 0 ≤ t) :
    derivWithin f (Ici 0) t ≤ 0 := by
  have h := hf.neg_one_pow_mul_iteratedDerivWithin_nonneg 1 ht
  rw [pow_one, iteratedDerivWithin_one] at h
  linarith

/-- Complete monotonicity is determined by the values of the function on `[0, ∞)`: if `g` agrees
with a completely monotone `f` throughout `[0, ∞)`, then `g` is completely monotone too. Both the
smoothness clause and the sign condition only see the function within `[0, ∞)`. -/
lemma congr (hf : IsCompletelyMonotone f) (h : Set.EqOn g f (Ici 0)) :
    IsCompletelyMonotone g := by
  refine ⟨hf.contDiffOn.congr fun x hx => h hx, fun n t ht => ?_⟩
  rw [iteratedDerivWithin_congr h (mem_Ici.mpr ht)]
  exact hf.neg_one_pow_mul_iteratedDerivWithin_nonneg n ht


end IsCompletelyMonotone

namespace IsCompletelyMonotone

variable {f g : ℝ → ℝ}

/-- For a completely monotone `f`, the `k`-th iterated derivative within `[0, ∞)` is
differentiable at any `t > 0`, with derivative the `(k+1)`-th iterated derivative. -/
lemma hasDerivAt_iteratedDerivWithin_succ
    (hcm : IsCompletelyMonotone f) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (iteratedDerivWithin k f (Ici 0))
      (iteratedDerivWithin (k + 1) f (Ici 0) t) t := by
  have horder : ((k + 1 : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  exact ContDiffOn.hasDerivAt_iteratedDerivWithin (k := k)
    (hcm.contDiffOn.of_le horder) (uniqueDiffOn_Ici 0) (Ici_mem_nhds ht)

/-- Completely monotone functions are closed under addition. -/
lemma add (hf : IsCompletelyMonotone f) (hg : IsCompletelyMonotone g) :
    IsCompletelyMonotone (f + g) := by
  rw [isCompletelyMonotone_iff_absolutelyMonotoneOn_comp_neg]
  convert (isCompletelyMonotone_iff_absolutelyMonotoneOn_comp_neg.mp hf).add
    (isCompletelyMonotone_iff_absolutelyMonotoneOn_comp_neg.mp hg) using 1
  ext u
  simp [Pi.add_apply]

end IsCompletelyMonotone

/-- A nonnegative constant function is completely monotone. -/
lemma isCompletelyMonotone_const {c : ℝ} (hc : 0 ≤ c) :
    IsCompletelyMonotone (fun _ : ℝ => c) := by
  refine ⟨contDiffOn_const, fun n t _ => ?_⟩
  rcases n with _ | n
  · simpa [iteratedDerivWithin_const] using hc
  · simp [iteratedDerivWithin_const]

/-- Complete monotonicity on the open half-line `(0, ∞)`: the function is `C^∞` there and its
ordinary iterated derivatives alternate in sign. This is the version used for derivatives of
Bernstein functions, whose right derivatives need not be finite at `0`. -/
def IsCompletelyMonotoneOnIoi (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ f (Ioi 0) ∧
    ∀ n : ℕ, ∀ t : ℝ, 0 < t → 0 ≤ (-1) ^ n * iteratedDeriv n f t

namespace IsCompletelyMonotoneOnIoi

variable {f g : ℝ → ℝ}

/-- A completely monotone function on `(0, ∞)` is smooth there. -/
lemma contDiffOn (hf : IsCompletelyMonotoneOnIoi f) : ContDiffOn ℝ ∞ f (Ioi 0) := hf.1

/-- The sign-alternation property on `(0, ∞)`. -/
lemma neg_one_pow_mul_iteratedDeriv_nonneg (hf : IsCompletelyMonotoneOnIoi f) (n : ℕ) {t : ℝ}
    (ht : 0 < t) : 0 ≤ (-1) ^ n * iteratedDeriv n f t := hf.2 n t ht

/-- A completely monotone function on `(0, ∞)` is nonnegative there. -/
lemma nonneg (hf : IsCompletelyMonotoneOnIoi f) {t : ℝ} (ht : 0 < t) : 0 ≤ f t := by
  simpa [iteratedDeriv_zero] using hf.neg_one_pow_mul_iteratedDeriv_nonneg 0 ht

/-- A function completely monotone on `(0, ∞)` that is continuous within `[0, ∞)` at the origin
is nonnegative on all of `[0, ∞)`: nonnegativity on `(0, ∞)` passes to the boundary point `0` in
the limit. -/
lemma nonneg_of_continuousWithinAt (hf : IsCompletelyMonotoneOnIoi f)
    (hcont : ContinuousWithinAt f (Ici 0) 0) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ f t := by
  rcases ht.lt_or_eq with h | h
  · exact hf.nonneg h
  · subst h
    have htends : Filter.Tendsto f (𝓝[>] (0 : ℝ)) (nhds (f 0)) :=
      hcont.tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    exact ge_of_tendsto htends (eventually_mem_nhdsWithin.mono fun x hx => hf.nonneg hx)

/-- The derivative of a completely monotone function on `(0, ∞)` is nonpositive there. -/
lemma deriv_nonpos (hf : IsCompletelyMonotoneOnIoi f) {t : ℝ} (ht : 0 < t) :
    deriv f t ≤ 0 := by
  have h := hf.neg_one_pow_mul_iteratedDeriv_nonneg 1 ht
  rw [pow_one, iteratedDeriv_one] at h
  linarith

/-- Complete monotonicity on `(0, ∞)` is preserved by pointwise equality there. -/
lemma congr (hf : IsCompletelyMonotoneOnIoi f) (h : Set.EqOn g f (Ioi 0)) :
    IsCompletelyMonotoneOnIoi g := by
  refine ⟨hf.contDiffOn.congr fun x hx => h hx, fun n t ht => ?_⟩
  rw [Filter.EventuallyEq.iteratedDeriv_eq n (h.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds ht))]
  exact hf.neg_one_pow_mul_iteratedDeriv_nonneg n ht

/-- Complete monotonicity on `(0, ∞)` is closed under addition. -/
lemma add (hf : IsCompletelyMonotoneOnIoi f) (hg : IsCompletelyMonotoneOnIoi g) :
    IsCompletelyMonotoneOnIoi (f + g) := by
  refine ⟨hf.contDiffOn.add hg.contDiffOn, fun n t ht => ?_⟩
  rw [iteratedDeriv_add
    ((hf.contDiffOn.contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le (by exact_mod_cast le_top))
    ((hg.contDiffOn.contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le (by exact_mod_cast le_top))]
  simpa [mul_add] using add_nonneg (hf.neg_one_pow_mul_iteratedDeriv_nonneg n ht)
    (hg.neg_one_pow_mul_iteratedDeriv_nonneg n ht)

/-- The closed-half-line Tau Ceti predicate restricts to complete monotonicity on `(0, ∞)`. -/
lemma _root_.TauCeti.IsCompletelyMonotone.isCompletelyMonotoneOnIoi
    (hf : IsCompletelyMonotone f) : IsCompletelyMonotoneOnIoi f :=
  ⟨hf.contDiffOn.mono Ioi_subset_Ici_self,
    fun n _ ht => hf.neg_one_pow_mul_iteratedDeriv_nonneg n ht⟩

/-- Positive right-translates of a function completely monotone on `(0, ∞)` satisfy the
strong closed-half-line predicate: the shift moves the boundary into the open half-line, where
all derivatives exist. Compare `IsCompletelyMonotone.comp_add_const`, which keeps the strong
predicate under nonnegative translates. -/
lemma isCompletelyMonotone_comp_add_const (hf : IsCompletelyMonotoneOnIoi f) {a : ℝ}
    (ha : 0 < a) :
    IsCompletelyMonotone (fun t : ℝ => f (t + a)) := by
  refine ⟨?_, fun n t ht => ?_⟩
  · have hmaps : MapsTo (fun t : ℝ => t + a) (Ici 0) (Ioi 0) := fun t ht =>
      mem_Ioi.mpr (by linarith [mem_Ici.mp ht])
    exact hf.contDiffOn.comp (by fun_prop) hmaps
  · have htpa : 0 < t + a := by linarith
    have hcont : ContDiffAt ℝ (n : WithTop ℕ∞) (fun t : ℝ => f (t + a)) t := by
      have hc : ContDiffAt ℝ (n : WithTop ℕ∞) f (t + a) :=
        (hf.contDiffOn.contDiffAt
          (isOpen_Ioi.mem_nhds htpa)).of_le (by exact_mod_cast le_top)
      simpa [Function.comp_def] using hc.comp t
        (by fun_prop : ContDiffAt ℝ (n : WithTop ℕ∞) (fun t : ℝ => t + a) t)
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hcont (mem_Ici.mpr ht),
      iteratedDeriv_comp_add_const]
    exact hf.neg_one_pow_mul_iteratedDeriv_nonneg n htpa

end IsCompletelyMonotoneOnIoi

/-! ## Closed-half-line complete monotonicity -/

/-- Roadmap-level complete monotonicity on the closed half-line.

This is the classical finite-measure hypothesis: the function is continuous on `[0, ∞)` and
completely monotone on the open half-line `(0, ∞)`. It is weaker at the endpoint than the existing
`IsCompletelyMonotone`, which requires all derivatives within `[0, ∞)` to exist at `0`. -/
def IsCompletelyMonotoneOnIci (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Ici 0) ∧ IsCompletelyMonotoneOnIoi f

namespace IsCompletelyMonotoneOnIci

variable {f g : ℝ → ℝ}

/-- A closed-half-line completely monotone function is continuous on `[0, ∞)`. -/
lemma continuousOn (hf : IsCompletelyMonotoneOnIci f) : ContinuousOn f (Ici 0) := hf.1

/-- A closed-half-line completely monotone function is completely monotone on `(0, ∞)`. -/
lemma isCompletelyMonotoneOnIoi (hf : IsCompletelyMonotoneOnIci f) :
    IsCompletelyMonotoneOnIoi f := hf.2

/-- The existing strong Tau Ceti predicate implies the roadmap-level closed-half-line predicate. -/
lemma of_isCompletelyMonotone (hf : IsCompletelyMonotone f) :
    IsCompletelyMonotoneOnIci f :=
  ⟨hf.contDiffOn.continuousOn, hf.isCompletelyMonotoneOnIoi⟩

/-- Closed-half-line complete monotonicity is closed under addition. -/
lemma add (hf : IsCompletelyMonotoneOnIci f) (hg : IsCompletelyMonotoneOnIci g) :
    IsCompletelyMonotoneOnIci (f + g) :=
  ⟨hf.continuousOn.add hg.continuousOn,
    hf.isCompletelyMonotoneOnIoi.add hg.isCompletelyMonotoneOnIoi⟩



/-- A closed-half-line completely monotone function is nonincreasing on `[0, ∞)`: the
derivative is nonpositive on the interior and continuity extends the monotonicity to the
endpoint. -/
lemma antitoneOn (hf : IsCompletelyMonotoneOnIci f) : AntitoneOn f (Ici 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0) hf.continuousOn
    (by
      simpa [interior_Ici] using
        hf.isCompletelyMonotoneOnIoi.contDiffOn.differentiableOn (by simp))
    fun x hx => ?_
  rw [interior_Ici] at hx
  exact hf.isCompletelyMonotoneOnIoi.deriv_nonpos hx

/-- A closed-half-line completely monotone function is nonnegative on `[0, ∞)`:
nonnegativity on the open half-line passes to `0` by continuity. -/
lemma nonneg (hf : IsCompletelyMonotoneOnIci f) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ f t :=
  hf.isCompletelyMonotoneOnIoi.nonneg_of_continuousWithinAt
    (hf.continuousOn.continuousWithinAt (by simp)) ht

/-- A closed-half-line completely monotone function is nonnegative at `0`. -/
lemma nonneg_zero (hf : IsCompletelyMonotoneOnIci f) : 0 ≤ f 0 :=
  hf.nonneg le_rfl

/-- A closed-half-line completely monotone function lies below its value at `0` on `[0, ∞)`. -/
lemma le_apply_zero (hf : IsCompletelyMonotoneOnIci f) {t : ℝ} (ht : 0 ≤ t) : f t ≤ f 0 :=
  hf.antitoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht


/-- Closed-half-line complete monotonicity is determined by values on `[0, ∞)`. -/
lemma congr (hf : IsCompletelyMonotoneOnIci f) (h : EqOn g f (Ici 0)) :
    IsCompletelyMonotoneOnIci g := by
  refine ⟨hf.continuousOn.congr fun x hx => h hx, ?_⟩
  exact hf.isCompletelyMonotoneOnIoi.congr fun x hx => h (Ioi_subset_Ici_self hx)

end IsCompletelyMonotoneOnIci

/-- The `max`-truncation of a function antitone on a closed half-line is antitone everywhere:
the shared totalization step of the half-line limit lemmas below. -/
private lemma antitone_comp_max {f : ℝ → ℝ} {a : ℝ} (hf : AntitoneOn f (Ici a)) :
    Antitone fun t : ℝ => f (max t a) := fun _ _ hab =>
  hf (mem_Ici.mpr (le_max_right _ _)) (mem_Ici.mpr (le_max_right _ _)) (max_le_max_right a hab)

/-- A function antitone and bounded below on a closed half-line converges at infinity. -/
private lemma exists_tendsto_atTop_of_antitoneOn_Ici {f : ℝ → ℝ} {a : ℝ} (hf : AntitoneOn f (Ici a))
    (hbdd : BddBelow (f '' Ici a)) :
    ∃ L, Tendsto f atTop (𝓝 L) := by
  set g := fun t : ℝ => f (max t a) with hg
  have hg_anti : Antitone g := antitone_comp_max hf
  have hg_bdd : BddBelow (Set.range g) := by
    obtain ⟨b, hb⟩ := hbdd
    exact ⟨b, by rintro y ⟨t, rfl⟩; exact hb ⟨max t a, mem_Ici.mpr (le_max_right _ _), rfl⟩⟩
  refine ⟨⨅ i, g i, ?_⟩
  exact (tendsto_atTop_ciInf hg_anti hg_bdd).congr'
    (eventually_atTop.mpr ⟨a, fun t ht => by simp [hg, max_eq_left ht]⟩)

/-- A function antitone on a closed half-line lies above its limit at infinity there. -/
private lemma le_of_tendsto_atTop_of_antitoneOn_Ici {f : ℝ → ℝ} {a : ℝ} (hf : AntitoneOn f (Ici a))
    {L : ℝ} (hL : Tendsto f atTop (𝓝 L)) {T : ℝ} (hT : a ≤ T) : L ≤ f T := by
  set g₀ := fun t : ℝ => f (max t a) with hg₀
  have hg_anti : Antitone g₀ := antitone_comp_max hf
  have := hg_anti.le_of_tendsto
    (hL.congr' (eventually_atTop.mpr ⟨a, fun t ht => by simp [hg₀, max_eq_left ht]⟩)) T
  simpa [hg₀, max_eq_left hT] using this

namespace IsCompletelyMonotoneOnIci

variable {f : ℝ → ℝ}

/-- A closed-half-line completely monotone function has a limit `L ≥ 0` at infinity: it is
antitone on `[0, ∞)` and bounded below by `0`. -/
lemma exists_nonneg_tendsto_atTop (hf : IsCompletelyMonotoneOnIci f) :
    ∃ L, Tendsto f atTop (𝓝 L) ∧ 0 ≤ L := by
  obtain ⟨L, hL⟩ := exists_tendsto_atTop_of_antitoneOn_Ici hf.antitoneOn
    ⟨0, by rintro y ⟨x, hx, rfl⟩; exact hf.nonneg hx⟩
  exact ⟨L, hL, ge_of_tendsto hL (eventually_atTop.mpr ⟨0, fun t ht => hf.nonneg ht⟩)⟩

/-- A closed-half-line completely monotone function lies above its limit at infinity on
`[0, ∞)`. -/
lemma le_of_tendsto_atTop (hcm : IsCompletelyMonotoneOnIci f) {L : ℝ}
    (hL : Tendsto f atTop (𝓝 L)) {T : ℝ} (hT : 0 ≤ T) : L ≤ f T :=
  le_of_tendsto_atTop_of_antitoneOn_Ici hcm.antitoneOn hL hT

end IsCompletelyMonotoneOnIci

namespace IsCompletelyMonotone

variable {f : ℝ → ℝ}

/-- A completely monotone function is nonincreasing on `[0, ∞)`: the strong predicate
implies the closed-half-line one, whose monotonicity applies. -/
lemma antitoneOn (hf : IsCompletelyMonotone f) : AntitoneOn f (Ici 0) :=
  (IsCompletelyMonotoneOnIci.of_isCompletelyMonotone hf).antitoneOn

end IsCompletelyMonotone

end TauCeti
end

/- TauCeti.Analysis.CompletelyMonotone.Laplace.Kernel -/
noncomputable section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/



/-!
# The Laplace kernel on `ℝ≥0`

The exponential kernel `p ↦ e^{-xp}` of the Laplace transform on `ℝ≥0`, as a plain function
and as a bundled bounded continuous function, together with its basic bounds and its
integrability against finite measures. This lightweight module is shared by the Chafaï
approximating-measure machinery and the Laplace-representation theory, which otherwise do not
depend on each other.

## Main declarations

* `TauCeti.laplaceKernelBoundedContinuous`: the kernel as a bounded continuous function.
* `TauCeti.integrable_exp_neg_mul`: the kernel is integrable against any finite measure.
-/


open MeasureTheory
open scoped BoundedContinuousFunction NNReal

namespace TauCeti

/-- The Laplace kernel `p ↦ e^{-tp}` is continuous in the coordinate variable. -/
lemma continuous_exp_neg_mul (t : ℝ) :
    Continuous fun x : ℝ≥0 => Real.exp (-(t * (x : ℝ))) := by
  fun_prop

/-- For `0 ≤ x` the Laplace kernel is bounded by `1` on `ℝ≥0`. -/
lemma exp_neg_mul_le_one {x : ℝ} (hx : 0 ≤ x) (p : ℝ≥0) :
    Real.exp (-(x * (p : ℝ))) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  exact neg_nonpos.mpr (mul_nonneg hx p.coe_nonneg)

/-- The Laplace kernel as a bundled bounded continuous test function of the nonnegative
variable `p`, for fixed nonnegative `x`. -/
noncomputable def laplaceKernelBoundedContinuous {x : ℝ} (hx : 0 ≤ x) : ℝ≥0 →ᵇ ℝ where
  toFun := fun p => Real.exp (-(x * (p : ℝ)))
  continuous_toFun := continuous_exp_neg_mul x
  map_bounded' :=
    ⟨1, fun p q => by
      rw [Real.dist_eq]
      have hp0 : 0 < Real.exp (-(x * (p : ℝ))) := Real.exp_pos _
      have hp1 := exp_neg_mul_le_one hx p
      have hq0 : 0 < Real.exp (-(x * (q : ℝ))) := Real.exp_pos _
      have hq1 := exp_neg_mul_le_one hx q
      exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩⟩

/-- The bundled Laplace kernel evaluates to the usual exponential kernel on `ℝ≥0`. -/
@[simp]
lemma laplaceKernelBoundedContinuous_apply {x : ℝ} (hx : 0 ≤ x) (p : ℝ≥0) :
    laplaceKernelBoundedContinuous hx p = Real.exp (-(x * (p : ℝ))) := by
  rw [laplaceKernelBoundedContinuous]; rfl

/-- **The Laplace kernel is integrable against a finite measure.** For `0 ≤ x` the kernel
`p ↦ e^{-xp}` is bounded and continuous on `ℝ≥0`, hence integrable against any finite measure. -/
lemma integrable_exp_neg_mul (μ : Measure ℝ≥0) [IsFiniteMeasure μ] {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun p : ℝ≥0 => Real.exp (-(x * (p : ℝ)))) μ := by
  have h := (laplaceKernelBoundedContinuous hx).integrable μ
  rwa [funext (laplaceKernelBoundedContinuous_apply hx)] at h

end TauCeti
end

/- TauCeti.Probability.Moments.Determinacy -/
noncomputable section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/





/-!
# Moment determinacy of finite measures with finite exponential moments

A finite measure on `ℝ` whose exponential moments are finite in a neighbourhood of the origin is
determined by its sequence of polynomial moments `∫ xⁿ dμ`.  This is the analytic engine behind the
completeness step (**B1**) of the `OrthogonalL2Bases` roadmap
(`TauCetiRoadmap/OrthogonalL2Bases/README.md`, *Part B1 — Completeness toolkit (moment
determinacy)*): the roadmap's `ae_eq_zero_of_forall_moment_eq_zero`-style lemmas rest on the fact
that "vanishing moments" pins a distribution down, which for finite measures is exactly the
determinacy result proved here.

The mechanism is the one the roadmap describes — the (complex) moment-generating function is
analytic on a strip around the imaginary axis, and its Taylor coefficients at `0` are the moments,
so matching moments force the two functions to agree, hence the characteristic functions agree and
the measures coincide.  The proof stays inside Mathlib's `ProbabilityTheory.complexMGF` /
`MeasureTheory.charFun` API:

* `ProbabilityTheory.analyticAt_complexMGF` and `analyticOnNhd_complexMGF` supply the analyticity
  on the strip `{z | z.re ∈ interior (integrableExpSet id μ)}`;
* `ProbabilityTheory.iteratedDeriv_complexMGF` identifies the `n`-th derivative at `0` with the
  `n`-th complex moment;
* the identity principle (`analyticOrderAt_eq_top`,
  `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`) propagates equality from `0` to the whole
  strip, in particular to the imaginary axis;
* `ProbabilityTheory.complexMGF_id_mul_I` turns the imaginary-axis values into `charFun`, and
  `MeasureTheory.Measure.ext_of_charFun` concludes.

The strip-propagation core of `charFun_eq_of_forall_integral_pow_eq` adapts Mathlib's
`ProbabilityTheory.eqOn_complexMGF_of_mgf'` (`Mathlib/Probability/Moments/ComplexMGF.lean`): it
reuses the same analyticity strip and the same
`convex_integrableExpSet.interior.…linear_preimage Complex.reLm |>.isPreconnected`
identity-principle idiom.  That file's `## TODO` note ("once we know that equal `mgf` implies equal
distributions …")
records the determinacy fact as an open gap in Mathlib; the results here complete it for finite
measures via the polynomial-moment route.

## Main declarations

* `TauCeti.charFun_eq_of_forall_integral_pow_eq`: matching moments (and finite exponential moments
  near `0`) give equal characteristic functions.
* `TauCeti.Measure.ext_of_forall_integral_pow_eq`: matching moments determine a finite measure on
  `ℝ`.
* `TauCeti.Measure.ext_of_forall_integral_pow_eq_of_exists_integrable_exp`: the same conclusion from
  the roadmap's exponential-moment hypothesis `∃ a > 0, Integrable (fun x => exp (a * |x|)) μ`,
  which already puts `0` in the interior of the integrability strip.  This is the form the
  completeness argument consumes: the hypothesis holds for Gaussian decay and automatically for
  compactly supported measures.
-/


namespace TauCeti

open MeasureTheory ProbabilityTheory Complex Filter
open scoped Topology

variable {μ ν : Measure ℝ}

end TauCeti
end

/- TauCeti.Probability.Moments.LaplaceDeterminacy -/
noncomputable section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/




/-!
# A finite measure on `ℝ≥0` is determined by its Laplace transform

## Main results

* `TauCeti.Measure.ext_of_forall_integral_exp_neg_natCast_mul_eq` — the sharp form: the transform's
  values at the natural numbers already determine the measure.
* `TauCeti.Measure.ext_of_forall_integral_exp_neg_mul_eq` — the convenience form, hypothesis at
  every nonnegative real.

## Implementation

The substitution `y = e^{-x}` converts the Laplace transform into a moment sequence: at a natural
argument `n`, `∫ e^{-n x} dμ = ∫ yⁿ d(μ.map (x ↦ e^{-x}))`. So matching Laplace transforms give
pushforwards with matching moments, and the pushforwards are moment-determinate because they are
carried by `(0, 1]` — bounded support makes the exponential-moment hypothesis of
`Measure.ext_of_forall_integral_pow_eq_of_exists_integrable_exp` automatic. Finally `x ↦ e^{-x}` is
injective and measurable between standard Borel spaces, hence a measurable embedding by
Lusin–Souslin, and `MeasurableEmbedding.map_injective` recovers `μ = ν` from the equal pushforwards.

Only the transform's values at *natural* arguments are used, which is why the primary statement
quantifies over `ℕ`; the real-argument form is a one-line corollary for callers that have it.

This is the uniqueness half of the Bernstein milestone in
`TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B. The existence half is a separate,
independent development, and the two are combined in the Hausdorff--Bernstein--Widder theorem
(`TauCeti.hausdorff_bernstein_widder_existsUnique` in
`Analysis/CompletelyMonotone/Bernstein/HausdorffBernsteinWidder.lean`).
Nothing here mentions complete monotonicity — the statement is about two arbitrary
finite measures — which is why it lives beside the other determinacy results rather than under
`Analysis/CompletelyMonotone/`.
-/



open MeasureTheory Set Filter
open scoped NNReal

namespace TauCeti

/-- The substitution `x ↦ e^{-x}`, which turns Laplace transforms into moments. -/
private def expNeg (x : ℝ≥0) : ℝ := Real.exp (-(x : ℝ))

@[simp]
private theorem expNeg_apply (x : ℝ≥0) : expNeg x = Real.exp (-(x : ℝ)) := rfl

end TauCeti
end

/- TauCeti.Analysis.CompletelyMonotone.Laplace.Representation -/
noncomputable section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/




-- Non-public: dominated convergence and the `mgf` derivative and analyticity calculus, all
-- consumed inside proofs only (the latter through the bridge `laplaceTransform_eq_mgf`).


-- Non-public: `Measure.ext_of_forall_integral_exp_neg_natCast_mul_eq` supplies the
-- Laplace-determinacy step in the uniqueness proof.


/-!
# Laplace representations for completely monotone functions

This file contains the Laplace-transform side of the finite-measure
Hausdorff--Bernstein--Widder theorem on `ℝ≥0`: helper lemmas for finite-measure Laplace
transforms and the predicate that a finite measure represents a function by its Laplace transform.

## Main declarations

* `TauCeti.laplaceTransform`: the Laplace transform of a measure on `ℝ≥0`, with its algebraic
  API and the bridge `TauCeti.laplaceTransform_eq_mgf` to Mathlib's moment-generating function.
* `TauCeti.RepresentsLaplace`: the predicate that a finite measure represents a function by its
  Laplace transform on `[0, ∞)`, with `congr`/`add`/`smul`/`unique` API.
* `TauCeti.isCompletelyMonotoneOnIci_laplaceTransform`,
  `TauCeti.isCompletelyMonotone_laplaceTransform_of_moments`: the easy direction of the
  representation theorem, in the closed-half-line and all-moments forms.
* `TauCeti.Measure.ext_of_forall_laplaceTransform_natCast_eq`: finite measures are determined
  by their Laplace transforms at the natural numbers.

## References

The finite-measure representation is the Hausdorff--Bernstein--Widder theorem, after
S. Bernstein (1928) and D. V. Widder, *The Laplace Transform*, Chapter IV; see also
R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions* (de Gruyter, 2nd ed. 2012),
Theorem 1.4. This file provides the Laplace-transform API used by the representation theorem.

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B (Bernstein theorem
  milestone).
-/


open MeasureTheory ProbabilityTheory Set Filter
open scoped BoundedContinuousFunction ContDiff ENNReal NNReal Pointwise Topology

namespace TauCeti

/-! ## Laplace transforms of finite measures on `ℝ≥0` -/

/-- The Laplace transform of a measure on `ℝ≥0`, evaluated at a real parameter `t`.

The theorem statements in this file use the transform only for `0 ≤ t`; for negative `t`, the
Bochner integral is still a total Lean term, but may be the default value when the integrand is not
integrable. -/
noncomputable def laplaceTransform (μ : Measure ℝ≥0) (t : ℝ) : ℝ :=
  ∫ x, Real.exp (-(t * (x : ℝ))) ∂μ

/-- The defining formula for `laplaceTransform`. Not `@[simp]`: simp should not unfold the
abstraction into a raw integral; the evaluation lemmas below are the simp normal forms. -/
lemma laplaceTransform_apply (μ : Measure ℝ≥0) (t : ℝ) :
    laplaceTransform μ t = ∫ x, Real.exp (-(t * (x : ℝ))) ∂μ := by
  rw [laplaceTransform]



/-- The Laplace transform is the moment-generating function of the coordinate negation
`p ↦ -p` on `ℝ≥0`. This bridge lets the transform consume Mathlib's `mgf` calculus. -/
lemma laplaceTransform_eq_mgf (μ : Measure ℝ≥0) :
    laplaceTransform μ = mgf (fun p : ℝ≥0 => -(p : ℝ)) μ := by
  ext t
  simp only [laplaceTransform, mgf, mul_neg]

/-- The value of the Laplace transform at the parameter `0` is the total mass (under the
total Bochner-integral convention both sides are `0` for an infinite measure). -/
@[simp]
lemma laplaceTransform_zero (μ : Measure ℝ≥0) :
    laplaceTransform μ 0 = μ.real univ := by
  rw [laplaceTransform_eq_mgf, mgf_zero']

/-- The Laplace transform of the zero measure vanishes identically. -/
@[simp]
lemma laplaceTransform_zero_measure (t : ℝ) :
    laplaceTransform (0 : Measure ℝ≥0) t = 0 := by
  simp [laplaceTransform_eq_mgf, mgf_zero_measure]

/-- Additivity of the Laplace transform in the measure, wherever the kernel is integrable
against both summands. -/
lemma laplaceTransform_add_measure (μ ν : Measure ℝ≥0) {t : ℝ}
    (hμ : Integrable (fun p : ℝ≥0 => Real.exp (-(t * (p : ℝ)))) μ)
    (hν : Integrable (fun p : ℝ≥0 => Real.exp (-(t * (p : ℝ)))) ν) :
    laplaceTransform (μ + ν) t = laplaceTransform μ t + laplaceTransform ν t := by
  simp only [laplaceTransform_eq_mgf]
  exact mgf_add_measure (by simpa [integrableExpSet, mul_neg] using hμ)
    (by simpa [integrableExpSet, mul_neg] using hν)

/-- The Laplace transform of the Dirac mass at `x₀` is the exponential kernel `exp (-(t · x₀))`;
the point masses are the building blocks of the representing mixtures. -/
@[simp]
lemma laplaceTransform_dirac (x₀ : ℝ≥0) (t : ℝ) :
    laplaceTransform (Measure.dirac x₀) t = Real.exp (-(t * (x₀ : ℝ))) := by
  rw [laplaceTransform_eq_mgf, mgf_dirac', mul_neg]

/-! ## Easy direction: finite measures give completely monotone Laplace transforms -/

/-! ## Representation predicate -/

/-- A finite measure represents a function by its Laplace transform on the nonnegative
half-line. -/
def RepresentsLaplace (μ : Measure ℝ≥0) (f : ℝ → ℝ) : Prop :=
  IsFiniteMeasure μ ∧ ∀ t : ℝ, 0 ≤ t → f t = laplaceTransform μ t

/-- `RepresentsLaplace μ f` unfolds to finiteness of `μ` and equality with the Laplace transform
on the nonnegative half-line. -/
lemma representsLaplace_iff {f : ℝ → ℝ} {μ : Measure ℝ≥0} :
    RepresentsLaplace μ f ↔
      IsFiniteMeasure μ ∧ ∀ t : ℝ, 0 ≤ t → f t = laplaceTransform μ t :=
  Iff.rfl

namespace RepresentsLaplace

variable {f : ℝ → ℝ} {μ : Measure ℝ≥0}

/-- A representing measure is finite. -/
lemma isFiniteMeasure (h : RepresentsLaplace μ f) : IsFiniteMeasure μ := h.1

/-- A representing measure has the advertised Laplace-transform values on `[0, ∞)`. -/
lemma eq_laplaceTransform (h : RepresentsLaplace μ f) {t : ℝ} (ht : 0 ≤ t) :
    f t = laplaceTransform μ t :=
  h.2 t ht

/-- A representation transports along agreement on the nonnegative half-line: the predicate
constrains `f` only there. -/
protected lemma congr {g : ℝ → ℝ} (hf : RepresentsLaplace μ f) (h : EqOn g f (Ici 0)) :
    RepresentsLaplace μ g :=
  ⟨hf.isFiniteMeasure, fun _ ht => (h (mem_Ici.mpr ht)).trans (hf.eq_laplaceTransform ht)⟩

/-- The sum of two representing measures represents the sum of the functions. -/
protected lemma add {f g : ℝ → ℝ} {μ ν : Measure ℝ≥0}
    (hf : RepresentsLaplace μ f) (hg : RepresentsLaplace ν g) :
    RepresentsLaplace (μ + ν) (f + g) := by
  have := hf.isFiniteMeasure
  have := hg.isFiniteMeasure
  refine ⟨inferInstance, fun t ht => ?_⟩
  rw [Pi.add_apply, hf.eq_laplaceTransform ht, hg.eq_laplaceTransform ht,
    laplaceTransform_add_measure μ ν (integrable_exp_neg_mul μ ht) (integrable_exp_neg_mul ν ht)]

end RepresentsLaplace

/-! ## Uniqueness: finite measures are determined by their Laplace transforms -/

end TauCeti
end

/- TauCeti.Analysis.CompletelyMonotone.Closure -/
noncomputable section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/




/-!
# Closure of completely monotone functions under products and differentiation

This file extends the basic API of `TauCeti.IsCompletelyMonotone` (sums and nonnegative scalar
multiples, in `TauCeti.Analysis.CompletelyMonotone.Basic`) with two further closure properties
called for by the `OneParameterSemigroups` roadmap:

* the **product** of two completely monotone functions is completely monotone, hence so is any
  finite product and any natural power;
* if `f` is completely monotone then so is `t ↦ -f'(t)`, the **negated derivative**.

Both are elementary consequences of the sign-alternation definition. For the product, the
Leibniz rule expands `(-1)ⁿ (fg)⁽ⁿ⁾` as a nonnegative combination
`∑ₖ (n choose k) · [(-1)ᵏ f⁽ᵏ⁾] · [(-1)ⁿ⁻ᵏ g⁽ⁿ⁻ᵏ⁾]` of products of the (nonnegative) alternating
derivatives of `f` and `g`. For the negated derivative, the `(n+1)`-st alternating derivative of
`f` is the `n`-th alternating derivative of `-f'`. Mathlib has the analogous closure lemmas for
`AbsolutelyMonotoneOn` only up to sums and scalar multiples (`AbsolutelyMonotoneOn.add`,
`AbsolutelyMonotoneOn.smul`), so the multiplicative and differential closure built here is new.

These workhorses combine with the prototypes `t ↦ e^{-x t}` to manufacture completely monotone
functions: e.g. any finite sum `∑ⱼ cⱼ e^{-xⱼ t}` with `cⱼ, xⱼ ≥ 0`, or a product like
`t ↦ e^{-x t} / (1 + t)`-style mixtures once their factors are known completely monotone. The
negated-derivative closure is the first step towards the completely-monotone ↔ Bernstein-function
correspondence (a Bernstein function is a nonnegative function whose derivative is completely
monotone).

## Main declarations

* `TauCeti.IsCompletelyMonotone.mul`: completely monotone functions are closed under pointwise
  multiplication.
* `TauCeti.IsCompletelyMonotone.prod`: closure under finite products.
* `TauCeti.IsCompletelyMonotone.pow`: closure under natural powers.
* `TauCeti.IsCompletelyMonotone.neg_one_pow_mul_iteratedDerivWithin`: every alternating
  iterated derivative of a completely monotone function is completely monotone.
* `TauCeti.IsCompletelyMonotone.neg_derivWithin`: the negated derivative within `[0, ∞)` of a
  completely monotone function is completely monotone.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012).
-/


open Set
open scoped ContDiff

namespace TauCeti

namespace IsCompletelyMonotone

variable {f g : ℝ → ℝ}

/-- Completely monotone functions are closed under pointwise multiplication. -/
theorem mul (hf : IsCompletelyMonotone f) (hg : IsCompletelyMonotone g) :
    IsCompletelyMonotone (f * g) := by
  refine ⟨hf.contDiffOn.mul hg.contDiffOn, fun n t ht => ?_⟩
  have hmem : t ∈ Ici (0 : ℝ) := mem_Ici.mpr ht
  have hu : UniqueDiffOn ℝ (Ici (0 : ℝ)) := uniqueDiffOn_Ici 0
  have hfn : ContDiffWithinAt ℝ n f (Ici 0) t :=
    (hf.contDiffOn.contDiffWithinAt hmem).of_le (by exact_mod_cast le_top)
  have hgn : ContDiffWithinAt ℝ n g (Ici 0) t :=
    (hg.contDiffOn.contDiffWithinAt hmem).of_le (by exact_mod_cast le_top)
  rw [iteratedDerivWithin_mul hmem hu hfn hgn, Finset.mul_sum]
  refine Finset.sum_nonneg fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have e1 := hf.neg_one_pow_mul_iteratedDerivWithin_nonneg i ht
  have e2 := hg.neg_one_pow_mul_iteratedDerivWithin_nonneg (n - i) ht
  have hsign : ((-1 : ℝ)) ^ n = (-1) ^ i * (-1) ^ (n - i) := by
    rw [← pow_add, Nat.add_sub_cancel' hin]
  have key : (-1 : ℝ) ^ n * ((n.choose i : ℝ) * iteratedDerivWithin i f (Ici 0) t
        * iteratedDerivWithin (n - i) g (Ici 0) t)
      = (n.choose i : ℝ) * ((-1) ^ i * iteratedDerivWithin i f (Ici 0) t)
        * ((-1) ^ (n - i) * iteratedDerivWithin (n - i) g (Ici 0) t) := by
    rw [hsign]; ring
  rw [key]
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) e1) e2

/-- Completely monotone functions are closed under taking natural powers. -/
theorem pow (hf : IsCompletelyMonotone f) (k : ℕ) : IsCompletelyMonotone (f ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact isCompletelyMonotone_const zero_le_one
  | succ k ih => rw [pow_succ]; exact ih.mul hf

/-- Every alternating iterated derivative of a completely monotone function is completely
monotone. -/
theorem neg_one_pow_mul_iteratedDerivWithin (hf : IsCompletelyMonotone f) (k : ℕ) :
    IsCompletelyMonotone (fun t => (-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) t) := by
  have hu : UniqueDiffOn ℝ (Ici (0 : ℝ)) := uniqueDiffOn_Ici 0
  have hcont : ContDiffOn ℝ ∞ (iteratedDerivWithin k f (Ici 0)) (Ici 0) := by
    induction k with
    | zero => simpa [iteratedDerivWithin_zero] using hf.contDiffOn
    | succ k ih =>
        simpa [iteratedDerivWithin_succ] using ih.derivWithin (m := ∞) hu (by simp)
  refine ⟨?_, fun n t ht => ?_⟩
  · simpa [smul_eq_mul] using hcont.const_smul ((-1 : ℝ) ^ k)
  have hshift :
      iteratedDerivWithin n (iteratedDerivWithin k f (Ici 0)) (Ici 0) =
        iteratedDerivWithin (n + k) f (Ici 0) := by
    induction n with
    | zero => simp [iteratedDerivWithin_zero]
    | succ n ih =>
        rw [iteratedDerivWithin_succ, ih, ← iteratedDerivWithin_succ]
        congr 1
        omega
  have hsign := hf.neg_one_pow_mul_iteratedDerivWithin_nonneg (n + k) ht
  have hiter :
      iteratedDerivWithin n
          (fun t => (-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) t) (Ici 0) t =
        (-1 : ℝ) ^ k * iteratedDerivWithin (n + k) f (Ici 0) t := by
    rw [iteratedDerivWithin_const_mul_field, hshift]
  rw [hiter]
  have key :
      (-1 : ℝ) ^ n * ((-1 : ℝ) ^ k * iteratedDerivWithin (n + k) f (Ici 0) t) =
        (-1 : ℝ) ^ (n + k) * iteratedDerivWithin (n + k) f (Ici 0) t := by
    rw [pow_add]
    ring
  rwa [key]

/-- The negated derivative within `[0, ∞)` of a completely monotone function is completely
monotone. -/
theorem neg_derivWithin (hf : IsCompletelyMonotone f) :
    IsCompletelyMonotone (fun t => -derivWithin f (Ici 0) t) := by
  simpa [pow_one, iteratedDerivWithin_one] using hf.neg_one_pow_mul_iteratedDerivWithin 1

end IsCompletelyMonotone

end TauCeti
end

/- TauCeti.Analysis.CompletelyMonotone.Integral -/
noncomputable section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/






/-!
# Integral lemmas for completely monotone functions

Taylor-remainder sign bounds and finite- and improper-integral facts about completely monotone
functions.

These extend the object API in `CompletelyMonotone/Basic.lean` with the sign of the Taylor
integral remainder, the finite-interval integral-of-`(-f')` identity, and improper-integral facts
for the first derivative within `[0, ∞)`.

## Main declarations

* `TauCeti.IsCompletelyMonotone.neg_one_pow_mul_taylor_remainder_nonneg`: the Taylor integral
  remainder has sign `(-1)ⁿ`.
* `TauCeti.IsCompletelyMonotone.continuousOn_iteratedDerivWithin_uIcc`: every iterated derivative
  within `[0, ∞)` is continuous on a compact interval `[x, T] ⊆ [0, ∞)`.
* `TauCeti.IsCompletelyMonotone.integral_neg_iteratedDerivWithin_one_Ici_eq_sub`: on a compact
  interval in `[0, ∞)`, the integral of `-f'` is the endpoint drop `f x - f T`.
* `TauCeti.IsCompletelyMonotone.neg_iteratedDerivWithin_one_integrableOn`,
  `TauCeti.IsCompletelyMonotone.integral_Ioi_neg_iteratedDerivWithin_one`: integrability and the
  improper integral of `-f'` on `(0, ∞)`, represented as `iteratedDerivWithin 1`.
* `TauCeti.IsCompletelyMonotone.integral_Ioi_neg_iteratedDerivWithin_one_of_nonneg`: the same
  improper integral from an arbitrary nonnegative endpoint, `∫ₓ^∞ (-f') = f x - L`.

## References

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B (Bernstein theorem
  milestone).

* D. V. Widder, *The Laplace Transform* (Princeton, 1941), Ch. IV.
* D. Chafaï, *Aspects of the Bernstein theorem* (2013).
-/


open MeasureTheory Set intervalIntegral Filter
open scoped ContDiff Topology

namespace TauCeti

variable {f : ℝ → ℝ}

private lemma nat_le_top (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top

/-- For a completely monotone function the `n`-th iterated derivative within a compact interval
`[x, T]` agrees with the one taken within the half-line `[0, ∞)` at any strictly positive interior
point. Complete monotonicity supplies the local `ContDiffAt` hypothesis, and both sides reduce to
the unrestricted iterated derivative at `t`. -/
private lemma IsCompletelyMonotone.iteratedDerivWithin_Icc_eq_Ici (hf : IsCompletelyMonotone f)
    {x T t : ℝ} {n : ℕ} (ht_pos : 0 < t) (ht : t ∈ Ioo x T) :
    iteratedDerivWithin n f (Icc x T) t = iteratedDerivWithin n f (Ici 0) t := by
  have hcont : ContDiffAt ℝ (n : WithTop ℕ∞) f t :=
    (hf.contDiffOn.contDiffAt (Ici_mem_nhds ht_pos)).of_le (nat_le_top _)
  have hxT : x < T := lt_trans ht.1 ht.2
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hxT) hcont
        (Ioo_subset_Icc_self ht),
      ← iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hcont
        (mem_Ici.mpr ht_pos.le)]

namespace IsCompletelyMonotone

end IsCompletelyMonotone

/-! ## Smoothness-index helpers -/

/-- The first iterated derivative within `[0, ∞)` of a completely monotone function is
nonpositive (the `derivWithin` sign condition restated for `iteratedDerivWithin 1`). -/
private lemma IsCompletelyMonotone.iteratedDerivWithin_one_nonpos
    (hf : IsCompletelyMonotone f) {t : ℝ} (ht : 0 ≤ t) :
    iteratedDerivWithin 1 f (Ici 0) t ≤ 0 := by
  rw [iteratedDerivWithin_one]; exact hf.derivWithin_nonpos ht

/-- Every iterated derivative within `[0, ∞)` of a completely monotone function is continuous on
the interval spanned by any two nonnegative endpoints. The endpoints need no ordering: `uIcc` is
the unordered interval, and `[0, ∞)` is order-connected. -/
lemma IsCompletelyMonotone.continuousOn_iteratedDerivWithin_uIcc (hcm : IsCompletelyMonotone f)
    (m : ℕ) {x T : ℝ} (hx : 0 ≤ x) (hT : 0 ≤ T) :
    ContinuousOn (iteratedDerivWithin m f (Ici 0)) (uIcc x T) :=
  (hcm.contDiffOn.continuousOn_iteratedDerivWithin (nat_le_top m)
    (uniqueDiffOn_Ici 0)).mono (ordConnected_Ici.uIcc_subset hx hT)

/-- On a compact interval in `[0, ∞)`, the integral of `-f'` for a completely monotone
function is the endpoint drop, with the derivative taken within `[0, ∞)`. -/
lemma IsCompletelyMonotone.integral_neg_iteratedDerivWithin_one_Ici_eq_sub
    (hcm : IsCompletelyMonotone f) {x T : ℝ} (hx : 0 ≤ x) (hxT : x ≤ T) :
    ∫ t in x..T, -iteratedDerivWithin 1 f (Ici 0) t = f x - f T := by
  by_cases h_eq : x = T
  · subst T
    simp
  have htransfer :
      ∫ t in x..T, -iteratedDerivWithin 1 f (Icc x T) t =
      ∫ t in x..T, -iteratedDerivWithin 1 f (Ici 0) t := by
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    rw [uIoo_of_le hxT] at ht
    have ht_pos : 0 < t := lt_of_le_of_lt hx ht.1
    exact congrArg Neg.neg (hcm.iteratedDerivWithin_Icc_eq_Ici ht_pos ht)
  rw [← htransfer]
  simpa [iteratedDerivWithin_one, intervalIntegral.integral_neg, neg_sub] using
    congrArg Neg.neg (intervalIntegral.integral_derivWithin_Icc_of_contDiffOn_Icc
      ((hcm.contDiffOn.mono
        (Icc_subset_Ici_self.trans (Ici_subset_Ici.mpr hx))).of_le (nat_le_top _)) hxT)

/-- The improper integral `∫ₓ^∞ (-f') dt = f x - L` from an arbitrary nonnegative endpoint `x`,
for a completely monotone function with limit `L` at infinity. -/
lemma IsCompletelyMonotone.integral_Ioi_neg_iteratedDerivWithin_one_of_nonneg
    (hcm : IsCompletelyMonotone f) {x : ℝ} (hx : 0 ≤ x) {L : ℝ} (hL : Tendsto f atTop (nhds L)) :
    ∫ t in Ioi x, -iteratedDerivWithin 1 f (Ici 0) t = f x - L := by
  have hcont : ContinuousWithinAt f (Ici x) x :=
    (hcm.contDiffOn.continuousOn.continuousWithinAt hx).mono (Ici_subset_Ici.mpr hx)
  have hderiv : ∀ t ∈ Ioi x, HasDerivAt f (iteratedDerivWithin 1 f (Ici 0) t) t :=
    fun t ht => hcm.hasDerivAt_iteratedDerivWithin_succ 0 (hx.trans_lt ht)
  have hneg : ∀ t ∈ Ioi x, iteratedDerivWithin 1 f (Ici 0) t ≤ 0 :=
    fun t ht => hcm.iteratedDerivWithin_one_nonpos (hx.trans ht.le)
  have hFTC : ∫ t in Ioi x, iteratedDerivWithin 1 f (Ici 0) t = L - f x :=
    integral_Ioi_of_hasDerivAt_of_nonpos hcont hderiv hneg hL
  rw [MeasureTheory.integral_neg, hFTC]
  ring

end TauCeti
end

/- TauCeti.Analysis.CompletelyMonotone.Bernstein.Measures -/
noncomputable section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/





-- Non-public: the bundled Laplace kernel and its integrability.


/-!
# Approximating measures for Bernstein's theorem

The Chafaï-style approximating measures for the **non-constant part** of a completely monotone
function in Bernstein's theorem. For a completely monotone `f` with `L = lim_{t→∞} f t`, the
densities `ρ_n(t) = (-1)ⁿ/(n-1)! · tⁿ⁻¹ · f⁽ⁿ⁾(t)` are nonnegative on `[0, ∞)`, the positive
support used by `chafaiMeasure`; they define finite measures whose total mass is bounded by
`f(0) - f(∞) = f(0) - L`, and after the rescaling `t ↦ (n-1)/t` give measures `chafaiRescaled f n`
on `ℝ≥0` whose Laplace kernels `(1 - xp/(n-1))₊ⁿ⁻¹` converge to `e^{-xp}`. These feed the Prokhorov
tightness argument and, in the limit, represent `f - L` (mass `f(0) - L`), i.e. the non-constant
part; the **full** Bernstein representing measure adds the atom `L · δ₀` at `0` (the constant `L =
∫ e^{-tx} d(L·δ₀)`). That final assembly — recovering `f` itself, not merely `f - L` — is performed
downstream in the Bernstein-theorem file, not here. This file supplies only the approximating
infrastructure.

These build on the `IsCompletelyMonotone` API in `CompletelyMonotone/Basic.lean` and
`CompletelyMonotone/Integral.lean`.

## Main declarations

* `TauCeti.chafaiDensity`, `TauCeti.chafaiMeasure`: the approximating densities and measures.
* `TauCeti.bernsteinKernel`, `TauCeti.continuous_bernsteinKernel`,
  `TauCeti.bernsteinKernel_nonneg`, `TauCeti.bernsteinKernel_le_one`,
  `TauCeti.bernsteinKernelBoundedContinuous`,
  `TauCeti.bernsteinKernelBoundedContinuous_apply`, `TauCeti.integrable_bernsteinKernel`,
  `TauCeti.bernsteinKernel_tendsto`: the rescaled Laplace kernel, its bundled
  bounded-continuous `p`-dependence on the nonnegative half-line, and its pointwise limit
  `e^{-xp}` (bundled as `TauCeti.laplaceKernelBoundedContinuous` in
  `CompletelyMonotone/Laplace/Kernel.lean`).
* `TauCeti.integral_exp_neg_mul_add_smul_dirac_zero`: adjoining an atom `c • δ₀` adds exactly
  `c` to the transform, the kernel being `1` at `0`.
* `TauCeti.chafaiRescaled`, `TauCeti.chafaiRescaled_mass_eq`: the `ℝ≥0`-valued pushed-forward
  measures and mass preservation.
* `TauCeti.chafaiRescaled_integral_bernsteinKernel`,
  `TauCeti.chafaiRescaled_integral_bernsteinKernelBoundedContinuous`,
  `TauCeti.ae_nonneg_bernsteinKernel_chafaiRescaled`: characteristic lemmas pairing the
  rescaled Chafaï measures with the Bernstein kernel without unfolding either definition.
* `TauCeti.chafaiMeasure_finite_mass`, `TauCeti.chafaiRescaled_finite_mass`: finiteness and the
  total-mass bound `≤ f(0) - L`.
* `TauCeti.chafaiRescaled_prokhorov_mass_bound`,
  `TauCeti.chafaiRescaled_tendsto_laplace_integral_of_weak`: Prokhorov-ready mass bounds and
  the Laplace test-function specialization of weak convergence for the rescaled measures.
* `TauCeti.chafaiRescaled_lintegral_coe_le`: first-moment / coe-lintegral bound.
* `TauCeti.chafaiRescaled_integral_bernsteinKernel_eq_sub_tendsto_atTop`: Chafaï
  reconstruction identity `f x - L = ∫ bernsteinKernel ∂chafaiRescaled`.
* `TauCeti.integral_bernsteinKernel_sub_laplaceKernel_tendsto_zero_of_mass_bound`:
  Bernstein-kernel to Laplace-kernel error tends to `0`.

## References

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B (Bernstein theorem milestone).

* D. Chafaï, *Aspects of the Bernstein theorem* (2013).
* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions* (de Gruyter, 2nd ed. 2012), Ch. 1.
-/


open MeasureTheory Set intervalIntegral Filter
open scoped BoundedContinuousFunction ContDiff NNReal Topology

namespace TauCeti

variable {f : ℝ → ℝ}

/-! ## Smoothness-index helpers -/



/-! ## Measure construction for Bernstein -/

/-- The density `ρ_n(t) = (-1)ⁿ/(n-1)! · tⁿ⁻¹ · f⁽ⁿ⁾(t)` for nonzero `n`, used for the `n`-th
approximating measure in the Bernstein proof (Chafaï 2013). By convention the `n = 0` branch
returns `0`. -/
noncomputable def chafaiDensity (f : ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  if n = 0 then 0
  else (-1 : ℝ) ^ n / (Nat.factorial (n - 1) : ℝ) *
    t ^ (n - 1) * iteratedDerivWithin n f (Ici 0) t

/-- `chafaiDensity f 0 = 0`. -/
@[simp] lemma chafaiDensity_zero (f : ℝ → ℝ) (t : ℝ) : chafaiDensity f 0 t = 0 := by
  rw [chafaiDensity, if_pos rfl]

/-- The defining formula for `chafaiDensity` at a nonzero order. -/
@[simp]
lemma chafaiDensity_of_ne_zero {n : ℕ} (hn : n ≠ 0) (f : ℝ → ℝ) (t : ℝ) :
    chafaiDensity f n t = (-1 : ℝ) ^ n / (Nat.factorial (n - 1) : ℝ) *
      t ^ (n - 1) * iteratedDerivWithin n f (Ici 0) t := by
  rw [chafaiDensity, if_neg hn]

/-- `chafaiDensity f n` is continuous on `[0, ∞)` when `f` has `n` continuous derivatives
there. -/
lemma continuousOn_chafaiDensity {n : ℕ} (hf : ContDiffOn ℝ (n : WithTop ℕ∞) f (Ici 0)) :
    ContinuousOn (chafaiDensity f n) (Ici 0) := by
  by_cases hn : n = 0
  · subst n
    have hzero : chafaiDensity f 0 = fun _ : ℝ => 0 := funext (chafaiDensity_zero f)
    rw [hzero]
    exact continuousOn_const
  have heq : chafaiDensity f n = fun t => (-1 : ℝ) ^ n / (Nat.factorial (n - 1) : ℝ) *
      t ^ (n - 1) * iteratedDerivWithin n f (Ici 0) t :=
    funext (chafaiDensity_of_ne_zero hn f)
  rw [heq]
  exact (continuousOn_const.mul ((continuousOn_pow _).mono fun _ _ => trivial)).mul
    (hf.continuousOn_iteratedDerivWithin le_rfl (uniqueDiffOn_Ici 0))

/-- The `n`-th Chafaï approximating measure `σ_n` for the Bernstein representation, with density
`ρ_n` on
`(0, ∞)`. -/
noncomputable def chafaiMeasure (f : ℝ → ℝ) (n : ℕ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun t => ENNReal.ofReal (chafaiDensity f n t))

/-- `chafaiMeasure` as a `withDensity`, exposed as a lemma rather than an unfoldable body. -/
lemma chafaiMeasure_eq_withDensity (f : ℝ → ℝ) (n : ℕ) :
    chafaiMeasure f n =
      (volume.restrict (Ioi 0)).withDensity (fun t => ENNReal.ofReal (chafaiDensity f n t)) := by
  rw [chafaiMeasure]

/-- The mass `chafaiMeasure f n` assigns to a measurable set, as a set lintegral of the density. -/
@[simp]
lemma chafaiMeasure_apply (f : ℝ → ℝ) (n : ℕ) {s : Set ℝ} (hs : MeasurableSet s) :
    chafaiMeasure f n s =
      ∫⁻ t in s, ENNReal.ofReal (chafaiDensity f n t) ∂(volume.restrict (Ioi 0)) := by
  rw [chafaiMeasure, withDensity_apply _ hs]

/-- The density `ρ_n(t)` is nonnegative when `t ≥ 0` and the `n`-th derivative has the
alternating sign at `t`. -/
lemma chafaiDensity_nonneg {n : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (hsign : 0 ≤ (-1 : ℝ) ^ n * iteratedDerivWithin n f (Ici 0) t) :
    0 ≤ chafaiDensity f n t := by
  simp only [chafaiDensity]
  split_ifs with hn
  · exact le_refl 0
  · have hfact_pos : (0 : ℝ) < ↑(Nat.factorial (n - 1)) :=
      Nat.cast_pos.mpr (Nat.factorial_pos _)
    calc (-1 : ℝ) ^ n / ↑(Nat.factorial (n - 1)) * t ^ (n - 1) *
          iteratedDerivWithin n f (Ici 0) t
        = t ^ (n - 1) / ↑(Nat.factorial (n - 1)) *
          ((-1 : ℝ) ^ n * iteratedDerivWithin n f (Ici 0) t) := by field_simp
      _ ≥ 0 := mul_nonneg (div_nonneg (pow_nonneg ht _) hfact_pos.le) hsign

/-- For `n = 1`, the density simplifies to `-f'(t)`. -/
lemma chafaiDensity_one (t : ℝ) :
    chafaiDensity f 1 t = -iteratedDerivWithin 1 f (Ici 0) t := by
  simp [chafaiDensity]

/-- Difference of two successive Chafaï densities, in the algebraic form used by integration by
parts. -/
private lemma chafaiDensity_succ_succ_sub_succ (f : ℝ → ℝ) (m : ℕ) (t : ℝ) :
    chafaiDensity f (m + 2) t - chafaiDensity f (m + 1) t =
      ↑(m + 1) * t ^ m *
          (((-1 : ℝ) ^ (m + 2) / ↑(m + 1).factorial) *
            iteratedDerivWithin (m + 1) f (Ici 0) t) +
        t ^ (m + 1) *
          (((-1 : ℝ) ^ (m + 2) / ↑(m + 1).factorial) *
            iteratedDerivWithin (m + 2) f (Ici 0) t) := by
  -- Put both densities into their nonzero defining branches.
  have hm2 : m + 2 ≠ 0 := by omega
  have hm1 : m + 1 ≠ 0 := by omega
  have hdens_m2 :
      chafaiDensity f (m + 2) t =
        (-1 : ℝ) ^ (m + 2) / ((m + 1).factorial : ℝ) *
          t ^ (m + 1) * iteratedDerivWithin (m + 2) f (Ici 0) t := by
    rw [chafaiDensity_of_ne_zero hm2]
    norm_num
  have hdens_m1 :
      chafaiDensity f (m + 1) t =
        (-1 : ℝ) ^ (m + 1) / (m.factorial : ℝ) *
          t ^ m * iteratedDerivWithin (m + 1) f (Ici 0) t := by
    rw [chafaiDensity_of_ne_zero hm1]
    norm_num
  rw [hdens_m2, hdens_m1]
  -- Move the two factorial denominators to the same `(m + 1)!` denominator and normalize the
  -- alternating sign.
  have hfact : ((m + 1).factorial : ℝ) = ((m + 1 : ℕ) : ℝ) * ↑m.factorial := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [hfact]
  have hfact_ne : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hsucc_ne : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hneg : (-1 : ℝ) ^ (m + 2) = (-1) ^ (m + 1) * (-1) := pow_succ (-1) (m + 1)
  rw [hneg]
  field_simp
  ring

/-! ## Rescaled measures and Prokhorov extraction -/

/-- The Bernstein kernel `φ_n(x,p) = max(1 - xp/(n-1), 0)ⁿ⁻¹` for `n ≥ 2`. After the change of
variable `p = (n-1)/t`, the Taylor integral kernel on `[0, T]` becomes `φ_n(x, p)`, which
converges pointwise to `e^{-xp}` as `n → ∞` (the classical `(1-x/n)ⁿ → e^{-x}` limit). -/
noncomputable def bernsteinKernel (n : ℕ) (x p : ℝ) : ℝ :=
  if n ≤ 1 then 0 else (max (1 - x * p / (↑(n - 1) : ℝ)) 0) ^ (n - 1)

/-- The Bernstein kernel vanishes for `n ≤ 1`. -/
@[simp] lemma bernsteinKernel_of_le_one {n : ℕ} (hn : n ≤ 1) (x p : ℝ) :
    bernsteinKernel n x p = 0 := by
  rw [bernsteinKernel, if_pos hn]

/-- The defining formula for the Bernstein kernel at `2 ≤ n`. -/
@[simp]
lemma bernsteinKernel_of_two_le {n : ℕ} (hn : 2 ≤ n) (x p : ℝ) :
    bernsteinKernel n x p = (max (1 - x * p / (↑(n - 1) : ℝ)) 0) ^ (n - 1) := by
  have hnle : ¬ n ≤ 1 := by omega
  rw [bernsteinKernel, if_neg hnle]

/-- The Bernstein kernel is continuous in `p` for fixed `n` and `x`. -/
lemma continuous_bernsteinKernel (n : ℕ) (x : ℝ) : Continuous (bernsteinKernel n x) := by
  unfold bernsteinKernel
  split_ifs <;> fun_prop

/-- The Bernstein kernel is nonnegative. -/
@[simp] lemma bernsteinKernel_nonneg (n : ℕ) (x p : ℝ) : 0 ≤ bernsteinKernel n x p := by
  rw [bernsteinKernel]; split_ifs <;> positivity

/-- On the nonnegative half-plane, the Bernstein kernel is bounded above by `1`. -/
lemma bernsteinKernel_le_one {n : ℕ} {x p : ℝ} (hx : 0 ≤ x) (hp : 0 ≤ p) :
    bernsteinKernel n x p ≤ 1 := by
  rw [bernsteinKernel]
  split_ifs with hn
  · norm_num
  · have hn_pos : (0 : ℝ) < (↑(n - 1) : ℝ) := Nat.cast_pos.mpr (by omega)
    have hratio_nonneg : 0 ≤ x * p / (↑(n - 1) : ℝ) :=
      div_nonneg (mul_nonneg hx hp) hn_pos.le
    have hbase_nonneg : 0 ≤ max (1 - x * p / (↑(n - 1) : ℝ)) 0 := le_max_right _ _
    have hbase_le_one : max (1 - x * p / (↑(n - 1) : ℝ)) 0 ≤ 1 := by
      exact max_le (by linarith) zero_le_one
    exact pow_le_one₀ hbase_nonneg hbase_le_one

/-- The Bernstein kernel as a bundled bounded continuous test function of the nonnegative
variable `p`, for fixed `n` and nonnegative `x`. -/
noncomputable def bernsteinKernelBoundedContinuous (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ℝ≥0 →ᵇ ℝ where
  toFun := fun p => bernsteinKernel n x (p : ℝ)
  continuous_toFun := (continuous_bernsteinKernel n x).comp continuous_subtype_val
  map_bounded' :=
    ⟨1, fun p q => by
      rw [Real.dist_eq]
      have hp0 : 0 ≤ bernsteinKernel n x (p : ℝ) := bernsteinKernel_nonneg n x (p : ℝ)
      have hp1 : bernsteinKernel n x (p : ℝ) ≤ 1 := bernsteinKernel_le_one hx p.2
      have hq0 : 0 ≤ bernsteinKernel n x (q : ℝ) := bernsteinKernel_nonneg n x (q : ℝ)
      have hq1 : bernsteinKernel n x (q : ℝ) ≤ 1 := bernsteinKernel_le_one hx q.2
      exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩⟩

/-- The bundled Bernstein kernel evaluates to the unbundled kernel on `ℝ≥0`. -/
@[simp]
lemma bernsteinKernelBoundedContinuous_apply (n : ℕ) {x : ℝ} (hx : 0 ≤ x) (p : ℝ≥0) :
    bernsteinKernelBoundedContinuous n hx p = bernsteinKernel n x (p : ℝ) := by
  rw [bernsteinKernelBoundedContinuous]; rfl

/-- **The Bernstein kernel at a nonnegative point is integrable against a finite measure.** For
`0 ≤ x`, the map `p ↦ bernsteinKernel n x p` is integrable against any finite measure on `ℝ≥0`.
The companion of `TauCeti.integrable_exp_neg_mul`, which says the same of the Laplace kernel. -/
lemma integrable_bernsteinKernel (μ : Measure ℝ≥0) [IsFiniteMeasure μ] (n : ℕ) {x : ℝ}
    (hx : 0 ≤ x) : Integrable (fun p : ℝ≥0 => bernsteinKernel n x (p : ℝ)) μ := by
  have h := (bernsteinKernelBoundedContinuous n hx).integrable μ
  rwa [funext (bernsteinKernelBoundedContinuous_apply n hx)] at h

/-- **An atom at `0` shifts the Laplace transform by its mass.** The kernel takes the value `1` at
`p = 0`, so adjoining `c • δ₀` to a finite measure adds exactly `c`. -/
@[simp]
lemma integral_exp_neg_mul_add_smul_dirac_zero (μ : Measure ℝ≥0) [IsFiniteMeasure μ] (c : ℝ≥0)
    {x : ℝ} (hx : 0 ≤ x) :
    ∫ p : ℝ≥0, Real.exp (-(x * (p : ℝ))) ∂(μ + c • Measure.dirac (0 : ℝ≥0))
      = (∫ p : ℝ≥0, Real.exp (-(x * (p : ℝ))) ∂μ) + c := by
  rw [integral_add_measure (integrable_exp_neg_mul μ hx)
      (integrable_exp_neg_mul (c • Measure.dirac (0 : ℝ≥0)) hx),
    integral_smul_nnreal_measure, integral_dirac]
  simp [NNReal.smul_def]

/-- The Bernstein kernel is measurable in `p` for fixed `n` and `x`. -/
lemma measurable_bernsteinKernel (n : ℕ) (x : ℝ) : Measurable (bernsteinKernel n x) := by
  unfold bernsteinKernel; split_ifs
  · exact measurable_const
  · fun_prop

/-- The rescaling map `t ↦ max ((n-1)/t) 0`, valued in `ℝ≥0`. -/
noncomputable def chafaiRescaling (n : ℕ) (t : ℝ) : ℝ≥0 :=
  Real.toNNReal (((n : ℝ) - 1) / t)

/-- The rescaling map `t ↦ max ((n-1)/t) 0`, valued in `ℝ≥0`, is measurable. -/
lemma measurable_chafaiRescaling (n : ℕ) :
    Measurable (chafaiRescaling n) :=
  continuous_real_toNNReal.measurable.comp (measurable_const.div measurable_id)

/-- On the positive part of the source, the `ℝ≥0` rescaling coerces back to `(n-1)/t`. -/
@[simp]
lemma chafaiRescaling_coe_of_pos {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 < t) :
    (chafaiRescaling n t : ℝ) = ((n : ℝ) - 1) / t := by
  have hnum : 0 ≤ (n : ℝ) - 1 := by
    exact sub_nonneg.mpr (by exact_mod_cast hn)
  have hnonneg : 0 ≤ ((n : ℝ) - 1) / t := div_nonneg hnum ht.le
  simp [chafaiRescaling, Real.coe_toNNReal', max_eq_left hnonneg]

/-- The rescaled measure `σ̃_n`: pushforward of `chafaiMeasure f n` under the `ℝ≥0` rescaling. -/
noncomputable def chafaiRescaled (f : ℝ → ℝ) (n : ℕ) : Measure ℝ≥0 :=
  Measure.map (chafaiRescaling n) (chafaiMeasure f n)

/-- `chafaiRescaled` as a pushforward, exposed as a lemma rather than an unfoldable body. -/
lemma chafaiRescaled_eq_map (f : ℝ → ℝ) (n : ℕ) :
    chafaiRescaled f n = Measure.map (chafaiRescaling n) (chafaiMeasure f n) := by
  rw [chafaiRescaled]

/-- The mass `chafaiRescaled f n` assigns to a measurable set, as the pushforward formula. -/
@[simp]
lemma chafaiRescaled_apply (f : ℝ → ℝ) (n : ℕ) {s : Set ℝ≥0} (hs : MeasurableSet s) :
    chafaiRescaled f n s = chafaiMeasure f n ((chafaiRescaling n) ⁻¹' s) := by
  rw [chafaiRescaled, Measure.map_apply (measurable_chafaiRescaling n) hs]

/-- Integrating against `chafaiRescaled f n` is integrating the pullback along the Chafaï
rescaling against `chafaiMeasure f n`. -/
lemma chafaiRescaled_integral (f : ℝ → ℝ) (n : ℕ) {g : ℝ≥0 → ℝ}
    (hg : AEStronglyMeasurable g (chafaiRescaled f n)) :
    ∫ x, g x ∂(chafaiRescaled f n) =
      ∫ t, g (chafaiRescaling n t) ∂(chafaiMeasure f n) := by
  rw [chafaiRescaled_eq_map] at hg ⊢
  exact MeasureTheory.integral_map (measurable_chafaiRescaling n).aemeasurable hg

/-- On positive source points, pulling the Bernstein kernel back along the Chafaï rescaling
gives the classical finite-order kernel `(max (1 - x / t) 0) ^ (n - 1)`. -/
lemma bernsteinKernel_chafaiRescaling_of_pos {n : ℕ} (hn : 2 ≤ n) (x : ℝ) {t : ℝ} (ht : 0 < t) :
    bernsteinKernel n x (chafaiRescaling n t : ℝ) = (max (1 - x / t) 0) ^ (n - 1) := by
  rw [bernsteinKernel_of_two_le hn]
  rw [chafaiRescaling_coe_of_pos (by omega : 1 ≤ n) ht]
  congr 2
  have hcast : ((n : ℝ) - 1) = (↑(n - 1) : ℝ) := by
    norm_num [Nat.cast_sub (by omega : 1 ≤ n)]
  have hn1 : (↑(n - 1) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : n - 1 ≠ 0)
  rw [hcast]
  field_simp [hn1, ht.ne']

/-- The Bernstein kernel is nonnegative almost everywhere against every rescaled Chafaï measure.
This is the public positivity lemma consumers need before using monotone or positivity facts for
the kernel pairing. -/
@[simp]
lemma ae_nonneg_bernsteinKernel_chafaiRescaled (f : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    0 ≤ᵐ[chafaiRescaled f n] fun p : ℝ≥0 => bernsteinKernel n x (p : ℝ) := by
  exact Filter.Eventually.of_forall fun p => bernsteinKernel_nonneg n x (p : ℝ)

/-- Characteristic pairing of the rescaled Chafaï measure with the Bernstein kernel: integrating
`p ↦ φ_n(x,p)` against `chafaiRescaled f n` is the same as integrating its Chafaï-rescaling
pullback against the original Chafaï measure. -/
@[simp]
lemma chafaiRescaled_integral_bernsteinKernel (f : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    ∫ p, bernsteinKernel n x (p : ℝ) ∂(chafaiRescaled f n) =
      ∫ t, bernsteinKernel n x (chafaiRescaling n t : ℝ) ∂(chafaiMeasure f n) := by
  exact chafaiRescaled_integral f n
    (((continuous_bernsteinKernel n x).comp continuous_subtype_val).measurable.aestronglyMeasurable)

/-- Pushforward preserves total mass. -/
lemma chafaiRescaled_mass_eq (f : ℝ → ℝ) (n : ℕ) :
    (chafaiRescaled f n) univ = (chafaiMeasure f n) univ := by
  unfold chafaiRescaled
  rw [Measure.map_apply (measurable_chafaiRescaling n) MeasurableSet.univ, Set.preimage_univ]

private lemma aemeasurable_chafaiDensity_ofReal (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f) (n : ℕ) :
    AEMeasurable (fun t => ENNReal.ofReal (chafaiDensity f n t))
      (volume.restrict (Ioi 0)) := by
  have hcont : ContinuousOn (chafaiDensity f n) (Ici 0) :=
    continuousOn_chafaiDensity (n := n) (hcm.contDiffOn.of_le (nat_le_top n))
  exact ((hcont.mono Ioi_subset_Ici_self).aemeasurable measurableSet_Ioi).ennreal_ofReal

private lemma chafaiDensity_neg_derivWithin_pred (f : ℝ → ℝ)
    {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 < t) :
    chafaiDensity (fun t => -derivWithin f (Ici 0) t) (n - 1) t =
      ((n : ℝ) - 1) / t * chafaiDensity f n t := by
  have hn0 : n ≠ 0 := by omega
  have hn10 : n - 1 ≠ 0 := by omega
  rw [chafaiDensity_of_ne_zero hn10, chafaiDensity_of_ne_zero hn0]
  have hiter : iteratedDerivWithin (n - 1)
        (fun t => -derivWithin f (Ici 0) t) (Ici 0) t =
      -iteratedDerivWithin n f (Ici 0) t := by
    -- The negated function elaborates as negation of `derivWithin`; expose that defeq.
    change iteratedDerivWithin (n - 1) (-(derivWithin f (Ici 0))) (Ici 0) t =
      -iteratedDerivWithin n f (Ici 0) t
    rw [iteratedDerivWithin_neg]
    congr 1
    rw [← iteratedDerivWithin_succ']
    congr 1
    omega
  rw [hiter]
  have hfact : ((n - 1).factorial : ℝ) =
      ((n - 1 : ℕ) : ℝ) * ((n - 2).factorial : ℝ) := by
    rw [show n - 1 = (n - 2) + 1 by omega, Nat.factorial_succ]
    norm_num
  rw [hfact]
  have hnp : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    norm_num [Nat.cast_sub (by omega : 1 ≤ n)]
  have hsub : n - 1 - 1 = n - 2 := by omega
  have hpow' : t ^ (n - 2) * t = t ^ (n - 1) := by
    rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]
  have hsign : -((-1 : ℝ) ^ (n - 1)) = (-1 : ℝ) ^ n := by
    have hpow : ((-1 : ℝ) ^ n) = (-1 : ℝ) ^ ((n - 1) + 1) := by
      congr
      omega
    rw [hpow, pow_succ]
    ring
  have hden : (n : ℝ) - 1 ≠ 0 := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  rw [hnp, hsub]
  field_simp [ht.ne', hden]
  calc
    -(((-1 : ℝ) ^ (n - 1) * t ^ (n - 2) *
          iteratedDerivWithin n f (Ici 0) t * t))
        = -((-1 : ℝ) ^ (n - 1)) * (t ^ (n - 2) * t) *
            iteratedDerivWithin n f (Ici 0) t := by ring
    _ = (-1 : ℝ) ^ n * t ^ (n - 1) *
            iteratedDerivWithin n f (Ici 0) t := by rw [hsign, hpow']
    _ = iteratedDerivWithin n f (Ici 0) t * (-1 : ℝ) ^ n * t ^ (n - 1) := by
          ring

private lemma chafaiRescaled_lintegral_coe_eq_chafaiMeasure_neg_derivWithin
    (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f) {n : ℕ} (hn : 2 ≤ n) :
    ∫⁻ p : ℝ≥0, ENNReal.ofReal (p : ℝ) ∂(chafaiRescaled f n) =
      (chafaiMeasure (fun t => -derivWithin f (Ici 0) t) (n - 1)) univ := by
  rw [chafaiRescaled_eq_map]
  rw [lintegral_map]
  swap
  · exact ENNReal.measurable_ofReal.comp (by fun_prop : Measurable fun p : ℝ≥0 => (p : ℝ))
  swap
  · exact measurable_chafaiRescaling n
  rw [chafaiMeasure_eq_withDensity]
  rw [lintegral_withDensity_eq_lintegral_mul₀]
  swap
  · exact aemeasurable_chafaiDensity_ofReal f hcm n
  swap
  · exact ((NNReal.continuous_coe.measurable.comp (measurable_chafaiRescaling n)).aemeasurable)
      |>.ennreal_ofReal
  rw [chafaiMeasure_eq_withDensity, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htpos : 0 < t := ht
  have hscale : (chafaiRescaling n t : ℝ) = ((n : ℝ) - 1) / t :=
    chafaiRescaling_coe_of_pos (by omega : 1 ≤ n) htpos
  have hdens_nonneg : 0 ≤ chafaiDensity f n t :=
    chafaiDensity_nonneg htpos.le (hcm.neg_one_pow_mul_iteratedDerivWithin_nonneg n htpos.le)
  have hdens_eq := chafaiDensity_neg_derivWithin_pred f hn htpos
  simp only [Pi.mul_apply]
  rw [hscale, ← ENNReal.ofReal_mul hdens_nonneg, mul_comm, ← hdens_eq]

/-- The Chafaï density of order `n` is interval-integrable on `[0, T]`: it is continuous on
`Ici 0` given `n`-fold differentiability there, and `[0, T]` sits inside that ray. -/
private lemma intervalIntegrable_chafaiDensity {f : ℝ → ℝ} {n : ℕ}
    (hf : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) f (Ici 0)) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun t => chafaiDensity f n t) volume 0 T :=
  ((continuousOn_chafaiDensity hf).mono Icc_subset_Ici_self).intervalIntegrable_of_Icc hT

/-- **IBP identity** for the CM density:
`∫₀ᵀ ρ_{m+2}(t) dt = B_{m+2}(T) + ∫₀ᵀ ρ_{m+1}(t) dt`. -/
private lemma chafaiDensity_ibp_identity (f : ℝ → ℝ) {m : ℕ}
    (hf : ContDiffOn ℝ ((m + 2 : ℕ) : WithTop ℕ∞) f (Ici 0)) (T : ℝ) (hT : 0 < T) :
    ∫ t in (0 : ℝ)..T, chafaiDensity f (m + 2) t =
    (-1 : ℝ) ^ (m + 2) * T ^ (m + 1) / ↑(m + 1).factorial *
      iteratedDerivWithin (m + 1) f (Ici 0) T +
    ∫ t in (0 : ℝ)..T, chafaiDensity f (m + 1) t := by
  set c : ℝ := (-1) ^ (m + 2) / ↑(m + 1).factorial
  set g := iteratedDerivWithin (m + 1) f (Ici 0)
  set F := fun t : ℝ => t ^ (m + 1) * (c * g t)
  have hf_m1 : ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) f (Ici 0) :=
    hf.of_le (by exact_mod_cast (by omega : m + 1 ≤ m + 2))
  -- The primitive is continuous up to the endpoints, and differentiates to the density difference.
  have hF_cont : ContinuousOn F (Icc 0 T) :=
    ((continuous_pow _).continuousOn).mul (continuousOn_const.mul
      ((hf_m1.continuousOn_iteratedDerivWithin le_rfl (uniqueDiffOn_Ici 0)).mono
        Icc_subset_Ici_self))
  -- The product rule gives two summands; `chafaiDensity_succ_succ_sub_succ` identifies them with
  -- the density difference, which is the form the integrability and FTC steps below want.
  have hF_deriv : ∀ t ∈ Ioo 0 T, HasDerivAt F
      (chafaiDensity f (m + 2) t - chafaiDensity f (m + 1) t) t := fun t ht => by
    have hg : HasDerivAt g (iteratedDerivWithin (m + 2) f (Ici 0) t) t :=
      ContDiffOn.hasDerivAt_iteratedDerivWithin hf (uniqueDiffOn_Ici 0) (Ici_mem_nhds ht.1)
    exact (chafaiDensity_succ_succ_sub_succ f m t).symm ▸
      (hasDerivAt_pow (m + 1) t).mul (hg.const_mul _)
  -- Both density branches are interval-integrable, so the difference is too.
  have h_int_m2 : IntervalIntegrable (fun t => chafaiDensity f (m + 2) t) volume 0 T :=
    intervalIntegrable_chafaiDensity hf hT.le
  have h_int_m1 : IntervalIntegrable (fun t => chafaiDensity f (m + 1) t) volume 0 T :=
    intervalIntegrable_chafaiDensity hf_m1 hT.le
  -- FTC now reads off the difference of the two integrals directly.
  have hstep1 := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT.le hF_cont hF_deriv
    (h_int_m2.sub h_int_m1)
  have hF0 : F 0 = 0 := by simp [F, zero_pow (by omega : m + 1 ≠ 0)]
  rw [hF0, sub_zero, intervalIntegral.integral_sub h_int_m2 h_int_m1] at hstep1
  -- The lower endpoint vanishes; the upper endpoint is the boundary term in the statement.
  suffices hgoal : (-1 : ℝ) ^ (m + 2) * T ^ (m + 1) / ↑(m + 1).factorial * g T = F T by linarith
  simp only [F, c]; ring

/-- Monotonicity of the finite-interval Chafaï-density integrals in the order:
for `2 ≤ k` and `0 ≤ T`, the integral of the `k`-th density on `[0,T]` is bounded above by the
integral of the preceding density, assuming the endpoint has the required alternating sign. -/
lemma integral_chafaiDensity_le_pred (f : ℝ → ℝ) {k : ℕ} (hk : 2 ≤ k)
    (hf : ContDiffOn ℝ (k : WithTop ℕ∞) f (Ici 0)) (T : ℝ) (hT : 0 ≤ T)
    (hsign : 0 ≤ (-1 : ℝ) ^ (k - 1) * iteratedDerivWithin (k - 1) f (Ici 0) T) :
    ∫ t in (0 : ℝ)..T, chafaiDensity f k t ≤ ∫ t in (0 : ℝ)..T, chafaiDensity f (k - 1) t := by
  -- The degenerate interval is immediate; otherwise reindex `k` as `m + 2` for the IBP lemma.
  rcases hT.eq_or_lt with rfl | hT_pos
  · simp
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hsub : m + 2 - 1 = m + 1 := by omega
  simp only [hsub]
  have hibp := chafaiDensity_ibp_identity (m := m) f hf T hT_pos
  set B := (-1 : ℝ) ^ (m + 2) * T ^ (m + 1) / ↑(m + 1).factorial *
    iteratedDerivWithin (m + 1) f (Ici 0) T
  -- The boundary term in the IBP identity is nonpositive by complete-monotone sign alternation.
  have hB : B ≤ 0 := by
    have hsign_m : 0 ≤ (-1 : ℝ) ^ (m + 1) * iteratedDerivWithin (m + 1) f (Ici 0) T := by
      simpa [hsub] using hsign
    have h_neg : (-1 : ℝ) ^ (m + 2) * iteratedDerivWithin (m + 1) f (Ici 0) T ≤ 0 := by
      have : (-1 : ℝ) ^ (m + 2) = (-1) ^ (m + 1) * (-1) := pow_succ (-1) (m + 1)
      rw [this]; nlinarith [hsign_m]
    suffices B = T ^ (m + 1) / ↑(m + 1).factorial *
        ((-1 : ℝ) ^ (m + 2) * iteratedDerivWithin (m + 1) f (Ici 0) T) by
      rw [this]
      exact mul_nonpos_of_nonneg_of_nonpos
        (div_nonneg (pow_nonneg hT_pos.le _) (Nat.cast_nonneg _)) h_neg
    simp only [B]; ring
  linarith

/-- The public `n = 0` convention for Chafaï measures: the zeroth approximating measure is
zero. -/
@[simp]
lemma chafaiMeasure_zero (f : ℝ → ℝ) : chafaiMeasure f 0 = 0 := by
  rw [chafaiMeasure_eq_withDensity]
  ext s hs
  rw [withDensity_apply _ hs]
  simp

/-- The rescaled Chafaï measure on the target type `ℝ≥0` shares the `n = 0` zero convention:
`chafaiRescaled f 0 = 0`, as the pushforward of the zero measure. -/
@[simp]
lemma chafaiRescaled_zero (f : ℝ → ℝ) : chafaiRescaled f 0 = 0 := by
  rw [chafaiRescaled_eq_map, chafaiMeasure_zero, Measure.map_zero]

private lemma integral_chafaiDensity_one_eq (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (T : ℝ) (hT : 0 < T) :
    ∫ t in (0 : ℝ)..T, chafaiDensity f 1 t = f 0 - f T := by
  have h1 : ∫ t in (0 : ℝ)..T, chafaiDensity f 1 t =
      ∫ t in (0 : ℝ)..T, -iteratedDerivWithin 1 f (Ici 0) t :=
    intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t _ => chafaiDensity_one t)
  rw [h1]
  exact IsCompletelyMonotone.integral_neg_iteratedDerivWithin_one_Ici_eq_sub hcm le_rfl hT.le

private lemma integral_chafaiDensity_le_sub (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (j : ℕ) (hj : 1 ≤ j) (T : ℝ) (hT : 0 < T) :
    ∫ t in (0 : ℝ)..T, chafaiDensity f j t ≤ f 0 - f T := by
  induction j with
  | zero => omega
  | succ p ih =>
    by_cases hp : p = 0
    · subst hp
      exact le_of_eq (integral_chafaiDensity_one_eq f hcm T hT)
    · calc ∫ t in (0 : ℝ)..T, chafaiDensity f (p + 1) t
          ≤ ∫ t in (0 : ℝ)..T, chafaiDensity f p t := by
            exact integral_chafaiDensity_le_pred f (k := p + 1) (by omega)
              (hcm.contDiffOn.of_le (nat_le_top (p + 1)))
              T hT.le (by
                simpa using hcm.neg_one_pow_mul_iteratedDerivWithin_nonneg p hT.le)
        _ ≤ f 0 - f T := ih (Nat.one_le_iff_ne_zero.mpr hp)

private lemma integral_chafaiDensity_le_tendsto_sub (f : ℝ → ℝ)
    (hcm : IsCompletelyMonotone f) (n : ℕ) (hn : 1 ≤ n) (L : ℝ)
    (hL : Tendsto f atTop (nhds L)) (T : ℝ) (hT : 0 < T) :
    ∫ t in (0 : ℝ)..T, chafaiDensity f n t ≤ f 0 - L := by
  linarith [integral_chafaiDensity_le_sub f hcm n hn T hT,
    (IsCompletelyMonotoneOnIci.of_isCompletelyMonotone hcm).le_of_tendsto_atTop hL hT.le]

private lemma chafaiDensity_integrableOn_Ioi_of_tendsto (f : ℝ → ℝ)
    (hcm : IsCompletelyMonotone f) (n : ℕ) (hn : 1 ≤ n) (L : ℝ) (hL : Tendsto f atTop (nhds L)) :
    IntegrableOn (chafaiDensity f n) (Ioi 0) := by
  have hcont : ContinuousOn (chafaiDensity f n) (Ici 0) :=
    continuousOn_chafaiDensity (n := n) ((hcm.contDiffOn).of_le (nat_le_top n))
  -- The improper-integrability criterion reduces the proof to compact integrability on each
  -- interval and a uniform bound for interval integrals of `|ρ_n|`.
  apply integrableOn_Ioi_of_intervalIntegral_norm_bounded (f 0 - L) 0
    (l := atTop) (b := id)
  -- Compact integrability comes from continuity of the density on `[0, ∞)`.
  · intro T
    exact (hcont.mono Icc_subset_Ici_self).integrableOn_compact isCompact_Icc
      |>.mono_set Ioc_subset_Icc_self
  · exact tendsto_id
  -- On positive intervals the density is nonnegative, so the norm integral is the density
  -- integral, bounded by the finite-interval Chafaï estimate.
  · filter_upwards [eventually_gt_atTop 0] with T hT
    simp only [id]
    calc ∫ t in (0 : ℝ)..T, ‖chafaiDensity f n t‖
        = ∫ t in (0 : ℝ)..T, chafaiDensity f n t := by
          apply intervalIntegral.integral_congr_ae
          apply ae_of_all
          intro t ht
          rw [uIoc_of_le hT.le] at ht
          rw [Real.norm_eq_abs,
            abs_of_nonneg (chafaiDensity_nonneg ht.1.le
              (hcm.neg_one_pow_mul_iteratedDerivWithin_nonneg n ht.1.le))]
      _ ≤ f 0 - L := integral_chafaiDensity_le_tendsto_sub f hcm n hn L hL T hT

private lemma chafaiMeasure_mass_le_of_tendsto (f : ℝ → ℝ)
    (hcm : IsCompletelyMonotone f) (n : ℕ) (hn : 1 ≤ n) (L : ℝ) (hL : Tendsto f atTop (nhds L))
    (hint : IntegrableOn (chafaiDensity f n) (Ioi 0)) :
    (chafaiMeasure f n) univ ≤ ENNReal.ofReal (f 0 - L) := by
  rw [chafaiMeasure_eq_withDensity]
  rw [withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_mem measurableSet_Ioi).mono fun t (ht : 0 < t) =>
      chafaiDensity_nonneg ht.le (hcm.neg_one_pow_mul_iteratedDerivWithin_nonneg n ht.le))]
  exact ENNReal.ofReal_le_ofReal
    (le_of_tendsto (intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id)
      (eventually_atTop.mpr ⟨1, fun T hT =>
        integral_chafaiDensity_le_tendsto_sub f hcm n hn L hL T (by linarith)⟩))

/-- **Total mass bound with a chosen limit**: `chafaiMeasure f n` is finite with total mass
`≤ f(0) - L` whenever `f(t) → L` at infinity. -/
lemma chafaiMeasure_finite_mass_of_tendsto (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (n : ℕ) (L : ℝ) (hL : Tendsto f atTop (nhds L)) :
    IsFiniteMeasure (chafaiMeasure f n) ∧
    (chafaiMeasure f n) univ ≤ ENNReal.ofReal (f 0 - L) := by
  by_cases hn0 : n = 0
  · subst n
    rw [chafaiMeasure_zero]
    exact ⟨inferInstance, by simp⟩
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hint : IntegrableOn (chafaiDensity f n) (Ioi 0) :=
    chafaiDensity_integrableOn_Ioi_of_tendsto f hcm n hn L hL
  have hfin : IsFiniteMeasure (chafaiMeasure f n) := by
    unfold chafaiMeasure
    exact isFiniteMeasure_withDensity_ofReal hint.hasFiniteIntegral
  have hmass : (chafaiMeasure f n) univ ≤ ENNReal.ofReal (f 0 - L) :=
    chafaiMeasure_mass_le_of_tendsto f hcm n hn L hL hint
  exact ⟨hfin, hmass⟩

/-- **Natural total mass bound**: for a completely monotone `f`, the Chafaï measures are finite
and uniformly bounded by `f(0) - L`, where `L` is the automatically obtained limit of `f` at
infinity. -/
lemma chafaiMeasure_finite_mass (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f) :
    ∃ L : ℝ, Tendsto f atTop (nhds L) ∧ 0 ≤ L ∧
      ∀ n,
        IsFiniteMeasure (chafaiMeasure f n) ∧
        (chafaiMeasure f n) univ ≤ ENNReal.ofReal (f 0 - L) := by
  obtain ⟨L, hL, hL_nn⟩ :=
    (IsCompletelyMonotoneOnIci.of_isCompletelyMonotone hcm).exists_nonneg_tendsto_atTop
  exact ⟨L, hL, hL_nn, fun n => chafaiMeasure_finite_mass_of_tendsto f hcm n L hL⟩

/-- **Natural rescaled total mass bound**: for a completely monotone `f`, the rescaled
Chafaï measures on `ℝ≥0` are finite and uniformly bounded by `f(0) - L`, where `L` is the
automatically obtained limit of `f` at infinity. -/
lemma chafaiRescaled_finite_mass (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f) :
    ∃ L : ℝ, Tendsto f atTop (nhds L) ∧ 0 ≤ L ∧
      ∀ n,
        IsFiniteMeasure (chafaiRescaled f n) ∧
        (chafaiRescaled f n) univ ≤ ENNReal.ofReal (f 0 - L) := by
  obtain ⟨L, hL, hL_nn, hfinite⟩ := chafaiMeasure_finite_mass f hcm
  refine ⟨L, hL, hL_nn, fun n => ?_⟩
  have hmass := chafaiRescaled_mass_eq f n
  refine ⟨?_, ?_⟩
  · exact ⟨by rw [hmass]; exact (hfinite n).1.measure_univ_lt_top⟩
  · rw [hmass]
    exact (hfinite n).2

/-- Uniform first-moment bound for the rescaled Chafaï measures. -/
lemma chafaiRescaled_lintegral_coe_le (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f) :
    ∀ n,
      ∫⁻ p : ℝ≥0, ENNReal.ofReal (p : ℝ) ∂(chafaiRescaled f n) ≤
        ENNReal.ofReal (-derivWithin f (Ici 0) 0) := by
  intro n
  have hderiv_nonneg : 0 ≤ -derivWithin f (Ici 0) 0 := by
    linarith [hcm.derivWithin_nonpos le_rfl]
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n
    · rw [chafaiRescaled_zero]
      simp
    · rw [chafaiRescaled_eq_map, lintegral_map]
      swap
      · exact ENNReal.measurable_ofReal.comp
          (by fun_prop : Measurable fun p : ℝ≥0 => (p : ℝ))
      swap
      · exact measurable_chafaiRescaling 1
      simp [chafaiRescaling]
  · obtain ⟨L, _hL, hL_nonneg, hfinite⟩ :=
      chafaiMeasure_finite_mass (fun t => -derivWithin f (Ici 0) t) hcm.neg_derivWithin
    calc
      ∫⁻ p : ℝ≥0, ENNReal.ofReal (p : ℝ) ∂(chafaiRescaled f n)
          = (chafaiMeasure (fun t => -derivWithin f (Ici 0) t) (n - 1)) univ :=
              chafaiRescaled_lintegral_coe_eq_chafaiMeasure_neg_derivWithin f hcm hn
      _ ≤ ENNReal.ofReal (-derivWithin f (Ici 0) 0 - L) := (hfinite (n - 1)).2
      _ ≤ ENNReal.ofReal (-derivWithin f (Ici 0) 0) :=
          ENNReal.ofReal_le_ofReal (by linarith)

/-- Prokhorov-ready mass bound for the rescaled Chafaï measures: a completely monotone function
supplies a nonnegative real mass constant `C = f(0) - L`, where `L` is the limit of `f` at
infinity, such that every `chafaiRescaled f n` is finite and has total mass at most `C`. -/
lemma chafaiRescaled_prokhorov_mass_bound (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f) :
    ∃ L : ℝ, ∃ C : ℝ≥0, Tendsto f atTop (nhds L) ∧ 0 ≤ L ∧ (C : ℝ) = f 0 - L ∧
      ∀ n,
        IsFiniteMeasure (chafaiRescaled f n) ∧
        (chafaiRescaled f n) univ ≤ (C : ENNReal) := by
  obtain ⟨L, hL, hL_nn, hfinite⟩ := chafaiRescaled_finite_mass f hcm
  have hL_le : L ≤ f 0 :=
    (IsCompletelyMonotoneOnIci.of_isCompletelyMonotone hcm).le_of_tendsto_atTop hL le_rfl
  let C : ℝ≥0 := ⟨f 0 - L, sub_nonneg.mpr hL_le⟩
  refine ⟨L, C, hL, hL_nn, rfl, fun n => ?_⟩
  refine ⟨(hfinite n).1, ?_⟩
  have hC : (C : ENNReal) = ENNReal.ofReal (f 0 - L) := by
    rw [← ENNReal.ofReal_coe_nnreal (p := C)]
    rfl
  rw [hC]
  exact (hfinite n).2

/-! ## Chafaï reconstruction and Bernstein-to-Laplace replacement -/

private lemma chafai_kernel_density_eq (f : ℝ → ℝ) (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (hx : 0 ≤ x) :
    ∫ t in Ioi 0, bernsteinKernel n x (((n : ℝ) - 1) / t) *
      chafaiDensity f n t =
    ∫ t in Ioi x, (-1 : ℝ) ^ n / ↑(n - 1).factorial *
      (t - x) ^ (n - 1) * iteratedDerivWithin n f (Ici 0) t := by
  have hn0 : n ≠ 0 := by omega
  have hn1 : ¬ n ≤ 1 := by omega
  have hsubset : Ioi x ⊆ Ioi 0 := Ioi_subset_Ioi hx
  have hvanish : ∀ t ∈ Ioi 0 \ Ioi x,
      bernsteinKernel n x (((n : ℝ) - 1) / t) * chafaiDensity f n t = 0 := by
    intro t ht
    simp only [Set.mem_sdiff, mem_Ioi, not_lt] at ht
    rw [← chafaiRescaling_coe_of_pos (by omega : 1 ≤ n) ht.1,
      bernsteinKernel_chafaiRescaling_of_pos hn x ht.1,
      max_eq_right (by rw [sub_nonpos, le_div_iff₀ ht.1]; linarith)]
    rw [zero_pow (by omega : n - 1 ≠ 0), zero_mul]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsubset hvanish]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [mem_Ioi] at ht
  have ht_pos : 0 < t := lt_of_le_of_lt hx ht
  dsimp only
  rw [← chafaiRescaling_coe_of_pos (by omega : 1 ≤ n) ht_pos,
    bernsteinKernel_chafaiRescaling_of_pos hn x ht_pos,
    max_eq_left (by rw [sub_nonneg, div_le_one₀ ht_pos]; linarith)]
  rw [chafaiDensity_of_ne_zero hn0]
  have key : (1 - x / t) ^ (n - 1) * t ^ (n - 1) = (t - x) ^ (n - 1) := by
    rw [← mul_pow]
    congr 1
    field_simp [ne_of_gt ht_pos]
  calc
    (1 - x / t) ^ (n - 1) *
        (((-1 : ℝ) ^ n / ↑(n - 1).factorial * t ^ (n - 1)) *
          iteratedDerivWithin n f (Ici 0) t)
        = (-1 : ℝ) ^ n / ↑(n - 1).factorial *
          ((1 - x / t) ^ (n - 1) * t ^ (n - 1)) *
          iteratedDerivWithin n f (Ici 0) t := by ring
    _ = _ := by rw [key]

/-- For `k ≠ 0`, dividing by `k!` and multiplying by `k` is dividing by `(k - 1)!`. This is the
coefficient bookkeeping produced by differentiating the order-`k` kernel. -/
private lemma div_factorial_mul_natCast {k : ℕ} (hk : k ≠ 0) (c z : ℝ) :
    c / ↑k.factorial * ((k : ℝ) * z) = c / ↑(k - 1).factorial * z := by
  have hfact : k.factorial = k * (k - 1).factorial := (Nat.mul_factorial_pred hk).symm
  rw [hfact]
  push_cast
  field_simp

private lemma ibp_finite_interval (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (k : ℕ) (hk : k ≠ 0) (x T : ℝ) (hx : 0 ≤ x) (hxT : x < T) :
    ∫ t in x..T, (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (t - x) ^ k *
      iteratedDerivWithin (k + 1) f (Ici 0) t =
    (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (T - x) ^ k *
      iteratedDerivWithin k f (Ici 0) T -
    ∫ t in x..T, (-1 : ℝ) ^ (k + 1) / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
      iteratedDerivWithin k f (Ici 0) t := by
  set c := (-1 : ℝ) ^ (k + 1) / ↑k.factorial
  set g := iteratedDerivWithin k f (Ici 0)
  set g' := iteratedDerivWithin (k + 1) f (Ici 0)
  set u := fun t : ℝ => c * (t - x) ^ k
  set u' := fun t : ℝ => c * (↑k * (t - x) ^ (k - 1))
  have hu'_eq : ∀ t, u' t =
      (-1 : ℝ) ^ (k + 1) / ↑(k - 1).factorial * (t - x) ^ (k - 1) := fun t => by
    simp only [u', c]
    exact div_factorial_mul_natCast hk _ _
  have hu_cont : ContinuousOn u (uIcc x T) :=
    continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).pow _)
  have hg_cont : ContinuousOn g (uIcc x T) :=
    hcm.continuousOn_iteratedDerivWithin_uIcc k hx (hx.trans hxT.le)
  have hu_deriv : ∀ t ∈ Ioo (min x T) (max x T),
      HasDerivWithinAt u (u' t) (Ioi t) t := by
    intro t _ht
    apply HasDerivAt.hasDerivWithinAt
    simpa [u, u', mul_assoc] using
      (((hasDerivAt_pow k (t - x)).comp t
        ((hasDerivAt_id t).sub_const x)).const_mul c)
  have hg_deriv : ∀ t ∈ Ioo (min x T) (max x T),
      HasDerivWithinAt g (g' t) (Ioi t) t := by
    intro t ht
    rw [min_eq_left hxT.le, max_eq_right hxT.le] at ht
    exact (hcm.hasDerivAt_iteratedDerivWithin_succ k (lt_of_le_of_lt hx ht.1)).hasDerivWithinAt
  have hu'_int : IntervalIntegrable u' volume x T :=
    (continuousOn_const.mul (continuousOn_const.mul
      ((continuousOn_id.sub continuousOn_const).pow _))).intervalIntegrable
  have hg'_int : IntervalIntegrable g' volume x T :=
    (hcm.continuousOn_iteratedDerivWithin_uIcc (k + 1) hx (hx.trans hxT.le)).intervalIntegrable
  have hibp := integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    hu_cont hg_cont hu_deriv hg_deriv hu'_int hg'_int
  have hu0 : u x = 0 := by simp [u, sub_self, zero_pow hk]
  rw [hu0, zero_mul, sub_zero] at hibp
  have h1 : ∫ t in x..T, (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (t - x) ^ k *
        iteratedDerivWithin (k + 1) f (Ici 0) t =
      ∫ t in x..T, u t * g' t :=
    intervalIntegral.integral_congr_ae (ae_of_all _ fun t _ => by ring)
  have h2 : ∫ t in x..T, u' t * g t =
      ∫ t in x..T, (-1 : ℝ) ^ (k + 1) / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
        iteratedDerivWithin k f (Ici 0) t :=
    intervalIntegral.integral_congr_ae (ae_of_all _ fun t _ => by rw [hu'_eq])
  linarith

private lemma normalized_iteratedDerivWithin_nonneg_antitone (f : ℝ → ℝ)
    (hcm : IsCompletelyMonotone f) (k : ℕ) :
    (∀ T, 0 ≤ T → 0 ≤ (-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) T) ∧
      AntitoneOn (fun T => (-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) T) (Ici 0) := by
  constructor
  · intro T hT
    exact hcm.neg_one_pow_mul_iteratedDerivWithin_nonneg k hT
  · apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · exact (hcm.contDiffOn.continuousOn_iteratedDerivWithin (nat_le_top k)
        (uniqueDiffOn_Ici 0)).const_mul ((-1 : ℝ) ^ k)
    · rw [interior_Ici]
      intro T hT
      exact ((hcm.hasDerivAt_iteratedDerivWithin_succ k hT).const_mul
        ((-1 : ℝ) ^ k)).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro T hT
      have hderiv : deriv (fun T => (-1 : ℝ) ^ k *
            iteratedDerivWithin k f (Ici 0) T) T =
          (-1 : ℝ) ^ k * iteratedDerivWithin (k + 1) f (Ici 0) T := by
        simpa using
          ((hcm.hasDerivAt_iteratedDerivWithin_succ k hT).const_mul
            ((-1 : ℝ) ^ k)).deriv
      rw [hderiv]
      have hsign : 0 ≤ (-1 : ℝ) ^ (k + 1) *
          iteratedDerivWithin (k + 1) f (Ici 0) T :=
        hcm.neg_one_pow_mul_iteratedDerivWithin_nonneg (k + 1) hT.le
      have hneg : 0 ≤ -(((-1 : ℝ) ^ k) *
          iteratedDerivWithin (k + 1) f (Ici 0) T) := by
        simpa [pow_succ, mul_assoc] using hsign
      linarith

/-- Pointwise lower bound for the density on `Icc (T/2) T`: at each such point `t`,
`chafaiDensity f k` is at least the constant `(1/(k-1)!)·(T/2)^(k-1)·h T`. -/
private lemma chafaiDensity_ge_const_on_Icc (f : ℝ → ℝ) (k : ℕ) (h : ℝ → ℝ)
    (T : ℝ) (hhT_nonneg : 0 ≤ h T) {t : ℝ} (ht : t ∈ Icc (T / 2) T) (hT_le_ht : h T ≤ h t)
    (h_density_eq_t :
      chafaiDensity f k t = (1 / ↑((k - 1).factorial)) * t ^ (k - 1) * h t) :
    (1 / ↑((k - 1).factorial)) * (T / 2) ^ (k - 1) * h T ≤ chafaiDensity f k t := by
  -- `0 ≤ T/2` follows from the membership hypothesis `T/2 ≤ t ≤ T`.
  have hT_nonneg : 0 ≤ T := by have := ht.1.trans ht.2; linarith
  -- Combine the power monotonicity `(T/2)^(k-1) ≤ t^(k-1)` with the pointwise bound `h T ≤ h t`.
  have hhalf_nonneg : 0 ≤ T / 2 := by linarith
  have ht_nonneg : 0 ≤ t := le_trans hhalf_nonneg ht.1
  have hpow : (T / 2) ^ (k - 1) ≤ t ^ (k - 1) := pow_le_pow_left₀ hhalf_nonneg ht.1 _
  have hcoeff_nonneg : (0 : ℝ) ≤ 1 / ↑((k - 1).factorial) := by positivity
  have hright_nonneg : 0 ≤ (1 / ↑((k - 1).factorial)) * t ^ (k - 1) :=
    mul_nonneg hcoeff_nonneg (pow_nonneg ht_nonneg _)
  rw [h_density_eq_t]
  calc
    (1 / ↑((k - 1).factorial)) * (T / 2) ^ (k - 1) * h T
        ≤ ((1 / ↑((k - 1).factorial)) * t ^ (k - 1)) * h T := by
          simpa [mul_assoc] using
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hcoeff_nonneg) hhT_nonneg
    _ ≤ ((1 / ↑((k - 1).factorial)) * t ^ (k - 1)) * h t :=
          mul_le_mul_of_nonneg_left hT_le_ht hright_nonneg

/-- Interval-integral form of the tail lower bound: integrating the pointwise bound
`chafaiDensity_ge_const_on_Icc` over `[T/2, T]` gives
`(1/(k-1)!)·(T/2)^k·h T ≤ ∫ t in T/2..T, chafaiDensity f k t`. -/
private lemma const_le_intervalIntegral_chafaiDensity (f : ℝ → ℝ) (k : ℕ) (hk : k ≠ 0)
    (h : ℝ → ℝ) (h_antitone : AntitoneOn h (Ici 0)) (T : ℝ) (hT_nonneg : 0 ≤ T) (h_density_eq :
      ∀ t ∈ Icc (T / 2) T,
        chafaiDensity f k t = (1 / ↑((k - 1).factorial)) * t ^ (k - 1) * h t)
    (hdens_int : IntervalIntegrable (chafaiDensity f k) volume (T / 2) T)
    (hhT_nonneg : 0 ≤ h T) :
    (1 / ↑((k - 1).factorial)) * (T / 2) ^ k * h T ≤
      ∫ t in T / 2..T, chafaiDensity f k t := by
  have hconst_int :
      IntervalIntegrable (fun _ : ℝ =>
        (1 / ↑((k - 1).factorial)) * (T / 2) ^ (k - 1) * h T) volume (T / 2) T :=
    intervalIntegrable_const
  -- Integrate the pointwise bound `chafaiDensity_ge_const_on_Icc` directly over `[T/2, T]`.
  have hmono_int :=
    intervalIntegral.integral_mono_on (by linarith) hconst_int hdens_int
      (fun t ht => chafaiDensity_ge_const_on_Icc f k h T hhT_nonneg ht
        (h_antitone (le_trans (by linarith : (0 : ℝ) ≤ T / 2) ht.1) hT_nonneg ht.2)
        (h_density_eq t ht))
  have hlen : T - T / 2 = T / 2 := by ring
  rw [intervalIntegral.integral_const, smul_eq_mul, hlen] at hmono_int
  -- Recombine `(T/2)·(T/2)^(k-1) = (T/2)^k` (uses `k ≠ 0`), as a named algebraic equality.
  have hpow : (T / 2) ^ (k - 1) * (T / 2) = (T / 2) ^ k := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk)]
  have hconst_eq :
      T / 2 * ((1 / ↑((k - 1).factorial)) * (T / 2) ^ (k - 1) * h T) =
        (1 / ↑((k - 1).factorial)) * (T / 2) ^ k * h T := by
    rw [← hpow]; ring
  rwa [hconst_eq] at hmono_int

/-- Boundary-term tail estimate, the engine of
`tendsto_sub_pow_mul_normalized_iteratedDerivWithin`: `(T-x)^k · h T` is
eventually squeezed by a multiple of the vanishing density tail `∫_{Ioi (T/2)}`. -/
private lemma density_tail_lower_bound_eventually (f : ℝ → ℝ)
    (hcm : IsCompletelyMonotone f) (k : ℕ) (hk : k ≠ 0) (x : ℝ)
    (h : ℝ → ℝ) (h_nonneg : ∀ T, 0 ≤ T → 0 ≤ h T) (h_antitone : AntitoneOn h (Ici 0))
    (h_density_eq : ∀ t, chafaiDensity f k t = (1 / ↑((k - 1).factorial)) * t ^ (k - 1) * h t)
    (hint_density : IntegrableOn (chafaiDensity f k) (Ioi 0)) :
    ∀ᶠ T in atTop,
      (T - x) ^ k * h T ≤
        ((4 : ℝ) ^ k * ↑((k - 1).factorial)) *
          ∫ t in Ioi (T / 2), chafaiDensity f k t := by
  have hcont_density : ContinuousOn (chafaiDensity f k) (Ici 0) :=
    continuousOn_chafaiDensity (n := k) (hcm.contDiffOn.of_le (nat_le_top k))
  filter_upwards [eventually_gt_atTop (max (2 * |x|) 2)] with T hT
  have hT2 : (2 : ℝ) < T := lt_of_le_of_lt (le_max_right (2 * |x|) 2) hT
  have hTpos : 0 < T := by linarith
  have hTabs : 2 * |x| < T := lt_of_le_of_lt (le_max_left (2 * |x|) 2) hT
  -- the shift is dominated by `T` in both directions, so `T - x` sits between `0` and `2 * T`
  have hTx_nonneg : 0 ≤ T - x := by linarith [le_abs_self x, abs_nonneg x]
  have hTx_le : T - x ≤ 2 * T := by linarith [neg_abs_le x, abs_nonneg x]
  have hhalf_nonneg : 0 ≤ T / 2 := by linarith
  have hhT_nonneg : 0 ≤ h T := h_nonneg T hTpos.le
  have h_interval_le :
      ∫ t in T / 2..T, chafaiDensity f k t ≤ ∫ t in Ioi (T / 2), chafaiDensity f k t := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact setIntegral_mono_set (hint_density.mono_set (Ioi_subset_Ioi hhalf_nonneg))
      ((ae_restrict_mem measurableSet_Ioi).mono fun t ht =>
        chafaiDensity_nonneg (lt_of_le_of_lt hhalf_nonneg ht).le
          (hcm.neg_one_pow_mul_iteratedDerivWithin_nonneg k (lt_of_le_of_lt hhalf_nonneg ht).le))
      (ae_of_all _ fun _ ht => Ioc_subset_Ioi_self ht)
  have hhalf_le :
      (T / 2) ^ k * h T ≤ ↑((k - 1).factorial) * ∫ t in Ioi (T / 2), chafaiDensity f k t := by
    have hfact_pos : (0 : ℝ) < ↑((k - 1).factorial) := Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hIcc_subset : Icc (T / 2) T ⊆ Ici 0 := fun t ht => le_trans hhalf_nonneg ht.1
    have hmul := mul_le_mul_of_nonneg_left
      ((const_le_intervalIntegral_chafaiDensity f k hk h h_antitone T hTpos.le
        (fun t _ => h_density_eq t)
        ((hcont_density.mono hIcc_subset).intervalIntegrable_of_Icc (by linarith))
        hhT_nonneg).trans h_interval_le) hfact_pos.le
    have hfact_cancel :
        ↑((k - 1).factorial) * ((1 / ↑((k - 1).factorial)) * (T / 2) ^ k * h T) =
          (T / 2) ^ k * h T := by field_simp
    rwa [hfact_cancel] at hmul
  calc
    (T - x) ^ k * h T ≤ (2 * T) ^ k * h T := by gcongr
    _ = (4 : ℝ) ^ k * ((T / 2) ^ k * h T) := by
      -- doubling the bound and halving the argument each cost a factor `2 ^ k`
      have h4 : (4 : ℝ) ^ k = 2 ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
      rw [mul_pow, div_pow, h4]
      field_simp
    _ ≤ (4 : ℝ) ^ k * (↑((k - 1).factorial) * ∫ t in Ioi (T / 2), chafaiDensity f k t) := by gcongr
    _ = ((4 : ℝ) ^ k * ↑((k - 1).factorial)) *
          ∫ t in Ioi (T / 2), chafaiDensity f k t := by ring

/-- **The weighted normalized derivative vanishes at infinity.** Let `f` be completely monotone,
let `k` be a nonzero order and let `x` be any real shift. Writing `h T` for the normalized
derivative
`(-1) ^ k * iteratedDerivWithin k f (Ici 0) T`, the products `(T - x) ^ k * h T` tend to `0` as
`T → ∞`. -/
private lemma tendsto_sub_pow_mul_normalized_iteratedDerivWithin (f : ℝ → ℝ)
    (hcm : IsCompletelyMonotone f) (k : ℕ) (hk : k ≠ 0) (x : ℝ) :
    Tendsto (fun T => (T - x) ^ k * ((-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) T))
      atTop (nhds 0) := by
  -- complete monotonicity already supplies the limit at infinity that integrability needs
  obtain ⟨L, hL, -⟩ :=
    (IsCompletelyMonotoneOnIci.of_isCompletelyMonotone hcm).exists_nonneg_tendsto_atTop
  set h := fun T => (-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) T
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
  obtain ⟨h_nonneg₀, h_antitone₀⟩ :=
    normalized_iteratedDerivWithin_nonneg_antitone f hcm k
  have h_nonneg : ∀ T, 0 ≤ T → 0 ≤ h T := by simpa [h] using h_nonneg₀
  have h_antitone : AntitoneOn h (Ici 0) := by simpa [h] using h_antitone₀
  have hint_density : IntegrableOn (chafaiDensity f k) (Ioi 0) :=
    chafaiDensity_integrableOn_Ioi_of_tendsto f hcm k hk1 L hL
  -- `tendsto_integral_Ioi_zero` takes the cut point along any map to `atTop`, so `T / 2` needs
  -- no separate composition argument.
  have htail_half : Tendsto (fun T : ℝ => ∫ t in Ioi (T / 2), chafaiDensity f k t)
      atTop (nhds 0) :=
    tendsto_integral_Ioi_zero (b := fun T : ℝ => T / 2)
      (tendsto_id.atTop_div_const (by norm_num))
  have hupper := density_tail_lower_bound_eventually f hcm k hk x h h_nonneg h_antitone
    (by
      intro t
      rw [chafaiDensity_of_ne_zero hk]
      simp only [h]
      field_simp)
    hint_density
  have hnonneg_event : ∀ᶠ T in atTop, 0 ≤ (T - x) ^ k * h T := by
    filter_upwards [eventually_gt_atTop (max x 0)] with T hT
    have hT0 : 0 < T := lt_of_le_of_lt (le_max_right x 0) hT
    have hxT : x < T := lt_of_le_of_lt (le_max_left x 0) hT
    exact mul_nonneg (pow_nonneg (sub_nonneg.mpr hxT.le) _) (h_nonneg T hT0.le)
  have hupper_tendsto :
      Tendsto (fun T : ℝ =>
        ((4 : ℝ) ^ k * ↑((k - 1).factorial)) *
          ∫ t in Ioi (T / 2), chafaiDensity f k t) atTop (nhds 0) := by
    simpa [mul_zero] using htail_half.const_mul (((4 : ℝ) ^ k) * ↑((k - 1).factorial))
  -- squeeze between nonnegativity and the vanishing tail bound
  exact squeeze_zero' hnonneg_event hupper hupper_tendsto

/-- **The shifted order-`k` kernel is dominated by the Chafaï density.** For `0 ≤ x ≤ t` the
kernel built from `(t - x) ^ (k - 1)` is nonnegative and bounded by the density built from
`t ^ (k - 1)`. -/
private lemma norm_ibp_kernel_le_chafaiDensity (f : ℝ → ℝ)
    {k : ℕ} (hk0 : k ≠ 0) {x t : ℝ} (hx : 0 ≤ x) (ht : x ≤ t)
    (hcm_sign : 0 ≤ (-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) t) :
    ‖(-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
      iteratedDerivWithin k f (Ici 0) t‖ ≤ chafaiDensity f k t := by
  have htx : 0 ≤ t - x := by linarith
  have htx_le : t - x ≤ t := by linarith
  rw [chafaiDensity_of_ne_zero hk0]
  have hfact : (0 : ℝ) < ↑(k - 1).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hval_nn : 0 ≤ (-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
      iteratedDerivWithin k f (Ici 0) t := by
    calc
      (-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
          iteratedDerivWithin k f (Ici 0) t
          = (t - x) ^ (k - 1) / ↑(k - 1).factorial *
            ((-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) t) := by field_simp
      _ ≥ 0 := mul_nonneg (div_nonneg (pow_nonneg htx _) hfact.le) hcm_sign
  rw [Real.norm_eq_abs, abs_of_nonneg hval_nn]
  calc
    (-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
        iteratedDerivWithin k f (Ici 0) t
        = (1 / ↑(k - 1).factorial) * (t - x) ^ (k - 1) *
          ((-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) t) := by field_simp
    _ ≤ (1 / ↑(k - 1).factorial) * t ^ (k - 1) *
        ((-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) t) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ htx htx_le _) (by positivity))
            hcm_sign
    _ = (-1 : ℝ) ^ k / ↑(k - 1).factorial * t ^ (k - 1) *
        iteratedDerivWithin k f (Ici 0) t := by field_simp

private lemma ibp_kernel_integrableOn (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (hx : 0 ≤ x) (L : ℝ) (hL : Tendsto f atTop (nhds L)) :
    IntegrableOn (fun t => (-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
      iteratedDerivWithin k f (Ici 0) t) (Ioi x) := by
  have hk0 : k ≠ 0 := by omega
  have hint_density : IntegrableOn (chafaiDensity f k) (Ioi 0) :=
    chafaiDensity_integrableOn_Ioi_of_tendsto f hcm k hk L hL
  apply Integrable.mono' (hint_density.mono_set (Ioi_subset_Ioi hx))
  · apply (ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi)
    exact ((continuousOn_const.mul
      ((continuousOn_id.sub continuousOn_const).pow _)).mul
      ((hcm.contDiffOn.continuousOn_iteratedDerivWithin (nat_le_top k)
        (uniqueDiffOn_Ici 0)).mono
        (fun t ht => mem_Ici.mpr (lt_of_le_of_lt hx ht).le)))
  · rw [ae_restrict_iff' measurableSet_Ioi]
    exact ae_of_all _ fun t ht => norm_ibp_kernel_le_chafaiDensity f hk0 hx (le_of_lt ht)
      (hcm.neg_one_pow_mul_iteratedDerivWithin_nonneg k (le_trans hx (le_of_lt ht)))

/-- Raising the sign exponent of the order-`k` kernel by one negates its integral. -/
private lemma intervalIntegral_neg_one_pow_succ_kernel (f : ℝ → ℝ) (k : ℕ) (x T : ℝ) :
    ∫ t in x..T, (-1 : ℝ) ^ (k + 1) / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
        iteratedDerivWithin k f (Ici 0) t =
      -(∫ t in x..T, (-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
        iteratedDerivWithin k f (Ici 0) t) := by
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr_ae (ae_of_all _ fun t _ => ?_)
  rw [pow_succ (-1 : ℝ) k]
  ring

/-- For a completely monotone `f` with limit `L` at infinity, `0 ≤ x` and `k ≠ 0`, the order-`k`
kernel identity implies the order-`k + 1` one: if the order-`k` kernel integrates against the
`k`-th derivative to `f x - L` on `(x, ∞)`, then so does the order-`k + 1` kernel against the
`(k + 1)`-st derivative. -/
private lemma chafai_repeated_ibp_succ (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (k : ℕ) (hk : k ≠ 0) (x : ℝ) (hx : 0 ≤ x) (L : ℝ) (hL : Tendsto f atTop (nhds L))
    (ih : ∫ t in Ioi x, (-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
      iteratedDerivWithin k f (Ici 0) t = f x - L) :
    ∫ t in Ioi x, (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (t - x) ^ k *
      iteratedDerivWithin (k + 1) f (Ici 0) t = f x - L := by
  -- Integrate by parts on `[x, T]`; the boundary term decays, so `T → ∞` transfers `ih`.
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
  have hintk := ibp_kernel_integrableOn f hcm k hk1 x hx L hL
  have hintkp1 := ibp_kernel_integrableOn f hcm (k + 1) (by omega) x hx L hL
  simp only [show k + 1 - 1 = k by omega] at hintkp1
  have htend_k : Tendsto (fun T => ∫ t in x..T,
      (-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
      iteratedDerivWithin k f (Ici 0) t) atTop (nhds (f x - L)) := by
    rw [← ih]
    exact intervalIntegral_tendsto_integral_Ioi x hintk tendsto_id
  have htend_sum : Tendsto (fun T =>
      (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (T - x) ^ k *
        iteratedDerivWithin k f (Ici 0) T +
      ∫ t in x..T, (-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
        iteratedDerivWithin k f (Ici 0) t) atTop (nhds (f x - L)) := by
    have hbdry : Tendsto (fun T => (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (T - x) ^ k *
        iteratedDerivWithin k f (Ici 0) T) atTop (nhds 0) := by
      have heq : ∀ T, -(1 / (k.factorial : ℝ)) *
          ((T - x) ^ k * ((-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) T)) =
          (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (T - x) ^ k *
            iteratedDerivWithin k f (Ici 0) T := fun T => by
        simp only [pow_succ]
        ring
      simpa using
        (((tendsto_sub_pow_mul_normalized_iteratedDerivWithin f hcm k hk x).const_mul
          (-(1 / (k.factorial : ℝ)))).congr heq)
    simpa [zero_add] using hbdry.add htend_k
  have htend_via_ibp : Tendsto (fun T => ∫ t in x..T,
      (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (t - x) ^ k *
      iteratedDerivWithin (k + 1) f (Ici 0) t) atTop (nhds (f x - L)) :=
    Tendsto.congr' ((eventually_gt_atTop x).mono fun T hxT => by
      have := ibp_finite_interval f hcm k hk x T hx hxT
      linarith [intervalIntegral_neg_one_pow_succ_kernel f k x T]) htend_sum
  exact tendsto_nhds_unique
    ((intervalIntegral_tendsto_integral_Ioi x hintkp1 tendsto_id).congr
      (fun T => by simp [id])) htend_via_ibp

/-- **Repeated integration by parts for a completely monotone function.** For `n ≥ 1`, `0 ≤ x`
and `f` tending to `L` at infinity, integrating the order-`n` kernel
`(-1) ^ n / (n - 1)! * (t - x) ^ (n - 1)` against the `n`-th derivative of `f` over `(x, ∞)`
recovers `f x - L`. This is the analytic identity behind the Chafaï reconstruction of `f` from
its derivatives. -/
private lemma chafai_repeated_ibp (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : 0 ≤ x) (L : ℝ) (hL : Tendsto f atTop (nhds L)) :
    ∫ t in Ioi x, (-1 : ℝ) ^ n / ↑(n - 1).factorial *
      (t - x) ^ (n - 1) *
      iteratedDerivWithin n f (Ici 0) t = f x - L := by
  induction n with
  | zero => omega
  | succ k ih =>
    by_cases hk : k = 0
    · subst hk
      simpa using hcm.integral_Ioi_neg_iteratedDerivWithin_one_of_nonneg hx hL
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      simp only [show k + 1 - 1 = k by omega]
      exact chafai_repeated_ibp_succ f hcm k hk x hx L hL (ih hk1)

/-- **Chafaï reconstruction identity** for the nonconstant part. -/
lemma chafaiRescaled_integral_bernsteinKernel_eq_sub_tendsto_atTop
    (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f) (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (hx : 0 ≤ x)
    (L : ℝ) (hL : Tendsto f atTop (nhds L)) :
    ∫ p, bernsteinKernel n x (p : ℝ) ∂(chafaiRescaled f n) = f x - L := by
  have h_integral_pullback :
      ∫ p : ℝ≥0, bernsteinKernel n x (p : ℝ) ∂(chafaiRescaled f n) =
        ∫ t, bernsteinKernel n x (chafaiRescaling n t : ℝ) ∂(chafaiMeasure f n) := by
    exact chafaiRescaled_integral f n
      ((measurable_bernsteinKernel n x).comp (by fun_prop : Measurable fun p : ℝ≥0 => (p : ℝ))
        |>.aestronglyMeasurable)
  have h_integral_density :
      ∫ t, bernsteinKernel n x (chafaiRescaling n t : ℝ) ∂(chafaiMeasure f n) =
        ∫ t in Ioi 0,
          bernsteinKernel n x (((n : ℝ) - 1) / t) * chafaiDensity f n t := by
    rw [chafaiMeasure_eq_withDensity]
    have hcont_density : ContinuousOn (chafaiDensity f n) (Ici 0) :=
      continuousOn_chafaiDensity (n := n) (hcm.contDiffOn.of_le (nat_le_top n))
    rw [integral_withDensity_eq_integral_toReal_smul₀
      (AEMeasurable.ennreal_ofReal
        ((hcont_density.mono Ioi_subset_Ici_self).aestronglyMeasurable
          measurableSet_Ioi |>.aemeasurable))
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    exact setIntegral_congr_ae measurableSet_Ioi
      (ae_of_all _ fun t ht => by
        simp only [smul_eq_mul, mem_Ioi] at ht ⊢
        rw [chafaiRescaling_coe_of_pos (by omega : 1 ≤ n) ht]
        rw [ENNReal.toReal_ofReal
          (chafaiDensity_nonneg ht.le
            (hcm.neg_one_pow_mul_iteratedDerivWithin_nonneg n ht.le))]
        ring)
  have hkernel := chafai_kernel_density_eq f n hn x hx
  have hibp := chafai_repeated_ibp f hcm n (by omega) x hx L hL
  rw [h_integral_pullback, h_integral_density, hkernel]
  exact hibp

private lemma bernsteinKernel_le_exp {n : ℕ} (hn : 2 ≤ n) {x p : ℝ} (_hx : 0 ≤ x) (_hp : 0 ≤ p) :
    bernsteinKernel n x p ≤ Real.exp (-(x * p)) := by
  rw [bernsteinKernel_of_two_le hn]
  by_cases h : 1 - x * p / ↑(n - 1) ≤ 0
  · rw [max_eq_right h]
    rw [zero_pow (by omega : n - 1 ≠ 0)]
    exact le_of_lt (Real.exp_pos _)
  · push Not at h
    rw [max_eq_left h.le]
    have hden_pos : (0 : ℝ) < ↑(n - 1) := Nat.cast_pos.mpr (by omega)
    have hle : 1 - x * p / ↑(n - 1) ≤ Real.exp (-(x * p / ↑(n - 1))) := by
      linarith [Real.add_one_le_exp (-(x * p / ↑(n - 1)))]
    calc
      (1 - x * p / ↑(n - 1)) ^ (n - 1)
          ≤ (Real.exp (-(x * p / ↑(n - 1)))) ^ (n - 1) :=
            pow_le_pow_left₀ h.le hle _
      _ = Real.exp (↑(n - 1) * -(x * p / ↑(n - 1))) := by
            rw [← Real.exp_nat_mul]
      _ = Real.exp (-(x * p)) := by
            congr 1
            field_simp [hden_pos.ne']

/-- **Local error bound for the Bernstein truncation.** For `0 ≤ u < 1` and `m : ℕ`, the
difference `exp (-(m·u)) - (1 - u) ^ m` is bounded above by the second-order term
`m·u² / (1 - u)`. This is the pointwise estimate driving the uniform convergence of the
Bernstein kernel to the Laplace kernel. -/
private lemma exp_neg_mul_sub_one_sub_pow_le (u : ℝ) (hu_nn : 0 ≤ u) (hu_lt_1 : u < 1) (m : ℕ) :
    Real.exp (-(↑m * u)) - (1 - u) ^ m ≤ ↑m * u ^ 2 / (1 - u) := by
  have h1u : 0 < 1 - u := by linarith
  -- The logarithmic lower bound converts the power into an exponential with a Taylor-tail term.
  have hpow_ge : (1 - u) ^ m ≥ Real.exp (-(↑m * u) - ↑m * u ^ 2 / (1 - u)) := by
    have heq : (1 - u) ^ m = Real.exp (↑m * Real.log (1 - u)) := by
      rw [← Real.rpow_natCast (1 - u) m, Real.rpow_def_of_pos h1u, mul_comm]
    rw [heq]
    gcongr
    have hfactor : -(↑m * u) - ↑m * u ^ 2 / (1 - u) = ↑m * (-u - u ^ 2 / (1 - u)) := by ring
    rw [hfactor]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg m)
    have habs : |u| < 1 := by rwa [abs_of_nonneg hu_nn]
    have hlog := Real.abs_log_sub_add_sum_range_le habs 1
    simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, div_one, pow_one] at hlog
    have hu_sq : u ^ (1 + 1) = u ^ 2 := by ring
    rw [abs_of_nonneg hu_nn, hu_sq] at hlog
    linarith [(abs_le.mp hlog).1]
  set b := ↑m * u ^ 2 / (1 - u) with hb_def
  have hb_nn : 0 ≤ b := div_nonneg (mul_nonneg (Nat.cast_nonneg m) (sq_nonneg u)) h1u.le
  have hmu_nn : 0 ≤ ↑m * u := mul_nonneg (Nat.cast_nonneg m) hu_nn
  -- `exp` sits above its tangent line at `0`, so the exponential gap is at most `b`.
  suffices h : Real.exp (-(↑m * u)) - Real.exp (-(↑m * u) - b) ≤ b by linarith
  have hsplit : Real.exp (-(↑m * u) - b) = Real.exp (-(↑m * u)) * Real.exp (-b) := by
    rw [← Real.exp_add]
    ring_nf
  rw [hsplit]
  nlinarith [Real.exp_pos (-(↑m * u)), Real.exp_pos (-b),
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr hmu_nn), Real.add_one_le_exp (-b)]

/-- **Compact-support tail estimate.** Once `M` exceeds `C + 2C²/ε`, the error parameter
`xp² / (M - xp)` stays below `ε / 2` for every `0 ≤ xp ≤ C`. Positivity of `M - C` follows
from the size hypothesis, so the only inputs are the pointwise bounds on `xp`. -/
private lemma sq_div_sub_lt_div_two (xp C ε M : ℝ) (hxp_nn : 0 ≤ xp) (hxp_le_C : xp ≤ C)
    (hε : 0 < ε) (hM : 2 * C ^ 2 / ε < M - C) :
    xp ^ 2 / (M - xp) < ε / 2 := by
  have haux : 0 ≤ 2 * C ^ 2 / ε := div_nonneg (by positivity) hε.le
  have hMC_pos : 0 < M - C := by linarith
  -- Monotone in the numerator and the denominator: `xp²/(M-xp) ≤ C²/(M-C)`.
  have hmono : xp ^ 2 / (M - xp) ≤ C ^ 2 / (M - C) :=
    div_le_div₀ (sq_nonneg C) (sq_le_sq' (by linarith) hxp_le_C) hMC_pos (by linarith)
  -- The size hypothesis on `M` forces `C²/(M-C) < ε/2`.
  have hsmall : C ^ 2 / (M - C) < ε / 2 := by
    rw [div_lt_div_iff₀ hMC_pos (by positivity : (0 : ℝ) < 2)]
    have h2 : ε * (M - C) > ε * (2 * C ^ 2 / ε) := mul_lt_mul_of_pos_left hM hε
    rw [mul_div_cancel₀ _ (ne_of_gt hε)] at h2
    linarith
  linarith

private lemma kernel_uniform_conv_compact (x R ε : ℝ) (hx : 0 < x) (hR : 0 < R) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ p, 0 ≤ p → p ≤ R →
      |bernsteinKernel n x p - Real.exp (-(x * p))| < ε := by
  set C := x * R
  have hC_pos : 0 < C := mul_pos hx hR
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (C + 2 + 2 * C ^ 2 / ε)
  refine ⟨N₀, fun n hn p hp hpR => ?_⟩
  have hn_gt : (↑n : ℝ) > C + 2 + 2 * C ^ 2 / ε := lt_of_lt_of_le hN₀ (Nat.cast_le.mpr hn)
  have haux : 0 ≤ 2 * C ^ 2 / ε := div_nonneg (by positivity) hε.le
  have hn_ge2 : 2 ≤ n := by exact_mod_cast (show (2 : ℝ) < ↑n by linarith [hC_pos]).le
  have hle := bernsteinKernel_le_exp hn_ge2 hx.le hp
  rw [abs_of_nonpos (by linarith), neg_sub]
  set m := n - 1
  have hm_pos : (0 : ℝ) < ↑m := Nat.cast_pos.mpr (by omega)
  have hm_eq : (↑m : ℝ) = ↑n - 1 := by rw [Nat.cast_sub (show 1 ≤ n by omega)]; simp
  have hxp_nn : 0 ≤ x * p := mul_nonneg hx.le hp
  have hxp_le_C : x * p ≤ C := mul_le_mul_of_nonneg_left hpR hx.le
  set u := x * p / ↑m with hu_def
  have hu_nn : 0 ≤ u := div_nonneg hxp_nn hm_pos.le
  have hu_lt_1 : u < 1 := by rw [div_lt_one hm_pos]; linarith [hm_eq]
  have hkernel_eq : bernsteinKernel n x p = (1 - u) ^ m := by
    rw [bernsteinKernel_of_two_le hn_ge2]
    congr 1
    exact max_eq_left (by
      -- `max_eq_left` needs the truncated factor `1 - x*p/m` nonneg; expose it as the defeq goal.
      change 0 ≤ 1 - x * p / (↑m : ℝ)
      rw [← hu_def]; linarith)
  rw [hkernel_eq]
  set b := ↑m * u ^ 2 / (1 - u) with hb_def
  have hmu : ↑m * u = x * p := by simp only [hu_def]; field_simp [hm_pos.ne']
  -- Assemble the two phase estimates: the local error is `≤ b`, and `b < ε/2` on `p ≤ R`.
  have hstep : Real.exp (-(x * p)) - (1 - u) ^ m ≤ b := by
    rw [hb_def, ← hmu]
    exact exp_neg_mul_sub_one_sub_pow_le u hu_nn hu_lt_1 m
  have hb_eq : b = (x * p) ^ 2 / (↑m - x * p) := by
    simp only [hb_def, hu_def]
    field_simp [hm_pos.ne']
  have hb_small : b < ε / 2 := by
    rw [hb_eq]
    exact sq_div_sub_lt_div_two (x * p) C ε ↑m hxp_nn hxp_le_C hε (by linarith [hm_eq])
  linarith

private lemma kernel_uniform_conv (x : ℝ) (hx : 0 < x) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ p, 0 ≤ p →
      |bernsteinKernel n x p - Real.exp (-(x * p))| < ε := by
  have htail : Tendsto (fun R => Real.exp (-(x * R))) atTop (nhds 0) := by
    apply Tendsto.comp Real.tendsto_exp_neg_atTop_nhds_zero
    exact tendsto_id.const_mul_atTop hx
  obtain ⟨R₀, hR₀⟩ := Metric.tendsto_atTop.mp htail (ε / 2) (half_pos hε)
  set R := max R₀ 1
  have hR_pos : 0 < R := lt_of_lt_of_le one_pos (le_max_right R₀ 1)
  have hR_tail : Real.exp (-(x * R)) < ε / 2 := by
    have h1 := hR₀ R (le_max_left _ _)
    rwa [dist_zero_right, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h1
  obtain ⟨N₁, hN₁⟩ := kernel_uniform_conv_compact x R (ε / 2) hx hR_pos (half_pos hε)
  refine ⟨max N₁ 2, fun n hn p hp => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_right N₁ 2) hn
  by_cases hpR : p ≤ R
  · linarith [hN₁ n (le_trans (le_max_left _ _) hn) p hp hpR]
  · push Not at hpR
    have h1 := bernsteinKernel_le_exp hn2 hx.le hp
    rw [abs_of_nonpos (by linarith)]
    have h2 : Real.exp (-(x * p)) ≤ Real.exp (-(x * R)) := by
      apply Real.exp_le_exp_of_le
      linarith [mul_le_mul_of_nonneg_left (le_of_lt hpR) hx.le]
    linarith [bernsteinKernel_nonneg n x p]

/-- Bernstein-to-Laplace replacement against a uniformly finite sequence of measures. -/
lemma integral_bernsteinKernel_sub_laplaceKernel_tendsto_zero_of_mass_bound (σ : ℕ → Measure ℝ≥0)
    (hmass : ∀ᶠ n in atTop, (σ n) univ ≤ ENNReal.ofReal C) (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun n => ∫ p : ℝ≥0,
        (bernsteinKernel n x (p : ℝ) - Real.exp (-(x * (p : ℝ)))) ∂(σ n))
      atTop (nhds 0) := by
  by_cases hx0 : x = 0
  · subst hx0
    suffices h : ∀ᶠ n in atTop, ∫ p : ℝ≥0,
        (bernsteinKernel n 0 (p : ℝ) - Real.exp (-(0 * (p : ℝ)))) ∂(σ n) = 0 by
      exact Tendsto.congr' (EventuallyEq.symm h) tendsto_const_nhds
    filter_upwards [eventually_ge_atTop 2] with n hn
    apply integral_eq_zero_of_ae
    apply ae_of_all
    intro p
    -- At `x = 0` the integrand is defeq to this explicit difference; expose it before rewriting.
    change bernsteinKernel n 0 (p : ℝ) - Real.exp (-(0 * (p : ℝ))) = 0
    rw [bernsteinKernel_of_two_le hn]
    simp
  · have hx_pos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hmax_pos : 0 < max C 1 := lt_max_of_lt_right one_pos
    obtain ⟨N, hN⟩ := kernel_uniform_conv x hx_pos
      (ε / (2 * max C 1)) (div_pos hε (by positivity))
    refine eventually_atTop.1 <| ((eventually_ge_atTop N).and hmass).mono fun n hn => ?_
    rcases hn with ⟨hn, hmass_n⟩
    rw [dist_zero_right]
    have : IsFiniteMeasure (σ n) := ⟨hmass_n.trans_lt ENNReal.ofReal_lt_top⟩
    calc
      ‖∫ p : ℝ≥0, (bernsteinKernel n x (p : ℝ) - Real.exp (-(x * (p : ℝ)))) ∂(σ n)‖
          ≤ ∫ p : ℝ≥0,
              ‖bernsteinKernel n x (p : ℝ) - Real.exp (-(x * (p : ℝ)))‖ ∂(σ n) :=
            norm_integral_le_integral_norm _
      _ ≤ ∫ _ : ℝ≥0, (ε / (2 * max C 1)) ∂(σ n) := by
          apply integral_mono_of_nonneg
            (ae_of_all _ fun _ => norm_nonneg _) (integrable_const _)
          exact ae_of_all _ fun p => by
            simpa [Real.norm_eq_abs] using le_of_lt (hN n hn (p : ℝ) p.2)
      _ = ε / (2 * max C 1) * ((σ n) univ).toReal := by
          simp [MeasureTheory.integral_const, smul_eq_mul, Measure.real, mul_comm]
      _ ≤ ε / (2 * max C 1) * max C 1 := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt (div_pos hε (by positivity)))
          exact ENNReal.toReal_le_of_le_ofReal (le_of_lt hmax_pos)
            (le_trans hmass_n (ENNReal.ofReal_le_ofReal (le_max_left C 1)))
      _ = ε / 2 := by field_simp
      _ < ε := half_lt_self hε

/-- Weak convergence of the rescaled Chafaï measures specializes to the Laplace kernel:
if all bounded-continuous test integrals for `chafaiRescaled f n` converge to those for `μ₀`,
then the integrals of `p ↦ exp (-x * p)` converge for every `x ≥ 0`. -/
lemma chafaiRescaled_tendsto_laplace_integral_of_weak {μ₀ : Measure ℝ≥0} {l : Filter ℕ}
    (hweak : ∀ g : BoundedContinuousFunction ℝ≥0 ℝ,
        Tendsto (fun n => ∫ p, g p ∂(chafaiRescaled f n)) l
          (nhds (∫ p, g p ∂μ₀)))
    {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n => ∫ p, Real.exp (-(x * (p : ℝ))) ∂(chafaiRescaled f n)) l
      (nhds (∫ p, Real.exp (-(x * (p : ℝ))) ∂μ₀)) := by
  simpa using hweak (laplaceKernelBoundedContinuous hx)

end TauCeti
end

/- TauCeti.Analysis.CompletelyMonotone.Bernstein.Tightness -/
noncomputable section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/






/-!
# Tightness of the Chafaï approximating measures

This file proves the tightness input for the Prokhorov extraction step in Bernstein's theorem.
For a completely monotone function `f`, the rescaled Chafaï measures have uniformly bounded
first moment:

`∫⁻ p, p ∂(chafaiRescaled f n) ≤ -f'(0)`.

Markov's inequality therefore bounds their mass outside `[0, R]` by `-f'(0) / R`, uniformly in
`n`. Since the intervals `[0, R]` are compact in `ℝ≥0`, this proves that the whole family is
tight.

## Main declarations

* `TauCeti.chafaiRescaled_measure_Ioi_le`: the uniform first-moment tail bound.
* `TauCeti.isTightMeasureSet_range_chafaiRescaled`: the rescaled Chafaï measures form a tight
  family.

## References

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B, Bernstein's theorem
  milestone (“measure extraction via Prokhorov tightness”).
* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012), Ch. 1.
* D. Chafaï, *Aspects of the Bernstein theorem* (2013).
-/


open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {f : ℝ → ℝ}

/-- The rescaled Chafaï measures satisfy the uniform Markov tail estimate

`chafaiRescaled f n (R, ∞) ≤ ofReal (-f'(0)) / R`

for every positive `R`. The derivative is taken within `[0, ∞)`, as in the definition of
complete monotonicity. -/
lemma chafaiRescaled_measure_Ioi_le (hcm : IsCompletelyMonotone f) (n : ℕ) {R : ℝ≥0} (hR : R ≠ 0) :
    chafaiRescaled f n (Ioi R) ≤
      ENNReal.ofReal (-derivWithin f (Ici 0) 0) / (R : ℝ≥0∞) := by
  let μ := chafaiRescaled f n
  let moment : ℝ≥0 → ℝ≥0∞ := fun p => ENNReal.ofReal (p : ℝ)
  have hmoment_meas : AEMeasurable moment μ :=
    (ENNReal.measurable_ofReal.comp (by fun_prop : Measurable fun p : ℝ≥0 => (p : ℝ)))
      |>.aemeasurable
  have hsubset : Ioi R ⊆ {p | (R : ℝ≥0∞) ≤ moment p} := by
    intro p hp
    simpa [moment, ENNReal.ofReal_coe_nnreal] using hp.le
  calc
    μ (Ioi R) ≤ μ {p | (R : ℝ≥0∞) ≤ moment p} := measure_mono hsubset
    _ ≤ (∫⁻ p, moment p ∂μ) / (R : ℝ≥0∞) :=
      meas_ge_le_lintegral_div hmoment_meas (by simpa using hR) (by simp)
    _ ≤ ENNReal.ofReal (-derivWithin f (Ici 0) 0) / (R : ℝ≥0∞) :=
      ENNReal.div_le_div_right (chafaiRescaled_lintegral_coe_le f hcm n) _

/-- The family of all rescaled Chafaï approximating measures of a completely monotone function
is tight. Equivalently, for every positive error tolerance there is a compact interval
`[0, R] ⊆ ℝ≥0` whose complement has at most that much mass for every approximation order. -/
theorem isTightMeasureSet_range_chafaiRescaled (hcm : IsCompletelyMonotone f) :
    IsTightMeasureSet (range (chafaiRescaled f)) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  by_cases hε_top : ε = ∞
  · refine ⟨∅, isCompact_empty, fun μ _ => ?_⟩
    simp [hε_top]
  let D : ℝ≥0 := ⟨-derivWithin f (Ici 0) 0,
    neg_nonneg.mpr (hcm.derivWithin_nonpos le_rfl)⟩
  let R : ℝ≥0 := D / ε.toNNReal + 1
  have hR : R ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_add_self))
  have hcompact : IsCompact (Iic R) := by
    have hset : Iic R = Icc (0 : ℝ≥0) R := by
      ext p
      simp
    rw [hset]
    exact isCompact_Icc
  refine ⟨Iic R, hcompact, ?_⟩
  intro μ hμ
  obtain ⟨n, rfl⟩ := hμ
  rw [compl_Iic]
  refine (chafaiRescaled_measure_Ioi_le hcm n hR).trans ?_
  have hD : ENNReal.ofReal (-derivWithin f (Ici 0) 0) = (D : ℝ≥0∞) := by
    exact (ENNReal.coe_nnreal_eq D).symm
  rw [hD]
  have hR_gt : D / ε.toNNReal < R := lt_add_one _
  have hε_toNNReal : ε.toNNReal ≠ 0 :=
    ENNReal.toNNReal_ne_zero.mpr ⟨hε.ne', hε_top⟩
  have hR_gt' : (D : ℝ≥0∞) / (ε.toNNReal : ℝ≥0∞) < (R : ℝ≥0∞) := by
    rw [← ENNReal.coe_div hε_toNNReal]
    exact_mod_cast hR_gt
  rw [ENNReal.coe_toNNReal hε_top] at hR_gt'
  exact (ENNReal.div_le_iff (by simpa using hR) (by simp)).2
    ((ENNReal.div_le_iff' hε.ne' hε_top).1 hR_gt'.le)

end TauCeti
end

/- TauCeti.MeasureTheory.Measure.Prokhorov -/
noncomputable section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/




/-!
# Weak cluster limits of tight finite measures

This file contains a generic finite-measure extraction lemma based on Mathlib's Prokhorov
compactness theorem for finite measures. It has no real-line support condition and no
normalization step: tightness and a uniform mass bound place the sequence in a compact set of
`FiniteMeasure`s, and compactness gives a weak cluster limit.

## Main declarations

* `TauCeti.finite_measure_cluster_limit`: a tight, mass-bounded sequence of finite measures has a
  weak cluster limit along an ultrafilter below `atTop`.
* `TauCeti.finite_measure_subseq_limit`: the corresponding subsequence form when the weak topology
  on `FiniteMeasure α` is first-countable.

## References

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B (Bernstein theorem milestone).
-/


open MeasureTheory Set Filter Topology
open scoped NNReal Topology

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
  [T2Space α] [BorelSpace α]

omit [T2Space α] [BorelSpace α] in
/-- A tight family of measures admits a **monotone** exhaustion by compact sets whose complements
carry uniformly small mass: given tolerances `u j > 0`, there are compact `K j`, increasing in `j`,
with `σ n (K j)ᶜ ≤ u j` for every `n`. Accumulating the sets supplied by tightness is what turns
the unrelated compact sets into the monotone family Mathlib's Prokhorov criterion expects. -/
private lemma exists_monotone_isCompact_measure_compl_le
    {σ : ℕ → Measure α} (hTight : IsTightMeasureSet (Set.range σ))
    {u : ℕ → ℝ≥0} (hu_pos : ∀ j, 0 < u j) :
    ∃ K : ℕ → Set α, Monotone K ∧ (∀ j, IsCompact (K j)) ∧
      ∀ j n, (σ n) (K j)ᶜ ≤ (u j : ENNReal) := by
  have hchoose : ∀ j, ∃ K : Set α, IsCompact K ∧ ∀ n, (σ n) Kᶜ ≤ (u j : ENNReal) := by
    intro j
    obtain ⟨K, hK, htail⟩ :=
      isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp hTight
        (u j : ENNReal) (by exact_mod_cast hu_pos j)
    exact ⟨K, hK, fun n => htail (σ n) (Set.mem_range_self n)⟩
  choose K hK_comp hK_tail using hchoose
  refine ⟨Set.accumulate K, Set.monotone_accumulate,
    fun j => isCompact_accumulate hK_comp j, fun j n => ?_⟩
  exact (measure_mono (compl_subset_compl.mpr (Set.subset_accumulate (s := K) (x := j)))).trans
    (hK_tail j n)

/-- A tight, uniformly mass-bounded sequence of finite measures has a weak cluster limit.

Given tightness of the sequence and a common total-mass bound, the conclusion is a finite limiting
measure with the same mass bound and weak convergence of all bounded-continuous test-function
integrals along an ultrafilter `U ≤ atTop`; no first-countability assumption on `FiniteMeasure α`
is needed. -/
lemma finite_measure_cluster_limit (σ : ℕ → Measure α) (C : ℝ≥0)
    (hmass : ∀ n, (σ n) univ ≤ (C : ENNReal)) (hTight : IsTightMeasureSet (Set.range σ)) :
    ∃ (μ₀ : Measure α) (U : Ultrafilter ℕ), (U : Filter ℕ) ≤ atTop ∧ IsFiniteMeasure μ₀ ∧
      μ₀ univ ≤ (C : ENNReal) ∧
      ∀ g : BoundedContinuousFunction α ℝ,
        Tendsto (fun n => ∫ x, g x ∂(σ n)) (U : Filter ℕ)
          (nhds (∫ x, g x ∂μ₀)) := by
  -- First coerce the sequence to `FiniteMeasure`; the uniform mass bound supplies finiteness.
  have hfin : ∀ n, IsFiniteMeasure (σ n) := fun n =>
    ⟨(hmass n).trans_lt ENNReal.coe_lt_top⟩
  let σf : ℕ → FiniteMeasure α := fun n => ⟨σ n, hfin n⟩
  -- Choose a positive sequence decreasing to zero; these values are the tail tolerances in
  -- Prokhorov's compact set criterion.
  obtain ⟨u, -, hu_pos, hu_lim⟩ :
      ∃ u : ℕ → ℝ≥0, StrictAnti u ∧ (∀ n, 0 < u n) ∧ Tendsto u atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto 0
  obtain ⟨K, hKmono, hK_comp, hK_tail⟩ :=
    exists_monotone_isCompact_measure_compl_le hTight hu_pos
  let S : Set (FiniteMeasure α) := {μ | μ.mass ≤ C ∧ ∀ j, μ (K j)ᶜ ≤ u j}
  have hcompact : IsCompact S := by
    simpa [S] using
      isCompact_setOfPred_finiteMeasure_mass_le_compl_isCompact_le
        (E := α) (C := C) (u := u) (K := K) hu_lim hK_comp (Or.inr hKmono)
  -- The finite-measure sequence lies in the compact Prokhorov set.
  have hσ_mem : ∀ n, σf n ∈ S := by
    refine fun n => ⟨?_, fun j => ?_⟩
    · dsimp [σf, S, FiniteMeasure.mass]
      exact ENNReal.coe_le_coe.mp (by simpa using hmass n)
    · exact ENNReal.coe_le_coe.mp (by simpa [σf] using hK_tail j n)
  -- Compactness gives a cluster point and an ultrafilter below `atTop` along which `σf`
  -- converges weakly.
  have hmap_le : map σf atTop ≤ 𝓟 S :=
    tendsto_principal.mpr (Eventually.of_forall hσ_mem)
  obtain ⟨μf, hμfS, hcluster⟩ := hcompact hmap_le
  have hmapcluster : MapClusterPt μf atTop σf := hcluster
  obtain ⟨U, hUle, hUtend⟩ := mapClusterPt_iff_ultrafilter.mp hmapcluster
  refine ⟨(μf : Measure α), U, hUle, inferInstance, ?_, ?_⟩
  -- Finally unwrap the compact-set membership into the mass bound and weak convergence of
  -- integrals against bounded continuous test functions.
  · have hle : (μf.mass : ENNReal) ≤ (C : ENNReal) := ENNReal.coe_le_coe.mpr hμfS.1
    rw [← FiniteMeasure.ennreal_mass]
    simpa using hle
  · intro g
    have hweak :=
      (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hUtend) g
    simpa [σf] using hweak

end TauCeti
end

/- TauCeti.Analysis.CompletelyMonotone.Bernstein.Theorem -/
noncomputable section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


-- Non-public: the Chafaï approximating measures, their tightness, and the Prokhorov extraction are
-- used only inside the proof; the statement mentions none of them.



/-!
# Bernstein's theorem: existence of a representing measure

A completely monotone function on `[0, ∞)` is the Laplace transform of a finite positive measure
on `ℝ≥0`.

## Main results

* `TauCeti.exists_representsLaplace_of_isCompletelyMonotone`

## Scope

This is the **existence** half of the Bernstein milestone in
`TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B. Uniqueness of the representing measure
is `TauCeti.RepresentsLaplace.unique`, the converse direction is
`TauCeti.isCompletelyMonotoneOnIci_laplaceTransform`, and all three combine in
`Bernstein/HausdorffBernsteinWidder.lean` as `TauCeti.hausdorff_bernstein_widder` and
`TauCeti.hausdorff_bernstein_widder_existsUnique`.

Finiteness of the representing measure is not an extra hypothesis but a consequence of complete
monotonicity on the *closed* half-line: `IsCompletelyMonotone` builds in `Set.Ici 0`, so `f` takes a
real value at `0`, and the representing measure has total mass `f 0`. On the open half-line alone
the value at `0` need not exist and the representing measure can be infinite — `1/t` is completely
monotone on `(0, ∞)` with representing measure Lebesgue.

## Implementation

`Bernstein/Measures.lean` supplies the Chafaï approximating measures `chafaiRescaled f n` on `ℝ≥0`
and the reconstruction identity `f x - L = ∫ bernsteinKernel n x ∂(chafaiRescaled f n)`, where
`L = lim_{t→∞} f t`. Those measures are uniformly mass-bounded and, by `Bernstein/Tightness.lean`,
tight. The three remaining steps are:

1. extract a weak limit `μ₀` from tightness;
2. pass the reconstruction identity to that limit, replacing the Bernstein kernel by `e^{-xp}`,
   which represents the non-constant part `f - L`;
3. add the atom `L • δ₀`, whose Laplace transform is the constant `L`, to represent `f` itself.

Step 1 uses `finite_measure_cluster_limit` rather than its subsequence form
`finite_measure_subseq_limit`: the latter needs `FirstCountableTopology (FiniteMeasure ℝ≥0)`, and
Mathlib's metrizability instances for spaces of measures are stated for `ProbabilityMeasure`, not
`FiniteMeasure`. No subsequence is actually required — every ingredient is a filter limit, so an
ultrafilter below `atTop` suffices, and being `NeBot` it still gives uniqueness of limits.

## References

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B (Bernstein theorem milestone).

* D. Chafaï, *Aspects of the Bernstein theorem* (2013) — the approximating measures this proof
  passes to the limit.
* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions* (de Gruyter, 2nd ed. 2012), Ch. 1.
-/


open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology

namespace TauCeti

variable {f : ℝ → ℝ}

/-- **The weak limit represents the non-constant part.** Along the ultrafilter `U`, the Chafaï
measures converge weakly to `μ₀`; passing the reconstruction identity to that limit replaces the
Bernstein kernel by `e^{-tp}` and exhibits `μ₀` as a representing measure for `f - L`, where `L` is
the limit of `f` at infinity. The atom carrying `L` itself is added by the caller.

Stated pointwise in `t`, which is how the caller consumes it. -/
private theorem sub_eq_integral_exp_neg_mul_of_weak_limit {L : ℝ} {C : ℝ≥0} {μ₀ : Measure ℝ≥0}
    {U : Ultrafilter ℕ} (hcm : IsCompletelyMonotone f) (hL : Tendsto f atTop (nhds L))
    (hmass' : ∀ᶠ n in atTop, (chafaiRescaled f n) univ ≤ (C : ℝ≥0∞)) (hU : (U : Filter ℕ) ≤ atTop)
    (hweak : ∀ g : BoundedContinuousFunction ℝ≥0 ℝ,
      Tendsto (fun n => ∫ x, g x ∂(chafaiRescaled f n)) (U : Filter ℕ) (nhds (∫ x, g x ∂μ₀)))
    {t : ℝ} (ht : 0 ≤ t) :
    f t - L = ∫ p : ℝ≥0, Real.exp (-(t * (p : ℝ))) ∂μ₀ := by
  have : (U : Filter ℕ).NeBot := U.neBot'
  have hlap : Tendsto (fun n => ∫ p, Real.exp (-(t * (p : ℝ))) ∂(chafaiRescaled f n))
      (U : Filter ℕ) (nhds (∫ p, Real.exp (-(t * (p : ℝ))) ∂μ₀)) :=
    chafaiRescaled_tendsto_laplace_integral_of_weak hweak ht
  have herr : Tendsto (fun n => ∫ p : ℝ≥0,
      (bernsteinKernel n t (p : ℝ) - Real.exp (-(t * (p : ℝ))))
        ∂(chafaiRescaled f n)) (U : Filter ℕ) (nhds 0) :=
    (integral_bernsteinKernel_sub_laplaceKernel_tendsto_zero_of_mass_bound
      (C := (C : ℝ)) (chafaiRescaled f)
      (hmass'.mono fun n hn => hn.trans
        (by simp [ENNReal.ofReal_coe_nnreal])) t ht).mono_left hU
  -- the mass bound makes the Chafaï measures eventually finite along `U`
  have hfin : ∀ᶠ n in (U : Filter ℕ), IsFiniteMeasure (chafaiRescaled f n) :=
    Filter.Eventually.mono (hU hmass') fun n hn => ⟨hn.trans_lt ENNReal.coe_lt_top⟩
  have hsplit : ∀ᶠ n in (U : Filter ℕ), ∫ p : ℝ≥0,
      (bernsteinKernel n t (p : ℝ) - Real.exp (-(t * (p : ℝ)))) ∂(chafaiRescaled f n)
        = (∫ p, bernsteinKernel n t (p : ℝ) ∂(chafaiRescaled f n))
          - ∫ p, Real.exp (-(t * (p : ℝ))) ∂(chafaiRescaled f n) := by
    filter_upwards [hfin] with n hn
    exact integral_sub (integrable_bernsteinKernel (chafaiRescaled f n) n ht)
      (integrable_exp_neg_mul (chafaiRescaled f n) ht)
  -- The Bernstein integral is constantly `f t - L` once `n ≥ 2`.
  have hconst : ∀ᶠ n in (U : Filter ℕ),
      ∫ p, bernsteinKernel n t (p : ℝ) ∂(chafaiRescaled f n) = f t - L := by
    have h2 : ∀ᶠ n in (U : Filter ℕ), 2 ≤ n := hU (eventually_ge_atTop 2)
    filter_upwards [h2] with n hn
    exact chafaiRescaled_integral_bernsteinKernel_eq_sub_tendsto_atTop f hcm n hn t ht L hL
  -- Pass to the limit: `(f t - L) - ∫ laplace → 0`.
  have hdiff : Tendsto (fun n => (f t - L)
      - ∫ p, Real.exp (-(t * (p : ℝ))) ∂(chafaiRescaled f n)) (U : Filter ℕ) (nhds 0) := by
    refine herr.congr' ?_
    filter_upwards [hconst, hsplit] with n hn hs
    rw [hs, hn]
  have hlim := hdiff.add hlap
  simp only [sub_add_cancel, zero_add] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim

/-- **Bernstein's theorem, existence half.** A completely monotone function on `[0, ∞)` is the
Laplace transform of a finite positive measure on `ℝ≥0`.

Uniqueness of that measure is not asserted here; it is `TauCeti.RepresentsLaplace.unique`, and
the two combine in the Hausdorff--Bernstein--Widder theorem. -/
theorem exists_representsLaplace_of_isCompletelyMonotone
    (hcm : IsCompletelyMonotone f) :
    ∃ μ : Measure ℝ≥0, RepresentsLaplace μ f := by
  obtain ⟨L, C, hL, hL_nn, -, hmass⟩ := chafaiRescaled_prokhorov_mass_bound f hcm
  have hmass' : ∀ n, (chafaiRescaled f n) univ ≤ (C : ℝ≥0∞) := fun n => (hmass n).2
  obtain ⟨μ₀, U, hU, hμ₀fin, -, hweak⟩ :=
    finite_measure_cluster_limit (chafaiRescaled f) C hmass'
      (isTightMeasureSet_range_chafaiRescaled hcm)
  -- The limit represents the non-constant part `f - L`.
  have key : ∀ t : ℝ, 0 ≤ t → f t - L = ∫ p, Real.exp (-(t * (p : ℝ))) ∂μ₀ :=
    fun t ht => sub_eq_integral_exp_neg_mul_of_weak_limit hcm hL (.of_forall hmass') hU hweak ht
  -- Add the atom `L · δ₀` to recover `f` itself.
  have := hμ₀fin
  refine ⟨μ₀ + L.toNNReal • Measure.dirac 0,
    representsLaplace_iff.mpr ⟨inferInstance, fun t ht => ?_⟩⟩
  rw [laplaceTransform_apply,
    integral_exp_neg_mul_add_smul_dirac_zero μ₀ _ ht, Real.coe_toNNReal L hL_nn]
  linarith [key t ht]

end TauCeti
end

/- TauCeti.Analysis.CompletelyMonotone.Bernstein.HausdorffBernsteinWidder -/
noncomputable section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


-- Non-public: the metrizability class of the finite-set tightness lemmas.

-- Non-public: Bernstein's existence theorem supplies the representing measures of the shifts.

-- Non-public: `finite_measure_cluster_limit` extracts the weak cluster point.


/-!
# Hausdorff--Bernstein--Widder theorem

This file proves the finite-measure form of the Hausdorff--Bernstein--Widder theorem for
completely monotone functions on the closed half-line: a function is continuous on `[0, ∞)`
and completely monotone on `(0, ∞)` if and only if it is the Laplace transform of a (unique)
finite positive measure on `ℝ≥0`.

The hard direction applies Bernstein's existence theorem
(`TauCeti.exists_representsLaplace_of_isCompletelyMonotone`) to the
positive shifts `t ↦ f (t + a)`, which satisfy the strong `IsCompletelyMonotone` predicate,
and passes to a weak cluster point of the representing measures as `a ↓ 0`; the tightness of
that family is an elementary Laplace-kernel tail estimate. The easy direction and the
uniqueness both live in `Laplace/Representation.lean`.

## Main declarations

* `TauCeti.exists_representsLaplace_of_isCompletelyMonotoneOnIci`
* `TauCeti.hausdorff_bernstein_widder`, `TauCeti.hausdorff_bernstein_widder_existsUnique`

## References

The finite-measure representation is the Hausdorff--Bernstein--Widder theorem, after
S. Bernstein (1928) and D. V. Widder, *The Laplace Transform*, Chapter IV.

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B (Bernstein theorem
  milestone).
-/


open MeasureTheory Set Filter
open scoped BoundedContinuousFunction ContDiff ENNReal NNReal Topology

namespace TauCeti

/-! ## Hard direction: tightness of the shifted representing measures -/

/-- A finite set of finite measures is tight: singletons are tight and tightness is closed
under unions. (The empty case routes through an arbitrary singleton, as Mathlib has no
dedicated empty-set tightness lemma.) -/
private lemma isTightMeasureSet_of_finite {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [TopologicalSpace.IsCompletelyPseudoMetrizableSpace α] [SecondCountableTopology α]
    [BorelSpace α] {S : Set (Measure α)} (hS : S.Finite)
    (hfin : ∀ ν ∈ S, IsFiniteMeasure ν) : IsTightMeasureSet S := by
  induction S, hS using Set.Finite.induction_on with
  | empty => exact (isTightMeasureSet_singleton (μ := (0 : Measure α))).subset (empty_subset _)
  | @insert ν S _ _ ih =>
      have : IsFiniteMeasure ν := hfin ν (mem_insert _ _)
      rw [insert_eq]
      exact isTightMeasureSet_singleton.union (ih fun ρ hρ => hfin ρ (mem_insert_of_mem _ hρ))

/-- A finite family of finite measures is tight. -/
private lemma isTightMeasureSet_range_finite
    {α ι : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [TopologicalSpace.IsCompletelyPseudoMetrizableSpace α] [SecondCountableTopology α]
    [BorelSpace α] [Finite ι] (μ : ι → Measure α)
    (hfin : ∀ i, IsFiniteMeasure (μ i)) :
    IsTightMeasureSet (Set.range μ) :=
  isTightMeasureSet_of_finite (finite_range μ) (by rintro ν ⟨i, rfl⟩; exact hfin i)

/-- Along a positive null sequence `aₙ ↓ 0`, the values `f (c + aₙ)` of a function continuous
within `[0, ∞)` converge to `f c`, for any `c ≥ 0`. -/
private lemma tendsto_apply_add_of_continuousOn
    {f : ℝ → ℝ} (hf : ContinuousOn f (Ici 0)) {c : ℝ} (hc : 0 ≤ c)
    {a : ℕ → ℝ} (ha_pos : ∀ n, 0 < a n) (ha : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => f (c + a n)) atTop (𝓝 (f c)) := by
  have hmem : Tendsto (fun n => c + a n) atTop (𝓝[Ici (0 : ℝ)] c) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨by simpa using tendsto_const_nhds.add ha,
        .of_forall fun n => mem_Ici.mpr (add_nonneg hc (ha_pos n).le)⟩
  exact (hf.continuousWithinAt (mem_Ici.mpr hc)).tendsto.comp hmem

/-- The Markov denominator `1 - e^{-xR}` is positive for `x, R > 0`. -/
private lemma one_sub_exp_neg_mul_pos {x R : ℝ} (hx : 0 < x) (hR : 0 < R) :
    0 < 1 - Real.exp (-(x * R)) := by
  have : Real.exp (-(x * R)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  linarith

/-- The `∫⁻` of the bounded coordinate `p ↦ 1 - exp(-x·p)` against a measure that represents
`t ↦ f (t + δ)` by its Laplace transform equals `f δ - f (x + δ)` (for `x > 0`). This is the
Laplace-value identity behind the shifted-measure tail estimate. -/
private lemma lintegral_ofReal_one_sub_exp_eq_of_representsLaplace
    {f : ℝ → ℝ} {μ : Measure ℝ≥0}
    {δ x : ℝ} (hμ : RepresentsLaplace μ (fun t : ℝ => f (t + δ))) (hx : 0 < x) :
    ∫⁻ p : ℝ≥0, ENNReal.ofReal (1 - Real.exp (-(x * (p : ℝ)))) ∂μ
      = ENNReal.ofReal (f δ - f (x + δ)) := by
  have := hμ.isFiniteMeasure
  have h_one : Integrable (fun _ : ℝ≥0 => (1 : ℝ)) μ := integrable_const 1
  have h_exp : Integrable (fun p : ℝ≥0 => Real.exp (-(x * (p : ℝ)))) μ :=
    integrable_exp_neg_mul μ hx.le
  have h_nonneg : 0 ≤ᵐ[μ] fun p : ℝ≥0 => 1 - Real.exp (-(x * (p : ℝ))) := by
    refine Filter.Eventually.of_forall fun p => ?_
    exact sub_nonneg.mpr (exp_neg_mul_le_one hx.le p)
  have hint : Integrable (fun p : ℝ≥0 => 1 - Real.exp (-(x * (p : ℝ)))) μ :=
    h_one.sub h_exp
  have h_int :
      ∫ p : ℝ≥0, (1 - Real.exp (-(x * (p : ℝ)))) ∂μ = f δ - f (x + δ) := by
    calc
      ∫ p : ℝ≥0, (1 - Real.exp (-(x * (p : ℝ)))) ∂μ
          = (∫ _p : ℝ≥0, (1 : ℝ) ∂μ) -
              ∫ p : ℝ≥0, Real.exp (-(x * (p : ℝ))) ∂μ := by
            rw [integral_sub h_one h_exp]
      _ = μ.real univ - laplaceTransform μ x := by
            simp [laplaceTransform_apply]
      _ = f δ - f (x + δ) := by
            have h0 := hμ.eq_laplaceTransform (t := 0) le_rfl
            have hxrep := hμ.eq_laplaceTransform (t := x) hx.le
            have h0' : f δ = μ.real univ := by
              simpa [laplaceTransform_zero] using h0
            rw [← h0', ← hxrep]
  rw [← ofReal_integral_eq_lintegral_ofReal hint h_nonneg, h_int]

/-- Markov tail bound: the mass outside the closed ball of radius `R` is controlled by the `∫⁻`
of `p ↦ 1 - exp(-x·p)` divided by its boundary value `1 - exp(-x·R)` (for `x, R > 0`). -/
private lemma measure_closedBall_compl_le_lintegral_div
    {μ : Measure ℝ≥0} {x R : ℝ} (hx : 0 < x) (hR : 0 < R) :
    μ (Metric.closedBall (0 : ℝ≥0) R)ᶜ ≤
      (∫⁻ p : ℝ≥0, ENNReal.ofReal (1 - Real.exp (-(x * (p : ℝ)))) ∂μ)
        / ENNReal.ofReal (1 - Real.exp (-(x * R))) := by
  set c : ℝ := 1 - Real.exp (-(x * R)) with hc_def
  have hc_pos : 0 < c := one_sub_exp_neg_mul_pos hx hR
  have hc_ne_zero : ENNReal.ofReal c ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hc_pos
  have hc_ne_top : ENNReal.ofReal c ≠ (∞ : ENNReal) := ENNReal.ofReal_ne_top
  have hcoord_meas :
      AEMeasurable (fun p : ℝ≥0 => ENNReal.ofReal (1 - Real.exp (-(x * (p : ℝ))))) μ :=
    (ENNReal.measurable_ofReal.comp
      (by fun_prop : Measurable fun p : ℝ≥0 => 1 - Real.exp (-(x * (p : ℝ)))))
        |>.aemeasurable
  refine (measure_mono ?_).trans (meas_ge_le_lintegral_div hcoord_meas hc_ne_zero hc_ne_top)
  intro p hp
  have hpdist : R < dist p (0 : ℝ≥0) := by
    simpa [Metric.mem_closedBall, not_le] using hp
  have hdist : dist p (0 : ℝ≥0) = (p : ℝ) := by
    simp [NNReal.dist_eq]
  have hRp : R ≤ (p : ℝ) := by linarith
  have hxp : x * R ≤ x * (p : ℝ) := mul_le_mul_of_nonneg_left hRp hx.le
  have hexp_le : Real.exp (-(x * (p : ℝ))) ≤ Real.exp (-(x * R)) :=
    Real.exp_le_exp.mpr (neg_le_neg hxp)
  have hreal : c ≤ 1 - Real.exp (-(x * (p : ℝ))) := by
    rw [hc_def]; linarith
  exact ENNReal.ofReal_le_ofReal hreal

/-- Tail bound for a Laplace-representing measure of a positive shift: the mass outside the
ball of radius `R` is controlled by the Laplace gap `f δ - f (x + δ)`. This is the tightness
input, not a decay rate in `R`: the denominator tends to `1` as `R → ∞`.

The estimate is Markov's inequality on the bounded coordinate `p ↦ 1 - exp (-x * p)`, factored into
`measure_closedBall_compl_le_lintegral_div` (the Markov bound) and
`lintegral_ofReal_one_sub_exp_eq_of_representsLaplace` (the Laplace-value identity). It is the
tightness input for shifting Bernstein's existence theorem back to the closed-half-line
theorem. -/
private lemma measure_closedBall_compl_le_of_representsLaplace_shift
    {f : ℝ → ℝ} {μ : Measure ℝ≥0}
    {δ x R : ℝ} (hμ : RepresentsLaplace μ (fun t : ℝ => f (t + δ)))
    (hx : 0 < x) (hR : 0 < R) :
    μ (Metric.closedBall (0 : ℝ≥0) R)ᶜ ≤
      ENNReal.ofReal ((f δ - f (x + δ)) / (1 - Real.exp (-(x * R)))) := by
  have hc_pos : 0 < 1 - Real.exp (-(x * R)) := one_sub_exp_neg_mul_pos hx hR
  calc
    μ (Metric.closedBall (0 : ℝ≥0) R)ᶜ
        ≤ (∫⁻ p : ℝ≥0, ENNReal.ofReal (1 - Real.exp (-(x * (p : ℝ)))) ∂μ)
            / ENNReal.ofReal (1 - Real.exp (-(x * R))) :=
          measure_closedBall_compl_le_lintegral_div hx hR
    _ = ENNReal.ofReal (f δ - f (x + δ)) / ENNReal.ofReal (1 - Real.exp (-(x * R))) := by
          rw [lintegral_ofReal_one_sub_exp_eq_of_representsLaplace hμ hx]
    _ = ENNReal.ofReal ((f δ - f (x + δ)) / (1 - Real.exp (-(x * R)))) := by
          rw [ENNReal.ofReal_div_of_pos hc_pos]

/-- The continuity-at-`0` step behind the tightness of the shifted representing measures: for any
`η > 0` there is a positive shift `x` and an index `N` beyond which the Laplace gap-quotient
`(f (aₙ) - f (x + aₙ)) / (1 - e⁻¹)` is at most `η`: the uniform-tail input to the tightness
of the shifted representing measures. The denominator `1 - e⁻¹` is the Markov constant
`1 - exp (-(x * R))` of `measure_closedBall_compl_le_of_representsLaplace_shift` at the radius
`R = x⁻¹` that the tightness proof chooses, so that `x * R = 1`. -/
private lemma exists_shift_uniform_gap_bound
    {f : ℝ → ℝ} (hf : ContinuousOn f (Ici 0))
    {a : ℕ → ℝ} (ha_pos : ∀ n, 0 < a n)
    (ha : Tendsto a atTop (𝓝 0))
    {η : ℝ} (hη : 0 < η) :
    ∃ x, 0 < x ∧ ∃ N, ∀ n, N ≤ n →
      (f (a n) - f (x + a n)) / (1 - Real.exp (-1)) ≤ η := by
  have hf_tendsto0 : Tendsto (fun n => f (a n)) atTop (𝓝 (f 0)) := by
    simpa using tendsto_apply_add_of_continuousOn hf le_rfl ha_pos ha
  let c0 : ℝ := 1 - Real.exp (-1)
  have hc0_pos : 0 < c0 := by
    have hexp_lt : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    dsimp [c0]
    linarith
  have hetac : 0 < η * c0 := mul_pos hη hc0_pos
  obtain ⟨m, hm⟩ :=
    (hf_tendsto0.eventually (eventually_gt_nhds (by linarith : f 0 - η * c0 < f 0))).exists
  let x : ℝ := a m
  have hx_pos : 0 < x := ha_pos m
  have hlim_lt : f 0 - f x < η * c0 := by
    simpa [x, sub_lt_comm] using hm
  have hfx_tendsto : Tendsto (fun n => f (x + a n)) atTop (𝓝 (f x)) :=
    tendsto_apply_add_of_continuousOn hf hx_pos.le ha_pos ha
  have hgap_tendsto :
      Tendsto (fun n => f (a n) - f (x + a n)) atTop (𝓝 (f 0 - f x)) :=
    hf_tendsto0.sub hfx_tendsto
  have hgap_event :
      ∀ᶠ n : ℕ in atTop, (f (a n) - f (x + a n)) / c0 ≤ η := by
    filter_upwards [hgap_tendsto.eventually_lt_const hlim_lt] with n hn
    rw [div_le_iff₀ hc0_pos]
    exact le_of_lt hn
  obtain ⟨N, hN⟩ := eventually_atTop.1 hgap_event
  exact ⟨x, hx_pos, N, hN⟩

/-- The representing measures of positive shifts of a closed-half-line completely monotone
function are uniformly tight as the shifts tend to `0`.

The proof combines the finite initial-segment tightness with a uniform tail estimate for the
remaining shifts (`exists_shift_uniform_gap_bound`) and the Laplace-kernel tail bound
`measure_closedBall_compl_le_of_representsLaplace_shift`. -/
private lemma isTightMeasureSet_range_of_representsLaplace_shift
    {f : ℝ → ℝ} (hf : ContinuousOn f (Ici 0))
    {a : ℕ → ℝ} (ha_pos : ∀ n, 0 < a n)
    (ha : Tendsto a atTop (𝓝 0))
    {μ : ℕ → Measure ℝ≥0}
    (hμ : ∀ n, RepresentsLaplace (μ n) (fun t : ℝ => f (t + a n))) :
    IsTightMeasureSet (Set.range μ) := by
  have hμ_fin : ∀ n, IsFiniteMeasure (μ n) := fun n => (hμ n).isFiniteMeasure
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  by_cases hε_top : ε = (∞ : ENNReal)
  · refine ⟨∅, isCompact_empty, ?_⟩
    intro ν _hν
    rw [hε_top]
    exact le_top
  have hε_real_pos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hε_top
  obtain ⟨x, hx_pos, N, hN⟩ :=
    exists_shift_uniform_gap_bound hf ha_pos ha hε_real_pos
  let μfin : {n // n < N} → Measure ℝ≥0 := fun n => μ n
  have hfin_tight : IsTightMeasureSet (Set.range μfin) :=
    isTightMeasureSet_range_finite μfin (fun n => hμ_fin n)
  obtain ⟨Kfin, hKfin_comp, hKfin_tail⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp hfin_tight ε hε
  -- The radius is tied to the shift so that `x * R = 1`, matching the `1 - e⁻¹` denominator
  -- in the gap bound above.
  let R : ℝ := x⁻¹
  have hR_pos : 0 < R := inv_pos.mpr hx_pos
  refine ⟨Kfin ∪ Metric.closedBall (0 : ℝ≥0) R,
    hKfin_comp.union (isCompact_closedBall _ _), ?_⟩
  intro ν hν
  rcases hν with ⟨n, rfl⟩
  by_cases hnlt : n < N
  · have hmem_fin : μ n ∈ Set.range μfin := ⟨⟨n, hnlt⟩, rfl⟩
    have hsubset : (Kfin ∪ Metric.closedBall (0 : ℝ≥0) R)ᶜ ⊆ Kfinᶜ :=
      compl_subset_compl.mpr (subset_union_left)
    exact (measure_mono hsubset).trans (hKfin_tail (μ n) hmem_fin)
  · have hNn : N ≤ n := le_of_not_gt hnlt
    have hball_subset :
        (Kfin ∪ Metric.closedBall (0 : ℝ≥0) R)ᶜ ⊆
          (Metric.closedBall (0 : ℝ≥0) R)ᶜ :=
      compl_subset_compl.mpr (subset_union_right)
    have htail :=
      measure_closedBall_compl_le_of_representsLaplace_shift (hμ n) hx_pos hR_pos
    have hden : 1 - Real.exp (-(x * R)) = 1 - Real.exp (-1) := by
      dsimp [R]
      rw [mul_inv_cancel₀ hx_pos.ne']
    have hquot :
        ENNReal.ofReal
          ((f (a n) - f (x + a n)) / (1 - Real.exp (-(x * R)))) ≤ ε := by
      rw [hden]
      exact ENNReal.ofReal_le_of_le_toReal (hN n hNn)
    calc
      μ n (Kfin ∪ Metric.closedBall (0 : ℝ≥0) R)ᶜ
          ≤ μ n (Metric.closedBall (0 : ℝ≥0) R)ᶜ := measure_mono hball_subset
      _ ≤ ENNReal.ofReal
            ((f (a n) - f (x + a n)) / (1 - Real.exp (-(x * R)))) := htail
      _ ≤ ε := hquot

/-- The representing measure of the positive shift `t ↦ f (t + δ)` has total mass
`f δ ≤ f 0`. -/
private lemma measure_univ_le_of_representsLaplace_shift
    {f : ℝ → ℝ} (hf : IsCompletelyMonotoneOnIci f) {δ : ℝ} (hδ : 0 ≤ δ)
    {μ : Measure ℝ≥0} (hμ : RepresentsLaplace μ (fun t : ℝ => f (t + δ))) :
    μ univ ≤ ENNReal.ofReal (f 0) := by
  have := hμ.isFiniteMeasure
  have hreal : μ.real univ = f δ := by
    simpa [laplaceTransform_zero] using (hμ.eq_laplaceTransform (t := 0) le_rfl).symm
  calc
    μ univ = ENNReal.ofReal (μ.real univ) := by rw [ofReal_measureReal]
    _ ≤ ENNReal.ofReal (f 0) :=
        ENNReal.ofReal_le_ofReal (hreal ▸ hf.le_apply_zero hδ)

/-- **Existence half of the Hausdorff--Bernstein--Widder theorem**: a function continuous on
`[0, ∞)` and completely monotone on `(0, ∞)` is the Laplace transform of a finite positive
measure on `ℝ≥0`. -/
theorem exists_representsLaplace_of_isCompletelyMonotoneOnIci
    {f : ℝ → ℝ} (hf : IsCompletelyMonotoneOnIci f) :
    ∃ μ : Measure ℝ≥0, RepresentsLaplace μ f := by
  classical
  -- Stage 1: the positive null sequence of shifts `aₙ = 1/(n+1)`.
  let a : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have ha_pos : ∀ n, 0 < a n := by
    intro n
    dsimp [a]
    positivity
  have ha : Tendsto a atTop (𝓝 0) := by
    simpa [a] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  -- Stage 2: representing measures for the shifted functions, from Bernstein's theorem.
  have hshift_cm : ∀ n, IsCompletelyMonotone (fun t : ℝ => f (t + a n)) :=
    fun n => hf.isCompletelyMonotoneOnIoi.isCompletelyMonotone_comp_add_const (ha_pos n)
  choose μ hμ using fun n =>
    exists_representsLaplace_of_isCompletelyMonotone (hshift_cm n)
  -- Stage 3: a uniform mass bound and tightness give a weak cluster point.
  let C : ℝ≥0 := ⟨f 0, hf.nonneg_zero⟩
  have hmass : ∀ n, (μ n) univ ≤ (C : ENNReal) := fun n =>
    calc
      (μ n) univ ≤ ENNReal.ofReal (f 0) :=
        measure_univ_le_of_representsLaplace_shift hf (ha_pos n).le (hμ n)
      _ = (C : ENNReal) := ENNReal.ofReal_eq_coe_nnreal hf.nonneg_zero
  have htight : IsTightMeasureSet (Set.range μ) :=
    isTightMeasureSet_range_of_representsLaplace_shift hf.continuousOn ha_pos ha hμ
  obtain ⟨μ₀, U, hUle, hμ₀_fin, _hmass₀, hweak⟩ :=
    finite_measure_cluster_limit (σ := μ) C hmass htight
  -- Stage 4: identify the cluster point as a representing measure via continuity at `0⁺`.
  refine ⟨μ₀, representsLaplace_iff.mpr ⟨hμ₀_fin, fun t ht => ?_⟩⟩
  have hf_arg_U : Tendsto (fun n => f (t + a n)) (U : Filter ℕ) (𝓝 (f t)) :=
    (tendsto_apply_add_of_continuousOn hf.continuousOn ht ha_pos ha).mono_left hUle
  have hshift_laplace :
      Tendsto (fun n => ∫ p, Real.exp (-(t * (p : ℝ))) ∂(μ n)) (U : Filter ℕ)
        (𝓝 (f t)) := by
    refine Tendsto.congr (fun n => ?_) hf_arg_U
    rw [(hμ n).eq_laplaceTransform (t := t) ht, laplaceTransform_apply]
  have hweak_laplace :
      Tendsto (fun n => ∫ p, Real.exp (-(t * (p : ℝ))) ∂(μ n)) (U : Filter ℕ)
        (𝓝 (laplaceTransform μ₀ t)) := by
    rw [laplaceTransform_apply]
    simpa using hweak (laplaceKernelBoundedContinuous ht)
  exact tendsto_nhds_unique hshift_laplace hweak_laplace

/-! ## Headline theorem -/

end TauCeti
end


open MeasureTheory Filter Set
open scoped Topology NNReal BoundedContinuousFunction
end

section
open Real Filter MeasureTheory Set
open scoped ContDiff Topology NNReal
namespace Mo360993

noncomputable def weightedPowerExp (s q t : ℝ) := t^(-q) * Real.exp (-t^s)

theorem weightedPowerExp_smooth (s q : ℝ) {x : ℝ} (hx : 0 < x) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (weightedPowerExp s q) x := by
  unfold weightedPowerExp
  exact (Real.contDiffAt_rpow_const_of_ne hx.ne').mul
    (Real.contDiffAt_rpow_const_of_ne hx.ne').neg.exp

theorem weightedPowerExp_deriv (s q : ℝ) {x : ℝ} (hx : 0 < x) :
    deriv (weightedPowerExp s q) x =
      (-q)*weightedPowerExp s (q+1) x + (-s)*weightedPowerExp s (q+1-s) x := by
  have hf := (Real.hasDerivAt_rpow_const (p := -q) (Or.inl hx.ne')).mul
    (Real.hasDerivAt_rpow_const (p := s) (Or.inl hx.ne')).neg.exp
  unfold weightedPowerExp
  convert! hf.deriv using 1
  rw [show -(q+1) = -q-1 by ring, show -(q+1-s) = -q+(s-1) by ring,
    Real.rpow_add hx]
  simp only [Pi.neg_apply]
  ring

theorem weightedPowerExp_sign {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1) (n : ℕ)
    (q : ℝ) (hq : 0 ≤ q) {x : ℝ} (hx : 0 < x) :
    0 ≤ (-1 : ℝ)^n * iteratedDeriv n (weightedPowerExp s q) x := by
  induction n generalizing q with
  | zero =>
    simp only [pow_zero, one_mul, iteratedDeriv_zero]
    unfold weightedPowerExp
    positivity
  | succ n ih =>
    have he : deriv (weightedPowerExp s q) =ᶠ[𝓝 x]
        fun z => (-q)*weightedPowerExp s (q+1) z + (-s)*weightedPowerExp s (q+1-s) z := by
      filter_upwards [lt_mem_nhds hx] with t ht using weightedPowerExp_deriv s q ht
    have hq' := weightedPowerExp_smooth s (q+1) (n := n) hx
    have hs'' := weightedPowerExp_smooth s (q+1-s) (n := n) hx
    rw [iteratedDeriv_succ', (he.iteratedDeriv n).eq_of_nhds,
      iteratedDeriv_fun_add (contDiffAt_const.mul hq') (contDiffAt_const.mul hs''),
      iteratedDeriv_const_mul _ hq', iteratedDeriv_const_mul _ hs'', pow_succ]
    nlinarith only [mul_nonneg hq (ih (q+1) (by linarith)), mul_nonneg hs (ih (q+1-s) (by linarith))]

theorem stretched_sign {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    0 ≤ (-1 : ℝ)^n * iteratedDeriv n (fun t : ℝ => Real.exp (-t^s)) t := by
  have h := weightedPowerExp_sign hs hs' n 0 (by norm_num) ht
  rw [show weightedPowerExp s 0 = (fun x : ℝ => Real.exp (-x^s)) by
    funext x; simp [weightedPowerExp]] at h
  exact h

theorem gaussian_mixture {a : ℝ} (ha : 0 < a) (ha' : a ≤ 2) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      ∀ x : ℝ, Real.exp (- |x|^a) = ∫ v in Ioi (0 : ℝ), Real.exp (-v*x^2) ∂μ := by
  let s := a/2
  have hs : 0 < s := by dsimp [s]; positivity
  have hs' : s ≤ 1 := by dsimp [s]; linarith
  have hcm : TauCeti.IsCompletelyMonotoneOnIci (fun t : ℝ => Real.exp (-t^s)) := by
    refine ⟨(Real.continuous_exp.comp (Real.continuous_rpow_const hs.le).neg).continuousOn, ?_, ?_⟩
    · intro t ht
      exact (Real.contDiffAt_rpow_const_of_ne (ne_of_gt ht)).neg.exp.contDiffWithinAt
    · exact fun n t ht => stretched_sign hs.le hs' n ht
  obtain ⟨ν, hν⟩ := TauCeti.exists_representsLaplace_of_isCompletelyMonotoneOnIci hcm
  let : IsFiniteMeasure ν := hν.1
  have hmass := hν.2 0 (le_refl 0)
  simp only [Real.zero_rpow hs.ne', neg_zero, Real.exp_zero, TauCeti.laplaceTransform_zero] at hmass
  let : IsProbabilityMeasure ν := ⟨(ENNReal.toReal_eq_one_iff _).mp hmass.symm⟩
  have hzero : ν.real {0} ≤ 0 := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds
      (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_rpow_atTop hs)))
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    change ν.real {0} ≤ Real.exp (-t^s)
    have he := hν.2 t ht
    dsimp only at he
    rw [he, TauCeti.laplaceTransform, ← integral_indicator_one (μ := ν) (measurableSet_singleton 0)]
    apply integral_mono ((integrable_const (1 : ℝ)).indicator (measurableSet_singleton _))
        (TauCeti.integrable_exp_neg_mul ν ht)
    intro p
    by_cases hp : p = 0
    · simp [hp]
    · simp [hp, Real.exp_nonneg]
  have hatom : ν {0} = 0 := by
    rw [← measureReal_eq_zero_iff]
    exact le_antisymm hzero measureReal_nonneg
  have hpos : ∀ᵐ v ∂ν, 0 < v := by
    rw [ae_iff]
    simpa using hatom
  have hm : Measurable (fun v : ℝ≥0 => (v : ℝ)) := by fun_prop
  refine ⟨ν.map (fun v : ℝ≥0 => (v : ℝ)), Measure.isProbabilityMeasure_map hm.aemeasurable, ?_⟩
  intro x
  have hmem : ∀ᵐ v ∂ν, v ∈ (fun z : ℝ≥0 => (z : ℝ)) ⁻¹' Ioi (0 : ℝ) := hpos
  rw [setIntegral_map measurableSet_Ioi (by fun_prop) hm.aemeasurable,
      Measure.restrict_eq_self_of_ae_mem hmem]
  have he := hν.2 (x^2) (sq_nonneg x)
  dsimp only at he
  rw [TauCeti.laplaceTransform] at he
  have hx : (x^2)^s = |x|^a := by
    rw [← sq_abs x, ← Real.rpow_natCast_mul (abs_nonneg x)]
    congr 1
    dsimp [s]
    push_cast; ring
  rw [← hx, he]
  apply integral_congr_ae
  filter_upwards with v
  congr 1
  ring
end Mo360993
end

section
open Real MeasureTheory Set Filter
open scoped Topology
namespace Mo360993Large

noncomputable def cutoff (s : ℝ) := if s ≤ 1 then 1 else 1/s^2

theorem cutoff_integrable : IntegrableOn cutoff (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1), integrableOn_union]
  constructor
  · apply (integrableOn_const (C := (1 : ℝ)) (s := Ioc (0 : ℝ) 1) (hs := by simp)).congr_fun _ measurableSet_Ioc
    intro x hx; simp [cutoff, hx.2]
  · have hi := integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) (c := 1) (by norm_num)
    apply hi.congr_fun _ measurableSet_Ioi
    intro x hx
    change 1 < x at hx
    have hx' : 0 < x := lt_trans (by norm_num : (0 : ℝ)<1) hx
    simp [cutoff, not_le.mpr hx, Real.rpow_neg hx'.le, Real.rpow_two, one_div]

theorem damped_linear {x : ℝ} (hx : 0 ≤ x) : x*Real.exp (-x) ≤ 1 := by
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
  linarith [Real.add_one_le_exp x]

theorem frullani_bound {s u : ℝ} (hs : 0 < s) (hu : 0 < u) :
    |(Real.exp (-s)-Real.exp (-(s*u)))/s| ≤ (1+u+u⁻¹)*cutoff s := by
  have h1 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h2 : Real.exp (-(s*u)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hs.le hu.le))
  rw [abs_div, abs_of_pos hs]
  unfold cutoff
  split_ifs with h
  · rw [mul_one, div_le_iff₀ hs, abs_le]
    have hi := inv_pos.mpr hu
    constructor <;> nlinarith [Real.add_one_le_exp (-s), Real.add_one_le_exp (-(s*u)),
      mul_pos hs hi, mul_pos hs hu]
  · rw [div_le_iff₀ hs, abs_le]
    have h₁ := damped_linear hs.le
    have h₂ := damped_linear (mul_nonneg hs.le hu.le)
    rw [mul_comm s u] at h₂ ⊢
    constructor
    · have hp := Real.exp_pos (-s)
      field_simp
      nlinarith [mul_nonneg (by positivity : 0 ≤ s*u) hp.le,
        mul_nonneg hs.le hu.le, sq_nonneg u]
    · have hp := Real.exp_pos (-(s*u))
      field_simp
      nlinarith [mul_le_mul_of_nonneg_left h₁ hu.le, mul_nonneg (mul_nonneg hs.le hu.le) hp.le, sq_nonneg u]

theorem frullani_exp {u : ℝ} (hu : 0 < u) :
    (∫ s in Ioi (0 : ℝ), (Real.exp (-s)-Real.exp (-(s*u)))/s) = Real.log u := by
  have hi : IntegrableOn (fun s : ℝ => (Real.exp (-s)-Real.exp (-(s*u)))/s) (Ioi 0) := by
    apply (cutoff_integrable.const_mul (1+u+u⁻¹)).mono' (Measurable.aestronglyMeasurable (by fun_prop))
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (0 : ℝ)))] with s hs
    exact frullani_bound hs hu
  let f (s : ℝ) := Real.exp (-s)
  have hc : Continuous f := by dsimp [f]; fun_prop
  have he (s : ℝ) : s⁻¹ • (f (1*s)-f (u*s)) = (Real.exp (-s)-Real.exp (-(s*u)))/s := by
    simp [f, smul_eq_mul, div_eq_mul_inv, mul_comm]
  have h := Frullani.integral_Ioi_eq (f := f) (hc.locallyIntegrable.locallyIntegrableOn _) one_pos hu
    (L := 1) (by simpa [f] using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds)
    (R := 0) Real.tendsto_exp_neg_atTop_nhds_zero (by simpa only [he] using hi)
  simpa only [he, div_one, sub_zero, smul_eq_mul, mul_one] using h

theorem kernel_frullani {u : ℝ} (hu : 0 < u) :
    Real.exp (-u)*(2+u*Real.log u) = 2*Real.exp (-u) +
      ∫ s in Ioi (0 : ℝ), (u*Real.exp (-u))*((Real.exp (-s)-Real.exp (-(s*u)))/s) := by
  rw [integral_const_mul, frullani_exp hu]; ring
end Mo360993Large
end

section
namespace Mo360993Large
open Real Filter Set MeasureTheory
open scoped Topology

noncomputable def compens (d : ℝ → ℝ) (s : ℝ) := (d (1+s)-Real.exp (-s)*d 1)/s
noncomputable def scaleFunctional (h d : ℝ → ℝ) := 2*h 1 + ∫ s in Ioi (0 : ℝ), compens d s
noncomputable def expFamily (u t : ℝ) := Real.exp (-t*u)
noncomputable def expSlope (u t : ℝ) := -u*Real.exp (-t*u)
noncomputable def envelope (u : ℝ) := (1+u+u^2)*Real.exp (-u)

theorem exp_compens (u s : ℝ) : compens (expSlope u) s =
      (u*Real.exp (-u))*((Real.exp (-s)-Real.exp (-(s*u)))/s) := by
  unfold compens expSlope
  rw [show -(1+s)*u = -u + -(s*u) by ring, Real.exp_add, neg_one_mul]
  ring

theorem exp_compens_bound {u s : ℝ} (hu : 0 < u) (hs : 0 < s) :
    |compens (expSlope u) s| ≤ envelope u * cutoff s := by
  rw [exp_compens, abs_mul, abs_of_nonneg (by positivity : 0 ≤ u*Real.exp (-u))]
  calc
    _ ≤ (u*Real.exp (-u))*((1+u+u⁻¹)*cutoff s) :=
      mul_le_mul_of_nonneg_left (frullani_bound hs hu) (by positivity)
    _ = _ := by unfold envelope; field_simp; ring

theorem exp_slope_bound {u t : ℝ} (hu : 0 ≤ u) (ht : 1 ≤ t) :
    |expSlope u t| ≤ envelope u := by
  have he : Real.exp (-t*u) ≤ Real.exp (-u) := Real.exp_le_exp.mpr (by nlinarith)
  simp only [expSlope, abs_mul, abs_neg, abs_of_nonneg hu, abs_of_pos (Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_left he hu).trans
    (mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg u]) (Real.exp_pos _).le)

theorem exponential_lift_data {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    {U A : X → ℝ} (hu : Measurable U) (ha : Measurable A) (hp : ∀ᵐ x ∂μ, 0 < U x)
    (hi : Integrable (fun x => |A x| *envelope (U x)) μ) :
    IntegrableOn (compens (fun t => ∫ x, A x*expSlope (U x) t ∂μ)) (Ioi 0) ∧
    (∫ x, A x*(Real.exp (-U x)*(2+U x*Real.log (U x))) ∂μ) =
      scaleFunctional (fun t => ∫ x, A x*expFamily (U x) t ∂μ)
        (fun t => ∫ x, A x*expSlope (U x) t ∂μ) := by
  let ν := volume.restrict (Ioi (0 : ℝ))
  have hs : ∀ᵐ s ∂ν, 0 < s := ae_restrict_mem measurableSet_Ioi
  let G (x : X) (s : ℝ) := A x*compens (expSlope (U x)) s
  have hg : Integrable (Function.uncurry G) (μ.prod ν) := by
    apply (hi.mul_prod cutoff_integrable).mono'
    · apply Measurable.aestronglyMeasurable
      unfold Function.uncurry G compens expSlope
      fun_prop
    · rw [Measure.ae_prod_iff_ae_ae]
      · filter_upwards [hp] with x hx
        filter_upwards [hs] with s hs'
        simp only [Function.uncurry, G, Real.norm_eq_abs, abs_mul]
        exact (mul_le_mul_of_nonneg_left (exp_compens_bound hx hs') (abs_nonneg _)).trans_eq (by ring)
      · have hcut : Measurable cutoff := Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const (by fun_prop)
        unfold Function.uncurry G compens expSlope envelope
        exact measurableSet_le (by fun_prop) (by fun_prop)
  have hi0 : Integrable (fun x => A x*Real.exp (-U x)) μ := by
    apply hi.mono' (by fun_prop)
    filter_upwards [hp] with x hx
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    unfold envelope
    nlinarith [mul_nonneg (by nlinarith [sq_nonneg (U x)] : 0 ≤ U x + (U x)^2) (Real.exp_pos (-U x)).le]
  have hd {t : ℝ} (ht : 1 ≤ t) : Integrable (fun x => A x*expSlope (U x) t) μ := by
    apply hi.mono' (by unfold expSlope; fun_prop)
    filter_upwards [hp] with x hx
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (exp_slope_bound hx.le ht) (abs_nonneg _)
  have hcomp (s : ℝ) (hs' : 0 < s) : (∫ x, G x s ∂μ) =
      compens (fun t => ∫ x, A x*expSlope (U x) t ∂μ) s := by
    unfold G compens
    have he (x : X) : A x*((expSlope (U x) (1+s)-Real.exp (-s)*expSlope (U x) 1)/s) =
        (A x*expSlope (U x) (1+s)-Real.exp (-s)*(A x*expSlope (U x) 1))/s := by ring
    simp_rw [he]
    rw [integral_div, integral_sub (hd (by linarith)) ((hd (le_refl 1)).const_mul _), integral_const_mul]
  refine ⟨hg.integral_prod_right.congr (hs.mono (fun s h => hcomp s h)), ?_⟩
  have hfirst : (∫ x, A x*(Real.exp (-U x)*(2+U x*Real.log (U x))) ∂μ) =
      ∫ x, (2*(A x*Real.exp (-U x)) + ∫ s, G x s ∂ν) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hp] with x hx
    dsimp only [G, ν]
    rw [integral_const_mul]
    simp_rw [exp_compens]
    rw [kernel_frullani hx]
    ring
  have hin : Integrable (fun x => ∫ s, G x s ∂ν) μ := hg.integral_prod_left
  rw [hfirst, integral_add (hi0.const_mul 2) hin, integral_const_mul, integral_integral_swap hg]
  unfold scaleFunctional expFamily
  simp only [neg_one_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [hs] with s hs'
  exact hcomp s hs'


theorem exponential_lift {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    {U A : X → ℝ} (hu : Measurable U) (ha : Measurable A) (hp : ∀ᵐ x ∂μ, 0 < U x)
    (hi : Integrable (fun x => |A x| *envelope (U x)) μ) :
    (∫ x, A x*(Real.exp (-U x)*(2+U x*Real.log (U x))) ∂μ) =
      scaleFunctional (fun t => ∫ x, A x*expFamily (U x) t ∂μ)
        (fun t => ∫ x, A x*expSlope (U x) t ∂μ) := (exponential_lift_data hu ha hp hi).2
end Mo360993Large
end

section
namespace Mo360993Large
open Real Set Filter MeasureTheory
open scoped Topology

theorem cosine_gaussian {b : ℝ} (hb : 0 < b) (w : ℝ) :
    (∫ x : ℝ, Real.cos (w*x)*Real.exp (-b*x^2)) =
      Real.sqrt (Real.pi/b)*Real.exp (-(w^2)/(4*b)) := by
  have he := fourierIntegral_gaussian (b := (b:ℂ)) (show 0 < (b:ℂ).re from hb) (w:ℂ)
  have hint : Integrable (fun x : ℝ => Complex.exp (Complex.I*(w:ℂ)*(x:ℂ))*Complex.exp (-(b:ℂ)*(x:ℂ)^2)) := by
    apply (integrable_cexp_neg_mul_sq (b := (b:ℂ)) (show 0 < (b:ℂ).re from hb)).bdd_mul (c := 1)
    · fun_prop
    · apply Filter.Eventually.of_forall
      intro x
      simp [Complex.norm_exp, Complex.mul_re]
  have h := congrArg Complex.re he
  rw [← RCLike.re_to_complex, ← integral_re hint] at h
  have hr : (Complex.ofReal (Real.sqrt (Real.pi/b))) = ((Real.pi:ℂ)/(b:ℂ)) ^ (1/2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity : 0 ≤ Real.pi/b)]
    push_cast; rfl
  have hh : Complex.exp (-(w:ℂ)^2/(4*(b:ℂ))) = (Real.exp (-(w^2)/(4*b)):ℂ) := by
    rw [Complex.ofReal_exp]; push_cast; rfl
  rw [← hr, hh, ← Complex.ofReal_mul, Complex.ofReal_re] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards with x
  have h₁ : Complex.I*(w:ℂ)*(x:ℂ) = ((w*x:ℝ):ℂ)*Complex.I := by push_cast; ring
  have h₂ : Complex.exp (-(b:ℂ)*(x:ℂ)^2) = (Real.exp (-b*x^2):ℂ) := by
    rw [Complex.ofReal_exp]; push_cast; rfl
  simp only [h₁,h₂, RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, mul_zero, sub_zero, Complex.exp_ofReal_mul_I_re]

theorem envelope_integrable {p b : ℝ} (hp : 0 < p) (hb : 0 < b) :
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


noncomputable def gp (r y t : ℝ) := t^(-r)*Real.exp (-y*t^(-2*r))

theorem scaled_mixture {μ : Measure ℝ} {a : ℝ} (ha : 0 < a)
    (hm : ∀ x : ℝ, Real.exp (- |x|^a) = ∫ v in Ioi (0 : ℝ), Real.exp (-v*x^2) ∂μ)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Real.exp (-t* |x|^a) = ∫ v in Ioi (0 : ℝ), Real.exp (-(v*t^(2/a))*x^2) ∂μ := by
  have he : |t^(1/a)*x|^a = t*|x|^a := by
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht _), Real.mul_rpow (Real.rpow_nonneg ht.le _) (abs_nonneg _),
      ← Real.rpow_mul ht.le, one_div_mul_cancel ha.ne', Real.rpow_one]
  have hp : (t^(1/a))^2 = t^(2/a) := by
    rw [← Real.rpow_mul_natCast ht.le]; congr 1; push_cast; ring
  rw [neg_mul, ← he, hm]
  apply integral_congr_ae
  filter_upwards with v
  rw [mul_pow, hp]; congr 1; ring

theorem gaussian_scale {v t a : ℝ} (hv : 0 < v) (ht : 0 < t) (ha : 0 < a) (w : ℝ) :
    (∫ x : ℝ, Real.cos (w*x)*Real.exp (-(v*t^(2/a))*x^2)) =
      Real.sqrt (Real.pi/v)*gp (1/a) (w^2/(4*v)) t := by
  rw [cosine_gaussian (mul_pos hv (Real.rpow_pos_of_pos ht _))]
  have hpow : t^(2/a) = (t^(1/a))^2 := by
    rw [← Real.rpow_mul_natCast ht.le]; congr 1; push_cast; ring
  have hneg : t^(-2*(1/a)) = (t^(2/a))⁻¹ := by
    rw [← Real.rpow_neg ht.le]; congr 1; ring
  have he : Real.sqrt (Real.pi/(v*t^(2/a))) = Real.sqrt (Real.pi/v)/t^(1/a) := by
    rw [hpow, ← div_div, Real.sqrt_div (by positivity), Real.sqrt_sq (Real.rpow_nonneg ht.le _)]
  unfold gp
  rw [he, hneg, Real.rpow_neg ht.le]
  have he' : -(w^2)/(4*(v*t^(2/a))) = -(w^2/(4*v))*(t^(2/a))⁻¹ := by ring
  rw [he']; ring

theorem spectral_family {a : ℝ} (ha : 0 < a) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hm : ∀ x : ℝ, Real.exp (- |x|^a) = ∫ v in Ioi (0 : ℝ), Real.exp (-v*x^2) ∂μ) :
    IntegrableOn (fun v : ℝ => Real.sqrt (Real.pi/v)) (Ioi 0) μ ∧
    ∀ t : ℝ, 0 < t → ∀ w : ℝ, (∫ x : ℝ, Real.cos (w*x)*Real.exp (-t* |x|^a)) =
      ∫ v in Ioi (0 : ℝ), Real.sqrt (Real.pi/v)*gp (1/a) (w^2/(4*v)) t ∂μ := by
  let ν := μ.restrict (Ioi (0 : ℝ))
  have hp : ∀ᵐ v ∂ν, 0 < v := ae_restrict_mem measurableSet_Ioi
  have hi {t : ℝ} (ht : 0 < t) : Integrable (fun p : ℝ × ℝ => Real.exp (-(p.2*t^(2/a))*p.1^2)) (volume.prod ν) := by
    apply (integrable_prod_iff (Measurable.aestronglyMeasurable (by fun_prop))).mpr
    constructor
    · apply Filter.Eventually.of_forall
      intro x
      apply (integrable_const (μ := ν) (1 : ℝ)).mono' (by fun_prop)
      filter_upwards [hp] with v hv
      simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr
        (mul_nonneg hv.le (Real.rpow_nonneg ht.le _))) (sq_nonneg x))
    · apply (envelope_integrable ha ht).congr
      filter_upwards with x
      simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact scaled_mixture ha hm ht x
  constructor
  · apply (hi (t := 1) one_pos).integral_prod_right.congr
    filter_upwards [hp] with v hv
    simpa [ν] using cosine_gaussian hv 0
  intro t ht w
  have hj : Integrable (Function.uncurry (fun x v : ℝ => Real.cos (w*x)*Real.exp (-(v*t^(2/a))*x^2))) (volume.prod ν) := by
    apply (hi ht).bdd_mul (c := 1)
    · exact (by fun_prop : Measurable (fun p : ℝ × ℝ => Real.cos (w*p.1))).aestronglyMeasurable
    · exact .of_forall (fun p => by simpa using Real.abs_cos_le_one (w*p.1))
  calc
    _ = ∫ x : ℝ, ∫ v, Real.cos (w*x)*Real.exp (-(v*t^(2/a))*x^2) ∂ν := by
      apply integral_congr_ae; filter_upwards with x
      rw [integral_const_mul, scaled_mixture ha hm ht x]
    _ = _ := by
      rw [integral_integral_swap hj]
      apply integral_congr_ae; filter_upwards [hp] with v hv
      exact gaussian_scale hv ht ha w
end Mo360993Large
end

section
namespace Mo360993Large
open Real Set Filter MeasureTheory
open scoped Topology
noncomputable def arg (r y t : ℝ) := y*t^(-2*r)
noncomputable def dgp (r y t : ℝ) := gp r y t / t * (-r + 2*r*arg r y t)
noncomputable def ddgp (r y t : ℝ) := gp r y t/t^2 *
  ((-r-1+2*r*arg r y t)*(-r+2*r*arg r y t)-4*r^2*arg r y t)

theorem der_power (q : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => t^q) (q*t^q/t) t := by
  convert Real.hasDerivAt_rpow_const (p := q) (Or.inl ht.ne') using 1
  rw [Real.rpow_sub ht, Real.rpow_one]; ring

theorem der_arg (r y : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (arg r y) ((-2*r)*arg r y t/t) t := by
  unfold arg
  convert! (der_power (-2*r) ht).const_mul y using 1
  ring

theorem der_gp (r y : ℝ) {t : ℝ} (ht : 0 < t) : HasDerivAt (gp r y) (dgp r y t) t := by
  have h := (der_power (-r) ht).mul (der_arg r y ht).neg.exp
  unfold dgp gp arg
  convert! h using 1
  · funext x; simp [arg, neg_mul]
  · simp [arg, neg_mul]; ring

theorem der_dgp (r y : ℝ) {t : ℝ} (ht : 0 < t) : HasDerivAt (dgp r y) (ddgp r y t) t := by
  have h := ((der_gp r y ht).div (hasDerivAt_id t) ht.ne').mul
    (((der_arg r y ht).const_mul (2*r)).const_add (-r))
  unfold dgp ddgp
  convert! h using 1
  simp only [Pi.div_apply, Pi.mul_apply, Pi.add_apply, id_eq]
  unfold dgp
  field_simp
  ring

theorem bounded_gp {r y t : ℝ} (hr : 0 ≤ r) (hy : 0 ≤ y) (ht : 1 ≤ t) : |gp r y t| ≤ 1 := by
  have ht' : 0 < t := lt_of_lt_of_le zero_lt_one ht
  unfold gp
  rw [abs_of_nonneg (by positivity)]
  apply mul_le_one₀ (Real.rpow_le_one_of_one_le_of_nonpos ht (neg_nonpos.mpr hr)) (Real.exp_pos _).le
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hy) (Real.rpow_nonneg ht'.le _))

theorem exp_quad_bound {z : ℝ} (hz : 0 ≤ z) : z^2*Real.exp (-z) ≤ 2 := by
  have he := Real.pow_div_factorial_le_exp z hz 2
  norm_num at he
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  linarith

theorem dgp_bound {r y t : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1) (hy : 0 ≤ y) (ht : 0 < t) :
    |dgp r y t| ≤ 3*(t^(-r)/t) := by
  let z := arg r y t
  have hz : 0 ≤ z := mul_nonneg hy (Real.rpow_nonneg ht.le _)
  have hz₁ := damped_linear hz
  have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hz)
  have hp : |(-r+2*r*z)*Real.exp (-z)| ≤ 3 := by
    rw [abs_le]
    constructor <;> nlinarith [Real.exp_pos (-z), mul_nonneg hr (Real.exp_pos (-z)).le,
      mul_nonneg hr (mul_nonneg hz (Real.exp_pos (-z)).le),
      mul_nonneg (sub_nonneg.mpr hr') (Real.exp_pos (-z)).le,
      mul_nonneg (sub_nonneg.mpr hr') (mul_nonneg hz (Real.exp_pos (-z)).le)]
  have heq : dgp r y t = (t^(-r)/t)*((-r+2*r*z)*Real.exp (-z)) := by unfold dgp gp z arg; rw [neg_mul]; ring
  rw [heq, abs_mul, abs_of_nonneg (div_nonneg (Real.rpow_nonneg ht.le _) ht.le), mul_comm 3]
  gcongr

theorem ddgp_bound {r y t : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1) (hy : 0 ≤ y) (ht : 1 ≤ t) :
    |ddgp r y t| ≤ 20 := by
  let z := arg r y t
  have ht' : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hz : 0 ≤ z := mul_nonneg hy (Real.rpow_nonneg ht'.le _)
  have h₀ : Real.exp (-z) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hz)
  have h₁ := damped_linear hz
  have h₂ := exp_quad_bound hz
  have hr2 : r^2 ≤ 1 := by nlinarith [sq_nonneg r, mul_nonneg (sub_nonneg.mpr hr') (show 0 ≤ 1+r by linarith)]
  have ha : (r^2+r)*Real.exp (-z) ≤ 2 := by nlinarith [mul_nonneg (by linarith : 0 ≤ 2-(r^2+r)) (Real.exp_pos (-z)).le]
  have hb : (8*r^2+2*r)*(z*Real.exp (-z)) ≤ 10 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 10-(8*r^2+2*r)) (mul_nonneg hz (Real.exp_pos (-z)).le)]
  have hc : 4*r^2*(z^2*Real.exp (-z)) ≤ 8 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr2) (mul_nonneg (sq_nonneg z) (Real.exp_pos (-z)).le)]
  have habs : |((-r-1+2*r*z)*(-r+2*r*z)-4*r^2*z)*Real.exp (-z)| ≤ 20 := by
    rw [abs_le]
    have ha' := mul_nonneg (add_nonneg (sq_nonneg r) hr) (Real.exp_pos (-z)).le
    have hb' := mul_nonneg (show 0 ≤ 8*r^2+2*r by positivity) (mul_nonneg hz (Real.exp_pos (-z)).le)
    have hc' := mul_nonneg (show 0 ≤ 4*r^2 by positivity) (mul_nonneg (sq_nonneg z) (Real.exp_pos (-z)).le)
    constructor <;> nlinarith
  have ht₁ : t^(-r)/t^2 ≤ 1 := (div_le_one (by positivity)).mpr
    ((Real.rpow_le_one_of_one_le_of_nonpos ht (by linarith)).trans (one_le_pow₀ ht))
  have heq : ddgp r y t = (t^(-r)/t^2)*(((-r-1+2*r*z)*(-r+2*r*z)-4*r^2*z)*Real.exp (-z)) := by
    unfold ddgp gp z arg; rw [neg_mul]; ring
  rw [heq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ t^(-r)/t^2)]
  exact (mul_le_mul_of_nonneg_left habs (by positivity)).trans (by linarith)

theorem dgp_compens_bound {r y s : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1) (hy : 0 ≤ y) (hs : 0 < s) :
    |(dgp r y (1+s)-Real.exp (-s)*dgp r y 1)/s| ≤ 23*cutoff s := by
  have hD {t : ℝ} (ht : 1 ≤ t) : |dgp r y t| ≤ 3/t := by
    apply (dgp_bound hr hr' hy (lt_of_lt_of_le zero_lt_one ht)).trans
    rw [← mul_div_assoc]
    gcongr
    linarith [Real.rpow_le_one_of_one_le_of_nonpos ht (neg_nonpos.mpr hr)]
  have hone : |dgp r y 1| ≤ 3 := by simpa using hD (le_refl 1)
  have hs₁ : 1 ≤ 1+s := by linarith
  have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs.le)
  rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
  unfold cutoff
  split_ifs with hs'
  · have hm := norm_image_sub_le_of_norm_deriv_le_segment' (a := (1 : ℝ)) (b := 1+s)
      (fun x hx => (der_dgp r y (lt_of_lt_of_le zero_lt_one hx.1)).hasDerivWithinAt)
      (fun x hx => ddgp_bound hr hr' hy hx.1) (1+s) ⟨hs₁,le_refl _⟩
    rw [Real.norm_eq_abs] at hm
    have he' : 1-Real.exp (-s) ≤ s := by linarith [Real.add_one_le_exp (-s)]
    have heq : dgp r y (1+s)-Real.exp (-s)*dgp r y 1 =
        (dgp r y (1+s)-dgp r y 1)+(1-Real.exp (-s))*dgp r y 1 := by ring
    rw [heq]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr he)]
    nlinarith [mul_le_mul he' hone (abs_nonneg _) hs.le]
  · have hds := hD hs₁
    have he' := damped_linear hs.le
    apply (abs_sub _ _).trans
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have he'' := mul_le_mul_of_nonneg_left hone (Real.exp_pos (-s)).le
    have hds' : |dgp r y (1+s)| ≤ 3/s := hds.trans (div_le_div_of_nonneg_left (by norm_num) hs (by linarith))
    have hds'' := (le_div_iff₀ hs).mp hds'
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left he'' hs.le]
end Mo360993Large
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/- Module Zeta23.GammaFacts.Series -/
section
noncomputable section

namespace Zeta23

namespace DigammaSeries

open Complex Filter Topology

def wTerm (n : ℕ) (z : ℂ) : ℂ := (1 + z / (n + 1)) * Complex.exp (-(z / (n + 1))) - 1

set_option maxHeartbeats 1600000 in
lemma one_add_wTerm (n : ℕ) (z : ℂ) :
    1 + wTerm n z = (1 + z / (n + 1)) * Complex.exp (-(z / (n + 1))) := by
  unfold wTerm
  ring

set_option maxHeartbeats 1600000 in
lemma norm_natCast_add_one (n : ℕ) : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
  rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real]
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)]

set_option maxHeartbeats 1600000 in
lemma norm_wTerm_le {z : ℂ} {n : ℕ} (h : ‖z‖ ≤ (n : ℝ) + 1) :
    ‖wTerm n z‖ ≤ 3 * (‖z‖ / ((n : ℝ) + 1)) ^ 2 := by
  set w : ℂ := z / ((n : ℂ) + 1) with hwdef
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hwnorm : ‖w‖ = ‖z‖ / ((n : ℝ) + 1) := by
    rw [hwdef, norm_div, norm_natCast_add_one]
  have hwn : ‖w‖ ≤ 1 := by
    rw [hwnorm, div_le_one hn1]
    exact h
  have hr : ‖Complex.exp (-w) - 1 + w‖ ≤ ‖w‖ ^ 2 := by
    have hx : ‖(-w : ℂ)‖ ≤ 1 := by rwa [norm_neg]
    have h2 := norm_exp_sub_one_sub_id_le hx
    rw [norm_neg] at h2
    calc ‖Complex.exp (-w) - 1 + w‖ = ‖Complex.exp (-w) - 1 - (-w)‖ := by ring_nf
      _ ≤ ‖w‖ ^ 2 := h2
  have hident : wTerm n z = (Complex.exp (-w) - 1 + w) - w ^ 2
      + w * (Complex.exp (-w) - 1 + w) := by
    unfold wTerm
    ring
  have hnw2 : ‖(w : ℂ) ^ 2‖ = ‖w‖ ^ 2 := norm_pow _ _
  calc ‖wTerm n z‖
      ≤ ‖(Complex.exp (-w) - 1 + w) - w ^ 2‖ + ‖w * (Complex.exp (-w) - 1 + w)‖ := by
        rw [hident]
        exact norm_add_le _ _
    _ ≤ (‖w‖ ^ 2 + ‖w‖ ^ 2) + ‖w‖ * ‖w‖ ^ 2 := by
        have h1 : ‖(Complex.exp (-w) - 1 + w) - w ^ 2‖ ≤ ‖w‖ ^ 2 + ‖w‖ ^ 2 := by
          calc ‖(Complex.exp (-w) - 1 + w) - w ^ 2‖
              ≤ ‖Complex.exp (-w) - 1 + w‖ + ‖(w : ℂ) ^ 2‖ := norm_sub_le _ _
            _ ≤ ‖w‖ ^ 2 + ‖w‖ ^ 2 := by
                rw [hnw2]
                exact add_le_add hr le_rfl

        have h2 : ‖w * (Complex.exp (-w) - 1 + w)‖ ≤ ‖w‖ * ‖w‖ ^ 2 := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left hr (norm_nonneg _)
        linarith
    _ ≤ 3 * ‖w‖ ^ 2 := by nlinarith [norm_nonneg w, hwn, sq_nonneg ‖w‖]
    _ = 3 * (‖z‖ / ((n : ℝ) + 1)) ^ 2 := by rw [hwnorm]

set_option maxHeartbeats 1600000 in
lemma summable_wBound (R : ℝ) : Summable (fun n : ℕ => 3 * (R / ((n : ℝ) + 1)) ^ 2) := by
  have h1 : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) := by
    have h2 : Summable (fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹) := by
      have := Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)
      have heq : (fun n : ℕ => ((n : ℝ) ^ (2 : ℝ))⁻¹) = fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹ := by
        funext n
        rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rwa [heq] at this
    have := (summable_nat_add_iff 1).mpr h2
    simpa [add_comm] using this
  have h3 : (fun n : ℕ => 3 * (R / ((n : ℝ) + 1)) ^ 2)
      = fun n : ℕ => (3 * R ^ 2) * ((((n : ℝ) + 1) ^ 2)⁻¹) := by
    funext n
    rw [div_pow]
    ring
  rw [h3]
  exact h1.mul_left _

set_option maxHeartbeats 1600000 in
lemma summable_norm_wTerm (z : ℂ) : Summable (fun n => ‖wTerm n z‖) := by
  refine (summable_wBound ‖z‖).of_norm_bounded_eventually ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [Filter.eventually_ge_atTop ⌈‖z‖⌉₊] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  refine norm_wTerm_le ?_
  calc ‖z‖ ≤ (⌈‖z‖⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ (n : ℝ) := by exact_mod_cast hn
    _ ≤ (n : ℝ) + 1 := by linarith

set_option maxHeartbeats 1600000 in
lemma multipliable_one_add_wTerm (z : ℂ) : Multipliable fun n => 1 + wTerm n z :=
  Complex.multipliable_one_add_of_summable ((summable_norm_wTerm z).of_norm)

set_option maxHeartbeats 1600000 in
lemma harmonic_cast_eq (N : ℕ) :
    ((harmonic N : ℚ) : ℝ) = ∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1) := by
  rw [harmonic]
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [one_div]

set_option maxHeartbeats 1600000 in
lemma inv_gammaSeq_eq {z : ℂ} (_hz : z ∈ Complex.integerComplement) {N : ℕ} (hN : 1 ≤ N) :
    (Complex.GammaSeq z N)⁻¹
      = z * Complex.exp ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1))
            - Real.log N : ℝ) : ℂ) * z)
          * ∏ n ∈ Finset.range N, (1 + wTerm n z) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  
  have hprod : ∏ n ∈ Finset.range N, (1 + wTerm n z)
      = (∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1)))
          * Complex.exp (-(∑ m ∈ Finset.range N, z / ((m : ℂ) + 1))) := by
    calc ∏ n ∈ Finset.range N, (1 + wTerm n z)
        = ∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1))
            * Complex.exp (-(z / ((n : ℂ) + 1))) :=
          Finset.prod_congr rfl fun n _ => one_add_wTerm n z
      _ = (∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1)))
            * ∏ n ∈ Finset.range N, Complex.exp (-(z / ((n : ℂ) + 1))) :=
          Finset.prod_mul_distrib
      _ = (∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1)))
            * Complex.exp (∑ n ∈ Finset.range N, -(z / ((n : ℂ) + 1))) := by
          rw [Complex.exp_sum]
      _ = _ := by rw [← Finset.sum_neg_distrib]
  
  have hfact_ne : ((N.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
  have hNz : ((N : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcpow : (N : ℂ) ^ z = Complex.exp (((Real.log N : ℝ) : ℂ) * z) := by
    rw [Complex.cpow_def_of_ne_zero hNz]
    congr 2
    rw [show ((N : ℂ)) = (((N : ℝ) : ℝ) : ℂ) by push_cast; ring]
    exact (Complex.ofReal_log hNR.le).symm
  have hdenom : ∏ j ∈ Finset.range (N + 1), (z + (j : ℂ))
      = z * ∏ n ∈ Finset.range N, (z + ((n : ℂ) + 1)) := by
    rw [Finset.prod_range_succ']
    rw [Nat.cast_zero, add_zero, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun n _ => ?_
    push_cast
    ring
  have hfactprod : ((N.factorial : ℕ) : ℂ) = ∏ n ∈ Finset.range N, ((n : ℂ) + 1) := by
    rw [show N.factorial = ∏ n ∈ Finset.range N, (n + 1) from
      (Finset.prod_range_add_one_eq_factorial N).symm]
    push_cast
    rfl
  have hfrac : ∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1))
      = (∏ n ∈ Finset.range N, (z + ((n : ℂ) + 1))) / ((N.factorial : ℕ) : ℂ) := by
    have h1 : ∀ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1))
        = (z + ((n : ℂ) + 1)) / ((n : ℂ) + 1) := by
      intro n _
      have hne : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
      field_simp
      ring
    rw [Finset.prod_congr rfl h1, Finset.prod_div_distrib, hfactprod]
  have hsumcast : (((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) : ℝ) : ℂ)
      = ∑ m ∈ Finset.range N, 1 / ((m : ℂ) + 1) := by
    push_cast
    rfl
  have hzsum : ∑ m ∈ Finset.range N, z / ((m : ℂ) + 1)
      = z * ∑ m ∈ Finset.range N, 1 / ((m : ℂ) + 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  
  rw [Complex.GammaSeq, hprod, hfrac, hdenom, hcpow, hzsum, ← hsumcast]
  rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub]
  set A : ℂ := ∏ n ∈ Finset.range N, (z + ((n : ℂ) + 1)) with hA
  set E1 : ℂ := Complex.exp ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) : ℝ) : ℂ) * z)
    with hE1
  set E2 : ℂ := Complex.exp (((Real.log N : ℝ) : ℂ) * z) with hE2
  have hE1ne : E1 ≠ 0 := Complex.exp_ne_zero _
  have hE2ne : E2 ≠ 0 := Complex.exp_ne_zero _
  have hexpneg : Complex.exp (-(z * (((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) : ℝ) : ℂ)))
      = E1⁻¹ := by
    rw [hE1, ← Complex.exp_neg]
    congr 1
    ring
  rw [hexpneg]
  field_simp

set_option maxHeartbeats 1600000 in
theorem inv_gamma_eq_prod {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    (Complex.Gamma z)⁻¹
      = z * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z)
          * ∏' n : ℕ, (1 + wTerm n z) := by
  have hzero : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m h
    exact hz ⟨-(m : ℤ), by push_cast; rw [h]⟩
  have hL : Tendsto (fun N => (Complex.GammaSeq z N)⁻¹) atTop (𝓝 ((Complex.Gamma z)⁻¹)) :=
    (Complex.GammaSeq_tendsto_Gamma z).inv₀ (Complex.Gamma_ne_zero hzero)
  have hhar : Tendsto (fun N : ℕ =>
      ((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) - Real.log N : ℝ))
      atTop (𝓝 Real.eulerMascheroniConstant) := by
    refine Real.tendsto_harmonic_sub_log.congr fun n => ?_
    rw [harmonic_cast_eq]
  have hexp : Tendsto (fun N : ℕ => Complex.exp
      ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) - Real.log N : ℝ) : ℂ) * z))
      atTop (𝓝 (Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z))) := by
    have h2 : Tendsto (fun N : ℕ =>
        ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) - Real.log N : ℝ) : ℂ)))
        atTop (𝓝 ((Real.eulerMascheroniConstant : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp hhar
    exact (Complex.continuous_exp.tendsto _).comp (h2.mul_const z)
  have hP : Tendsto (fun N => ∏ n ∈ Finset.range N, (1 + wTerm n z)) atTop
      (𝓝 (∏' n : ℕ, (1 + wTerm n z))) :=
    (multipliable_one_add_wTerm z).hasProd.tendsto_prod_nat
  have hRHS : Tendsto (fun N : ℕ => z * Complex.exp
      ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) - Real.log N : ℝ) : ℂ) * z)
      * ∏ n ∈ Finset.range N, (1 + wTerm n z)) atTop
      (𝓝 (z * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z)
        * ∏' n : ℕ, (1 + wTerm n z))) :=
    (tendsto_const_nhds.mul hexp).mul hP
  have heq : ∀ᶠ N in atTop, (Complex.GammaSeq z N)⁻¹
      = z * Complex.exp
        ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) - Real.log N : ℝ) : ℂ) * z)
      * ∏ n ∈ Finset.range N, (1 + wTerm n z) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    exact inv_gammaSeq_eq hz hN
  exact tendsto_nhds_unique (hL.congr' heq) hRHS

set_option maxHeartbeats 1600000 in
lemma logDeriv_one_add_wTerm {z : ℂ} (hz : z ∈ Complex.integerComplement) (n : ℕ) :
    logDeriv (fun s => 1 + wTerm n s) z = 1 / (z + n + 1) - 1 / ((n : ℂ) + 1) := by
  have hn1 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  have hzn : z + ((n : ℂ) + 1) ≠ 0 := by
    have := Complex.integerComplement_add_ne_zero hz ((n : ℤ) + 1)
    push_cast at this ⊢
    convert this using 2
  have hzn' : z + (n : ℂ) + 1 ≠ 0 := by
    rw [add_assoc]
    exact hzn
  have hfun : (fun s => 1 + wTerm n s)
      = fun s : ℂ => (1 + s / ((n : ℂ) + 1)) * Complex.exp (-(s / ((n : ℂ) + 1))) := by
    funext s
    exact one_add_wTerm n s
  rw [hfun]
  have h1z : (1 + z / ((n : ℂ) + 1)) ≠ 0 := by
    intro h
    apply hzn
    have h2 := congrArg (fun t => t * ((n : ℂ) + 1)) h
    simp only [add_mul, one_mul, zero_mul] at h2
    rw [div_mul_cancel₀ _ hn1] at h2
    rw [← h2]
    ring
  have hd1 : HasDerivAt (fun s : ℂ => 1 + s / ((n : ℂ) + 1)) (1 / ((n : ℂ) + 1)) z := by
    have h3 := ((hasDerivAt_id z).div_const ((n : ℂ) + 1)).const_add 1
    simpa [one_div] using h3
  have hd2 : HasDerivAt (fun s : ℂ => Complex.exp (-(s / ((n : ℂ) + 1))))
      (-(1 / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1)))) z := by
    have hlin : HasDerivAt (fun s : ℂ => -(s / ((n : ℂ) + 1))) (-(1 / ((n : ℂ) + 1))) z := by
      exact ((hasDerivAt_id z).div_const ((n : ℂ) + 1)).neg
    have h5 := hlin.cexp
    simpa [mul_comm] using h5
  have hprod : HasDerivAt
      (fun s : ℂ => (1 + s / ((n : ℂ) + 1)) * Complex.exp (-(s / ((n : ℂ) + 1))))
      (1 / ((n : ℂ) + 1) * Complex.exp (-(z / ((n : ℂ) + 1)))
        + (1 + z / ((n : ℂ) + 1)) * (-(1 / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1))))) z :=
    hd1.mul hd2
  unfold logDeriv
  rw [Pi.div_apply, hprod.deriv]
  have hexpne : Complex.exp (-(z / ((n : ℂ) + 1))) ≠ 0 := Complex.exp_ne_zero _
  have h3 : (1 : ℂ) + (n : ℂ) + z ≠ 0 := by
    intro h
    apply hzn'
    linear_combination h
  field_simp [h3]
  have h4 : ((1 : ℂ) + (n : ℂ) + z) * ((1 + (n : ℂ) + z)⁻¹) = 1 := mul_inv_cancel₀ h3
  linear_combination (-z) * h4

set_option maxHeartbeats 1600000 in
theorem summable_digamma_series {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / (z + n + 1)) := by
  refine Summable.of_norm ?_
  refine Summable.of_norm_bounded_eventually
    (g := fun n : ℕ => 2 * ‖z‖ * ((((n : ℝ) + 1) ^ 2)⁻¹)) ?_ ?_
  · have h1 : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) := by
      have h2 : Summable (fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹) := by
        have h3 := Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)
        have heq : (fun n : ℕ => ((n : ℝ) ^ (2 : ℝ))⁻¹) = fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹ := by
          funext n
          rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        rwa [heq] at h3
      have h4 := (summable_nat_add_iff 1).mpr h2
      simpa [add_comm] using h4
    exact h1.mul_left _
  · rw [Nat.cofinite_eq_atTop]
    filter_upwards [Filter.eventually_ge_atTop ⌈2 * ‖z‖⌉₊] with n hn
    have hn1 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
    have hzn : z + ((n : ℂ) + 1) ≠ 0 := by
      have := Complex.integerComplement_add_ne_zero hz ((n : ℤ) + 1)
      push_cast at this ⊢
      convert this using 2
    have hzn' : z + (n : ℂ) + 1 ≠ 0 := by
      rw [add_assoc]
      exact hzn
    have hident : 1 / ((n : ℂ) + 1) - 1 / (z + n + 1)
        = z / (((n : ℂ) + 1) * (z + n + 1)) := by
      field_simp
      ring
    have h2n : 2 * ‖z‖ ≤ (n : ℝ) := by
      calc 2 * ‖z‖ ≤ (⌈2 * ‖z‖⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (n : ℝ) := by exact_mod_cast hn
    have hlow : ((n : ℝ) + 1) / 2 ≤ ‖z + (n : ℂ) + 1‖ := by
      have h1 : ‖((n : ℂ) + 1)‖ - ‖z‖ ≤ ‖z + (n : ℂ) + 1‖ := by
        have h2 := norm_sub_le (z + (n : ℂ) + 1) z
        have h3 : (z + (n : ℂ) + 1) - z = ((n : ℂ) + 1) := by ring
        rw [h3] at h2
        linarith
      rw [norm_natCast_add_one] at h1
      linarith [norm_nonneg z]
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), hident, norm_div, norm_mul,
      norm_natCast_add_one]
    calc ‖z‖ / (((n : ℝ) + 1) * ‖z + (n : ℂ) + 1‖)
        ≤ ‖z‖ / (((n : ℝ) + 1) * (((n : ℝ) + 1) / 2)) := by
          gcongr
      _ = 2 * ‖z‖ * ((((n : ℝ) + 1) ^ 2)⁻¹) := by
          field_simp

set_option maxHeartbeats 1600000 in
theorem hasSum_digamma_series {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / (z + n + 1))
      (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z) := by
  set γc : ℂ := ((Real.eulerMascheroniConstant : ℝ) : ℂ) with hγc
  have hz0 : z ≠ 0 := Complex.integerComplement.ne_zero hz
  have hzero : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m h
    exact hz ⟨-(m : ℤ), by push_cast; rw [h]⟩
  have hΓne : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero hzero
  have hopenZ : IsOpen Complex.integerComplement := isOpen_compl_range_intCast
  set U : Set ℂ := Metric.ball (0 : ℂ) (‖z‖ + 1) with hU
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hzU : z ∈ U := by
    rw [hU, Metric.mem_ball, dist_zero_right]
    linarith [norm_nonneg z]
  have htend : MultipliableLocallyUniformlyOn (fun n (s : ℂ) => 1 + wTerm n s) U := by
    refine Summable.multipliableLocallyUniformlyOn_nat_one_add hUopen
      (summable_wBound (‖z‖ + 1)) ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop ⌈‖z‖ + 1⌉₊] with n hn x hx
      have hx1 : ‖x‖ ≤ ‖z‖ + 1 := by
        rw [hU, Metric.mem_ball, dist_zero_right] at hx
        linarith
      have hn1 : ‖z‖ + 1 ≤ (n : ℝ) + 1 := by
        calc ‖z‖ + 1 ≤ (⌈‖z‖ + 1⌉₊ : ℝ) := Nat.le_ceil _
          _ ≤ (n : ℝ) := by exact_mod_cast hn
          _ ≤ (n : ℝ) + 1 := by linarith
      calc ‖wTerm n x‖ ≤ 3 * (‖x‖ / ((n : ℝ) + 1)) ^ 2 :=
            norm_wTerm_le (le_trans hx1 hn1)
        _ ≤ 3 * ((‖z‖ + 1) / ((n : ℝ) + 1)) ^ 2 := by
            gcongr
    · intro n
      have hc : Continuous (wTerm n) := by
        unfold wTerm
        fun_prop
      exact hc.continuousOn
  have hfne : ∀ n : ℕ, (fun s : ℂ => 1 + wTerm n s) z ≠ 0 := by
    intro n
    have hn1 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
    have hzn : z + ((n : ℂ) + 1) ≠ 0 := by
      have := Complex.integerComplement_add_ne_zero hz ((n : ℤ) + 1)
      push_cast at this ⊢
      convert this using 2
    simp only [one_add_wTerm]
    apply mul_ne_zero _ (Complex.exp_ne_zero _)
    intro h
    apply hzn
    have h2 := congrArg (fun t => t * ((n : ℂ) + 1)) h
    simp only [add_mul, one_mul, zero_mul] at h2
    rw [div_mul_cancel₀ _ hn1] at h2
    rw [← h2]
    ring
  have hgne : z * Complex.exp (γc * z) ≠ 0 := mul_ne_zero hz0 (Complex.exp_ne_zero _)
  have hPne : (∏' n : ℕ, (1 + wTerm n z)) ≠ 0 := by
    intro h
    have h2 := inv_gamma_eq_prod hz
    rw [← hγc, h, mul_zero] at h2
    exact inv_ne_zero hΓne h2
  have hsummable : Summable fun n : ℕ => logDeriv (fun s => 1 + wTerm n s) z := by
    have hcongr : (fun n : ℕ => logDeriv (fun s => 1 + wTerm n s) z)
        = fun n : ℕ => -(1 / ((n : ℂ) + 1) - 1 / (z + n + 1)) := by
      funext n
      rw [logDeriv_one_add_wTerm hz n]
      ring
    rw [hcongr]
    exact (summable_digamma_series hz).neg
  have hlogP : logDeriv (fun s => ∏' n : ℕ, (1 + wTerm n s)) z
      = ∑' n : ℕ, logDeriv (fun s => 1 + wTerm n s) z := by
    refine logDeriv_tprod_eq_tsum hUopen hzU hfne ?_ hsummable htend hPne
    intro n
    have hd : Differentiable ℂ fun s : ℂ => 1 + wTerm n s := by
      unfold wTerm
      fun_prop
    exact hd.differentiableOn
  have hgdiff : Differentiable ℂ fun s : ℂ => s * Complex.exp (γc * s) := by
    fun_prop
  have hPdiff : DifferentiableAt ℂ (fun s => ∏' n : ℕ, (1 + wTerm n s)) z := by
    have hev : (fun s : ℂ => (Complex.Gamma s)⁻¹ / (s * Complex.exp (γc * s)))
        =ᶠ[nhds z] (fun s => ∏' n : ℕ, (1 + wTerm n s)) := by
      filter_upwards [hopenZ.mem_nhds hz] with s hs
      have h2 := inv_gamma_eq_prod hs
      rw [← hγc] at h2
      have hsne : s * Complex.exp (γc * s) ≠ 0 :=
        mul_ne_zero (Complex.integerComplement.ne_zero hs) (Complex.exp_ne_zero _)
      rw [h2]
      exact mul_div_cancel_left₀ _ hsne
    have hd : DifferentiableAt ℂ
        (fun s : ℂ => (Complex.Gamma s)⁻¹ / (s * Complex.exp (γc * s))) z := by
      refine DifferentiableAt.div ?_ (hgdiff z) hgne
      exact Complex.differentiable_one_div_Gamma z
    exact hd.congr_of_eventuallyEq hev.symm
  have hldinv : logDeriv (fun s => (Complex.Gamma s)⁻¹) z = -Complex.digamma z := by
    have h1 : logDeriv ((·⁻¹) ∘ Complex.Gamma) z
        = logDeriv (·⁻¹) (Complex.Gamma z) * deriv Complex.Gamma z := by
      refine logDeriv_comp ?_ (Complex.differentiableAt_Gamma z hzero)
      exact differentiableAt_inv hΓne
    rw [show (fun s => (Complex.Gamma s)⁻¹) = (·⁻¹) ∘ Complex.Gamma from rfl, h1, logDeriv_inv]
    rw [Complex.digamma_def, logDeriv_apply]
    field_simp
  have hev2 : (fun s => (Complex.Gamma s)⁻¹)
      =ᶠ[nhds z] fun s => (s * Complex.exp (γc * s)) * ∏' n : ℕ, (1 + wTerm n s) := by
    filter_upwards [hopenZ.mem_nhds hz] with s hs
    have h2 := inv_gamma_eq_prod hs
    rw [← hγc] at h2
    rw [h2]
  have hlogeq : logDeriv (fun s => (Complex.Gamma s)⁻¹) z
      = logDeriv (fun s => (s * Complex.exp (γc * s)) * ∏' n : ℕ, (1 + wTerm n s)) z := by
    unfold logDeriv
    rw [Pi.div_apply, Pi.div_apply, hev2.deriv_eq, hev2.eq_of_nhds]
  have hmul : logDeriv (fun s => (s * Complex.exp (γc * s)) * ∏' n : ℕ, (1 + wTerm n s)) z
      = logDeriv (fun s : ℂ => s * Complex.exp (γc * s)) z
        + logDeriv (fun s => ∏' n : ℕ, (1 + wTerm n s)) z :=
    logDeriv_mul z hgne hPne (hgdiff z) hPdiff
  have hldg : logDeriv (fun s : ℂ => s * Complex.exp (γc * s)) z = 1 / z + γc := by
    have hder : HasDerivAt (fun s : ℂ => s * Complex.exp (γc * s))
        (1 * Complex.exp (γc * z) + z * (γc * Complex.exp (γc * z))) z := by
      have h1 : HasDerivAt (fun s : ℂ => Complex.exp (γc * s)) (γc * Complex.exp (γc * z)) z := by
        have hlin : HasDerivAt (fun s : ℂ => γc * s) γc z := by
          simpa using (hasDerivAt_id z).const_mul γc
        have h5 := hlin.cexp
        simpa [mul_comm] using h5
      exact (hasDerivAt_id z).mul h1
    unfold logDeriv
    rw [Pi.div_apply, hder.deriv]
    have he : Complex.exp (γc * z) ≠ 0 := Complex.exp_ne_zero _
    field_simp
  have hmain : -Complex.digamma z
      = (1 / z + γc) + ∑' n : ℕ, logDeriv (fun s => 1 + wTerm n s) z := by
    rw [← hldinv, hlogeq, hmul, hldg, hlogP]
  have htsum : ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / (z + n + 1))
      = Complex.digamma z + γc + 1 / z := by
    have h1 : ∑' n : ℕ, logDeriv (fun s => 1 + wTerm n s) z
        = ∑' n : ℕ, -(1 / ((n : ℂ) + 1) - 1 / (z + n + 1)) := by
      congr 1
      funext n
      rw [logDeriv_one_add_wTerm hz n]
      ring
    rw [h1, tsum_neg] at hmain
    linear_combination hmain
  have h := (summable_digamma_series hz).hasSum
  rwa [htsum] at h

set_option maxHeartbeats 1600000 in
theorem digamma_series {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    Complex.digamma z = -(Real.eulerMascheroniConstant : ℂ) - 1 / z
      + ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / (z + n + 1)) := by
  rw [(hasSum_digamma_series hz).tsum_eq]
  ring

end DigammaSeries
end Zeta23
end
end
end

section
namespace Mo360993Large
open Real Filter Set MeasureTheory Finset
open scoped Topology

noncomputable def B (v : ℝ) := 2 - Real.eulerMascheroniConstant*v +
  ∑' k : ℕ, v^2/(((k:ℝ)+1)*((k:ℝ)+1+v))

theorem recip_step (m : ℕ) : HasSum (fun n : ℕ =>
    1/((m:ℝ)+n+1) - 1/((m:ℝ)+n+2)) (1/((m:ℝ)+1)) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => sub_nonneg.mpr
    (one_div_le_one_div_of_le (by positivity) (by linarith))) _).mpr
  have h (N : ℕ) : (∑ k ∈ range N, (1/((m:ℝ)+k+1) - 1/((m:ℝ)+k+2))) =
      1/((m:ℝ)+1) - 1/((m:ℝ)+N+1) := by
    induction N with
    | zero => simp
    | succ N ih => rw [sum_range_succ, ih, Nat.cast_succ]; ring
  simp_rw [h]
  have hlim : Tendsto (fun N : ℕ => 1/((m:ℝ)+N+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_mono (fun N : ℕ => (show (N:ℝ) ≤ m+N+1 by linarith [Nat.cast_nonneg (α := ℝ) m])) tendsto_natCast_atTop_atTop)
  simpa using (tendsto_const_nhds (x := 1/((m:ℝ)+1))).sub hlim

theorem psi_positive_nat (m : ℕ) :
    HasSum (fun n : ℕ => 1/((n:ℝ)+1) - 1/((m:ℝ)+n+1))
      ((Complex.digamma ((m:ℂ)+1)).re + Real.eulerMascheroniConstant) := by
  induction m with
  | zero => simp [Complex.digamma_one]
  | succ m ih =>
    have hr := Complex.digamma_apply_add_one ((m:ℂ)+1) (fun k => by
      intro h
      have e := congrArg Complex.re h
      simp at e
      linarith)
    convert! ih.add (recip_step m) using 1
    · funext n; push_cast; ring
    · push_cast
      rw [hr, Complex.add_re]
      have hi : (((m:ℂ)+1)⁻¹).re = 1/((m:ℝ)+1) := by
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_add,
          ← Complex.ofReal_inv, Complex.ofReal_re, one_div]
      rw [hi]; ring

theorem psi_positive_series {v : ℝ} (hv : 0 < v) :
    HasSum (fun n : ℕ => 1/((n:ℝ)+1) - 1/(v+n+1))
      ((Complex.digamma ((v:ℂ)+1)).re + Real.eulerMascheroniConstant) := by
  by_cases h : (v : ℂ) ∈ Complex.integerComplement
  · have H := Complex.hasSum_re (Zeta23.DigammaSeries.hasSum_digamma_series h)
    have hr := Complex.digamma_apply_add_one (v:ℂ) (fun k => by
      intro e; have h' := congrArg Complex.re e; simp at h'; linarith)
    rw [hr, Complex.add_re]
    convert! H using 1
    · funext n
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_div, ← Complex.ofReal_add, ← Complex.ofReal_add, ← Complex.ofReal_div, ← Complex.ofReal_sub, Complex.ofReal_re]
    · simp only [Complex.add_re, Complex.ofReal_re, one_div]
      ring
  · rw [Complex.mem_integerComplement_iff, not_not] at h
    rcases h with ⟨k,hk⟩
    have he : (k : ℝ) = v := by exact_mod_cast hk
    have hk' : 0 ≤ k := by exact_mod_cast (he.trans_gt hv).le
    lift k to ℕ using hk'
    subst v
    simpa using psi_positive_nat k

theorem B_eq_digamma {v : ℝ} (hv : 0 < v) :
    B v = 2 + v*(Complex.digamma ((v:ℂ)+1)).re := by
  have H := (psi_positive_series hv).mul_left v
  have he (n : ℕ) : v*(1/((n:ℝ)+1)-1/(v+n+1)) = v^2/(((n:ℝ)+1)*((n:ℝ)+1+v)) := by
    field_simp; ring
  unfold B
  simp_rw [he] at H
  rw [H.tsum_eq]; ring

theorem log_gamma_integral {v : ℝ} (hv : 0 < v) :
    (∫ u in Ioi (0 : ℝ), u^v * (Real.log u * Real.exp (-u))) =
      Real.Gamma (v+1)*(Complex.digamma ((v:ℂ)+1)).re := by
  let z : ℂ := (v:ℂ)+1
  have hz : 0 < z.re := by change 0 < v+1; linarith
  have hn : ∀ᶠ w : ℂ in 𝓝 z, 0 < w.re := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
  have hd := (Complex.hasDerivAt_GammaIntegral hz).congr_of_eventuallyEq
    (hn.mono fun w hw => Complex.Gamma_eq_integral hw)
  have he : (∫ u in Ioi (0 : ℝ), (u:ℂ)^(z-1) * ((Real.log u:ℂ) * (Real.exp (-u):ℂ))) =
      ((∫ u in Ioi (0 : ℝ), u^v*(Real.log u*Real.exp (-u)) : ℝ):ℂ) := by
    calc
      _ = ∫ u in Ioi (0 : ℝ), ((u^v * (Real.log u*Real.exp (-u)):ℝ):ℂ) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u hu
        simp [z, Complex.ofReal_cpow (le_of_lt hu)]
      _ = _ := integral_ofReal (𝕜 := ℂ) (μ := volume.restrict (Ioi (0 : ℝ))) (f := fun u : ℝ => u^v*(Real.log u*Real.exp (-u)))
  have hΓ : Complex.Gamma z = (Real.Gamma (v+1):ℂ) := by
    dsimp [z]; rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.Gamma_ofReal]
  have hΓ' := Real.Gamma_pos_of_pos (show 0 < v+1 by linarith)
  have hc : Complex.Gamma z * Complex.digamma z =
      ((∫ u in Ioi (0 : ℝ), u^v*(Real.log u*Real.exp (-u)) : ℝ):ℂ) := by
    rw [Complex.digamma_def, logDeriv_apply, hd.deriv, he, hΓ]
    field_simp [Complex.ofReal_ne_zero.mpr hΓ'.ne']
  have hreal := congrArg Complex.re hc
  rw [hΓ, Complex.re_ofReal_mul, Complex.ofReal_re] at hreal
  exact hreal.symm
end Mo360993Large
end

section
namespace Mo360993Large
open Real Set Filter MeasureTheory
open scoped Topology

noncomputable def powerH (v t : ℝ) := t^(-v)
noncomputable def powerD (v t : ℝ) := -v*t^(-(v+1))

theorem scale_congr {h k d e : ℝ → ℝ} (h1 : h 1 = k 1) (h2 : ∀ t, 1 ≤ t → d t = e t) :
    scaleFunctional h d = scaleFunctional k e := by
  unfold scaleFunctional; rw [h1]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs; unfold compens; rw [h2 1 (le_refl _), h2 (1+s) (by linarith [show 0 < s from hs])]

theorem integral_gamma_weight {v t : ℝ} (hv : 0 < v) (ht : 0 < t) :
    (∫ u in Ioi (0 : ℝ), u^(v-1)*Real.exp (-t*u)) = powerH v t * Real.Gamma v := by
  simp only [neg_mul, powerH, Real.integral_rpow_mul_exp_neg_mul_Ioi hv ht, one_div,
    Real.inv_rpow ht.le, Real.rpow_neg ht.le]

theorem gamma_integr {q : ℝ} (hq : -1 < q) :
    IntegrableOn (fun u : ℝ => u^q*Real.exp (-u)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := q) hq (p := 1) (b := 1) one_pos one_pos
  simpa using h

theorem rpow_step {u : ℝ} (hu : 0 < u) (v : ℝ) : u^(v-1)*u = u^v := by
  simpa only [sub_add_cancel, Real.rpow_one] using (Real.rpow_add hu (v-1) 1).symm

theorem weight_envelope {v : ℝ} (hv : 0 < v) :
    IntegrableOn (fun u : ℝ => |u^(v-1)/Real.Gamma v| * envelope u) (Ioi 0) := by
  have h := (((gamma_integr (q := v-1) (by linarith)).add (gamma_integr (q := v) (by linarith))).add
    (gamma_integr (q := v+1) (by linarith))).div_const (Real.Gamma v)
  apply h.congr
  filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (0 : ℝ)))] with u hu
  have hu' : 0 < u := hu
  rw [abs_of_nonneg (div_nonneg (Real.rpow_nonneg hu'.le _) (Real.Gamma_pos_of_pos hv).le)]
  simp only [Pi.add_apply, envelope]
  rw [Real.rpow_add_one hu'.ne', ← rpow_step hu' v]; ring

theorem gamma_log_integr {v : ℝ} (hv : 0 < v) :
    IntegrableOn (fun u : ℝ => u^v*(Real.log u*Real.exp (-u))) (Ioi 0) := by
  apply ((gamma_integr (q := v+1) (by linarith)).add (gamma_integr (q := v-1) (by linarith))).mono'
    (by fun_prop)
  filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (0 : ℝ)))] with u hu
  have h : 0 < u := hu
  have hlo := Real.log_le_sub_one_of_pos (inv_pos.mpr h)
  rw [Real.log_inv] at hlo
  have hhi := Real.log_le_sub_one_of_pos h
  have habs : |Real.log u| ≤ u+u⁻¹ := abs_le.mpr (by constructor <;> linarith [inv_pos.mpr h])
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg h.le _), abs_of_pos (Real.exp_pos _), Pi.add_apply]
  have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right habs (Real.exp_pos (-u)).le) (Real.rpow_nonneg h.le v)
  rw [Real.rpow_add_one h.ne', Real.rpow_sub_one h.ne']
  exact hh.trans_eq (by ring)

theorem normalized_power {v t : ℝ} (hv : 0 < v) (ht : 0 < t) :
    (∫ u in Ioi (0 : ℝ), (u^(v-1)/Real.Gamma v)*expFamily u t) = powerH v t ∧
    (∫ u in Ioi (0 : ℝ), (u^(v-1)/Real.Gamma v)*expSlope u t) = powerD v t := by
  have hΓ := Real.Gamma_pos_of_pos hv
  constructor
  · simp_rw [expFamily, div_mul_eq_mul_div, integral_div, integral_gamma_weight hv ht]
    field_simp
  · calc
      _ = (∫ u in Ioi (0 : ℝ), u^((v+1)-1)*Real.exp (-t*u)) * (-1/Real.Gamma v) := by
        rw [← integral_mul_const]; apply setIntegral_congr_fun measurableSet_Ioi
        intro u hu
        simp only [add_sub_cancel_right, expSlope, ← rpow_step (show 0 < u from hu) v]; ring
      _ = _ := by rw [integral_gamma_weight (by linarith : 0 < v+1) ht, Real.Gamma_add_one hv.ne']; unfold powerD powerH; field_simp <;> ring

theorem power_functional {v : ℝ} (hv : 0 < v) : scaleFunctional (powerH v) (powerD v) = B v := by
  have he := exponential_lift (μ := volume.restrict (Ioi (0 : ℝ))) (U := id)
    (A := fun u : ℝ => u^(v-1)/Real.Gamma v) measurable_id (by fun_prop)
    (ae_restrict_mem measurableSet_Ioi) (weight_envelope hv)
  simp only [id_eq] at he
  rw [scale_congr (normalized_power hv one_pos).1 (fun t ht => (normalized_power hv (lt_of_lt_of_le zero_lt_one ht)).2)] at he
  rw [← he, B_eq_digamma hv]
  have hΓ := Real.Gamma_pos_of_pos hv
  calc
    _ = (2*(∫ u in Ioi (0 : ℝ), u^(v-1)*Real.exp (-u)) +
        (∫ u in Ioi (0 : ℝ), u^v*(Real.log u*Real.exp (-u))))/Real.Gamma v := by
      rw [← integral_const_mul, ← integral_add ((gamma_integr (q := v-1) (by linarith)).const_mul 2) (gamma_log_integr hv), ← integral_div]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu; dsimp only; rw [← rpow_step (show 0 < u from hu) v]; ring
    _ = _ := by
      have hi := integral_gamma_weight hv (t := 1) one_pos
      simp [powerH] at hi
      rw [hi, log_gamma_integral hv, Real.Gamma_add_one hv.ne']
      field_simp <;> ring
end Mo360993Large
end

section
namespace Mo360993Large
open Real MeasureTheory Set Filter
open scoped Topology

theorem remainder_integral_nonneg {R D : ℝ → ℝ} (hR : R 0 = 0)
    (hD : D 0 = 0) (hd : ∀ s, 0 ≤ s → HasDerivAt R (D s) s)
    (hc : ∀ s, 0 < s → ContinuousAt D s) (hm : Measurable D)
    (hi : IntegrableOn (fun s => D s / s) (Ioi 0))
    (hs : ∀ s, 0 < s → 0 ≤ R s) (ht : Tendsto (fun s => R s/s) atTop (𝓝 0)) :
    0 ≤ ∫ s in Ioi (0 : ℝ), D s/s := by
  let q : ℝ → ℝ := (Ioi (0 : ℝ)).indicator (fun s => D s/s)
  have hqi : Integrable q := (integrable_indicator_iff measurableSet_Ioi).mpr hi
  have hqm : Measurable q := (hm.div measurable_id).indicator measurableSet_Ioi
  let P (x : ℝ) := (∫ s in (0 : ℝ)..x, q s) - R x/x
  have hdiv : ContinuousAt (fun s => R s/s) 0 := by
    rw [continuousAt_iff_punctured_nhds]
    simpa [hR, hD, div_eq_inv_mul, smul_eq_mul] using (hd 0 (le_refl _)).tendsto_slope_zero
  have h0 : ContinuousWithinAt P (Ici 0) 0 :=
    ((hqi.continuous_primitive 0).continuousAt.sub hdiv).continuousWithinAt
  have hi' : Tendsto P atTop (𝓝 (∫ s in Ioi (0 : ℝ), D s/s)) := by
    have hq := intervalIntegral_tendsto_integral_Ioi 0 hqi.integrableOn tendsto_id
    have he : (∫ s in Ioi (0 : ℝ), q s) = ∫ s in Ioi (0 : ℝ), D s/s := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs; exact Set.indicator_of_mem hs _
    rw [he] at hq
    simpa [P] using hq.sub ht
  have hd' (s : ℝ) (hs : 0 < s) : HasDerivAt P (R s/s^2) s := by
    have hq : q =ᶠ[𝓝 s] (fun s => D s/s) := by
      filter_upwards [Ioi_mem_nhds hs] with t ht
      exact Set.indicator_of_mem ht _
    have hqa : ContinuousAt q s := ((hc s hs).div continuousAt_id hs.ne').congr hq.symm
    have H := (intervalIntegral.integral_hasDerivAt_right (a := 0) hqi.intervalIntegrable
      hqm.stronglyMeasurable.stronglyMeasurableAtFilter hqa).sub ((hd s hs.le).div (hasDerivAt_id s) hs.ne')
    unfold P
    convert! H using 1
    rw [hq.eq_of_nhds]
    dsimp
    field_simp
    ring
  have he := integral_Ioi_of_hasDerivAt_of_nonneg h0 (fun x hx => hd' x hx)
    (fun x hx => div_nonneg (hs x hx) (sq_nonneg _)) hi'
  have hn : 0 ≤ ∫ s in Ioi (0 : ℝ), R s/s^2 := by
    apply setIntegral_nonneg measurableSet_Ioi; intro x hx; exact div_nonneg (hs x hx) (sq_nonneg _)
  simpa [he, P] using hn
end Mo360993Large
end

section
namespace Mo360993Large
open Real MeasureTheory Set Filter
open scoped Topology

theorem power_comp_integrable {v : ℝ} (hv : 0 < v) : IntegrableOn (compens (powerD v)) (Ioi 0) := by
  have he := (exponential_lift_data (μ := volume.restrict (Ioi (0 : ℝ))) (U := id)
    (A := fun u : ℝ => u^(v-1)/Real.Gamma v) measurable_id (by fun_prop)
    (ae_restrict_mem measurableSet_Ioi) (weight_envelope hv)).1
  apply he.congr_fun _ measurableSet_Ioi
  intro s hs; unfold compens
  simp only [id_eq]
  rw [(normalized_power hv (t := 1+s) (by linarith [show 0 < s from hs])).2, (normalized_power hv one_pos).2]

theorem gp_comp_integrable {r y : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1) (hy : 0 ≤ y) :
    IntegrableOn (compens (dgp r y)) (Ioi 0) := by
  apply (cutoff_integrable.const_mul 23).mono' (Measurable.aestronglyMeasurable (by unfold compens dgp gp arg; fun_prop))
  filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (0 : ℝ)))] with s hs
  exact dgp_compens_bound hr hr' hy hs

def lin4 (a b c d : ℝ) (f g h k : ℝ → ℝ) (t : ℝ) := a*f t+b*g t+c*h t+d*k t

theorem compens_lin4 (a b c d : ℝ) (f g h k : ℝ → ℝ) :
    compens (lin4 a b c d f g h k) = lin4 a b c d (compens f) (compens g) (compens h) (compens k) := by
  funext s; unfold compens lin4; ring

theorem integral_lin4 (a b c d : ℝ) {f g h k : ℝ → ℝ} {μ : Measure ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) (hk : Integrable k μ) :
    Integrable (lin4 a b c d f g h k) μ ∧
    (∫ t, lin4 a b c d f g h k t ∂μ) = a*(∫ t, f t ∂μ)+b*(∫ t, g t ∂μ)+c*(∫ t, h t ∂μ)+d*(∫ t, k t ∂μ) := by
  have h1 : Integrable (fun x => a*f x + b*g x) μ := (hf.const_mul a).add (hg.const_mul b)
  have h2 : Integrable (fun x => a*f x + b*g x + c*h x) μ := h1.add (hh.const_mul c)
  unfold lin4
  refine ⟨h2.add (hk.const_mul d), ?_⟩
  rw [integral_add h2 (hk.const_mul d), integral_add h1 (hh.const_mul c), integral_add (hf.const_mul a) (hg.const_mul b)]
  simp only [integral_const_mul]

theorem scale_lin4 (a b c d : ℝ) (f g h k f' g' h' k' : ℝ → ℝ)
    (hf : IntegrableOn (compens f') (Ioi 0)) (hg : IntegrableOn (compens g') (Ioi 0))
    (hh : IntegrableOn (compens h') (Ioi 0)) (hk : IntegrableOn (compens k') (Ioi 0)) :
    scaleFunctional (lin4 a b c d f g h k) (lin4 a b c d f' g' h' k') =
    a*scaleFunctional f f'+b*scaleFunctional g g'+c*scaleFunctional h h'+d*scaleFunctional k k' := by
  unfold scaleFunctional; rw [compens_lin4, (integral_lin4 a b c d hf hg hh hk).2]; unfold lin4; ring

theorem power_der {v t : ℝ} (ht : 0 < t) : HasDerivAt (powerH v) (powerD v t) t := by
  unfold powerH powerD
  convert! der_power (-v) ht using 1
  rw [show -(v+1) = -v-1 by ring, Real.rpow_sub_one ht.ne']; ring

noncomputable def model (r y : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  lin4 (1+y+y^2/2+y^3/6) (-y-y^2-y^3/2) (y^2/2+y^3/2) (-y^3/6)
    (f r) (f (3*r)) (f (5*r)) (f (7*r))

theorem model_der {r y t : ℝ} (ht : 0 < t) :
    HasDerivAt (model r y powerH) (model r y powerD t) t :=
  (((((power_der (v := r) ht).const_mul _).add ((power_der (v := 3*r) ht).const_mul _)).add
    ((power_der (v := 5*r) ht).const_mul _)).add ((power_der (v := 7*r) ht).const_mul _))

theorem model_comp_integrable {r y : ℝ} (hr : 0 < r) : IntegrableOn (compens (model r y powerD)) (Ioi 0) := by
  unfold model; rw [compens_lin4]
  exact (integral_lin4 _ _ _ _ (power_comp_integrable hr) (power_comp_integrable (by positivity))
    (power_comp_integrable (by positivity)) (power_comp_integrable (by positivity))).1

noncomputable def cub (r y : ℝ) := B r + (B r-B (3*r))*y +
  (B r-2*B (3*r)+B (5*r))*y^2/2 + (B r-3*B (3*r)+3*B (5*r)-B (7*r))*y^3/6

theorem model_functional {r y : ℝ} (hr : 0 < r) :
    scaleFunctional (model r y powerH) (model r y powerD) = cub r y := by
  unfold model; rw [scale_lin4 _ _ _ _ _ _ _ _ _ _ _ _ (power_comp_integrable hr)
    (power_comp_integrable (by positivity)) (power_comp_integrable (by positivity)) (power_comp_integrable (by positivity))]
  rw [power_functional hr, power_functional (show 0 < 3*r by positivity),
    power_functional (show 0 < 5*r by positivity), power_functional (show 0 < 7*r by positivity)]
  unfold cub; ring

theorem model_value (r y : ℝ) : Real.exp y * gp r y 1 = model r y powerH 1 := by
  simp [gp,model,lin4,powerH,Real.exp_neg]; ring
theorem model_slope (r y : ℝ) : Real.exp y * dgp r y 1 = model r y powerD 1 := by
  simp [dgp,gp,arg,model,lin4,powerD,Real.exp_neg]; field_simp <;> ring

theorem model_lower {r y t : ℝ} (hr : 0 ≤ r) (hy : 0 ≤ y) (ht : 1 ≤ t) :
    model r y powerH t ≤ Real.exp y * gp r y t := by
  have hp : 0 < t := lt_of_lt_of_le zero_lt_one ht
  let b := t^(-2*r)
  let z := y*(1-b)
  have hb : b ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht (by nlinarith)
  have hz : 0 ≤ z := mul_nonneg hy (sub_nonneg.mpr hb)
  have h := Real.sum_le_exp_of_nonneg hz 4
  norm_num [Finset.sum_range_succ] at h
  have hh (n : ℕ) : t^(-((2*(n:ℝ)+1)*r)) = t^(-r)*b^n := by
    dsimp [b]
    rw [← Real.rpow_mul_natCast hp.le, ← Real.rpow_add hp]; congr 1; ring
  have h1 := hh 1; have h2 := hh 2; have h3 := hh 3
  norm_num at h1 h2 h3
  have he : Real.exp y*gp r y t = t^(-r)*Real.exp z := by
    unfold gp z b
    rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  rw [he]; unfold model lin4 powerH
  rw [h1,h2,h3]
  apply le_trans _ (mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hp.le _))
  apply le_of_eq; dsimp [z]; ring

set_option maxHeartbeats 1500000 in
theorem model_comparison {r y : ℝ} (hr : 0 < r) (hr' : r ≤ 1) (hy : 0 ≤ y) :
    Real.exp (-y)*cub r y ≤ scaleFunctional (gp r y) (dgp r y) := by
  let R (s : ℝ) := Real.exp y * gp r y (1+s) - model r y powerH (1+s)
  let D (s : ℝ) := Real.exp y * dgp r y (1+s) - model r y powerD (1+s)
  have hR : R 0 = 0 := by simpa only [R,add_zero,sub_eq_zero] using model_value r y
  have hD : D 0 = 0 := by simpa only [D,add_zero,sub_eq_zero] using model_slope r y
  have hd (s : ℝ) (hs : 0 ≤ s) : HasDerivAt R (D s) s := by
    have ht : 0 < 1+s := by linarith
    simpa [R,D] using! ((((der_gp r y ht).const_mul (Real.exp y)).sub (model_der (r := r) (y := y) ht)).comp s ((hasDerivAt_id s).const_add 1))
  have hc (s : ℝ) (hs : 0 < s) : ContinuousAt D s := by
    have ht : 0 < 1+s := by linarith
    have hp (v : ℝ) : ContinuousAt (powerD v) (1+s) :=
      continuousAt_const.mul (der_power (-(v+1)) ht).continuousAt
    have hm : ContinuousAt (model r y powerD) (1+s) :=
      ((((continuousAt_const.mul (hp r)).add (continuousAt_const.mul (hp (3*r)))).add
        (continuousAt_const.mul (hp (5*r)))).add (continuousAt_const.mul (hp (7*r))))
    exact (((continuousAt_const.mul (der_dgp r y ht).continuousAt).sub hm).comp
      (continuousAt_const.add continuousAt_id))
  have hh : Measurable D := by
    unfold D dgp gp arg model lin4 powerD
    fun_prop
  have he (s : ℝ) : D s / s = Real.exp y*compens (dgp r y) s-compens (model r y powerD) s := by
    unfold D compens
    rw [← model_slope]
    ring
  have i1 := (gp_comp_integrable hr.le hr' hy).const_mul (Real.exp y)
  have i2 := model_comp_integrable (y := y) hr
  have hi : IntegrableOn (fun s => D s / s) (Ioi 0) := by simp_rw [he]; exact i1.sub i2
  have hs (s : ℝ) (hs : 0 < s) : 0 ≤ R s := sub_nonneg.mpr (model_lower hr.le hy (by linarith))
  have ht : Tendsto (fun s : ℝ => 1+s) atTop atTop := tendsto_atTop_mono (fun x => (show x ≤ 1+x by linarith)) tendsto_id
  have hpower {v : ℝ} (hv : 0 < v) : Tendsto (fun s : ℝ => powerH v (1+s)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hv).comp ht
  have hgp : Tendsto (fun s : ℝ => gp r y (1+s)) atTop (𝓝 0) := by
    have hz := (hpower (v := 2*r) (by positivity)).const_mul (-y)
    unfold gp; simpa [powerH,neg_mul] using (hpower hr).mul (Real.continuous_exp.continuousAt.tendsto.comp hz)
  have hm : Tendsto (fun s : ℝ => model r y powerH (1+s)) atTop (𝓝 0) := by
    simpa [model,lin4] using (((((hpower hr).const_mul (1+y+y^2/2+y^3/6)).add ((hpower (v := 3*r) (by positivity)).const_mul (-y-y^2-y^3/2))).add
      ((hpower (v := 5*r) (by positivity)).const_mul (y^2/2+y^3/2))).add ((hpower (v := 7*r) (by positivity)).const_mul (-y^3/6)))
  have hlim : Tendsto (fun s => R s/s) atTop (𝓝 0) := ((hgp.const_mul (Real.exp y)).sub hm).div_atTop tendsto_id
  have hn := remainder_integral_nonneg hR hD hd hc hh hi hs hlim
  simp_rw [he] at hn; rw [integral_sub i1 i2, integral_const_mul] at hn
  rw [← model_functional hr (y := y)]
  unfold scaleFunctional
  rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]
  nlinarith only [hn,model_value r y]
end Mo360993Large
end

section
namespace Mo360993Large
open Real Set Filter MeasureTheory
open scoped Topology

theorem envelope_est {u : ℝ} (hu : 0 ≤ u) : envelope u ≤ 11*Real.exp (-(u/2)) := by
  have h₂ := Real.pow_div_factorial_le_exp (u/2) (by positivity) 2
  norm_num at h₂
  have h₁ := Real.add_one_le_exp (u/2)
  have h₀ := Real.one_le_exp (by positivity : 0 ≤ u/2)
  have h : 1+u+u^2 ≤ 11*Real.exp (u/2) := by nlinarith
  unfold envelope
  apply (mul_le_mul_of_nonneg_right h (Real.exp_pos _).le).trans_eq
  rw [mul_assoc, ← Real.exp_add]; congr 2; ring

theorem physical_lift {a : ℝ} (ha : 0 < a) (w : ℝ) :
    (∫ x : ℝ, Real.cos (w*x)*(Real.exp (-|x|^a)*(2+|x|^a*Real.log (|x|^a)))) =
      scaleFunctional (fun t => ∫ x : ℝ, Real.cos (w*x)*expFamily (|x|^a) t)
        (fun t => ∫ x : ℝ, Real.cos (w*x)*expSlope (|x|^a) t) := by
  apply exponential_lift (by fun_prop) (by fun_prop)
  · filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
    exact Real.rpow_pos_of_pos (abs_pos.mpr hx) _
  · apply ((envelope_integrable ha (b := 1/2) (by norm_num)).const_mul 11).mono' (by unfold envelope; fun_prop)
    filter_upwards with x
    let u := |x|^a
    have hu : 0 ≤ u := Real.rpow_nonneg (abs_nonneg _) _
    have hp : 0 ≤ envelope u := mul_nonneg (by positivity) (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hp)]
    exact ((mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) hp).trans_eq (one_mul _)).trans
      ((envelope_est hu).trans_eq (by dsimp [u]; congr 2; ring))

theorem semigroup_bound {t b u : ℝ} (ht : 0 < t) (hb : t/2 < b) (hu : 0 ≤ u) :
    |expSlope u b| ≤ (4/t)*Real.exp (-(t/4)*u) := by
  unfold expSlope; rw [abs_mul, abs_neg, abs_of_nonneg hu, abs_of_pos (Real.exp_pos _)]
  have h₁ : Real.exp (-b*u) ≤ Real.exp ((-(t/4)*u)+(-(t/4)*u)) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr hb.le) hu])
  have h₂ := damped_linear (show 0 ≤ (t/4)*u by positivity)
  rw [show -((t/4)*u) = -(t/4)*u by ring] at h₂
  have h₃ : u*Real.exp (-(t/4)*u) ≤ 4/t := (le_div_iff₀ ht).mpr (by linarith only [show u*Real.exp (-(t/4)*u)*t = 4*((t/4)*u*Real.exp (-(t/4)*u)) by ring,h₂])
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left h₁ hu
    _ = (u*Real.exp (-(t/4)*u))*Real.exp (-(t/4)*u) := by rw [Real.exp_add,mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_right h₃ (Real.exp_pos _).le

theorem physical_der {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (w : ℝ) :
    HasDerivAt (fun b => ∫ x : ℝ, Real.cos (w*x)*expFamily (|x|^a) b)
      (∫ x : ℝ, Real.cos (w*x)*expSlope (|x|^a) t) t := by
  have hi : Integrable (fun x : ℝ => Real.cos (w*x)*expFamily (|x|^a) t) :=
    (envelope_integrable ha ht).bdd_mul (c := 1) (by fun_prop) (.of_forall (fun x => by simpa using Real.abs_cos_le_one (w*x)))
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun b (x : ℝ) => Real.cos (w*x)*expFamily (|x|^a) b)
    (F' := fun b (x : ℝ) => Real.cos (w*x)*expSlope (|x|^a) b)
    (bound := fun x : ℝ => (4/t)*Real.exp (-(t/4)*|x|^a))
    (Ioi_mem_nhds (by linarith : t/2<t)) (.of_forall (fun _ => by unfold expFamily; fun_prop))
    hi (by unfold expSlope; fun_prop) _ ((envelope_integrable ha (b := t/4) (by positivity)).const_mul _) _).2
  · filter_upwards with x b hb
    rw [Real.norm_eq_abs,abs_mul]
    exact ((mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)).trans_eq (one_mul _)).trans
      (semigroup_bound ht hb (Real.rpow_nonneg (abs_nonneg x) _))
  · filter_upwards with x b hb
    unfold expFamily expSlope
    convert! (((hasDerivAt_id b).neg.mul_const (|x|^a)).exp.const_mul (Real.cos (w*x))) using 1
    simp only [Pi.neg_apply, id_eq]; ring

theorem gaussian_der {V : Type*} [MeasurableSpace V] {ν : Measure V} {C Y : V → ℝ}
    (hC : Integrable C ν) (hC' : Measurable C) (hY : Measurable Y) (hpos : ∀ᵐ v ∂ν, 0 ≤ Y v)
    {r t : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1) (ht : 0 < t) :
    HasDerivAt (fun b => ∫ v, C v*gp r (Y v) b ∂ν) (∫ v, C v*dgp r (Y v) t ∂ν) t := by
  have hi : Integrable (fun v => C v*gp r (Y v) t) ν := by
    apply (hC.norm.mul_const (t^(-r))).mono' (by unfold gp; fun_prop)
    filter_upwards [hpos] with v hv
    simp only [gp, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht.le _), abs_of_pos (Real.exp_pos _)]
    have h := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hv) (Real.rpow_nonneg ht.le (-2*r)))
    nlinarith only [mul_nonneg (mul_nonneg (abs_nonneg (C v)) (Real.rpow_nonneg ht.le (-r))) (sub_nonneg.mpr h)]
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun b v => C v*gp r (Y v) b)
    (F' := fun b v => C v*dgp r (Y v) b)
    (bound := fun v => ‖C v‖*(3*((t/2)^(-r)/(t/2))))
    (Ioi_mem_nhds (by linarith : t/2<t)) (.of_forall (fun _ => by unfold gp; fun_prop))
    hi (by unfold dgp gp arg; fun_prop) _ (hC.norm.mul_const _) _).2
  · filter_upwards [hpos] with v hv b hb
    have hh : 0 < t/2 := by positivity
    have hb' : t/2 < b := hb
    simp only [Real.norm_eq_abs,abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply (dgp_bound hr hr' hv (hh.trans hb')).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact div_le_div₀ (Real.rpow_nonneg hh.le _) (Real.rpow_le_rpow_of_nonpos hh hb'.le (neg_nonpos.mpr hr)) hh hb'.le
  · filter_upwards with v b hb
    exact (der_gp r (Y v) (lt_trans (half_pos ht) hb)).const_mul _
end Mo360993Large
end

section
namespace Mo360993Large
open Real MeasureTheory Set Filter
open scoped Topology

theorem gaussian_lift {V : Type*} [MeasurableSpace V] {ν : Measure V} [SFinite ν]
    {C Y : V → ℝ} (hC : Integrable C ν) (hC' : Measurable C) (hY : Measurable Y)
    (hpos : ∀ᵐ v ∂ν, 0 ≤ Y v) {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1) :
    Integrable (fun v => C v*scaleFunctional (gp r (Y v)) (dgp r (Y v))) ν ∧
    (∫ v, C v*scaleFunctional (gp r (Y v)) (dgp r (Y v)) ∂ν) =
    scaleFunctional (fun t => ∫ v, C v*gp r (Y v) t ∂ν) (fun t => ∫ v, C v*dgp r (Y v) t ∂ν) := by
  let σ := volume.restrict (Ioi (0 : ℝ))
  have hs : ∀ᵐ s ∂σ, 0 < s := ae_restrict_mem measurableSet_Ioi
  let F (v : V) (s : ℝ) := C v*compens (dgp r (Y v)) s
  have hcut : Measurable cutoff := Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const (by fun_prop)
  have hf : Integrable (Function.uncurry F) (ν.prod σ) := by
    apply (hC.norm.mul_prod (cutoff_integrable.const_mul 23)).mono'
    · apply Measurable.aestronglyMeasurable; unfold F Function.uncurry compens dgp gp arg; fun_prop
    · rw [Measure.ae_prod_iff_ae_ae]
      · filter_upwards [hpos] with v hv
        filter_upwards [hs] with s hs'
        simp only [Function.uncurry,F,Real.norm_eq_abs,abs_mul]
        exact mul_le_mul_of_nonneg_left (dgp_compens_bound hr hr' hv hs') (abs_nonneg _)
      · exact measurableSet_le (by unfold Function.uncurry F compens dgp gp arg; fun_prop) (by fun_prop)
  have h0 : Integrable (fun v => C v*gp r (Y v) 1) ν := by
    apply hC.mono (by unfold gp; fun_prop)
    filter_upwards [hpos] with v hv
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    exact ((mul_le_mul_of_nonneg_left (bounded_gp hr hv (le_refl _)) (abs_nonneg _)).trans_eq (mul_one _))
  have hd {t : ℝ} (ht : 1 ≤ t) : Integrable (fun v => C v*dgp r (Y v) t) ν := by
    apply (hC.norm.mul_const (3*(t^(-r)/t))).mono' (by unfold dgp gp arg; fun_prop)
    filter_upwards [hpos] with v hv
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (dgp_bound hr hr' hv (lt_of_lt_of_le zero_lt_one ht)) (abs_nonneg _)
  have he (v : V) : C v*scaleFunctional (gp r (Y v)) (dgp r (Y v)) =
      2*(C v*gp r (Y v) 1) + ∫ s, F v s ∂σ := by
    unfold scaleFunctional F σ; rw [integral_const_mul]; ring
  have hint : Integrable (fun v => ∫ s, F v s ∂σ) ν := hf.integral_prod_left
  constructor
  · simp_rw [he]; exact (h0.const_mul 2).add hint
  simp_rw [he]
  rw [integral_add (h0.const_mul 2) hint, integral_const_mul, integral_integral_swap hf]
  unfold scaleFunctional
  congr 1
  apply integral_congr_ae
  filter_upwards [hs] with s hs'
  unfold F compens
  have he' (v : V) : C v*((dgp r (Y v) (1+s)-Real.exp (-s)*dgp r (Y v) 1)/s) =
      (C v*dgp r (Y v) (1+s)-Real.exp (-s)*(C v*dgp r (Y v) 1))/s := by ring
  simp_rw [he']
  rw [integral_div, integral_sub (hd (by linarith)) ((hd (le_refl 1)).const_mul _), integral_const_mul]
end Mo360993Large
end

section
namespace Mo360993Large
open Real Set Filter MeasureTheory
open scoped Topology

theorem int_cub {V : Type*} [MeasurableSpace V] {ν : Measure V} {C Y : V → ℝ}
    (hC : Integrable C ν) (hC' : Measurable C) (hY : Measurable Y) (hp : ∀ᵐ v ∂ν, 0 ≤ Y v) (r : ℝ) :
    Integrable (fun v => C v*Real.exp (-Y v)*cub r (Y v)) ν := by
  let T (n : ℕ) (v : V) := C v*Real.exp (-Y v)*(Y v)^n
  have hi (n : ℕ) : Integrable (T n) ν := by
    apply (hC.norm.mul_const (n.factorial:ℝ)).mono' (by unfold T; fun_prop)
    filter_upwards [hp] with v hv
    have he := Real.pow_div_factorial_le_exp (Y v) hv n
    have hn : 0 < (n.factorial:ℝ) := by positivity
    have hn' := (div_le_iff₀ hn).mp he
    have hh : Real.exp (-Y v)*Y v^n ≤ n.factorial := by
      rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]
      linarith
    simp only [T,Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _),abs_of_nonneg (pow_nonneg hv n)]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hh (abs_nonneg _)
  let c1 := B r-B (3*r)
  let c2 := (B r-2*B (3*r)+B (5*r))/2
  let c3 := (B r-3*B (3*r)+3*B (5*r)-B (7*r))/6
  apply (((((hi 0).const_mul (B r)).add ((hi 1).const_mul c1)).add ((hi 2).const_mul c2)).add ((hi 3).const_mul c3)).congr
  filter_upwards with v
  simp only [Pi.add_apply,T,pow_zero,pow_one,c1,c2,c3,cub]
  ring

theorem large_cosine_bound {a : ℝ} (ha : 0 < a) (har : 1 ≤ a) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hm : ∀ x : ℝ, Real.exp (-|x|^a) = ∫ v in Ioi (0 : ℝ), Real.exp (-v*x^2) ∂μ)
    (w : ℝ) :
    (∫ v in Ioi (0 : ℝ), Real.sqrt (Real.pi/v)*Real.exp (-(w^2/(4*v)))*cub (1/a) (w^2/(4*v)) ∂μ) ≤
      ∫ x : ℝ, Real.cos (w*x)*(Real.exp (-|x|^a)*(2+|x|^a*Real.log (|x|^a))) := by
  let ν := μ.restrict (Ioi (0 : ℝ))
  let r := 1/a
  let C (v : ℝ) := Real.sqrt (Real.pi/v)
  let Y (v : ℝ) := w^2/(4*v)
  have hr : 0 < r := by dsimp [r]; positivity
  have hr' : r ≤ 1 := (div_le_one ha).mpr har
  have hC' : Measurable C := by unfold C; fun_prop
  have hY : Measurable Y := by unfold Y; fun_prop
  have hpos : ∀ᵐ v ∂ν, 0 ≤ Y v := (ae_restrict_mem (μ := μ) measurableSet_Ioi).mono (fun v hv =>
    div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (le_of_lt hv)))
  obtain ⟨hC, hspec⟩ := spectral_family ha hm
  have hi : Integrable C ν := hC
  obtain ⟨hL,hLeq⟩ := gaussian_lift hi hC' hY hpos hr.le hr'
  have hder (t : ℝ) (ht : 0 < t) :
      (∫ x : ℝ, Real.cos (w*x)*expSlope (|x|^a) t) = ∫ v, C v*dgp r (Y v) t ∂ν := by
    have hes : (fun b => ∫ v, C v*gp r (Y v) b ∂ν) =ᶠ[𝓝 t]
        (fun b => ∫ x : ℝ, Real.cos (w*x)*expFamily (|x|^a) b) := by
      filter_upwards [Ioi_mem_nhds ht] with b hb using (hspec b hb w).symm
    exact ((physical_der ha ht w).congr_of_eventuallyEq hes).unique (gaussian_der hi hC' hY hpos hr.le hr' ht)
  have heq := scale_congr
    (h := fun t => ∫ x : ℝ, Real.cos (w*x)*expFamily (|x|^a) t)
    (k := fun t => ∫ v, C v*gp r (Y v) t ∂ν)
    (d := fun t => ∫ x : ℝ, Real.cos (w*x)*expSlope (|x|^a) t)
    (e := fun t => ∫ v, C v*dgp r (Y v) t ∂ν)
    (hspec 1 one_pos w) (fun t ht => hder t (lt_of_lt_of_le zero_lt_one ht))
  rw [physical_lift ha w, heq, ← hLeq]
  apply integral_mono_ae (int_cub hi hC' hY hpos r) hL
  filter_upwards [hpos] with v hv
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (model_comparison hr hr' hv) (Real.sqrt_nonneg _)

end Mo360993Large

theorem Mo360993Full.large : OMA.R_mo_360993_R1.H2 := by
  intro a ha ha'
  have hp : 0 < a := by linarith
  obtain ⟨μ,hμ,hm⟩ := Mo360993.gaussian_mixture hp ha'.le
  let : MeasureTheory.IsProbabilityMeasure μ := hμ
  refine ⟨μ,hμ,hm,?_⟩
  intro w
  have h := Mo360993Large.large_cosine_bound hp (by linarith) hm (2*Real.pi*w)
  convert! h using 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  have he : -2*Real.pi*x*w = -((2*Real.pi*w)*x) := by ring
  rw [he, Real.cos_neg]
end
end

section
/-! Bound the four finite differences of the digamma series on intervals
[i/80,(i+1)/80]. The tail of the linear coefficient is bounded by a
telescoping reciprocal sum. All other omitted summands are nonnegative. -/

open Real Finset Filter Set
open scoped Topology
namespace Mo360993
def scale : ℕ := 1000000

def lower (x y : ℕ) : ℕ := scale * x / y

def upper (x y : ℕ) : ℕ := (scale * x + y - 1) / y

def coeffs (i : ℕ) : ℕ × ℕ × ℕ × ℕ := Id.run do
  let den := 80
  let j := i + 1
  let mut constant := 2 * scale - upper (58 * j) (100 * den)
  let mut penalty := upper (8 * j^2) (den^2 * 128)
  let mut quadratic := 0
  let mut cubic := 0
  for k in [:128] do
    let n := k + 1
    let v := den * n
    let m := (v + j) * (v + 3*j)
    let w := m * (v + 5*j)
    constant := constant + lower (i^2) (v * (v+j))
    penalty := penalty + upper (2*j*(4*v*j + 3*j^2)) (v*m)
    quadratic := quadratic + lower (4*i^2*v) w
    cubic := cubic + lower (8*i^3*v) (w*(v+7*j))
  return (constant, penalty - lower (2*57*i) (100*den), quadratic, cubic)

def cellOK (i : ℕ) : Bool :=
  let (a, b, c, d) := coeffs i
  decide (27*d < 4*b ∧ 27*d < 4*a ∧ (4*b-27*d)^2 < 16*c*(4*a-27*d))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem cubic_cells : (List.range 24).all (fun i => cellOK (40+i)) = true := by
  decide +kernel

theorem cubic_pos (a b c d y : ℝ) (hc : 0 < c) (hd : 0 ≤ d) (hy : 0 ≤ y)
    (h : (4*b - 27*d)^2 < 16*c*(4*a - 27*d)) :
    0 < a - b*y + c*y^2 + d*y^3 := by
  have tangent : 0 ≤ d * ((y - 3/2)^2 * (y + 3)) :=
    mul_nonneg hd (mul_nonneg (sq_nonneg _) (by linarith))
  have hs := sq_nonneg (8*c*y - (4*b - 27*d))
  nlinarith only [h, hs, mul_nonneg hc.le tangent, hc]




/-- Pass from the verified integer in a cell to all real arguments and all
coefficients enclosed by that cell's four directed bounds. -/
theorem enclosed_cubic_pos (i : ℕ) (hi : 40 ≤ i ∧ i < 64)
    (A B C D y : ℝ) (hy : 0 ≤ y)
    (hA : (coeffs i).1 ≤ A * scale) (hB : B * scale ≤ (coeffs i).2.1)
    (hC : (coeffs i).2.2.1 ≤ C * scale) (hD : (coeffs i).2.2.2 ≤ D * scale) :
    0 < A - B*y + C*y^2 + D*y^3 := by
  have hbool := List.all_eq_true.mp cubic_cells (i-40) (List.mem_range.mpr (by omega))
  rw [show 40+(i-40) = i by omega] at hbool
  obtain ⟨a,b,c,d,he⟩ : ∃ a b c d, coeffs i = (a,b,c,d) := by
    obtain ⟨a,b,c,d⟩ := coeffs i
    exact ⟨a,b,c,d,rfl⟩
  simp only [cellOK, he, decide_eq_true_eq] at hbool
  simp only [he] at hA hB hC hD
  obtain ⟨hb, ha, hs⟩ := hbool
  have hc : 0 < c := by
    by_contra! h
    have : c = 0 := by omega
    simp [this] at hs
  have hcast : ((4:ℝ)*b-27*d)^2 < 16*c*(4*a-27*d) := by
    have hh : ((4*b-27*d : ℕ) : ℝ)^2 < 16*(c:ℝ)*((4*a-27*d : ℕ) : ℝ) := by exact_mod_cast hs
    simpa only [Nat.cast_sub hb.le, Nat.cast_sub ha.le, Nat.cast_mul, Nat.cast_ofNat] using hh
  have hpos := cubic_pos (a:ℝ) b c d y (by exact_mod_cast hc) (by positivity) hy hcast
  have hscale : 0 < (scale : ℝ) := by norm_num [scale]
  apply (mul_pos_iff_of_pos_right hscale).mp
  nlinarith only [hpos, hA, mul_nonneg (sub_nonneg.mpr hB) hy,
    mul_nonneg (sub_nonneg.mpr hC) (sq_nonneg y),
    mul_nonneg (sub_nonneg.mpr hD) (pow_nonneg hy 3)]

set_option maxRecDepth 10000 in
theorem euler_bounds : 0.57 < Real.eulerMascheroniConstant ∧
    Real.eulerMascheroniConstant < 0.58 := by
  have lo := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 256
  have hi := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 256
  simp only [Real.eulerMascheroniSeq, Real.eulerMascheroniSeq',
    Nat.cast_ofNat, OfNat.ofNat_ne_zero, if_false] at lo hi
  have log256 : Real.log 256 = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2^8 by norm_num, Real.log_pow]
    norm_num
  have log257 : Real.log 257 ≤ Real.log 256 + 1/256 := by
    rw [← sub_le_iff_le_add', ← Real.log_div (by norm_num) (by norm_num)]
    exact (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
  have hrat : (6124/1000 : ℚ) ≤ harmonic 256 ∧ harmonic 256 ≤ 6125/1000 := by
    decide +kernel
  have hreal : (6124/1000 : ℝ) ≤ (harmonic 256 : ℝ) ∧ (harmonic 256 : ℝ) ≤ 6125/1000 := by
    constructor
    · simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hrat.1
    · simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hrat.2
  norm_num only [show (256:ℝ)+1 = 257 by norm_num] at lo
  constructor <;> linarith [hreal.1, hreal.2, Real.log_two_gt_d9, Real.log_two_lt_d9]




def aTerm {K : Type*} [Field K] (l u n : K) :=
  l^2/(n*(n+u))

def bTerm {K : Type*} [Field K] (u n : K) :=
  2*u*(1/n - n/((n+u)*(n+3*u)))

def cTerm {K : Type*} [Field K] (l u n : K) :=
  4*n*l^2/((n+u)*(n+3*u)*(n+5*u))

def dTerm {K : Type*} [Field K] (l u n : K) :=
  8*n*l^3/((n+u)*(n+3*u)*(n+5*u)*(n+7*u))

def capA {K : Type*} [Field K] (l u : K) := 2-58/100*u+
  ∑ k ∈ range 128, aTerm l u ((k : K)+1)
def capB {K : Type*} [Field K] (l u : K) := 8*u^2/128-2*57/100*l+
  ∑ k ∈ range 128, bTerm u ((k : K)+1)
def capC {K : Type*} [Field K] (l u : K) :=
  ∑ k ∈ range 128, cTerm l u ((k : K)+1)
def capD {K : Type*} [Field K] (l u : K) :=
  ∑ k ∈ range 128, dTerm l u ((k : K)+1)

def capsOK (i : ℕ) : Prop :=
  let l : ℚ := i/80
  let u : ℚ := (i+1)/80
  let (a,b,c,d) := coeffs i
  a ≤ capA l u*scale ∧ capB l u*scale ≤ b ∧ c ≤ capC l u*scale ∧ d ≤ capD l u*scale

instance (i : ℕ) : Decidable (capsOK i) := by unfold capsOK; dsimp only; infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem caps_checked : (List.range 24).all (fun k => decide (capsOK (40+k))) = true := by
  decide +kernel



noncomputable def moment (r : ℝ) := 2-Real.eulerMascheroniConstant*r+
  ∑' k : ℕ, aTerm r r ((k:ℝ)+1)

theorem aTerm_summable {v : ℝ} (hv : 0 < v) :
    Summable (fun k : ℕ => aTerm v v ((k : ℝ)+1)) := by
  have hs := (summable_nat_add_iff 1).mpr ((Real.summable_one_div_nat_pow (p := 2)).mpr (by omega))
  apply Summable.of_nonneg_of_le (f := fun k : ℕ => v^2 * (1/((k:ℝ)+1)^2))
  · intro k; unfold aTerm; positivity
  · intro k
    unfold aTerm
    rw [mul_one_div]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith [mul_nonneg (show 0 ≤ (k:ℝ)+1 by positivity) hv.le])
  · simpa using hs.mul_left (v^2)

theorem bTerm_eq {n r : ℝ} (hn : 0 < n) (hr : 0 < r) :
    aTerm (3*r) (3*r) n - aTerm r r n = bTerm r n := by
  unfold aTerm bTerm
  field_simp
  ring

theorem cTerm_eq {n r : ℝ} (hn : 0 < n) (hr : 0 < r) :
    aTerm r r n - 2*aTerm (3*r) (3*r) n + aTerm (5*r) (5*r) n = 2*cTerm r r n := by
  unfold aTerm cTerm
  field_simp
  ring

theorem dTerm_eq {n r : ℝ} (hn : 0 < n) (hr : 0 < r) :
    aTerm r r n - 3*aTerm (3*r) (3*r) n + 3*aTerm (5*r) (5*r) n -
      aTerm (7*r) (7*r) n = 6*dTerm r r n := by
  unfold aTerm dTerm
  field_simp
  ring

theorem bTerm_le {n r u : ℝ} (hn : 0 < n) (hr : 0 ≤ r) (hu : r ≤ u) :
    bTerm r n ≤ bTerm u n := by
  have hu' : 0 ≤ u := hr.trans hu
  unfold bTerm
  apply mul_le_mul (by linarith) _ _ (by positivity)
  · apply sub_le_sub_left
    apply div_le_div_of_nonneg_left hn.le (by positivity)
    gcongr
  · apply sub_nonneg.mpr
    apply (div_le_div_iff₀ (by positivity) hn).mpr
    nlinarith [sq_nonneg r, mul_nonneg hn.le hr]

theorem bTerm_le_tail {n r : ℝ} (hn : 0 < n) (hr : 0 ≤ r) :
    bTerm r n ≤ 8*r^2/n^2 := by
  unfold bTerm
  field_simp
  nlinarith [mul_nonneg (sq_nonneg r) (sq_nonneg n),
    mul_nonneg (pow_nonneg hr 3) hn.le, pow_nonneg hr 4,
    mul_nonneg (pow_nonneg hr 3) (sq_nonneg n),
    mul_nonneg (pow_nonneg hr 4) hn.le]

theorem bounds_acd_terms {n l r u : ℝ} (hn : 0 < n) (hl : 0 ≤ l)
    (hlr : l ≤ r) (hru : r ≤ u) :
    aTerm l u n ≤ aTerm r r n ∧ cTerm l u n ≤ cTerm r r n ∧ dTerm l u n ≤ dTerm r r n := by
  have hr := hl.trans hlr
  have hu := hr.trans hru
  unfold aTerm cTerm dTerm
  constructor
  · gcongr
  constructor <;> gcongr

theorem bTail_sum {r : ℝ} (hr : 0 ≤ r) (m : ℕ) :
    (∑ k ∈ range m, bTerm r ((k : ℝ)+129)) ≤ 8*r^2*(1/128-1/((m:ℝ)+128)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, Nat.cast_succ]
    have h1 := bTerm_le_tail (n := (m:ℝ)+129) (by positivity) hr
    have h2 : 1/((m:ℝ)+129)^2 ≤ 1/((m:ℝ)+128)-1/((m:ℝ)+129) := by
      field_simp
      nlinarith
    have h3 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 8*r^2 by positivity)
    rw [show (m:ℝ)+1+128 = (m:ℝ)+129 by ring]
    linarith [show 8*r^2 / ((m:ℝ)+129)^2 = 8*r^2 * (1/((m:ℝ)+129)^2) by ring]


theorem aTerm_hasSum {v : ℝ} (hv : 0 < v) :
    HasSum (fun k : ℕ => aTerm v v ((k:ℝ)+1)) (moment v - 2+Real.eulerMascheroniConstant*v) := by
  unfold moment
  convert! (aTerm_summable hv).hasSum using 1
  ring

theorem moment_bounds {l r u : ℝ} (hl : 0 ≤ l) (hr : 0 < r) (hlr : l ≤ r) (hru : r ≤ u) :
    capA l u ≤ moment r ∧ moment (3*r)-moment r ≤ capB l u ∧
    capC l u ≤ (moment r-2*moment (3*r)+moment (5*r))/2 ∧
    capD l u ≤ (moment r-3*moment (3*r)+3*moment (5*r)-moment (7*r))/6 := by
  let γ := Real.eulerMascheroniConstant
  have hu := hr.le.trans hru
  have ha := aTerm_hasSum hr
  have h3 := aTerm_hasSum (show 0 < 3*r by positivity)
  have h5 := aTerm_hasSum (show 0 < 5*r by positivity)
  have h7 := aTerm_hasSum (show 0 < 7*r by positivity)
  have hb : HasSum (fun k : ℕ => bTerm r ((k:ℝ)+1)) (moment (3*r)-moment r+2*γ*r) := by
    convert! (h3.sub ha).congr_fun (fun k => (bTerm_eq (n := (k:ℝ)+1) (by positivity) hr).symm) using 1
    dsimp [γ]; ring
  have hc : HasSum (fun k : ℕ => cTerm r r ((k:ℝ)+1))
      ((moment r-2*moment (3*r)+moment (5*r))/2) := by
    have h := ((ha.sub (h3.mul_left 2)).add h5).mul_left (1/2)
    convert! h.congr_fun (g := fun k : ℕ => cTerm r r ((k:ℝ)+1)) (fun k => by
      rw [cTerm_eq (by positivity) hr]; ring) using 1
    ring
  have hd : HasSum (fun k : ℕ => dTerm r r ((k:ℝ)+1))
      ((moment r-3*moment (3*r)+3*moment (5*r)-moment (7*r))/6) := by
    have h := (((ha.sub (h3.mul_left 3)).add (h5.mul_left 3)).sub h7).mul_left (1/6)
    convert! h.congr_fun (g := fun k : ℕ => dTerm r r ((k:ℝ)+1)) (fun k => by
      rw [dTerm_eq (by positivity) hr]; ring) using 1
    ring
  have lower_sum {f g : ℕ → ℝ} {s : ℝ} (hs : HasSum f s) (hfg : ∀ n, g n ≤ f n)
      (hn : ∀ n, 0 ≤ f n) : (∑ k ∈ range 128, g k) ≤ s :=
    (sum_le_sum (fun k _ => hfg k)).trans (hs.tsum_eq ▸ hs.summable.sum_le_tsum _ (fun k _ => hn k))
  have hbounds (k : ℕ) := bounds_acd_terms (n := (k:ℝ)+1) (by positivity) hl hlr hru
  refine ⟨?_,?_,?_,?_⟩
  · unfold capA
    have hsum := lower_sum ha (fun k => (hbounds k).1) (fun k => by unfold aTerm; positivity)
    have hg := mul_le_mul euler_bounds.2.le hru hr.le (by norm_num)
    linarith only [hsum, hg]
  · unfold capB
    have hlimit : moment (3*r)-moment r+2*γ*r ≤
        8*u^2/128 + ∑ k ∈ range 128, bTerm u ((k:ℝ)+1) := by
      apply le_of_tendsto hb.tendsto_sum_nat
      filter_upwards [eventually_ge_atTop (128 : ℕ)] with m hm
      obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hm
      rw [sum_range_add]
      have hfront : (∑ k ∈ range 128, bTerm r ((k:ℝ)+1)) ≤
          ∑ k ∈ range 128, bTerm u ((k:ℝ)+1) :=
        sum_le_sum (fun _ _ => bTerm_le (by positivity) hr.le hru)
      have htail := bTail_sum hr.le j
      simp only [Nat.cast_add, Nat.cast_ofNat]
      simp_rw [show ∀ k : ℕ, (128 : ℝ)+(k:ℝ)+1 = (k:ℝ)+129 by intro k; ring]
      have hprod : 0 ≤ 8*r^2*(1/((j:ℝ)+128)) := by positivity
      nlinarith only [htail, hfront, hprod, pow_le_pow_left₀ hr.le hru 2]
    have hg := mul_le_mul euler_bounds.1.le hlr hl (euler_bounds.1.le.trans' (by norm_num))
    dsimp [γ] at hlimit
    linarith only [hlimit,hg]
  · exact lower_sum hc (fun k => (hbounds k).2.1) (fun k => by unfold cTerm; positivity)
  · exact lower_sum hd (fun k => (hbounds k).2.2) (fun k => by unfold dTerm; positivity)



theorem cap_enclosures (i : ℕ) (hi : 40 ≤ i ∧ i < 64) :
    let l : ℝ := i/80
    let u : ℝ := (i+1)/80
    (coeffs i).1 ≤ capA l u * scale ∧ capB l u * scale ≤ (coeffs i).2.1 ∧
      (coeffs i).2.2.1 ≤ capC l u * scale ∧ (coeffs i).2.2.2 ≤ capD l u * scale := by
  have hb := List.all_eq_true.mp caps_checked (i-40) (List.mem_range.mpr (by omega))
  rw [show 40+(i-40) = i by omega] at hb
  have hq := of_decide_eq_true hb
  obtain ⟨a,b,c,d,he⟩ : ∃ a b c d, coeffs i = (a,b,c,d) := by
    obtain ⟨a,b,c,d⟩ := coeffs i
    exact ⟨a,b,c,d,rfl⟩
  simp only [capsOK,he] at hq
  simp only [he]
  obtain ⟨ha,hb,hc,hd⟩ := hq
  simp only [capA,capB,capC,capD,aTerm,bTerm,cTerm,dTerm] at ha hb hc hd ⊢
  refine ⟨?_,?_,?_,?_⟩
  · have cast := (Rat.cast_le (K := ℝ)).mpr ha
    push_cast at cast
    exact cast
  · have cast := (Rat.cast_le (K := ℝ)).mpr hb
    push_cast at cast
    exact cast
  · have cast := (Rat.cast_le (K := ℝ)).mpr hc
    push_cast at cast
    exact cast
  · have cast := (Rat.cast_le (K := ℝ)).mpr hd
    push_cast at cast
    exact cast

theorem cell_cover {r : ℝ} (hr : r ∈ Set.Icc (1/2) (4/5)) :
    ∃ i : ℕ, (40 ≤ i ∧ i < 64) ∧ (i:ℝ)/80 ≤ r ∧ r ≤ ((i:ℝ)+1)/80 := by
  let k := ⌊80*r⌋₊
  have hr' : 0 ≤ r := by linarith [hr.1]
  have h₀ : (k:ℝ) ≤ 80*r := Nat.floor_le (by positivity)
  have h₁ : 80*r < (k:ℝ)+1 := Nat.lt_floor_add_one _
  by_cases h : 63 < k
  · refine ⟨63, by norm_num, ?_, ?_⟩
    · have hh : (63:ℝ) < (k:ℝ) := by exact_mod_cast h
      linarith
    · norm_num; linarith [hr.2]
  · refine ⟨k, ⟨?_,by omega⟩, by linarith, by linarith⟩
    by_contra! hh
    have hh' : (k:ℝ) ≤ 39 := by exact_mod_cast (show k ≤ 39 by omega)
    linarith [hr.1]


theorem scalar_cubic {r y : ℝ} (hr : r ∈ Set.Icc (1/2) (4/5)) (hy : 0 ≤ y) :
    0 ≤ moment r + (moment r - moment (3*r))*y +
      (moment r - 2*moment (3*r) + moment (5*r))*y^2/2 +
      (moment r - 3*moment (3*r) + 3*moment (5*r) - moment (7*r))*y^3/6 := by
  obtain ⟨i,hi,hlr,hru⟩ := cell_cover hr
  have h := moment_bounds (l := (i:ℝ)/80) (u := ((i:ℝ)+1)/80)
    (by positivity) (by linarith [hr.1]) hlr hru
  obtain ⟨hA,hB,hC,hD⟩ := h
  obtain ⟨cA,cB,cC,cD⟩ := cap_enclosures i hi
  have hn : 0 ≤ (scale : ℝ) := Nat.cast_nonneg _
  have hpos := enclosed_cubic_pos i hi _ _ _ _ y hy
    (cA.trans (mul_le_mul_of_nonneg_right hA hn))
    ((mul_le_mul_of_nonneg_right hB hn).trans cB)
    (cC.trans (mul_le_mul_of_nonneg_right hC hn))
    (cD.trans (mul_le_mul_of_nonneg_right hD hn))
  linarith only [hpos]


end Mo360993

theorem Mo360993Full.scalar : OMA.R_mo_360993_R1.H3 := by
  intro r y hr hy
  exact Mo360993.scalar_cubic hr hy
end

theorem OMA.solution : type_of% @OMA.S_mo_360993.main := by
  exact OMA.R_mo_360993_R1.main Mo360993Full.small Mo360993Full.large Mo360993Full.scalar
