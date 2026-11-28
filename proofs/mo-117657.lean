import OMAStatements.S_mo_117657

/-! Two support waves with the same radius profile traversed at different
frequencies. Their curvature variations scale with frequency, while the
area deficit decreases with frequency. -/

open Real Set MeasureTheory OMA.S_mo_117657

private noncomputable def wave (n : ℕ) (a : ℝ) (x : ℝ) : ℝ :=
  1 + a * cos ((n : ℝ) * x)

private noncomputable def baseRadius (x : ℝ) : ℝ := 1 - cos x / 2

private noncomputable def variationDensity (x : ℝ) : ℝ :=
  |-(sin x / 2) / (baseRadius x) ^ 2|

private lemma baseRadius_pos (x : ℝ) : 0 < baseRadius x := by
  unfold baseRadius
  linarith [cos_le_one x]

private lemma wave_periodic (n : ℕ) (a : ℝ) : Function.Periodic (wave n a) (2 * π) := by
  intro x
  have h := (cos_periodic.nsmul n) ((n : ℝ) * x)
  simp only [wave, mul_add, nsmul_eq_mul] at h ⊢
  rw [h]


private noncomputable def waveSlope (n : ℕ) (a : ℝ) (x : ℝ) : ℝ :=
  a * (-sin ((n : ℝ) * x) * (n : ℝ))

private noncomputable def waveSlopeDeriv (n : ℕ) (a : ℝ) (x : ℝ) : ℝ :=
  a * (-(cos ((n : ℝ) * x) * (n : ℝ)) * (n : ℝ))

private lemma wave_hasDerivAt (n : ℕ) (a x : ℝ) :
    HasDerivAt (wave n a) (waveSlope n a x) x := by
  change HasDerivAt (fun t => 1 + a * cos ((n : ℝ) * t)) _ x
  simpa only [waveSlope, Function.comp_apply, id_eq, mul_one] using
    (((hasDerivAt_cos _).comp x ((hasDerivAt_id x).const_mul (n : ℝ))).const_mul a).const_add 1

private lemma waveSlope_hasDerivAt (n : ℕ) (a x : ℝ) :
    HasDerivAt (waveSlope n a) (waveSlopeDeriv n a x) x := by
  change HasDerivAt (fun t => a * (-sin ((n : ℝ) * t) * (n : ℝ))) _ x
  simpa [waveSlopeDeriv, Function.comp_def] using
    (((hasDerivAt_sin _).comp x ((hasDerivAt_id x).const_mul (n : ℝ))).neg.mul_const (n : ℝ)).const_mul a

private lemma supportRadius_formula (n : ℕ) (a x : ℝ)
    (ha : a * (1 - (n : ℝ)^2) = -1 / 2) :
    wave n a x + waveSlopeDeriv n a x = baseRadius ((n : ℝ) * x) := by
  unfold wave waveSlopeDeriv baseRadius
  calc
    _ = 1 + (a * (1 - (n : ℝ)^2)) * cos ((n : ℝ) * x) := by ring
    _ = _ := by rw [ha]; ring

private lemma waveSlope_periodic (n : ℕ) (a : ℝ) :
    Function.Periodic (waveSlope n a) (2 * π) := by
  intro x
  have h := (sin_periodic.nsmul n) ((n : ℝ) * x)
  simp only [waveSlope, mul_add, nsmul_eq_mul] at h ⊢
  rw [h]

private noncomputable def curveX (n : ℕ) (a : ℝ) (x : ℝ) : ℝ :=
  wave n a x * cos x - waveSlope n a x * sin x

private noncomputable def curveY (n : ℕ) (a : ℝ) (x : ℝ) : ℝ :=
  wave n a x * sin x + waveSlope n a x * cos x

private lemma curveX_hasDerivAt (n : ℕ) (a t : ℝ)
    (ha : a * (1 - (n : ℝ)^2) = -1 / 2) :
    HasDerivAt (curveX n a) (-(baseRadius ((n : ℝ) * t) * sin t)) t := by
  have h := ((wave_hasDerivAt n a t).mul (hasDerivAt_cos t)).sub
    ((waveSlope_hasDerivAt n a t).mul (hasDerivAt_sin t))
  convert h using 1
  · rfl
  · rw [← supportRadius_formula n a t ha]
    ring

private lemma curveY_hasDerivAt (n : ℕ) (a t : ℝ)
    (ha : a * (1 - (n : ℝ)^2) = -1 / 2) :
    HasDerivAt (curveY n a) (baseRadius ((n : ℝ) * t) * cos t) t := by
  have h := ((wave_hasDerivAt n a t).mul (hasDerivAt_sin t)).add
    ((waveSlope_hasDerivAt n a t).mul (hasDerivAt_cos t))
  convert h using 1
  · rfl
  · rw [← supportRadius_formula n a t ha]
    ring

private lemma speed_formula (n : ℕ) (a : ℝ)
    (ha : a * (1 - (n : ℝ)^2) = -1 / 2) :
    speed (curveX n a) (curveY n a) = fun t => baseRadius ((n : ℝ) * t) := by
  funext t
  unfold speed
  rw [(curveX_hasDerivAt n a t ha).deriv, (curveY_hasDerivAt n a t ha).deriv, neg_sq, mul_pow, mul_pow,
    ← mul_add, sin_sq_add_cos_sq, mul_one, sqrt_sq (baseRadius_pos _).le]

private lemma curvature_formula (n : ℕ) (a : ℝ)
    (ha : a * (1 - (n : ℝ)^2) = -1 / 2) :
    absCurvature (curveX n a) (curveY n a) = fun t => (baseRadius ((n : ℝ) * t))⁻¹ := by
  let r (t : ℝ) := baseRadius ((n : ℝ) * t)
  have hr (t : ℝ) : DifferentiableAt ℝ r t := by
    unfold r baseRadius
    fun_prop
  have hx : deriv (curveX n a) = fun t => -(r t * sin t) :=
    funext fun t => (curveX_hasDerivAt n a t ha).deriv
  have hy : deriv (curveY n a) = fun t => r t * cos t :=
    funext fun t => (curveY_hasDerivAt n a t ha).deriv
  funext t
  unfold absCurvature
  have hxd : deriv (fun t => -(r t * sin t)) t = -(deriv r t * sin t + r t * cos t) :=
    ((hr t).hasDerivAt.mul (hasDerivAt_sin t)).neg.deriv
  have hyd : deriv (fun t => r t * cos t) t = deriv r t * cos t + r t * -sin t :=
    ((hr t).hasDerivAt.mul (hasDerivAt_cos t)).deriv
  rw [hx, hy, speed_formula n a ha, hxd, hyd]
  change |-(r t * sin t) * (deriv r t * cos t + r t * -sin t) -
    r t * cos t * -(deriv r t * sin t + r t * cos t)| / r t ^ 3 = (r t)⁻¹
  have hdet : -(r t * sin t) * (deriv r t * cos t + r t * -sin t) -
      r t * cos t * -(deriv r t * sin t + r t * cos t) = r t ^ 2 := by
    calc
      _ = r t ^ 2 * (sin t ^ 2 + cos t ^ 2) := by ring
      _ = _ := by rw [sin_sq_add_cos_sq, mul_one]
  rw [hdet, abs_of_nonneg (sq_nonneg _)]
  field_simp [show r t ≠ 0 from (baseRadius_pos _).ne']
private lemma density_continuous : Continuous variationDensity := by
  unfold variationDensity
  exact (continuous_sin.div_const 2).neg.div
    ((continuous_const.sub (continuous_cos.div_const 2)).pow 2)
    (fun x => pow_ne_zero _ (baseRadius_pos x).ne') |>.abs

private lemma density_periodic : Function.Periodic variationDensity (2 * π) := by
  intro x
  simp only [variationDensity, baseRadius, sin_add_two_pi, cos_add_two_pi]

private lemma density_integral_pos : 0 < ∫ x in (0 : ℝ)..2 * π, variationDensity x := by
  apply intervalIntegral.integral_pos (by positivity) density_continuous.continuousOn
  · intro x _
    exact abs_nonneg _
  · refine ⟨π / 2, ⟨by positivity, by linarith [pi_pos]⟩, ?_⟩
    norm_num [variationDensity, baseRadius, sin_pi_div_two, cos_pi_div_two]

private lemma variation_formula (n : ℕ) (a : ℝ)
    (ha : a * (1 - (n : ℝ)^2) = -1 / 2) :
    curvatureVariation (curveX n a) (curveY n a) =
      (n : ℝ) * ∫ x in (0 : ℝ)..2 * π, variationDensity x := by
  have hr (x : ℝ) : HasDerivAt baseRadius (sin x / 2) x := by
    change HasDerivAt (fun t => 1 - cos t / 2) _ x
    simpa only [neg_div, neg_neg] using ((hasDerivAt_cos x).div_const 2).const_sub 1
  have h (x : ℝ) :
      HasDerivAt (absCurvature (curveX n a) (curveY n a))
        ((-(sin ((n : ℝ) * x) / 2) / (baseRadius ((n : ℝ) * x)) ^ 2) * (n : ℝ)) x := by
    rw [curvature_formula n a ha]
    simpa [Function.comp_def] using ((hr _).inv (baseRadius_pos _).ne').comp x
      ((hasDerivAt_id x).const_mul (n : ℝ))
  unfold curvatureVariation
  simp_rw [(h _).deriv, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n), mul_comm _ (n : ℝ)]
  change (∫ x in (0 : ℝ)..2 * π, (n : ℝ) * variationDensity ((n : ℝ) * x)) = _
  rw [intervalIntegral.integral_const_mul, intervalIntegral.mul_integral_comp_mul_left, mul_zero]
  simpa [zsmul_eq_mul] using density_periodic.intervalIntegral_add_zsmul_eq (n : ℤ) 0
    (fun a b => density_continuous.intervalIntegrable a b)
private lemma sin_scaled_endpoint (n : ℕ) : sin ((n : ℝ) * (2 * π)) = 0 := by
  convert sin_nat_mul_pi (n * 2) using 1
  push_cast
  ring

private lemma integral_cos_scaled (n : ℕ) (hn : 0 < n) :
    (∫ x in (0 : ℝ)..2 * π, cos ((n : ℝ) * x)) = 0 := by
  have h := intervalIntegral.mul_integral_comp_mul_left (f := cos) (a := 0) (b := 2 * π) (n : ℝ)
  rw [mul_zero, integral_cos, sin_zero, sub_zero, sin_scaled_endpoint] at h
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast (Nat.ne_of_gt hn))

private lemma integral_cos_sq_scaled (n : ℕ) (hn : 0 < n) :
    (∫ x in (0 : ℝ)..2 * π, cos ((n : ℝ) * x)^2) = π := by
  have h := intervalIntegral.mul_integral_comp_mul_left
    (f := fun x => cos x ^ 2) (a := 0) (b := 2 * π) (n : ℝ)
  simp only [mul_zero] at h
  simp only [integral_cos_sq, sin_zero, sin_scaled_endpoint, mul_zero, sub_zero, zero_add] at h
  apply mul_left_cancel₀ (show (n : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hn))
  linarith


private lemma length_formula (n : ℕ) (a : ℝ) (hn : 0 < n)
    (ha : a * (1 - (n : ℝ)^2) = -1 / 2) :
    curveLength (curveX n a) (curveY n a) = 2 * π := by
  have hcos : Continuous (fun x => cos ((n : ℝ) * x)) := by fun_prop
  unfold curveLength
  rw [speed_formula n a ha]
  change (∫ x in (0 : ℝ)..2 * π, 1 - cos ((n : ℝ) * x) / 2) = _
  rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
    (hcos.div_const _ |>.intervalIntegrable _ _), intervalIntegral.integral_div,
    integral_cos_scaled n hn]
  simp

private lemma totalCurvature_formula (n : ℕ) (a : ℝ)
    (ha : a * (1 - (n : ℝ)^2) = -1 / 2) :
    totalAbsCurvature (curveX n a) (curveY n a) = 2 * π := by
  unfold totalAbsCurvature
  simp_rw [speed_formula n a ha, curvature_formula n a ha,
    inv_mul_cancel₀ ((baseRadius_pos _).ne')]
  simp

private lemma area_formula (n : ℕ) (a : ℝ) (hn : 0 < n)
    (ha : a * (1 - (n : ℝ)^2) = -1 / 2) (ha4 : a < 4) :
    enclosedArea (curveX n a) (curveY n a) = π - a * π / 4 := by
  let c (x : ℝ) := cos ((n : ℝ) * x)
  let u (x : ℝ) := 1 + (a - 1 / 2) * c x
  let v (x : ℝ) := (a / 2) * c x^2
  have hc : Continuous c := by dsimp [c]; fun_prop
  have hu : Continuous u := continuous_const.add (hc.const_mul _)
  have hv : Continuous v := (hc.pow 2).const_mul _
  have he (x : ℝ) :
      curveX n a x * deriv (curveY n a) x - curveY n a x * deriv (curveX n a) x = u x - v x := by
    rw [(curveX_hasDerivAt n a x ha).deriv, (curveY_hasDerivAt n a x ha).deriv]
    calc
      _ = wave n a x * baseRadius ((n : ℝ) * x) * (sin x^2 + cos x^2) := by
        unfold curveX curveY
        ring
      _ = _ := by
        rw [sin_sq_add_cos_sq, mul_one]
        unfold wave baseRadius u v c
        ring
  unfold enclosedArea
  simp_rw [he]
  rw [intervalIntegral.integral_sub (hu.intervalIntegrable _ _) (hv.intervalIntegrable _ _)]
  unfold u v
  rw [intervalIntegral.integral_add (continuous_const.intervalIntegrable _ _)
    ((hc.const_mul _).intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  change |(∫ _ in (0 : ℝ)..2 * π, (1 : ℝ)) +
    (a - 1 / 2) * (∫ x in (0 : ℝ)..2 * π, cos ((n : ℝ) * x)) -
    a / 2 * (∫ x in (0 : ℝ)..2 * π, cos ((n : ℝ) * x) ^ 2)| / 2 = _
  rw [integral_cos_scaled n hn, integral_cos_sq_scaled n hn]
  simp
  rw [abs_of_nonneg (by nlinarith [mul_pos (sub_pos.mpr ha4) pi_pos])]
  ring

private lemma curve_periodic (n : ℕ) (a : ℝ) :
    Function.Periodic (curveX n a) (2 * π) ∧ Function.Periodic (curveY n a) (2 * π) := by
  constructor <;> intro t <;>
    simp only [curveX, curveY, wave_periodic n a t, waveSlope_periodic n a t,
      cos_add_two_pi, sin_add_two_pi]

private lemma support_strict (n : ℕ) (a s t : ℝ)
    (ha : a * (1 - (n : ℝ)^2) = -1 / 2) (hst : s < t) (htt : t < s + 2 * π) :
    curveX n a t * cos s + curveY n a t * sin s <
      curveX n a s * cos s + curveY n a s * sin s := by
  let F (u : ℝ) := curveX n a u * cos s + curveY n a u * sin s
  have hF (u : ℝ) :
      HasDerivAt F (-(baseRadius ((n : ℝ) * u) * sin (u - s))) u := by
    have h := ((curveX_hasDerivAt n a u ha).mul_const (cos s)).add
      ((curveY_hasDerivAt n a u ha).mul_const (sin s))
    convert h using 1
    rw [sin_sub]
    ring
  have hFc : Continuous F := continuous_iff_continuousAt.mpr fun u => (hF u).continuousAt
  change F t < F s
  by_cases ht : t ≤ s + π
  · have hanti : StrictAntiOn F (Icc s (s + π)) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hFc.continuousOn
      intro u hu
      rw [interior_Icc] at hu
      rw [(hF u).deriv]
      exact neg_neg_of_pos (mul_pos (baseRadius_pos _)
        (sin_pos_of_pos_of_lt_pi (by linarith [hu.1]) (by linarith [hu.2])))
    exact hanti ⟨le_rfl, by linarith [pi_pos]⟩ ⟨hst.le, ht⟩ hst
  · have hmono : StrictMonoOn F (Icc (s + π) (s + 2 * π)) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hFc.continuousOn
      intro u hu
      rw [interior_Icc] at hu
      rw [(hF u).deriv]
      have hsine : sin (u - s) < 0 := by
        have he := sin_add_two_pi (u - s - 2 * π)
        rw [show u - s - 2 * π + 2 * π = u - s by ring] at he
        rw [he]
        exact sin_neg_of_neg_of_neg_pi_lt (by linarith [hu.2]) (by linarith [hu.1])
      exact neg_pos.mpr (mul_neg_of_pos_of_neg (baseRadius_pos _) hsine)
    have he : F (s + 2 * π) = F s := by
      unfold F
      rw [(curve_periodic n a).1 s, (curve_periodic n a).2 s]
    rw [← he]
    exact hmono ⟨(lt_of_not_ge ht).le, htt.le⟩ ⟨by linarith [pi_pos], le_rfl⟩ htt

private lemma curve_simple_closed (n : ℕ) (a : ℝ)
    (ha : a * (1 - (n : ℝ)^2) = -1 / 2) :
    SmoothSimpleClosed (curveX n a) (curveY n a) := by
  have hX : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (curveX n a) := by
    unfold curveX wave waveSlope
    fun_prop
  have hY : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (curveY n a) := by
    unfold curveY wave waveSlope
    fun_prop
  refine ⟨hX, hY, (curve_periodic n a).1, (curve_periodic n a).2, ?_, ?_⟩
  · rw [speed_formula n a ha]
    exact fun t => baseRadius_pos _
  · have hne (s t : ℝ) (hs : s ∈ Ico 0 (2 * π)) (ht : t ∈ Ico 0 (2 * π)) (hst : s < t) :
        (curveX n a s, curveY n a s) ≠ (curveX n a t, curveY n a t) := by
      have htt : t < s + 2 * π := by linarith [hs.1, ht.2]
      intro he
      have hx := congrArg Prod.fst he
      have hy := congrArg Prod.snd he
      have hp := support_strict n a s t ha hst htt
      change curveX n a s = curveX n a t at hx
      change curveY n a s = curveY n a t at hy
      rw [hx, hy] at hp
      exact (lt_irrefl _ hp)
    intro s hs t ht he
    rcases lt_trichotomy s t with h | h | h
    · exact (hne s t hs ht h he).elim
    · exact h
    · exact (hne t s ht hs h he.symm).elim

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_117657.main) := by
  intro h
  have h2 : (1 / 6 : ℝ) * (1 - (↑(2 : ℕ) : ℝ)^2) = -1 / 2 := by norm_num
  have h3 : (1 / 16 : ℝ) * (1 - (↑(3 : ℕ) : ℝ)^2) = -1 / 2 := by norm_num
  have H := h (curveX 3 (1 / 16)) (curveY 3 (1 / 16))
    (curveX 2 (1 / 6)) (curveY 2 (1 / 6))
    (curve_simple_closed 3 _ h3) (curve_simple_closed 2 _ h2)
    ((length_formula 3 _ (by decide) h3).trans (length_formula 2 _ (by decide) h2).symm)
    ((totalCurvature_formula 3 _ h3).trans (totalCurvature_formula 2 _ h2).symm) (by
      rw [variation_formula 2 _ h2, variation_formula 3 _ h3]
      push_cast
      linarith [density_integral_pos])
  rw [area_formula 3 _ (by decide) h3 (by norm_num),
    area_formula 2 _ (by decide) h2 (by norm_num)] at H
  linarith [pi_pos]
