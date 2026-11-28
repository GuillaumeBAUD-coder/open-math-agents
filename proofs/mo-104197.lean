import OMAStatements.S_mo_104197

private lemma rpow_tangent_le {p t s : ℝ} (hp : 1 ≤ p) (ht : 0 < t) (hs : 0 < s) :
    p * t ^ (p - 1) * (s - t) ≤ s ^ p - t ^ p := by
  rcases lt_trichotomy t s with hts | rfl | hst
  · have hcont : ContinuousOn (fun x : ℝ => x ^ p) (Set.Icc t s) := by
      intro x hx
      exact (Real.continuousAt_rpow_const x p (Or.inl (lt_of_lt_of_le ht hx.1).ne')).continuousWithinAt
    have hderiv : ∀ x ∈ Set.Ioo t s, HasDerivAt (fun x : ℝ => x ^ p) (p * x ^ (p - 1)) x := by
      intro x hx
      exact Real.hasDerivAt_rpow_const (Or.inl (lt_trans ht hx.1).ne')
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun x : ℝ => x ^ p)
      (fun x : ℝ => p * x ^ (p - 1)) hts hcont hderiv
    have hpow : t ^ (p - 1) ≤ c ^ (p - 1) :=
      Real.rpow_le_rpow ht.le hc.1.le (sub_nonneg.mpr hp)
    have hp_pos : 0 < p := by linarith only [hp]
    have hmul : p * t ^ (p - 1) ≤ p * c ^ (p - 1) :=
      mul_le_mul_of_nonneg_left hpow hp_pos.le
    rw [hslope] at hmul
    exact (le_div_iff₀ (sub_pos.mpr hts)).mp hmul
  · simp
  · have hcont : ContinuousOn (fun x : ℝ => x ^ p) (Set.Icc s t) := by
      intro x hx
      exact (Real.continuousAt_rpow_const x p (Or.inl (lt_of_lt_of_le hs hx.1).ne')).continuousWithinAt
    have hderiv : ∀ x ∈ Set.Ioo s t, HasDerivAt (fun x : ℝ => x ^ p) (p * x ^ (p - 1)) x := by
      intro x hx
      exact Real.hasDerivAt_rpow_const (Or.inl (lt_trans hs hx.1).ne')
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun x : ℝ => x ^ p)
      (fun x : ℝ => p * x ^ (p - 1)) hst hcont hderiv
    have hpow : c ^ (p - 1) ≤ t ^ (p - 1) :=
      Real.rpow_le_rpow (lt_trans hs hc.1).le hc.2.le (sub_nonneg.mpr hp)
    have hp_pos : 0 < p := by linarith only [hp]
    have hmul : p * c ^ (p - 1) ≤ p * t ^ (p - 1) :=
      mul_le_mul_of_nonneg_left hpow hp_pos.le
    rw [hslope] at hmul
    have hmul2 := (div_le_iff₀ (sub_pos.mpr hst)).mp hmul
    linarith only [hmul2]

private lemma rpow_diff_sq_le_aux {x y α : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) (hα : 0 < α) :
    (y ^ α - x ^ α) ^ 2 ≤ 4 * α ^ 2 * (x ^ α + y ^ α) * (x ^ (1 + α) + y ^ (1 + α)) := by
  have hx_pos : 0 < x := by linarith only [hx]
  have hy_pos : 0 < y := by linarith only [hx, hxy]
  have hdiv_pos : 0 < y / x := div_pos hy_pos hx_pos
  have h1 : 1 - α * Real.log (y / x) ≤ (y / x) ^ (-α) := by
    rw [Real.rpow_def_of_pos hdiv_pos]
    linarith only [Real.add_one_le_exp (Real.log (y / x) * -α)]
  have hs_pos : 0 < Real.sqrt (y / x) := Real.sqrt_pos.mpr hdiv_pos
  have hlog_s : Real.log (Real.sqrt (y / x)) ≤ Real.sqrt (y / x) := by
    have h := Real.add_one_le_exp (Real.log (Real.sqrt (y / x)))
    rw [Real.exp_log hs_pos] at h
    linarith only [h]
  have hlog_div : Real.log (y / x) ≤ 2 * Real.sqrt (y / x) := by
    have hsq : Real.sqrt (y / x) * Real.sqrt (y / x) = y / x := Real.mul_self_sqrt hdiv_pos.le
    calc Real.log (y / x)
        = Real.log (Real.sqrt (y / x) * Real.sqrt (y / x)) := by rw [hsq]
      _ = Real.log (Real.sqrt (y / x)) + Real.log (Real.sqrt (y / x)) :=
          Real.log_mul hs_pos.ne' hs_pos.ne'
      _ ≤ 2 * Real.sqrt (y / x) := by linarith only [hlog_s]
  have hdiv_rpow : (y / x) ^ (-α) = x ^ α / y ^ α := by
    rw [Real.rpow_neg hdiv_pos.le, Real.div_rpow hy_pos.le hx_pos.le, inv_div]
  have hy_pow_pos : 0 < y ^ α := Real.rpow_pos_of_pos hy_pos α
  have hdiff_le : y ^ α - x ^ α ≤ 2 * α * y ^ α * Real.sqrt (y / x) := by
    have hstep1 : α * Real.log (y / x) ≤ α * (2 * Real.sqrt (y / x)) :=
      mul_le_mul_of_nonneg_left hlog_div hα.le
    have hstep : 1 - x ^ α / y ^ α ≤ 2 * α * Real.sqrt (y / x) := by
      rw [← hdiv_rpow]
      linarith only [h1, hstep1]
    have hmul := mul_le_mul_of_nonneg_left hstep hy_pow_pos.le
    have hLHS : y ^ α * (1 - x ^ α / y ^ α) = y ^ α - x ^ α := by
      field_simp [hy_pow_pos.ne']
    linarith only [hmul, hLHS]
  have hdiff_nonneg : 0 ≤ y ^ α - x ^ α :=
    sub_nonneg.mpr (Real.rpow_le_rpow hx_pos.le hxy hα.le)
  have hsq_le : (y ^ α - x ^ α) ^ 2 ≤ 4 * α ^ 2 * ((y ^ α) ^ 2 * (y / x)) := by
    have h0 := mul_self_le_mul_self hdiff_nonneg hdiff_le
    have hsqrt_sq : Real.sqrt (y / x) ^ 2 = y / x := Real.sq_sqrt hdiv_pos.le
    calc (y ^ α - x ^ α) ^ 2
        = (y ^ α - x ^ α) * (y ^ α - x ^ α) := sq _
      _ ≤ (2 * α * y ^ α * Real.sqrt (y / x)) * (2 * α * y ^ α * Real.sqrt (y / x)) := h0
      _ = 4 * α ^ 2 * ((y ^ α) ^ 2 * Real.sqrt (y / x) ^ 2) := by ring
      _ = 4 * α ^ 2 * ((y ^ α) ^ 2 * (y / x)) := by rw [hsqrt_sq]
  have hdiv_le_y : y / x ≤ y := div_le_self hy_pos.le hx
  have hy1a : (y ^ α) ^ 2 * y = y ^ α * y ^ (1 + α) := by
    rw [Real.rpow_add hy_pos 1 α, Real.rpow_one]
    ring
  have hx_pow_nonneg : 0 ≤ x ^ α := (Real.rpow_pos_of_pos hx_pos α).le
  have hx1a_nonneg : 0 ≤ x ^ (1 + α) := (Real.rpow_pos_of_pos hx_pos (1 + α)).le
  have hy1a_nonneg : 0 ≤ y ^ (1 + α) := (Real.rpow_pos_of_pos hy_pos (1 + α)).le
  have hprod_le : (y ^ α) ^ 2 * (y / x) ≤ (x ^ α + y ^ α) * (x ^ (1 + α) + y ^ (1 + α)) := by
    calc (y ^ α) ^ 2 * (y / x)
        ≤ (y ^ α) ^ 2 * y := mul_le_mul_of_nonneg_left hdiv_le_y (sq_nonneg _)
      _ = y ^ α * y ^ (1 + α) := hy1a
      _ ≤ (x ^ α + y ^ α) * (x ^ (1 + α) + y ^ (1 + α)) :=
          mul_le_mul (le_add_of_nonneg_left hx_pow_nonneg)
            (le_add_of_nonneg_left hx1a_nonneg) hy1a_nonneg
            (add_nonneg hx_pow_nonneg hy_pow_pos.le)
  have hc_nonneg : 0 ≤ 4 * α ^ 2 := by positivity
  calc (y ^ α - x ^ α) ^ 2
      ≤ 4 * α ^ 2 * ((y ^ α) ^ 2 * (y / x)) := hsq_le
    _ ≤ 4 * α ^ 2 * ((x ^ α + y ^ α) * (x ^ (1 + α) + y ^ (1 + α))) :=
        mul_le_mul_of_nonneg_left hprod_le hc_nonneg
    _ = 4 * α ^ 2 * (x ^ α + y ^ α) * (x ^ (1 + α) + y ^ (1 + α)) := by ring

private lemma rpow_diff_sq_le {x y α : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hα : 0 < α) :
    (x ^ α - y ^ α) ^ 2 ≤ 4 * α ^ 2 * (x ^ α + y ^ α) * (x ^ (1 + α) + y ^ (1 + α)) := by
  rcases le_total x y with hxy | hyx
  · rw [← neg_sub (y ^ α) (x ^ α), neg_sq]
    exact rpow_diff_sq_le_aux hx hxy hα
  · have h := rpow_diff_sq_le_aux hy hyx hα
    have hid : (x ^ α + y ^ α) * (x ^ (1 + α) + y ^ (1 + α)) =
        (y ^ α + x ^ α) * (y ^ (1 + α) + x ^ (1 + α)) := by ring
    linarith only [h, hid]

private lemma ratio_algebra {α δ p xa ya X U : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1 / 10)
    (hp_eq : p = 1 + α)
    (hA_pos : 0 < xa + ya) (hX_pos : 0 < X) (hU_pos : 0 < U)
    (ht : p * xa * (2 * δ + δ ^ 2) + p * ya * (-2 * δ + δ ^ 2) ≤ U - X)
    (hdiff_sq : (xa - ya) ^ 2 ≤ 4 * α ^ 2 * (xa + ya) * X) :
    X / U ≤ 1 + 10 * α ^ 2 := by
  have hp_pos : 0 < p := by linarith only [hα0, hp_eq]
  have hp4 : 4 * p ≤ 5 := by linarith only [hα1, hp_eq]
  have hid1 : p * (δ ^ 2 * (xa + ya) + 2 * δ * (xa - ya)) =
      p * xa * (2 * δ + δ ^ 2) + p * ya * (-2 * δ + δ ^ 2) := by ring
  have hsum : p * (δ ^ 2 * (xa + ya) + 2 * δ * (xa - ya)) ≤ U - X := by
    linarith only [ht, hid1]
  have hsq : 0 ≤ (δ * (xa + ya) + (xa - ya)) ^ 2 := sq_nonneg _
  have hid2 : (δ * (xa + ya) + (xa - ya)) ^ 2 =
      (xa + ya) * (δ ^ 2 * (xa + ya) + 2 * δ * (xa - ya)) + (xa - ya) ^ 2 := by ring
  have hcomp : -(xa - ya) ^ 2 ≤ (xa + ya) * (δ ^ 2 * (xa + ya) + 2 * δ * (xa - ya)) := by
    linarith only [hsq, hid2]
  have hmul_sum : (xa + ya) * (p * (δ ^ 2 * (xa + ya) + 2 * δ * (xa - ya))) ≤
      (xa + ya) * (U - X) := mul_le_mul_of_nonneg_left hsum hA_pos.le
  have hmul_comp : -(p * (xa - ya) ^ 2) ≤
      (xa + ya) * (p * (δ ^ 2 * (xa + ya) + 2 * δ * (xa - ya))) := by
    have h := mul_le_mul_of_nonneg_left hcomp hp_pos.le
    linarith only [h, show p * -((xa - ya) ^ 2) = -(p * (xa - ya) ^ 2) by ring,
      show p * ((xa + ya) * (δ ^ 2 * (xa + ya) + 2 * δ * (xa - ya))) =
        (xa + ya) * (p * (δ ^ 2 * (xa + ya) + 2 * δ * (xa - ya))) by ring]
  have hbound : p * (xa - ya) ^ 2 ≤ 5 * α ^ 2 * (xa + ya) * X := by
    have h1 := mul_le_mul_of_nonneg_left hdiff_sq hp_pos.le
    have h2 : p * (4 * α ^ 2 * (xa + ya) * X) = (4 * p) * (α ^ 2 * (xa + ya) * X) := by ring
    have h3 : (4 * p) * (α ^ 2 * (xa + ya) * X) ≤ 5 * (α ^ 2 * (xa + ya) * X) :=
      mul_le_mul_of_nonneg_right hp4 (by positivity)
    linarith only [h1, h2, h3, show 5 * (α ^ 2 * (xa + ya) * X) = 5 * α ^ 2 * (xa + ya) * X by ring]
  have hcomb : (xa + ya) * (-(5 * α ^ 2 * X)) ≤ (xa + ya) * (U - X) := by
    linarith only [hmul_sum, hmul_comp, hbound,
      show (xa + ya) * (-(5 * α ^ 2 * X)) = -(5 * α ^ 2 * (xa + ya) * X) by ring]
  have hcancel0 := le_of_mul_le_mul_left hcomb hA_pos
  have hcancel : (1 - 5 * α ^ 2) * X ≤ U := by linarith only [hcancel0]
  have hα2 : α ^ 2 ≤ 1 / 100 := by
    have h := mul_le_mul hα1 hα1 hα0.le (by norm_num)
    linarith only [h, show α * α = α ^ 2 by ring]
  have hrem : 0 ≤ 5 * α ^ 2 * (1 - 10 * α ^ 2) :=
    mul_nonneg (by positivity) (by linarith only [hα2])
  have hquad : 1 ≤ (1 - 5 * α ^ 2) * (1 + 10 * α ^ 2) := by
    linarith only [hrem, show (1 - 5 * α ^ 2) * (1 + 10 * α ^ 2) =
      1 + 5 * α ^ 2 * (1 - 10 * α ^ 2) by ring]
  have h1 : (1 + 10 * α ^ 2) * ((1 - 5 * α ^ 2) * X) ≤ (1 + 10 * α ^ 2) * U :=
    mul_le_mul_of_nonneg_left hcancel (by positivity)
  have h2 := mul_le_mul_of_nonneg_right hquad hX_pos.le
  have hnum_le : X ≤ (1 + 10 * α ^ 2) * U := by
    linarith only [h1, h2, show (1 + 10 * α ^ 2) * ((1 - 5 * α ^ 2) * X) =
      (1 - 5 * α ^ 2) * (1 + 10 * α ^ 2) * X by ring]
  exact (div_le_iff₀ hU_pos).mpr hnum_le

private lemma ratio_le {α a b δ : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1 / 10)
    (ha : 0 < a) (hb : 0 < b) (hδ0 : 0 < δ) (_hδ1 : δ < 1) :
    ((1 + a) ^ (1 + α) + (1 + b) ^ (1 + α)) /
      ((1 + δ ^ 2 + 2 * δ + a) ^ (1 + α) + (1 + δ ^ 2 - 2 * δ + b) ^ (1 + α)) ≤
    1 + 10 * α ^ 2 := by
  have hx1 : 1 ≤ 1 + a := by linarith only [ha]
  have hy1 : 1 ≤ 1 + b := by linarith only [hb]
  have hx_pos : 0 < 1 + a := by linarith only [ha]
  have hy_pos : 0 < 1 + b := by linarith only [hb]
  have hu_pos : 0 < 1 + δ ^ 2 + 2 * δ + a := by positivity
  have hv_pos : 0 < 1 + δ ^ 2 - 2 * δ + b := by
    have hsq : 0 ≤ (1 - δ) ^ 2 := sq_nonneg (1 - δ)
    linarith only [hb, hsq]
  have hp1 : 1 ≤ 1 + α := by linarith only [hα0]
  have ht1 := rpow_tangent_le hp1 hx_pos hu_pos
  have ht2 := rpow_tangent_le hp1 hy_pos hv_pos
  have hsub : 1 + α - 1 = α := by ring
  have hux : 1 + δ ^ 2 + 2 * δ + a - (1 + a) = 2 * δ + δ ^ 2 := by ring
  have hvy : 1 + δ ^ 2 - 2 * δ + b - (1 + b) = -2 * δ + δ ^ 2 := by ring
  rw [hsub, hux] at ht1
  rw [hsub, hvy] at ht2
  exact ratio_algebra (δ := δ) hα0 hα1 rfl
    (add_pos (Real.rpow_pos_of_pos hx_pos α) (Real.rpow_pos_of_pos hy_pos α))
    (add_pos (Real.rpow_pos_of_pos hx_pos (1 + α)) (Real.rpow_pos_of_pos hy_pos (1 + α)))
    (add_pos (Real.rpow_pos_of_pos hu_pos (1 + α)) (Real.rpow_pos_of_pos hv_pos (1 + α)))
    (by have h := add_le_add ht1 ht2; linarith only [h])
    (rpow_diff_sq_le hx1 hy1 hα0)

private lemma qiuRatioSup_le (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1 / 10) :
    OMA.S_mo_104197.QiuRatioSup α ≤ 1 + 10 * α ^ 2 := by
  unfold OMA.S_mo_104197.QiuRatioSup
  apply csSup_le
  · refine ⟨_, 1, 1, 1 / 2, by norm_num, by norm_num, by norm_num, by norm_num, rfl⟩
  · rintro c ⟨a, b, δ, ha, hb, hδ0, hδ1, rfl⟩
    exact ratio_le hα0 hα1 ha hb hδ0 hδ1

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_104197.main) := by
  rintro ⟨M, ε, hM, hε, h⟩
  let α : ℝ := min (1 / 10) (min (ε / 2) (M / 20))
  have hα_pos : 0 < α := by positivity
  have hα_lt_ε : α < ε := by
    have h1 : α ≤ ε / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith only [hε, h1]
  have hα_le_tenth : α ≤ 1 / 10 := min_le_left _ _
  have hα_le_M : α ≤ M / 20 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hlow := h α hα_pos hα_lt_ε
  have hhigh := qiuRatioSup_le α hα_pos hα_le_tenth
  have hM_lt : 10 * α < M := by linarith only [hM, hα_le_M]
  have hM_mul : 10 * α ^ 2 < M * α := by
    have hmul := mul_lt_mul_of_pos_right hM_lt hα_pos
    linarith only [hmul, show 10 * α * α = 10 * α ^ 2 by ring]
  linarith only [hlow, hhigh, hM_mul]
