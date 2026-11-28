import OMAStatements.S_oeis_a127974

-- Problem: A127974: Numerators in expansion of (1-x)^(-2/3).
-- Upstream: formal-conjectures statements/oeis-a127974.lean:0 (declaration OMA.S_oeis_a127974.main)
-- Credit: @yhay81 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter MeasureTheory Set Topology

namespace OMA.Proof_oeis_a127974

private noncomputable def F (x : ℝ) : ℝ :=
  (1 / 6) * Real.log ((1 + x) ^ 2 / (x ^ 2 - x + 1)) +
    (1 / Real.sqrt 3) * Real.arctan ((2 * x - 1) / Real.sqrt 3)

private lemma quad_pos (x : ℝ) : 0 < x ^ 2 - x + 1 := by
  nlinarith [sq_nonneg (x - 1 / 2)]

private lemma hasDerivAt_F {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt F (1 / (1 + x ^ 3)) x := by
  have h1x : 0 < 1 + x := by linarith
  have hq : 0 < x ^ 2 - x + 1 := quad_pos x
  have h1x3 : 0 < 1 + x ^ 3 := by positivity
  have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsq3_ne : Real.sqrt 3 ≠ 0 := by positivity
  have hd_num : HasDerivAt (fun t : ℝ => (1 + t) ^ 2) (2 * (1 + x) ^ (2 - 1) * 1) x :=
    ((hasDerivAt_id x).const_add 1).pow 2
  have hd_den : HasDerivAt (fun t : ℝ => t ^ 2 - t + 1) (2 * x ^ (2 - 1) - 1) x :=
    ((hasDerivAt_pow 2 x).sub (hasDerivAt_id x)).add_const 1
  have hd_log : HasDerivAt (fun t : ℝ => Real.log ((1 + t) ^ 2 / (t ^ 2 - t + 1)))
      (((2 * (1 + x) ^ (2 - 1) * 1 * (x ^ 2 - x + 1) - (1 + x) ^ 2 * (2 * x ^ (2 - 1) - 1)) /
        (x ^ 2 - x + 1) ^ 2) / ((1 + x) ^ 2 / (x ^ 2 - x + 1))) x :=
    (hd_num.div hd_den hq.ne').log (div_pos (pow_pos h1x 2) hq).ne'
  have hd_arg : HasDerivAt (fun t : ℝ => (2 * t - 1) / Real.sqrt 3) ((2 * 1) / Real.sqrt 3) x :=
    (((hasDerivAt_id x).const_mul 2).sub_const 1).div_const (Real.sqrt 3)
  have hd_atan : HasDerivAt (fun t : ℝ => Real.arctan ((2 * t - 1) / Real.sqrt 3))
      ((1 / (1 + ((2 * x - 1) / Real.sqrt 3) ^ 2)) * ((2 * 1) / Real.sqrt 3)) x := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_arctan ((2 * x - 1) / Real.sqrt 3)).comp x hd_arg
  have hsum := (hd_log.const_mul (1 / 6)).add (hd_atan.const_mul (1 / Real.sqrt 3))
  have hval : 1 / 6 * (((2 * (1 + x) ^ (2 - 1) * 1 * (x ^ 2 - x + 1) -
      (1 + x) ^ 2 * (2 * x ^ (2 - 1) - 1)) / (x ^ 2 - x + 1) ^ 2) /
      ((1 + x) ^ 2 / (x ^ 2 - x + 1))) +
      1 / Real.sqrt 3 * ((1 / (1 + ((2 * x - 1) / Real.sqrt 3) ^ 2)) * ((2 * 1) / Real.sqrt 3)) =
      1 / (1 + x ^ 3) := by
    have hden_eq : 1 + ((2 * x - 1) / Real.sqrt 3) ^ 2 = 4 * (x ^ 2 - x + 1) / 3 := by
      rw [div_pow, hsq3]; ring
    have hatan_eq : 1 / Real.sqrt 3 * ((1 / (1 + ((2 * x - 1) / Real.sqrt 3) ^ 2)) *
        ((2 * 1) / Real.sqrt 3)) = 1 / (2 * (x ^ 2 - x + 1)) := by
      rw [hden_eq]
      field_simp [hq.ne', hsq3_ne]
      ring_nf
      rw [hsq3]
      ring
    rw [hatan_eq]
    simp only [Nat.reduceSub, pow_one, mul_one]
    have h1 : (2 * (1 + x) * (x ^ 2 - x + 1) - (1 + x) ^ 2 * (2 * x - 1)) / (x ^ 2 - x + 1) ^ 2 /
        ((1 + x) ^ 2 / (x ^ 2 - x + 1)) = (3 - 3 * x) / (1 + x ^ 3) := by
      rw [div_eq_div_iff (div_ne_zero (pow_ne_zero 2 h1x.ne') hq.ne') h1x3.ne',
        div_mul_eq_mul_div₀, mul_div_assoc', div_eq_div_iff (pow_ne_zero 2 hq.ne') hq.ne']
      ring
    rw [h1, eq_div_iff h1x3.ne']
    have hfac : 1 + x ^ 3 = (1 + x) * (x ^ 2 - x + 1) := by ring
    calc (1 / 6 * ((3 - 3 * x) / (1 + x ^ 3)) + 1 / (2 * (x ^ 2 - x + 1))) * (1 + x ^ 3)
        = (1 / 6 * (3 - 3 * x)) * ((1 + x ^ 3) / (1 + x ^ 3)) +
          ((1 + x) * (x ^ 2 - x + 1)) / (2 * (x ^ 2 - x + 1)) := by
            rw [← hfac]; ring
      _ = 1 / 6 * (3 - 3 * x) * 1 + (1 + x) / 2 := by
            rw [div_self h1x3.ne', mul_div_mul_right _ _ hq.ne']
      _ = 1 := by ring
  rw [← hval]
  exact hsum

private lemma tendsto_F_atTop : Tendsto F atTop (𝓝 (Real.pi / (2 * Real.sqrt 3))) := by
  have hrat : Tendsto (fun x : ℝ => (1 + x) ^ 2 / (x ^ 2 - x + 1)) atTop (𝓝 1) := by
    have hnum : Tendsto (fun x : ℝ => 1 + 2 * x⁻¹ + x⁻¹ ^ 2) atTop (𝓝 (1 + 2 * 0 + 0 ^ 2)) :=
      ((tendsto_const_nhds.add (tendsto_inv_atTop_zero.const_mul 2)).add
        (tendsto_inv_atTop_zero.pow 2))
    have hden : Tendsto (fun x : ℝ => 1 - x⁻¹ + x⁻¹ ^ 2) atTop (𝓝 (1 - 0 + 0 ^ 2)) :=
      ((tendsto_const_nhds.sub tendsto_inv_atTop_zero).add (tendsto_inv_atTop_zero.pow 2))
    have hq : Tendsto (fun x : ℝ => (1 + 2 * x⁻¹ + x⁻¹ ^ 2) / (1 - x⁻¹ + x⁻¹ ^ 2))
        atTop (𝓝 ((1 + 2 * 0 + 0 ^ 2) / (1 - 0 + 0 ^ 2))) :=
      hnum.div hden (by norm_num)
    simp only [mul_zero, add_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, div_one] at hq
    refine hq.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have h1 : x ^ 2 - x + 1 ≠ 0 := (quad_pos x).ne'
    have h2 : 1 - x⁻¹ + x⁻¹ ^ 2 ≠ 0 := by
      have : 1 - x⁻¹ + x⁻¹ ^ 2 = (x ^ 2 - x + 1) / x ^ 2 := by field_simp [hx.ne']
      rw [this]
      exact div_ne_zero h1 (pow_ne_zero 2 hx.ne')
    field_simp [hx.ne', h1, h2]
    ring
  have hlog : Tendsto (fun x : ℝ => (1 / 6 : ℝ) * Real.log ((1 + x) ^ 2 / (x ^ 2 - x + 1)))
      atTop (𝓝 0) := by
    have := ((Real.continuousAt_log one_ne_zero).tendsto.comp hrat).const_mul (1 / 6 : ℝ)
    simpa [Real.log_one] using this
  have hlin : Tendsto (fun x : ℝ => (2 * x - 1) / Real.sqrt 3) atTop atTop := by
    have h1 : Tendsto (fun x : ℝ => 2 * x) atTop atTop :=
      Tendsto.const_mul_atTop (by norm_num) tendsto_id
    have h2 : Tendsto (fun x : ℝ => 2 * x + (-1 : ℝ)) atTop atTop :=
      h1.atTop_add tendsto_const_nhds
    simpa [sub_eq_add_neg] using h2.atTop_div_const (by positivity : (0 : ℝ) < Real.sqrt 3)
  have hatan : Tendsto (fun x : ℝ => (1 / Real.sqrt 3) * Real.arctan ((2 * x - 1) / Real.sqrt 3))
      atTop (𝓝 (Real.pi / (2 * Real.sqrt 3))) := by
    have h1 : Tendsto (fun x : ℝ => Real.arctan ((2 * x - 1) / Real.sqrt 3))
        atTop (𝓝 (Real.pi / 2)) :=
      (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hlin
    have h2 := h1.const_mul (1 / Real.sqrt 3)
    have heq : (1 / Real.sqrt 3) * (Real.pi / 2) = Real.pi / (2 * Real.sqrt 3) := by ring
    rwa [heq] at h2
  have hsum := hlog.add hatan
  rw [zero_add] at hsum
  exact hsum

private lemma integrableOn_inv_one_add_cube :
    IntegrableOn (fun x : ℝ => 1 / (1 + x ^ 3)) (Ioi (0 : ℝ)) :=
  integrableOn_Ioi_deriv_of_nonneg'
    (fun x hx => hasDerivAt_F hx)
    (fun x hx => by
      have : 0 < x := hx
      positivity)
    tendsto_F_atTop

private lemma integral_base :
    ∫ x in Ioi (0 : ℝ), 1 / (1 + x ^ 3) = 2 * Real.pi / (3 * Real.sqrt 3) := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun x hx => hasDerivAt_F hx)
    (fun x hx => by
      have : 0 < x := hx
      positivity)
    tendsto_F_atTop
  have hF0 : F 0 = -Real.pi / (6 * Real.sqrt 3) := by
    simp only [F, add_zero, one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      sub_zero, zero_add, div_one, Real.log_one, mul_zero, zero_sub, neg_div]
    rw [Real.arctan_neg, one_div, Real.arctan_inv_sqrt_three]
    ring
  rw [h, hF0]
  ring

private lemma integrableOn_inv_one_add_cube_pow {n : ℕ} (hn : 1 ≤ n) :
    IntegrableOn (fun x : ℝ => 1 / (1 + x ^ 3) ^ n) (Ioi (0 : ℝ)) := by
  refine integrableOn_inv_one_add_cube.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro x hx
    have hx' : 0 < x := hx
    have hne : (1 + x ^ 3) ^ n ≠ 0 := by positivity
    exact (continuousAt_const.div
      ((continuousAt_const.add (continuousAt_id.pow 3)).pow n) hne).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx' : 0 < x := hx
    have h1 : 1 ≤ 1 + x ^ 3 := by nlinarith [pow_nonneg hx'.le 3]
    have hpow : 1 + x ^ 3 ≤ (1 + x ^ 3) ^ n := by
      calc 1 + x ^ 3 = (1 + x ^ 3) ^ 1 := (pow_one _).symm
        _ ≤ (1 + x ^ 3) ^ n := pow_le_pow_right₀ h1 hn
    rw [Real.norm_of_nonneg (by positivity)]
    exact one_div_le_one_div_of_le (by positivity) hpow

private noncomputable def G (m : ℕ) (x : ℝ) : ℝ :=
  x / (3 * ((m + 1 : ℕ) : ℝ) * (1 + x ^ 3) ^ (m + 1))

private lemma hasDerivAt_G (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (G m)
      (1 / (1 + x ^ 3) ^ (m + 2) -
        ((3 * (m : ℝ) + 2) / (3 * ((m + 1 : ℕ) : ℝ))) * (1 / (1 + x ^ 3) ^ (m + 1))) x := by
  have hm : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have h1x3 : 0 < 1 + x ^ 3 := by positivity
  have hden_ne : 3 * ((m + 1 : ℕ) : ℝ) * (1 + x ^ 3) ^ (m + 1) ≠ 0 := by positivity
  have hd_inner : HasDerivAt (fun t : ℝ => 1 + t ^ 3) (3 * x ^ (3 - 1)) x :=
    (hasDerivAt_pow 3 x).const_add 1
  have hd_pow : HasDerivAt (fun t : ℝ => (1 + t ^ 3) ^ (m + 1))
      (((m + 1 : ℕ) : ℝ) * (1 + x ^ 3) ^ m * (3 * x ^ (3 - 1))) x :=
    hd_inner.pow (m + 1)
  have hd_den : HasDerivAt (fun t : ℝ => 3 * ((m + 1 : ℕ) : ℝ) * (1 + t ^ 3) ^ (m + 1))
      (3 * ((m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) * (1 + x ^ 3) ^ m * (3 * x ^ (3 - 1)))) x :=
    hd_pow.const_mul (3 * ((m + 1 : ℕ) : ℝ))
  have hdiv := (hasDerivAt_id x).div hd_den hden_ne
  simp only [id_eq] at hdiv
  have hval : (1 * (3 * ((m + 1 : ℕ) : ℝ) * (1 + x ^ 3) ^ (m + 1)) -
      x * (3 * ((m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) * (1 + x ^ 3) ^ m * (3 * x ^ (3 - 1))))) /
      (3 * ((m + 1 : ℕ) : ℝ) * (1 + x ^ 3) ^ (m + 1)) ^ 2 =
      1 / (1 + x ^ 3) ^ (m + 2) -
        ((3 * (m : ℝ) + 2) / (3 * ((m + 1 : ℕ) : ℝ))) * (1 / (1 + x ^ 3) ^ (m + 1)) := by
    have hp1 : (1 + x ^ 3) ^ (m + 1) = (1 + x ^ 3) ^ m * (1 + x ^ 3) := pow_succ _ m
    have hp2 : (1 + x ^ 3) ^ (m + 2) = (1 + x ^ 3) ^ m * (1 + x ^ 3) ^ 2 := by rw [pow_add]
    have hpm : (1 + x ^ 3) ^ m ≠ 0 := by positivity
    simp only [Nat.reduceSub]
    rw [hp2, hp1]
    push_cast
    field_simp [hm.ne', h1x3.ne', hpm]
    ring
  rw [← hval]
  exact hdiv

private lemma tendsto_G_atTop (m : ℕ) : Tendsto (G m) atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ tendsto_inv_atTop_zero
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    unfold G
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    unfold G
    have hx0 : 0 < x := by linarith
    have hm1 : (1 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast Nat.succ_pos m
    have h1 : 1 ≤ 1 + x ^ 3 := by nlinarith [pow_nonneg hx0.le 3]
    have hpow : 1 + x ^ 3 ≤ (1 + x ^ 3) ^ (m + 1) := by
      calc 1 + x ^ 3 = (1 + x ^ 3) ^ 1 := (pow_one _).symm
        _ ≤ (1 + x ^ 3) ^ (m + 1) := pow_le_pow_right₀ h1 (Nat.succ_pos m)
    have hx2 : x ^ 2 ≤ 3 * ((m + 1 : ℕ) : ℝ) * (1 + x ^ 3) ^ (m + 1) := by
      have : x ^ 2 ≤ 1 + x ^ 3 := by nlinarith
      nlinarith
    calc x / (3 * ((m + 1 : ℕ) : ℝ) * (1 + x ^ 3) ^ (m + 1))
        ≤ x / x ^ 2 := div_le_div_of_nonneg_left hx0.le (by positivity) hx2
      _ = x⁻¹ := by field_simp [hx0.ne']

private lemma integral_succ (m : ℕ) :
    ∫ x in Ioi (0 : ℝ), 1 / (1 + x ^ 3) ^ (m + 2) =
      ((3 * (m : ℝ) + 2) / (3 * ((m + 1 : ℕ) : ℝ))) *
        ∫ x in Ioi (0 : ℝ), 1 / (1 + x ^ 3) ^ (m + 1) := by
  have hint2 := integrableOn_inv_one_add_cube_pow (n := m + 2) (by omega)
  have hint1 := integrableOn_inv_one_add_cube_pow (n := m + 1) (by omega)
  have hsub := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun x hx => hasDerivAt_G m hx)
    (hint2.sub (hint1.const_mul _))
    (tendsto_G_atTop m)
  have hG0 : G m 0 = 0 := by simp [G]
  rw [hG0, sub_self, integral_sub hint2 (hint1.const_mul _), integral_const_mul] at hsub
  linarith

private lemma coeff_series_zero :
    PowerSeries.coeff 0 OMA.S_oeis_a127974.series = 1 := by
  simp [OMA.S_oeis_a127974.series]

private lemma coeff_series_succ (m : ℕ) :
    PowerSeries.coeff (m + 1) OMA.S_oeis_a127974.series =
      ((3 * (m : ℚ) + 2) / (3 * ((m + 1 : ℕ) : ℚ))) *
        PowerSeries.coeff m OMA.S_oeis_a127974.series := by
  simp only [OMA.S_oeis_a127974.series, PowerSeries.coeff_rescale,
    PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one, Ring.choose_eq_smul,
    descPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_sub,
    Polynomial.smeval_X, Polynomial.smeval_natCast, pow_zero, pow_one,
    Nat.factorial_succ, Nat.cast_mul, mul_inv]
  have hm : ((m + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hfac : (m.factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp [hm, hfac]
  ring

private lemma integral_eq_rat (m : ℕ) :
    (((1 / 9 : ℚ) * PowerSeries.coeff m OMA.S_oeis_a127974.series : ℚ) : ℝ) =
      (1 / (2 * Real.sqrt 3 * Real.pi)) *
        ∫ x in Ioi (0 : ℝ), 1 / (1 + x ^ 3) ^ (m + 1) := by
  induction m with
  | zero =>
    rw [coeff_series_zero, mul_one]
    simp only [Nat.zero_add, pow_one, integral_base]
    have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have h3 : Real.sqrt 3 ≠ 0 := by positivity
    push_cast
    field_simp [hpi, h3]
    nlinarith [hsq3]
  | succ m ih =>
    rw [coeff_series_succ, integral_succ]
    have hcast : (((1 / 9 : ℚ) *
        (((3 * (m : ℚ) + 2) / (3 * ((m + 1 : ℕ) : ℚ))) *
          PowerSeries.coeff m OMA.S_oeis_a127974.series) : ℚ) : ℝ) =
      ((3 * (m : ℝ) + 2) / (3 * ((m + 1 : ℕ) : ℝ))) *
        (((1 / 9 : ℚ) * PowerSeries.coeff m OMA.S_oeis_a127974.series : ℚ) : ℝ) := by
      push_cast
      ring
    rw [hcast, ih]
    ring

private def prodNum (m : ℕ) : ℤ :=
  ∏ k ∈ Finset.range m, (3 * (k : ℤ) + 2)

private lemma coeff_series_eq_div (m : ℕ) :
    PowerSeries.coeff m OMA.S_oeis_a127974.series =
      (prodNum m : ℚ) / ((3 ^ m * m.factorial : ℕ) : ℚ) := by
  induction m with
  | zero =>
    simp [coeff_series_zero, prodNum]
  | succ m ih =>
    have hP : prodNum (m + 1) = prodNum m * (3 * (m : ℤ) + 2) :=
      Finset.prod_range_succ _ m
    rw [coeff_series_succ, ih, hP]
    have hm : ((m + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hfac : (m.factorial : ℚ) ≠ 0 := by positivity
    rw [pow_succ, Nat.factorial_succ]
    push_cast
    field_simp [hm, hfac]

private lemma not_three_dvd_prodNum (m : ℕ) : ¬ (3 : ℤ) ∣ prodNum m := by
  induction m with
  | zero =>
    simp [prodNum]
  | succ m ih =>
    have hP : prodNum (m + 1) = prodNum m * (3 * (m : ℤ) + 2) :=
      Finset.prod_range_succ _ m
    rw [hP]
    intro hdvd
    have hprime : Prime (3 : ℤ) := Int.prime_three
    rcases hprime.dvd_or_dvd hdvd with h1 | h2
    · exact ih h1
    · rcases h2 with ⟨k, hk⟩
      omega

private lemma not_three_dvd_coeff_num (m : ℕ) :
    ¬ (3 : ℤ) ∣ (PowerSeries.coeff m OMA.S_oeis_a127974.series).num := by
  have hQne : ((3 ^ m * m.factorial : ℕ) : ℤ) ≠ 0 := by positivity
  have hdvd : (PowerSeries.coeff m OMA.S_oeis_a127974.series).num ∣ prodNum m := by
    rw [coeff_series_eq_div]
    have heq : (prodNum m : ℚ) / ((3 ^ m * m.factorial : ℕ) : ℚ) =
        Rat.divInt (prodNum m) ((3 ^ m * m.factorial : ℕ) : ℤ) := by
      rw [Rat.divInt_eq_div]
      push_cast
      rfl
    rw [heq]
    exact Rat.num_dvd (prodNum m) hQne
  intro h3
  exact not_three_dvd_prodNum m (dvd_trans h3 hdvd)

private lemma num_one_ninth_mul {r : ℚ} (h3 : ¬ (3 : ℤ) ∣ r.num) :
    ((1 / 9 : ℚ) * r).num = r.num := by
  have heq : (1 / 9 : ℚ) * r = (r.num : ℚ) / (((9 * r.den : ℕ) : ℤ) : ℚ) := by
    conv_lhs => rw [← r.num_div_den]
    push_cast
    ring
  rw [heq]
  refine Rat.num_div_eq_of_coprime (by have := r.pos; positivity) ?_
  rw [Int.natAbs_natCast]
  refine Nat.Coprime.mul_right ?_ r.reduced
  have hcop3 : Nat.Coprime r.num.natAbs 3 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro hd
    exact h3 (Int.natCast_dvd.mpr hd)
  simpa using hcop3.pow_right 2

end OMA.Proof_oeis_a127974

theorem OMA.solution : type_of% @OMA.S_oeis_a127974.main := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  refine ⟨(1 / 9 : ℚ) * PowerSeries.coeff m OMA.S_oeis_a127974.series, ?_, ?_⟩
  · exact OMA.Proof_oeis_a127974.integral_eq_rat m
  · simp only [OMA.S_oeis_a127974.a]
    exact OMA.Proof_oeis_a127974.num_one_ninth_mul
      (OMA.Proof_oeis_a127974.not_three_dvd_coeff_num m)
