import OMAStatements.S_oeis_a127974

open MeasureTheory Set Filter Real Topology

namespace OMA.S_oeis_a127974

lemma smeval_desc (r : ℚ) (m : ℕ) :
    (descPochhammer ℤ m).smeval r = ∏ j ∈ Finset.range m, (r - j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [descPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_sub,
      Polynomial.smeval_X, Polynomial.smeval_natCast, ih, Finset.prod_range_succ]
    simp

lemma coeff_eq (m : ℕ) :
    PowerSeries.coeff m series = ∏ k ∈ Finset.range m, ((3 * k + 2 : ℚ) / (3 * k + 3)) := by
  unfold series
  rw [PowerSeries.coeff_rescale, PowerSeries.binomialSeries_coeff, Ring.choose_eq_smul, smeval_desc]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, ← ih, Nat.factorial_succ]
    have : ((m : ℚ) + 1) ≠ 0 := by positivity
    have h3 : (3 * (m : ℚ) + 3) ≠ 0 := by positivity
    have hf : ((m.factorial : ℕ) : ℚ) ≠ 0 := by positivity
    simp only [smul_eq_mul, mul_one, Nat.cast_mul, Nat.cast_succ]
    field_simp
    ring

lemma base_deriv (x : ℝ) (hx : 0 ≤ x) :
    HasDerivAt (fun x : ℝ => (1 / 3) * Real.log (x + 1) - (1 / 6) * Real.log (x ^ 2 - x + 1)
      + (1 / √3) * Real.arctan ((2 * x - 1) / √3)) (1 / (1 + x ^ 3)) x := by
  have h1 : 0 < x + 1 := by linarith
  have h2 : 0 < x ^ 2 - x + 1 := by nlinarith [sq_nonneg (x - 1 / 2)]
  have hs : (0 : ℝ) < √3 := by positivity
  have hs2 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have d1 : HasDerivAt (fun x : ℝ => Real.log (x + 1)) (1 / (x + 1)) x := by
    have := ((hasDerivAt_id x).add_const 1).log h1.ne'
    simpa using this
  have d2 : HasDerivAt (fun x : ℝ => Real.log (x ^ 2 - x + 1))
      ((2 * x - 1) / (x ^ 2 - x + 1)) x := by
    have : HasDerivAt (fun x : ℝ => x ^ 2 - x + 1) (2 * x - 1) x := by
      have := (((hasDerivAt_pow 2 x).sub (hasDerivAt_id x)).add_const 1)
      simpa using this
    exact this.log h2.ne'
  have d3 : HasDerivAt (fun x : ℝ => Real.arctan ((2 * x - 1) / √3))
      (1 / (1 + ((2 * x - 1) / √3) ^ 2) * (2 / √3)) x := by
    have : HasDerivAt (fun x : ℝ => (2 * x - 1) / √3) (2 / √3) x := by
      have := (((hasDerivAt_id x).const_mul 2).sub_const 1).div_const √3
      simpa using this
    exact this.arctan
  have := ((d1.const_mul (1 / 3)).sub (d2.const_mul (1 / 6))).add (d3.const_mul (1 / √3))
  have e : 1 / √3 * (1 / (1 + ((2 * x - 1) / √3) ^ 2) * (2 / √3))
      = 2 / (√3 ^ 2 + (2 * x - 1) ^ 2) := by
    field_simp
  have h3 : (0 : ℝ) < 1 + x ^ 3 := by positivity
  have h4 : (0 : ℝ) < 3 + (2 * x - 1) ^ 2 := by positivity
  have key : 1 / 3 * (1 / (x + 1)) - 1 / 6 * ((2 * x - 1) / (x ^ 2 - x + 1)) +
      1 / √3 * (1 / (1 + ((2 * x - 1) / √3) ^ 2) * (2 / √3)) = 1 / (1 + x ^ 3) := by
    rw [e, hs2, show (3 : ℝ) + (2 * x - 1) ^ 2 = 4 * (x ^ 2 - x + 1) by ring,
      show (1 : ℝ) + x ^ 3 = (x + 1) * (x ^ 2 - x + 1) by ring]
    have h1' := h1.ne'
    have h2' := h2.ne'
    generalize hQ : x ^ 2 - x + 1 = Q at h2'
    field_simp
    subst hQ
    ring
  exact this.congr_deriv key

lemma base_tendsto :
    Tendsto (fun x : ℝ => (1 / 3) * Real.log (x + 1) - (1 / 6) * Real.log (x ^ 2 - x + 1)
      + (1 / √3) * Real.arctan ((2 * x - 1) / √3)) atTop (𝓝 (0 + (1 / √3) * (π / 2))) := by
  refine Tendsto.add ?_ (Tendsto.const_mul _ ?_)
  · have hg : Tendsto (fun x : ℝ => (1 + x⁻¹) ^ 2 / (1 - x⁻¹ + x⁻¹ ^ 2)) atTop
        (𝓝 ((1 + 0) ^ 2 / (1 - 0 + 0 ^ 2))) := by
      have h0 := tendsto_inv_atTop_zero (𝕜 := ℝ)
      exact ((h0.const_add 1).pow 2).div ((h0.const_sub 1).add (h0.pow 2)) (by norm_num)
    have hl := (Real.continuousAt_log
      (by norm_num : ((1 + 0) ^ 2 / (1 - 0 + 0 ^ 2) : ℝ) ≠ 0)).tendsto.comp hg
    have hl' : Tendsto (fun x : ℝ => (1 / 6) * Real.log ((1 + x⁻¹) ^ 2 / (1 - x⁻¹ + x⁻¹ ^ 2)))
        atTop (𝓝 0) := by
      have := hl.const_mul (1 / 6)
      simpa using this
    refine hl'.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    have h2 : 0 < x ^ 2 - x + 1 := by nlinarith [sq_nonneg (x - 1 / 2)]
    have e : (1 + x⁻¹) ^ 2 / (1 - x⁻¹ + x⁻¹ ^ 2) = (x + 1) ^ 2 / (x ^ 2 - x + 1) := by
      field_simp
    rw [e, Real.log_div (by positivity) h2.ne', Real.log_pow]
    push_cast
    ring
  · have : Tendsto (fun x : ℝ => (2 * x - 1) / √3) atTop atTop := by
      apply Tendsto.atTop_div_const (by positivity)
      exact tendsto_atTop_add_const_right _ _
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
    exact (tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp this

lemma J1 : IntegrableOn (fun x : ℝ => 1 / (1 + x ^ 3)) (Ioi 0) ∧
    ∫ x in Ioi (0 : ℝ), 1 / (1 + x ^ 3) = 2 * π / (3 * √3) := by
  have hd : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun x : ℝ => (1 / 3) * Real.log (x + 1)
      - (1 / 6) * Real.log (x ^ 2 - x + 1) + (1 / √3) * Real.arctan ((2 * x - 1) / √3))
      (1 / (1 + x ^ 3)) x := fun x hx => base_deriv x hx
  have hi := integrableOn_Ioi_deriv_of_nonneg' hd
    (fun x hx => by have : (0 : ℝ) < x := hx; positivity) base_tendsto
  refine ⟨hi, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hd hi base_tendsto]
  have hs : (0 : ℝ) < √3 := by positivity
  have e : (2 * (0 : ℝ) - 1) / √3 = -(√3)⁻¹ := by ring
  simp only [e, Real.arctan_neg, Real.arctan_inv_sqrt_three]
  norm_num
  field_simp
  ring

lemma integ (n : ℕ) (hn : 1 ≤ n) :
    IntegrableOn (fun x : ℝ => 1 / (1 + x ^ 3) ^ n) (Ioi 0) := by
  refine Integrable.mono' J1.1
    (by fun_prop : Measurable fun x : ℝ => 1 / (1 + x ^ 3) ^ n).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx => ?_)
  have hx0 : (0 : ℝ) < x := hx
  have h1 : (1 : ℝ) ≤ 1 + x ^ 3 := by have := pow_pos hx0 3; linarith
  rw [Real.norm_of_nonneg (by positivity)]
  apply one_div_le_one_div_of_le (by positivity)
  calc 1 + x ^ 3 = (1 + x ^ 3) ^ 1 := (pow_one _).symm
    _ ≤ (1 + x ^ 3) ^ n := pow_le_pow_right₀ h1 hn

lemma recJ (n : ℕ) (hn : 1 ≤ n) :
    3 * (n : ℝ) * ∫ x in Ioi (0 : ℝ), 1 / (1 + x ^ 3) ^ (n + 1)
      = (3 * n - 1) * ∫ x in Ioi (0 : ℝ), 1 / (1 + x ^ 3) ^ n := by
  have hd : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun x : ℝ => x / (1 + x ^ 3) ^ n)
      ((1 - 3 * n) * (1 / (1 + x ^ 3) ^ n) + 3 * n * (1 / (1 + x ^ 3) ^ (n + 1))) x := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := hx
    have hp : (0 : ℝ) < 1 + x ^ 3 := by positivity
    have d1 : HasDerivAt (fun x : ℝ => (1 + x ^ 3) ^ n)
        (n * (1 + x ^ 3) ^ (n - 1) * (3 * x ^ 2)) x := by
      have : HasDerivAt (fun x : ℝ => 1 + x ^ 3) (3 * x ^ 2) x := by
        have := (hasDerivAt_pow 3 x).const_add 1
        simpa using this
      exact this.pow n
    have := (hasDerivAt_id x).div d1 (by positivity)
    refine this.congr_deriv ?_
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel, id]
    have hp' := hp.ne'
    generalize hQ : 1 + x ^ 3 = Q at hp'
    push_cast
    field_simp
    subst hQ
    ring
  have hi : IntegrableOn (fun x : ℝ => (1 - 3 * (n : ℝ)) * (1 / (1 + x ^ 3) ^ n)
      + 3 * n * (1 / (1 + x ^ 3) ^ (n + 1))) (Ioi 0) :=
    ((integ n hn).const_mul _).add ((integ (n + 1) (by omega)).const_mul _)
  have ht : Tendsto (fun x : ℝ => x / (1 + x ^ 3) ^ n) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ (tendsto_inv_atTop_zero (𝕜 := ℝ))
    · filter_upwards [eventually_ge_atTop 0] with x hx
      positivity
    · filter_upwards [eventually_ge_atTop 1] with x hx
      have hx0 : (0 : ℝ) < x := by linarith
      have h1 : (1 : ℝ) ≤ 1 + x ^ 3 := by have := pow_pos hx0 3; linarith
      have h2 : x ^ 2 ≤ (1 + x ^ 3) ^ n := by
        calc x ^ 2 ≤ 1 + x ^ 3 := by nlinarith [pow_pos hx0 2]
          _ = (1 + x ^ 3) ^ 1 := (pow_one _).symm
          _ ≤ (1 + x ^ 3) ^ n := pow_le_pow_right₀ h1 hn
      calc x / (1 + x ^ 3) ^ n ≤ x / x ^ 2 :=
            div_le_div_of_nonneg_left hx0.le (by positivity) h2
        _ = x⁻¹ := by field_simp
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hd hi ht
  rw [integral_add ((integ n hn).const_mul _) ((integ (n + 1) (by omega)).const_mul _),
    integral_const_mul, integral_const_mul] at h
  simp only [zero_div, sub_zero] at h
  linarith

lemma closed (m : ℕ) : ∫ x in Ioi (0 : ℝ), 1 / (1 + x ^ 3) ^ (m + 1)
    = 2 * π / (3 * √3) * ((∏ k ∈ Finset.range m, ((3 * k + 2 : ℚ) / (3 * k + 3)) : ℚ) : ℝ) := by
  induction m with
  | zero => simpa using J1.2
  | succ m ih =>
    have h := recJ (m + 1) (by omega)
    rw [ih] at h
    rw [Finset.prod_range_succ]
    push_cast at h ⊢
    have h3 : (3 * (m : ℝ) + 3) ≠ 0 := by positivity
    have e : ∫ x in Ioi (0 : ℝ), 1 / (1 + x ^ 3) ^ (m + 1 + 1)
        = (3 * (m : ℝ) + 2) / (3 * m + 3) * (2 * π / (3 * √3) *
          ∏ k ∈ Finset.range m, ((3 * (k : ℝ) + 2) / (3 * k + 3))) := by
      rw [div_mul_eq_mul_div, eq_div_iff h3]
      linear_combination h
    rw [e]
    ring

lemma num9 (m : ℕ) :
    ((∏ k ∈ Finset.range m, ((3 * k + 2 : ℚ) / (3 * k + 3))) / 9).num
      = (∏ k ∈ Finset.range m, ((3 * k + 2 : ℚ) / (3 * k + 3))).num := by
  generalize hc : (∏ k ∈ Finset.range m, ((3 * k + 2 : ℚ) / (3 * k + 3))) = c
  have hc' : c = Rat.divInt (∏ k ∈ Finset.range m, (3 * (k : ℤ) + 2))
      (∏ k ∈ Finset.range m, (3 * (k : ℤ) + 3)) := by
    rw [Rat.divInt_eq_div, ← hc, Finset.prod_div_distrib]
    push_cast
    rfl
  have hQ : (∏ k ∈ Finset.range m, (3 * (k : ℤ) + 3)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 (fun k _ => by positivity)
  have h3 : ¬ (3 : ℤ) ∣ c.num := by
    intro h
    have h1 : c.num ∣ ∏ k ∈ Finset.range m, (3 * (k : ℤ) + 2) := by
      rw [hc']
      exact Rat.num_dvd _ hQ
    have h2 := h.trans h1
    rw [Prime.dvd_finsetProd_iff Int.prime_three] at h2
    obtain ⟨k, _, hk⟩ := h2
    omega
  have e : c / 9 = (c.num : ℚ) / (((9 * c.den : ℕ) : ℤ) : ℚ) := by
    conv_lhs => rw [← Rat.num_div_den c]
    push_cast
    field_simp
  rw [e, Rat.num_div_eq_of_coprime (by have := c.den_pos; positivity)]
  rw [Int.natAbs_natCast]
  refine Nat.Coprime.mul_right ?_ c.reduced
  have h3' : ¬ 3 ∣ c.num.natAbs := by
    intro h
    exact h3 (Int.natCast_dvd.2 h)
  have := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3'
  exact (Nat.Coprime.pow_left 2 this).symm

end OMA.S_oeis_a127974

open OMA.S_oeis_a127974 in
theorem OMA.solution : type_of% @OMA.S_oeis_a127974.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨(∏ k ∈ Finset.range m, ((3 * k + 2 : ℚ) / (3 * k + 3))) / 9, ?_, ?_⟩
  · rw [closed m]
    have hs : (0 : ℝ) < √3 := by positivity
    have hs2 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
    push_cast
    generalize (∏ k ∈ Finset.range m, ((3 * (k : ℝ) + 2) / (3 * k + 3))) = c
    have : 1 / (2 * √3 * π) * (2 * π / (3 * √3) * c) = c / (3 * (√3 * √3)) := by
      field_simp
    rw [this, hs2]
    ring
  · rw [num9]
    simp only [Nat.add_sub_cancel]
    unfold a
    rw [coeff_eq]
