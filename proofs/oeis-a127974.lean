import OMAStatements.S_oeis_a127974

/-!
# Proof of the integral conjecture of OEIS A127974

Source: https://oeis.org/A127974
Credit: @bmendonca3

For `n ≥ 1`, `(1 / (2 √3 π)) ∫_{x ≥ 0} dx / (1 + x^3)^n = c(n-1) / 9`, where `c(m)` is the
coefficient of `x^m` in `(1 - x)^(-2/3)`, and the numerator of `c(n-1) / 9` is the numerator
`a(n-1)` of `c(n-1)`.

Outline. Write `I(n)` for the integral.
* `c(m) m! 3^m = ∏_{k < m} (3 k + 2)`, so `c(m+1) (3 m + 3) = c(m) (3 m + 2)`.
* `I(1) = 2 π / (3 √3)`: an antiderivative of `1 / (1 + x^3)` is
  `log (1 + x) / 3 - log (x^2 - x + 1) / 6 + arctan ((2 x - 1) / √3) / √3`.
* `3 n I(n+1) = (3 n - 1) I(n)`: integrate the derivative of `x / (1 + x^3)^n`, which is
  `(1 - 3 n) / (1 + x^3)^n + 3 n / (1 + x^3)^(n+1)`.
* So `I(m+1) = (2 π / (3 √3)) c(m)` by induction, and the number in the statement is
  `c(n-1) / 9`.
* The product `∏_{k < m} (3 k + 2)` is prime to `3`, so the numerator of `c(m)` is prime to `3`
  and division by `9` does not change it.
-/

namespace OMA.A127974Proof

open OMA.S_oeis_a127974 MeasureTheory Set Filter Topology

/-- The coefficient of `x^m` in `(1 - x)^(-2/3)`, with the denominators cleared. -/
lemma coeff_series_mul (m : ℕ) :
    PowerSeries.coeff m series * ((m.factorial : ℚ) * 3 ^ m)
      = ∏ k ∈ Finset.range m, (3 * (k : ℚ) + 2) := by
  have h1 : (m.factorial : ℚ) * Ring.choose (-2 / 3 : ℚ) m
      = (descPochhammer ℤ m).smeval (-2 / 3 : ℚ) := by
    rw [Ring.descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul]
  have h2 : ∀ j : ℕ, (-1 : ℚ) ^ j * (descPochhammer ℤ j).smeval (-2 / 3 : ℚ) * 3 ^ j
      = ∏ k ∈ Finset.range j, (3 * (k : ℚ) + 2) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Finset.prod_range_succ, ← ih, descPochhammer_succ_right, Polynomial.smeval_mul,
        Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast, pow_one, pow_zero,
        nsmul_one]
      ring
  rw [← h2 m]
  unfold series
  rw [PowerSeries.coeff_rescale, PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one]
  linear_combination ((-1 : ℚ) ^ m * 3 ^ m) * h1

/-- The numerator of the coefficient is prime to `3`. -/
lemma three_not_dvd_num (m : ℕ) : ¬ (3 : ℤ) ∣ (PowerSeries.coeff m series).num := by
  set c := PowerSeries.coeff m series with hc
  intro h3
  have hP : ((c.num * ((m.factorial : ℤ) * 3 ^ m) : ℤ) : ℚ)
      = ((c.den * ∏ k ∈ Finset.range m, (3 * (k : ℤ) + 2) : ℤ) : ℚ) := by
    have h := coeff_series_mul m
    rw [← hc] at h
    push_cast
    rw [← h]
    linear_combination (-(m.factorial : ℚ) * 3 ^ m) * Rat.mul_den_eq_num c
  have hP' : c.num * ((m.factorial : ℤ) * 3 ^ m)
      = c.den * ∏ k ∈ Finset.range m, (3 * (k : ℤ) + 2) := by exact_mod_cast hP
  have hdvd : (3 : ℤ) ∣ c.den * ∏ k ∈ Finset.range m, (3 * (k : ℤ) + 2) := by
    rw [← hP']; exact Dvd.dvd.mul_right h3 _
  have hp3 : Prime (3 : ℤ) := Int.prime_three
  rcases hp3.dvd_or_dvd hdvd with h | h
  · have hcop : IsCoprime c.num (c.den : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      exact c.reduced
    exact hp3.not_isUnit (hcop.isUnit_of_dvd' h3 h)
  · rw [hp3.dvd_finsetProd_iff] at h
    obtain ⟨k, -, hk⟩ := h
    omega

/-- Division by `9` does not change the numerator. -/
lemma num_div_nine (m : ℕ) :
    (PowerSeries.coeff m series / 9).num = (PowerSeries.coeff m series).num := by
  set c := PowerSeries.coeff m series with hc
  have h3 := three_not_dvd_num m
  rw [← hc] at h3
  have hcop : IsCoprime c.num (9 * (c.den : ℤ)) := by
    have h9 : IsCoprime c.num (9 : ℤ) := by
      have : IsCoprime c.num (3 : ℤ) :=
        ((Int.prime_three.coprime_iff_not_dvd).mpr h3).symm
      simpa using this.pow_right (n := 2)
    refine h9.mul_right ?_
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact c.reduced
  have hq : c / 9 = ((c.num : ℚ) / ((9 * (c.den : ℤ) : ℤ) : ℚ)) := by
    conv_lhs => rw [← Rat.num_div_den c]
    push_cast
    field_simp
  rw [hq]
  exact Rat.num_div_eq_of_coprime (by positivity) (Int.isCoprime_iff_gcd_eq_one.mp hcop)

/-- For `x ≥ 0`, `1 + x^3` dominates `(1 + x^2) / 2`. -/
lemma half_le_cube {x : ℝ} (hx : 0 ≤ x) : (1 + x ^ 2) / 2 ≤ 1 + x ^ 3 := by
  nlinarith [sq_nonneg (x - 1), mul_nonneg hx (sq_nonneg (x - 1))]

/-- For `x ≥ 0` and `n ≥ 1`, `1 + x^3 ≤ (1 + x^3)^n`. -/
lemma cube_le_pow {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : 1 ≤ n) :
    1 + x ^ 3 ≤ (1 + x ^ 3) ^ n :=
  le_self_pow₀ (by have := pow_nonneg hx 3; linarith) (by omega)

/-- The integrand is integrable on `(0, ∞)` for `n ≥ 1`. -/
lemma integrableOn_pow {n : ℕ} (hn : 1 ≤ n) :
    IntegrableOn (fun x : ℝ => 1 / (1 + x ^ 3) ^ n) (Ioi 0) := by
  have hg : IntegrableOn (fun x : ℝ => 2 * (1 + x ^ 2)⁻¹) (Ioi 0) :=
    (integrable_inv_one_add_sq.const_mul 2).integrableOn
  refine Integrable.mono' hg (by fun_prop : Measurable _).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : (0 : ℝ) ≤ x := le_of_lt hx
  have h1 := half_le_cube hx0
  have h2 := cube_le_pow hx0 hn
  have h3 : (0 : ℝ) < 1 + x ^ 2 := by positivity
  rw [Real.norm_of_nonneg (by positivity), div_le_iff₀ (by linarith)]
  have h4 : 2 * (1 + x ^ 2)⁻¹ * ((1 + x ^ 2) / 2) = 1 := by field_simp
  have h5 : (0 : ℝ) ≤ 2 * (1 + x ^ 2)⁻¹ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (h1.trans h2) h5]

/-- The reduction formula `3 n I(n+1) = (3 n - 1) I(n)`. -/
lemma integral_succ {n : ℕ} (hn : 1 ≤ n) :
    (3 * (n : ℝ)) * ∫ x in Ioi (0 : ℝ), 1 / (1 + x ^ 3) ^ (n + 1)
      = (3 * (n : ℝ) - 1) * ∫ x in Ioi (0 : ℝ), 1 / (1 + x ^ 3) ^ n := by
  have hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun x : ℝ => x / (1 + x ^ 3) ^ n)
      ((1 - 3 * (n : ℝ)) * (1 / (1 + x ^ 3) ^ n) + 3 * (n : ℝ) * (1 / (1 + x ^ 3) ^ (n + 1)))
      x := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := hx
    have hpos : (0 : ℝ) < 1 + x ^ 3 := by positivity
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hne := hpos.ne'
    have h := (hasDerivAt_id' x).fun_div (((hasDerivAt_pow 3 x).const_add 1).fun_pow (k + 1))
      (pow_ne_zero _ hne)
    refine h.congr_deriv ?_
    simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
    ring
  have hint : IntegrableOn (fun x : ℝ => (1 - 3 * (n : ℝ)) * (1 / (1 + x ^ 3) ^ n)
      + 3 * (n : ℝ) * (1 / (1 + x ^ 3) ^ (n + 1))) (Ioi 0) :=
    ((integrableOn_pow hn).const_mul _).add ((integrableOn_pow (by omega)).const_mul _)
  have hlim : Tendsto (fun x : ℝ => x / (1 + x ^ 3) ^ n) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds tendsto_inv_atTop_zero
      ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      positivity
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      have h2 := cube_le_pow hx.le hn
      have h3 : x ^ 2 ≤ 1 + x ^ 3 := by
        rcases le_total x 1 with h | h
        · nlinarith [pow_nonneg hx.le 3]
        · nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr h)]
      rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ hx]
      nlinarith
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  rw [integral_add ((integrableOn_pow hn).const_mul _) ((integrableOn_pow (by omega)).const_mul _),
    integral_const_mul, integral_const_mul] at h
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, zero_div, sub_self]
    at h
  linarith

/-- The case `n = 1`: `I(1) = 2 π / (3 √3)`. -/
lemma integral_one :
    ∫ x in Ioi (0 : ℝ), 1 / (1 + x ^ 3) ^ 1 = 2 * Real.pi / (3 * Real.sqrt 3) := by
  set s : ℝ := Real.sqrt 3 with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : s ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hq : ∀ x : ℝ, 0 < x ^ 2 - x + 1 := fun x => by nlinarith [sq_nonneg (x - 1 / 2)]
  have hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt
      (fun x : ℝ => 1 / 3 * Real.log (1 + x) - 1 / 6 * Real.log (x ^ 2 - x + 1)
        + 1 / s * Real.arctan ((2 * x - 1) / s))
      (1 / (1 + x ^ 3) ^ 1) x := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := hx
    have hpos : (0 : ℝ) < 1 + x := by positivity
    have h1 : HasDerivAt (fun x : ℝ => Real.log (1 + x)) (1 / (1 + x)) x :=
      ((hasDerivAt_id x).const_add 1).log hpos.ne'
    have h2 : HasDerivAt (fun x : ℝ => Real.log (x ^ 2 - x + 1))
        ((2 * x - 1) / (x ^ 2 - x + 1)) x := by
      have h := (((hasDerivAt_pow 2 x).fun_sub (hasDerivAt_id' x)).add_const 1).log (hq x).ne'
      refine h.congr_deriv ?_
      norm_num
    have h3 : HasDerivAt (fun x : ℝ => Real.arctan ((2 * x - 1) / s))
        (1 / (1 + ((2 * x - 1) / s) ^ 2) * (2 / s)) x := by
      have h := ((((hasDerivAt_id' x).const_mul 2).sub_const 1).div_const s).arctan
      refine h.congr_deriv ?_
      rw [mul_one]
    have h := ((h1.const_mul (1 / 3)).fun_sub (h2.const_mul (1 / 6))).fun_add
      (h3.const_mul (1 / s))
    refine h.congr_deriv ?_
    have h4 : 1 / s * (1 / (1 + ((2 * x - 1) / s) ^ 2) * (2 / s))
        = 2 / (3 + (2 * x - 1) ^ 2) := by
      rw [div_pow, hs2]
      have h5 : (3 : ℝ) + (2 * x - 1) ^ 2 ≠ 0 := by positivity
      field_simp
      exact hs2.symm
    have h7 : x * (x - 1) + 1 ≠ 0 := by
      rw [show x * (x - 1) + 1 = x ^ 2 - x + 1 by ring]
      exact (hq x).ne'
    have h8 := hpos.ne'
    rw [h4, show (3 : ℝ) + (2 * x - 1) ^ 2 = 4 * (x ^ 2 - x + 1) by ring, pow_one,
      show (1 : ℝ) + x ^ 3 = (1 + x) * (x ^ 2 - x + 1) by ring]
    field_simp
    ring
  have hlim : Tendsto (fun x : ℝ => 1 / 3 * Real.log (1 + x) - 1 / 6 * Real.log (x ^ 2 - x + 1)
        + 1 / s * Real.arctan ((2 * x - 1) / s)) atTop (𝓝 (0 + 1 / s * (Real.pi / 2))) := by
    refine Tendsto.add ?_ ?_
    · have hr : Tendsto (fun x : ℝ => 1 + 3 * x / (x ^ 2 - x + 1)) atTop (𝓝 (1 + 0)) := by
        refine tendsto_const_nhds.add ?_
        have h6 : Tendsto (fun x : ℝ => 6 * x⁻¹) atTop (𝓝 0) := by
          simpa using tendsto_inv_atTop_zero.const_mul (6 : ℝ)
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h6 ?_ ?_
        · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
          have := hq x
          positivity
        · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
          have := hq x
          rw [div_le_iff₀ this, ← div_eq_mul_inv, div_mul_eq_mul_div, le_div_iff₀ hx]
          nlinarith [sq_nonneg (x - 1)]
      have hlog := (Real.continuousAt_log (by norm_num : (1 + 0 : ℝ) ≠ 0)).tendsto.comp hr
      have hlog' : Tendsto (fun x : ℝ => 1 / 6 * Real.log (1 + 3 * x / (x ^ 2 - x + 1))) atTop
          (𝓝 0) := by
        simpa using hlog.const_mul (1 / 6 : ℝ)
      refine hlog'.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      have h1 := (hq x).ne'
      have h3 : 1 + 3 * x / (x ^ 2 - x + 1) = (1 + x) ^ 2 / (x ^ 2 - x + 1) := by
        rw [eq_div_iff h1, add_mul, div_mul_cancel₀ _ h1]
        ring
      rw [h3, Real.log_div (by positivity) h1, Real.log_pow]
      push_cast
      ring
    · refine Tendsto.const_mul _ ?_
      refine (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp ?_
      refine Tendsto.atTop_div_const hs0 ?_
      exact tendsto_atTop_add_const_right _ _
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (integrableOn_pow le_rfl) hlim
  rw [h]
  have h0 : Real.arctan ((2 * 0 - 1) / s) = -(Real.pi / 6) := by
    rw [show (2 * 0 - 1 : ℝ) / s = -(s⁻¹) by ring, Real.arctan_neg, hs,
      Real.arctan_inv_sqrt_three]
  rw [h0]
  simp only [add_zero, Real.log_one, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, sub_self, zero_add]
  field_simp
  ring

/-- The recurrence of the coefficients: `c(m+1) (3 m + 3) = c(m) (3 m + 2)`. -/
lemma coeff_succ (m : ℕ) :
    PowerSeries.coeff (m + 1) series * (3 * (m : ℚ) + 3)
      = PowerSeries.coeff m series * (3 * (m : ℚ) + 2) := by
  have h1 := coeff_series_mul (m + 1)
  have h0 := coeff_series_mul m
  rw [Finset.prod_range_succ, ← h0, Nat.factorial_succ] at h1
  push_cast at h1
  have hf : ((m.factorial : ℚ) * 3 ^ m) ≠ 0 := by positivity
  apply mul_right_cancel₀ hf
  linear_combination h1

/-- The value of the integral: `I(m+1) = (2 π / (3 √3)) c(m)`. -/
lemma integral_eq (m : ℕ) :
    ∫ x in Ioi (0 : ℝ), 1 / (1 + x ^ 3) ^ (m + 1)
      = 2 * Real.pi / (3 * Real.sqrt 3) * ((PowerSeries.coeff m series : ℚ) : ℝ) := by
  induction m with
  | zero =>
    have h : PowerSeries.coeff 0 series = 1 := by simpa using coeff_series_mul 0
    rw [integral_one, h, Rat.cast_one, mul_one]
  | succ m ih =>
    have h := integral_succ (n := m + 1) (by omega)
    rw [ih] at h
    have hc : ((PowerSeries.coeff (m + 1) series : ℚ) : ℝ) * (3 * (m : ℝ) + 3)
        = ((PowerSeries.coeff m series : ℚ) : ℝ) * (3 * (m : ℝ) + 2) := by
      exact_mod_cast coeff_succ m
    push_cast at h
    have h3 : (3 * (m : ℝ) + 3) ≠ 0 := by positivity
    apply mul_left_cancel₀ h3
    linear_combination h - (2 * Real.pi / (3 * Real.sqrt 3)) * hc

end OMA.A127974Proof

open OMA.S_oeis_a127974 OMA.A127974Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a127974.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨PowerSeries.coeff m series / 9, ?_, ?_⟩
  · have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hs0 : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    rw [integral_eq m]
    push_cast
    field_simp
    rw [hs]
    ring
  · rw [Nat.add_sub_cancel]
    exact num_div_nine m
