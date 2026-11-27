import FormalConjectures.OptimizationConstants.«1a»

/-!
# Lower bound C1a >= 13 / 10 via 5-tent Bochner-admissible kernel
-/

namespace C1aLower

open MeasureTheory Set Real

/- ### Block A: Box, Tent, and Elementary Cosine Orthogonality -/

noncomputable def box (b x : ℝ) : ℝ :=
  (1 / (2 * b)) * Set.indicator (Set.Icc (-b) b) (fun _ => (1 : ℝ)) x

noncomputable def tent (b x : ℝ) : ℝ :=
  (1 / (2 * b)) * max 0 (1 - |x| / (2 * b))

lemma box_nonneg {b : ℝ} (hb : 0 < b) (x : ℝ) : 0 ≤ box b x := by
  unfold box
  apply mul_nonneg
  · positivity
  · exact Set.indicator_nonneg (fun _ _ => zero_le_one) x

lemma box_even (b x : ℝ) : box b (-x) = box b x := by
  unfold box
  congr 1
  simp only [Set.indicator, Set.mem_Icc]
  split_ifs with h1 h2 h2
  · rfl
  · exfalso; apply h2; constructor <;> linarith
  · exfalso; apply h1; constructor <;> linarith
  · rfl

lemma box_eq_zero_of_lt {b x : ℝ} (hx : b < |x|) : box b x = 0 := by
  unfold box
  have hn : x ∉ Set.Icc (-b) b := by
    simp only [Set.mem_Icc, not_and, not_le]
    intro _
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h] at hx; exact hx
    · rw [abs_of_neg h] at hx; linarith
  simp [Set.indicator_of_notMem hn]

lemma box_measurable (b : ℝ) : Measurable (box b) := by
  unfold box
  exact (measurable_const.indicator measurableSet_Icc).const_mul _

lemma box_integrable (b : ℝ) : Integrable (box b) := by
  unfold box
  have h1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc (-b) b) :=
    integrableOn_const measure_Icc_lt_top.ne
  exact (h1.integrable_indicator measurableSet_Icc).const_mul _

lemma tent_nonneg {b : ℝ} (hb : 0 < b) (x : ℝ) : 0 ≤ tent b x := by
  unfold tent
  exact mul_nonneg (by positivity) (le_max_left _ _)

lemma tent_even (b x : ℝ) : tent b (-x) = tent b x := by
  unfold tent
  rw [abs_neg]

lemma tent_eq_zero_of_le {b x : ℝ} (hb : 0 < b) (hx : 2 * b ≤ |x|) : tent b x = 0 := by
  unfold tent
  have h1 : 1 - |x| / (2 * b) ≤ 0 := by
    have : 1 ≤ |x| / (2 * b) := (one_le_div (by positivity)).2 hx
    linarith
  rw [max_eq_left h1, mul_zero]

lemma tent_continuous (b : ℝ) : Continuous (tent b) := by
  unfold tent
  exact continuous_const.mul (continuous_const.max (continuous_const.sub (continuous_abs.div_const _)))

lemma tent_integrable {b : ℝ} (hb : 0 < b) : Integrable (tent b) := by
  have heq : tent b = Set.indicator (Set.Icc (-(2 * b)) (2 * b)) (tent b) := by
    ext x
    by_cases hx : x ∈ Set.Icc (-(2 * b)) (2 * b)
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      apply tent_eq_zero_of_le hb
      simp only [Set.mem_Icc, not_and, not_le] at hx
      by_cases h1 : -(2 * b) ≤ x
      · exact (hx h1).le.trans (le_abs_self x)
      · push Not at h1
        exact (by linarith : 2 * b ≤ -x).trans (neg_le_abs x)
  rw [heq]
  exact (tent_continuous b).integrableOn_Icc.integrable_indicator measurableSet_Icc

lemma integral_box {b : ℝ} (hb : 0 < b) : (∫ x, box b x) = 1 := by
  unfold box
  rw [integral_const_mul, integral_indicator measurableSet_Icc, setIntegral_const,
    Real.volume_real_Icc_of_le (by linarith), smul_eq_mul, mul_one]
  field_simp
  ring

lemma box_conv_box {b : ℝ} (hb : 0 < b) (t : ℝ) :
    (∫ x, box b x * box b (t - x)) = tent b t := by
  have hpt : ∀ x, box b x * box b (t - x) =
      (1 / (2 * b) ^ 2) * Set.indicator (Set.Icc (max (-b) (t - b)) (min b (t + b)))
        (fun _ => (1 : ℝ)) x := by
    intro x
    unfold box
    have hmem : x ∈ Set.Icc (-b) b ∧ t - x ∈ Set.Icc (-b) b ↔
        x ∈ Set.Icc (max (-b) (t - b)) (min b (t + b)) := by
      simp only [Set.mem_Icc, max_le_iff, le_min_iff]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> constructor <;> linarith
    by_cases h : x ∈ Set.Icc (max (-b) (t - b)) (min b (t + b))
    · have h12 := hmem.mpr h
      rw [Set.indicator_of_mem h12.1, Set.indicator_of_mem h12.2, Set.indicator_of_mem h]
      ring
    · have hn : ¬(x ∈ Set.Icc (-b) b ∧ t - x ∈ Set.Icc (-b) b) := mt hmem.mp h
      rw [Set.indicator_of_notMem h, mul_zero]
      rcases not_and_or.mp hn with hx1 | hx2
      · simp [Set.indicator_of_notMem hx1]
      · simp [Set.indicator_of_notMem hx2]
  simp_rw [hpt, integral_const_mul, integral_indicator measurableSet_Icc, setIntegral_const,
    Real.volume_real_Icc, smul_eq_mul, mul_one]
  have hsub : min b (t + b) - max (-b) (t - b) = 2 * b - |t| := by
    rcases le_total t 0 with ht | ht
    · rw [min_eq_right (by linarith), max_eq_left (by linarith), abs_of_nonpos ht]
      ring
    · rw [min_eq_left (by linarith), max_eq_right (by linarith), abs_of_nonneg ht]
      ring
  rw [hsub, max_comm]
  unfold tent
  have hmax : max 0 (2 * b - |t|) = (2 * b) * max 0 (1 - |t| / (2 * b)) := by
    rcases le_or_gt |t| (2 * b) with ht | ht
    · have h1 : 0 ≤ 2 * b - |t| := by linarith
      have h2 : 0 ≤ 1 - |t| / (2 * b) := by
        have : |t| / (2 * b) ≤ 1 := (div_le_one (by positivity)).2 ht
        linarith
      rw [max_eq_right h1, max_eq_right h2]
      field_simp
    · have h1 : 2 * b - |t| ≤ 0 := by linarith
      have h2 : 1 - |t| / (2 * b) ≤ 0 := by
        have : 1 ≤ |t| / (2 * b) := (one_le_div (by positivity)).2 ht.le
        linarith
      rw [max_eq_left h1, max_eq_left h2, mul_zero]
  rw [hmax]
  field_simp

lemma integral_tent {b : ℝ} (hb : 0 < b) : (∫ t, tent b t) = 1 := by
  have heq : (∫ t, tent b t) = 2 * ∫ t in (0 : ℝ)..(2 * b), (1 / (2 * b)) * (1 - t / (2 * b)) := by
    have hsplit : (∫ t, tent b t) = ∫ t in Set.Icc (-(2 * b)) (2 * b), tent b t := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      apply tent_eq_zero_of_le hb
      simp only [Set.mem_Icc, not_and, not_le] at ht
      by_cases h1 : -(2 * b) ≤ t
      · exact (ht h1).le.trans (le_abs_self t)
      · push Not at h1
        exact (by linarith : 2 * b ≤ -t).trans (neg_le_abs t)
    rw [hsplit, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      ((tent_continuous b).intervalIntegrable _ _) ((tent_continuous b).intervalIntegrable _ _)]
    have hleft : (∫ t in -(2 * b)..0, tent b t) = ∫ t in 0..(2 * b), tent b t := by
      have := intervalIntegral.integral_comp_neg (f := tent b) (a := 0) (b := 2 * b)
      simp only [neg_zero] at this
      rw [← this]
      congr 1
      ext t
      exact tent_even b t
    rw [hleft, ← two_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    rcases ht with ⟨ht0, ht1⟩
    dsimp only [tent]
    rw [abs_of_nonneg ht0, max_eq_right]
    have : t / (2 * b) ≤ 1 := (div_le_one (by positivity)).2 ht1
    linarith
  rw [heq]
  have hcalc : (∫ t in (0 : ℝ)..(2 * b), (1 / (2 * b)) * (1 - t / (2 * b))) = 1 / 2 := by
    let F : ℝ → ℝ := fun t => (1 / (2 * b)) * (t - t ^ 2 / (4 * b))
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) (2 * b),
        HasDerivAt F ((1 / (2 * b)) * (1 - t / (2 * b))) t := by
      intro t _
      have h1 : HasDerivAt (fun x : ℝ => x - x ^ 2 / (4 * b)) (1 - t / (2 * b)) t := by
        have hp : HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t := by
          simpa using (hasDerivAt_pow 2 t)
        have hdiv : HasDerivAt (fun x : ℝ => x ^ 2 / (4 * b)) (t / (2 * b)) t := by
          rw [show t / (2 * b) = 2 * t / (4 * b) by field_simp; ring]
          exact hp.div_const (4 * b)
        exact (hasDerivAt_id t).sub hdiv
      exact h1.const_mul (1 / (2 * b))
    have hint : IntervalIntegrable (fun t => (1 / (2 * b)) * (1 - t / (2 * b)))
        MeasureTheory.volume 0 (2 * b) :=
      (continuous_const.mul (continuous_const.sub (continuous_id.div_const _))).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    dsimp [F]
    field_simp
    ring
  rw [hcalc]
  ring

lemma tent_inner {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t, tent a t * tent b t) = (1 / (2 * b)) * (1 - a / (3 * b)) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hsplit : (∫ t, tent a t * tent b t) = ∫ t in Set.Icc (-(2 * a)) (2 * a), tent a t * tent b t := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    have hzero : tent a t = 0 := by
      apply tent_eq_zero_of_le ha
      simp only [Set.mem_Icc, not_and, not_le] at ht
      by_cases h1 : -(2 * a) ≤ t
      · exact (ht h1).le.trans (le_abs_self t)
      · push Not at h1
        exact (by linarith : 2 * a ≤ -t).trans (neg_le_abs t)
    rw [hzero, zero_mul]
  rw [hsplit, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  have hcont : Continuous (fun t => tent a t * tent b t) := (tent_continuous a).mul (tent_continuous b)
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have hleft : (∫ t in -(2 * a)..0, tent a t * tent b t) = ∫ t in 0..(2 * a), tent a t * tent b t := by
    have := intervalIntegral.integral_comp_neg (f := fun t => tent a t * tent b t) (a := 0) (b := 2 * a)
    simp only [neg_zero] at this
    rw [← this]
    congr 1
    ext t
    rw [tent_even a t, tent_even b t]
  rw [hleft, ← two_mul]
  have hcongr : (∫ t in (0 : ℝ)..(2 * a), tent a t * tent b t) =
      ∫ t in (0 : ℝ)..(2 * a),
        (1 / (4 * a * b)) * (1 - (1 / (2 * a) + 1 / (2 * b)) * t + (1 / (4 * a * b)) * t ^ 2) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    rcases ht with ⟨ht0, ht1⟩
    dsimp only [tent]
    rw [abs_of_nonneg ht0]
    have ha1 : 0 ≤ 1 - t / (2 * a) := by
      have : t / (2 * a) ≤ 1 := (div_le_one (by positivity)).2 ht1
      linarith
    have hb1 : 0 ≤ 1 - t / (2 * b) := by
      have : t / (2 * b) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
      linarith
    rw [max_eq_right ha1, max_eq_right hb1]
    field_simp
    ring
  rw [hcongr, intervalIntegral.integral_const_mul]
  have hpoly : (∫ t in (0 : ℝ)..(2 * a),
      (1 - (1 / (2 * a) + 1 / (2 * b)) * t + (1 / (4 * a * b)) * t ^ 2)) =
      2 * a - (1 / (2 * a) + 1 / (2 * b)) * ((2 * a) ^ 2 / 2) + (1 / (4 * a * b)) * ((2 * a) ^ 3 / 3) := by
    let F : ℝ → ℝ := fun t =>
      t - (1 / (2 * a) + 1 / (2 * b)) * (t ^ 2 / 2) + (1 / (4 * a * b)) * (t ^ 3 / 3)
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) (2 * a),
        HasDerivAt F (1 - (1 / (2 * a) + 1 / (2 * b)) * t + (1 / (4 * a * b)) * t ^ 2) t := by
      intro t _
      have h2 : HasDerivAt (fun x : ℝ => x ^ 2 / 2) t t := by
        have hp : HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t := by
          simpa using (hasDerivAt_pow 2 t)
        have h := hp.div_const 2
        rwa [show 2 * t / 2 = t by ring] at h
      have h3 : HasDerivAt (fun x : ℝ => x ^ 3 / 3) (t ^ 2) t := by
        have hp : HasDerivAt (fun x : ℝ => x ^ 3) (3 * t ^ 2) t := by
          simpa using (hasDerivAt_pow 3 t)
        have h := hp.div_const 3
        rwa [show 3 * t ^ 2 / 3 = t ^ 2 by ring] at h
      exact ((hasDerivAt_id t).sub (h2.const_mul _)).add (h3.const_mul _)
    have hint : IntervalIntegrable
        (fun t => 1 - (1 / (2 * a) + 1 / (2 * b)) * t + (1 / (4 * a * b)) * t ^ 2)
        MeasureTheory.volume 0 (2 * a) :=
      ((continuous_const.sub (continuous_const.mul continuous_id)).add
        (continuous_const.mul (continuous_pow 2))).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    dsimp [F]
    ring
  rw [hpoly]
  field_simp
  ring

lemma box_cos_integral {b c : ℝ} (hb : 0 < b) (hc : c ≠ 0) :
    (∫ x, box b x * Real.cos (c * x)) = Real.sin (c * b) / (c * b) := by
  have hsplit : (∫ x, box b x * Real.cos (c * x)) =
      (1 / (2 * b)) * ∫ x in (-b)..b, Real.cos (c * x) := by
    have hsupp : (∫ x, box b x * Real.cos (c * x)) =
        ∫ x in Set.Icc (-b) b, (1 / (2 * b)) * Real.cos (c * x) := by
      rw [← integral_indicator measurableSet_Icc]
      congr 1
      ext x
      unfold box
      simp only [Set.indicator]
      split_ifs <;> ring
    rw [hsupp, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
      intervalIntegral.integral_const_mul]
  rw [hsplit]
  have hcos : (∫ x in (-b)..b, Real.cos (c * x)) = (Real.sin (c * b) - Real.sin (c * (-b))) / c := by
    have h := intervalIntegral.integral_comp_mul_left (fun t => Real.cos t) hc (a := -b) (b := b)
    rw [smul_eq_mul] at h
    rw [h, integral_cos]
    ring
  rw [hcos, mul_neg, Real.sin_neg]
  field_simp
  ring

lemma box_sin_integral {b c : ℝ} (hb : 0 < b) :
    (∫ x, box b x * Real.sin (c * x)) = 0 := by
  have hsupp : (∫ x, box b x * Real.sin (c * x)) =
      (1 / (2 * b)) * ∫ x in (-b)..b, Real.sin (c * x) := by
    have h1 : (∫ x, box b x * Real.sin (c * x)) =
        ∫ x in Set.Icc (-b) b, (1 / (2 * b)) * Real.sin (c * x) := by
      rw [← integral_indicator measurableSet_Icc]
      congr 1
      ext x
      unfold box
      simp only [Set.indicator]
      split_ifs <;> ring
    rw [h1, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
      intervalIntegral.integral_const_mul]
  rw [hsupp]
  have hodd : (∫ x in (-b)..b, Real.sin (c * x)) = 0 := by
    have h := intervalIntegral.integral_comp_neg (f := fun x => Real.sin (c * x)) (a := -b) (b := b)
    simp only [neg_neg] at h
    have hneg : (∫ x in (-b)..b, Real.sin (c * (-x))) = - ∫ x in (-b)..b, Real.sin (c * x) := by
      rw [← intervalIntegral.integral_neg]
      congr 1
      ext x
      rw [mul_neg, Real.sin_neg]
    rw [hneg] at h
    linarith
  rw [hodd, mul_zero]

lemma cos_period_integral_eq_zero {u : ℝ} (hu : 0 < u) {k : ℤ} (hk : k ≠ 0) :
    (∫ t in (-(u / 2))..(u / 2), Real.cos ((2 * Real.pi * (k : ℝ) / u) * t)) = 0 := by
  have hc : 2 * Real.pi * (k : ℝ) / u ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) (Int.cast_ne_zero.mpr hk)) hu.ne'
  have h := intervalIntegral.integral_comp_mul_left (fun t => Real.cos t) hc (a := -(u / 2)) (b := u / 2)
  rw [smul_eq_mul] at h
  rw [h, integral_cos]
  have h1 : 2 * Real.pi * (k : ℝ) / u * (u / 2) = (k : ℝ) * Real.pi := by field_simp
  have h2 : 2 * Real.pi * (k : ℝ) / u * -(u / 2) = -((k : ℝ) * Real.pi) := by field_simp
  rw [h1, h2, Real.sin_neg, Real.sin_int_mul_pi]
  ring

lemma cos_orthog {u : ℝ} (hu : 0 < u) {j k : ℕ} (hj : 1 ≤ j) (hk : 1 ≤ k) :
    (∫ t in (-(u / 2))..(u / 2),
      Real.cos (2 * Real.pi * (j : ℝ) * t / u) * Real.cos (2 * Real.pi * (k : ℝ) * t / u)) =
      if j = k then u / 2 else 0 := by
  let m : ℤ := (j : ℤ) + (k : ℤ)
  let d : ℤ := (j : ℤ) - (k : ℤ)
  have hm : m ≠ 0 := by omega
  have hprod : ∀ t : ℝ,
      Real.cos (2 * Real.pi * (j : ℝ) * t / u) * Real.cos (2 * Real.pi * (k : ℝ) * t / u) =
      (Real.cos ((2 * Real.pi * (m : ℝ) / u) * t) +
       Real.cos ((2 * Real.pi * (d : ℝ) / u) * t)) / 2 := by
    intro t
    have h := Real.two_mul_cos_mul_cos (2 * Real.pi * (j : ℝ) * t / u) (2 * Real.pi * (k : ℝ) * t / u)
    have hadd : 2 * Real.pi * (j : ℝ) * t / u + 2 * Real.pi * (k : ℝ) * t / u =
        (2 * Real.pi * (m : ℝ) / u) * t := by simp only [m, Int.cast_add, Int.cast_natCast]; ring
    have hsub : 2 * Real.pi * (j : ℝ) * t / u - 2 * Real.pi * (k : ℝ) * t / u =
        (2 * Real.pi * (d : ℝ) / u) * t := by simp only [d, Int.cast_sub, Int.cast_natCast]; ring
    rw [hadd, hsub] at h
    linarith
  simp_rw [hprod, intervalIntegral.integral_div]
  have hint1 : IntervalIntegrable
      (fun t => Real.cos ((2 * Real.pi * (m : ℝ) / u) * t))
      MeasureTheory.volume (-(u / 2)) (u / 2) :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hint2 : IntervalIntegrable
      (fun t => Real.cos ((2 * Real.pi * (d : ℝ) / u) * t))
      MeasureTheory.volume (-(u / 2)) (u / 2) :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hint1 hint2]
  rw [cos_period_integral_eq_zero hu hm, zero_add]
  split_ifs with hjk
  · have hd : d = 0 := by omega
    rw [hd]
    simp only [Int.cast_zero, mul_zero, zero_div, zero_mul, Real.cos_zero,
      intervalIntegral.integral_const, smul_eq_mul, mul_one]
    ring
  · have hd : d ≠ 0 := by omega
    rw [cos_period_integral_eq_zero hu hd, zero_div]

/- ### Block B: Cauchy-Schwarz, Convolution/Correlation Identities, Eq (1) and Eq (2) -/

lemma integral_mul_sq_le {μ : Measure ℝ} {u v : ℝ → ℝ}
    (hu : Integrable (fun x => u x ^ 2) μ)
    (hv : Integrable (fun x => v x ^ 2) μ)
    (huv : Integrable (fun x => u x * v x) μ) :
    (∫ x, u x * v x ∂μ) ^ 2 ≤ (∫ x, u x ^ 2 ∂μ) * (∫ x, v x ^ 2 ∂μ) := by
  set A := ∫ x, u x ^ 2 ∂μ
  set B := ∫ x, u x * v x ∂μ
  set C := ∫ x, v x ^ 2 ∂μ
  have hA0 : 0 ≤ A := integral_nonneg (fun x => sq_nonneg (u x))
  have hquad : ∀ c : ℝ, 0 ≤ c ^ 2 * A - 2 * c * B + C := by
    intro c
    have h0 : 0 ≤ ∫ x, (c * u x - v x) ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
    have h12 : Integrable (fun x => c ^ 2 * u x ^ 2 - 2 * c * (u x * v x)) μ :=
      (hu.const_mul (c ^ 2)).sub (huv.const_mul (2 * c))
    have hpt : (fun x => (c * u x - v x) ^ 2) =
        fun x => (c ^ 2 * u x ^ 2 - 2 * c * (u x * v x)) + v x ^ 2 := by
      ext x; ring
    rw [hpt, integral_add h12 hv, integral_sub (hu.const_mul _) (huv.const_mul _),
      integral_const_mul, integral_const_mul] at h0
    exact h0
  rcases eq_or_lt_of_le hA0 with hAeq | hApos
  · have hB0 : B = 0 := by
      by_contra hBne
      have hq := hquad ((C + 1) / (2 * B))
      rw [← hAeq, mul_zero, zero_sub] at hq
      have hsimp : 2 * ((C + 1) / (2 * B)) * B = C + 1 := by
        field_simp
      linarith
    rw [hB0, ← hAeq]
    norm_num
  · have hq := hquad (B / A)
    have hsimp : (B / A) ^ 2 * A - 2 * (B / A) * B + C = (A * C - B ^ 2) / A := by
      field_simp
      ring
    rw [hsimp] at hq
    have hnonneg : 0 ≤ A * C - B ^ 2 := (div_nonneg_iff.mp hq).elim
      (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hApos))
    linarith

lemma integral_mul_le_sqrt_mul_sqrt {μ : Measure ℝ} {u v : ℝ → ℝ}
    (hu : Integrable (fun x => u x ^ 2) μ)
    (hv : Integrable (fun x => v x ^ 2) μ)
    (huv : Integrable (fun x => u x * v x) μ) :
    ∫ x, u x * v x ∂μ ≤ Real.sqrt ((∫ x, u x ^ 2 ∂μ) * (∫ x, v x ^ 2 ∂μ)) :=
  Real.le_sqrt_of_sq_le (integral_mul_sq_le hu hv huv)

noncomputable def conv (h : ℝ → ℝ) (t : ℝ) : ℝ := ∫ x, h (t - x) * h x
noncomputable def corr (h : ℝ → ℝ) (t : ℝ) : ℝ := ∫ x, h (x + t) * h x

lemma conv_eq_zero_of_lt {h : ℝ → ℝ} (hh_supp : ∀ x, 1 / 4 < |x| → h x = 0)
    {t : ℝ} (ht : 1 / 2 < |t|) : conv h t = 0 := by
  unfold conv
  have hzero : (fun x => h (t - x) * h x) = 0 := by
    ext x
    by_cases hx : 1 / 4 < |x|
    · simp [hh_supp x hx]
    · have htx : 1 / 4 < |t - x| := by
        have htri : |t| ≤ |t - x| + |x| := by
          simpa [sub_add_cancel] using abs_add_le (t - x) x
        linarith
      simp [hh_supp (t - x) htx]
  rw [hzero]
  simp

lemma corr_eq_zero_of_lt {h : ℝ → ℝ} (hh_supp : ∀ x, 1 / 4 < |x| → h x = 0)
    {t : ℝ} (ht : 1 / 2 < |t|) : corr h t = 0 := by
  unfold corr
  have hzero : (fun x => h (x + t) * h x) = 0 := by
    ext x
    by_cases hx : 1 / 4 < |x|
    · simp [hh_supp x hx]
    · have hxt : 1 / 4 < |x + t| := by
        have htri : |t| ≤ |x + t| + |x| := by
          have : t = (x + t) - x := by ring
          calc |t| = |(x + t) - x| := by rw [← this]
            _ ≤ |x + t| + |x| := abs_sub (x + t) x
        linarith
      simp [hh_supp (x + t) hxt]
  rw [hzero]
  simp

lemma conv_nonneg {h : ℝ → ℝ} (hh0 : ∀ x, 0 ≤ h x) (t : ℝ) : 0 ≤ conv h t :=
  integral_nonneg (fun _ => mul_nonneg (hh0 _) (hh0 _))

lemma corr_nonneg {h : ℝ → ℝ} (hh0 : ∀ x, 0 ≤ h x) (t : ℝ) : 0 ≤ corr h t :=
  integral_nonneg (fun _ => mul_nonneg (hh0 _) (hh0 _))

lemma corr_even {h : ℝ → ℝ} (t : ℝ) : corr h (-t) = corr h t := by
  unfold corr
  have h1 := integral_add_right_eq_self (μ := volume) (fun x => h (x + (-t)) * h x) t
  rw [← h1]
  congr 1
  ext x
  ring_nf

lemma conv_integrable_mul {h : ℝ → ℝ} (hh_l2 : MemLp h 2) (t : ℝ) :
    Integrable (fun x => h (t - x) * h x) :=
  (hh_l2.comp_measurePreserving (Measure.measurePreserving_sub_left volume t)).integrable_mul hh_l2

lemma corr_integrable_mul {h : ℝ → ℝ} (hh_l2 : MemLp h 2) (t : ℝ) :
    Integrable (fun x => h (x + t) * h x) :=
  (hh_l2.comp_measurePreserving (measurePreserving_add_right volume t)).integrable_mul hh_l2

lemma conv_le_sq {h : ℝ → ℝ} (hh_l2 : MemLp h 2) (t : ℝ) :
    conv h t ≤ ∫ x, h x ^ 2 := by
  unfold conv
  have h1 : Integrable (fun x => h (t - x) ^ 2) :=
    (hh_l2.comp_measurePreserving (Measure.measurePreserving_sub_left volume t)).integrable_sq
  have h2 : Integrable (fun x => h x ^ 2) := hh_l2.integrable_sq
  have hcs := integral_mul_le_sqrt_mul_sqrt h1 h2 (conv_integrable_mul hh_l2 t)
  have heq : (∫ x, h (t - x) ^ 2) = ∫ x, h x ^ 2 :=
    integral_sub_left_eq_self (fun x => h x ^ 2) volume t
  rw [heq, ← sq, Real.sqrt_sq (integral_nonneg (fun x => sq_nonneg (h x)))] at hcs
  exact hcs

lemma corr_le_sq {h : ℝ → ℝ} (hh_l2 : MemLp h 2) (t : ℝ) :
    corr h t ≤ ∫ x, h x ^ 2 := by
  unfold corr
  have h1 : Integrable (fun x => h (x + t) ^ 2) :=
    (hh_l2.comp_measurePreserving (measurePreserving_add_right volume t)).integrable_sq
  have h2 : Integrable (fun x => h x ^ 2) := hh_l2.integrable_sq
  have hcs := integral_mul_le_sqrt_mul_sqrt h1 h2 (corr_integrable_mul hh_l2 t)
  have heq : (∫ x, h (x + t) ^ 2) = ∫ x, h x ^ 2 :=
    integral_add_right_eq_self (fun x => h x ^ 2) t
  rw [heq, ← sq, Real.sqrt_sq (integral_nonneg (fun x => sq_nonneg (h x)))] at hcs
  exact hcs

lemma conv_measurable {h : ℝ → ℝ} (hh_meas : Measurable h) : Measurable (conv h) := by
  have hm : Measurable (fun p : ℝ × ℝ => h (p.1 - p.2) * h p.2) :=
    (hh_meas.comp (measurable_fst.sub measurable_snd)).mul (hh_meas.comp measurable_snd)
  exact (hm.stronglyMeasurable.integral_prod_right').measurable

lemma corr_measurable {h : ℝ → ℝ} (hh_meas : Measurable h) : Measurable (corr h) := by
  have hm : Measurable (fun p : ℝ × ℝ => h (p.2 + p.1) * h p.2) :=
    (hh_meas.comp (measurable_snd.add measurable_fst)).mul (hh_meas.comp measurable_snd)
  exact (hm.stronglyMeasurable.integral_prod_right').measurable

lemma conv_integrable {h : ℝ → ℝ} (hh_meas : Measurable h) (hh0 : ∀ x, 0 ≤ h x)
    (hh_supp : ∀ x, 1 / 4 < |x| → h x = 0) (hh_l2 : MemLp h 2) :
    Integrable (conv h) := by
  set C := ∫ x, h x ^ 2
  have hdom : Integrable (Set.indicator (Set.Icc (-1 / 2 : ℝ) (1 / 2)) (fun _ => C)) :=
    (integrableOn_const measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc
  refine hdom.mono (conv_measurable hh_meas).aestronglyMeasurable ?_
  filter_upwards with t
  rw [Real.norm_of_nonneg (conv_nonneg hh0 t)]
  by_cases ht : t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)
  · rw [Set.indicator_of_mem ht, Real.norm_of_nonneg (integral_nonneg (fun x => sq_nonneg _))]
    exact conv_le_sq hh_l2 t
  · have hlt : 1 / 2 < |t| := by
      simp only [Set.mem_Icc, not_and, not_le] at ht
      by_cases h1 : -1 / 2 ≤ t
      · exact (ht h1).trans_le (le_abs_self t)
      · push Not at h1
        exact (by linarith : 1 / 2 < -t).trans_le (neg_le_abs t)
    rw [conv_eq_zero_of_lt hh_supp hlt]
    exact norm_nonneg _

lemma corr_integrable {h : ℝ → ℝ} (hh_meas : Measurable h) (hh0 : ∀ x, 0 ≤ h x)
    (hh_supp : ∀ x, 1 / 4 < |x| → h x = 0) (hh_l2 : MemLp h 2) :
    Integrable (corr h) := by
  set C := ∫ x, h x ^ 2
  have hdom : Integrable (Set.indicator (Set.Icc (-1 / 2 : ℝ) (1 / 2)) (fun _ => C)) :=
    (integrableOn_const measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc
  refine hdom.mono (corr_measurable hh_meas).aestronglyMeasurable ?_
  filter_upwards with t
  rw [Real.norm_of_nonneg (corr_nonneg hh0 t)]
  by_cases ht : t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)
  · rw [Set.indicator_of_mem ht, Real.norm_of_nonneg (integral_nonneg (fun x => sq_nonneg _))]
    exact corr_le_sq hh_l2 t
  · have hlt : 1 / 2 < |t| := by
      simp only [Set.mem_Icc, not_and, not_le] at ht
      by_cases h1 : -1 / 2 ≤ t
      · exact (ht h1).trans_le (le_abs_self t)
      · push Not at h1
        exact (by linarith : 1 / 2 < -t).trans_le (neg_le_abs t)
    rw [corr_eq_zero_of_lt hh_supp hlt]
    exact norm_nonneg _

lemma conv_sq_integrable {h : ℝ → ℝ} (hh_meas : Measurable h) (hh0 : ∀ x, 0 ≤ h x)
    (hh_supp : ∀ x, 1 / 4 < |x| → h x = 0) (hh_l2 : MemLp h 2) :
    Integrable (fun t => conv h t ^ 2) := by
  set C := ∫ x, h x ^ 2
  refine ((conv_integrable hh_meas hh0 hh_supp hh_l2).const_mul C).mono
    ((conv_measurable hh_meas).pow_const 2).aestronglyMeasurable ?_
  filter_upwards with t
  have h0 := conv_nonneg hh0 t
  have hC := conv_le_sq hh_l2 t
  rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (mul_nonneg (integral_nonneg (fun _ => sq_nonneg _)) h0)]
  nlinarith

lemma corr_sq_integrable {h : ℝ → ℝ} (hh_meas : Measurable h) (hh0 : ∀ x, 0 ≤ h x)
    (hh_supp : ∀ x, 1 / 4 < |x| → h x = 0) (hh_l2 : MemLp h 2) :
    Integrable (fun t => corr h t ^ 2) := by
  set C := ∫ x, h x ^ 2
  refine ((corr_integrable hh_meas hh0 hh_supp hh_l2).const_mul C).mono
    ((corr_measurable hh_meas).pow_const 2).aestronglyMeasurable ?_
  filter_upwards with t
  have h0 := corr_nonneg hh0 t
  have hC := corr_le_sq hh_l2 t
  rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (mul_nonneg (integral_nonneg (fun _ => sq_nonneg _)) h0)]
  nlinarith

lemma ofReal_conv_eq_lintegral {h : ℝ → ℝ} (hh0 : ∀ x, 0 ≤ h x) (hh_l2 : MemLp h 2) (t : ℝ) :
    ENNReal.ofReal (conv h t) = ∫⁻ x, ENNReal.ofReal (h (t - x)) * ENNReal.ofReal (h x) := by
  unfold conv
  rw [ofReal_integral_eq_lintegral_ofReal (conv_integrable_mul hh_l2 t)
    (ae_of_all _ (fun x => mul_nonneg (hh0 _) (hh0 _)))]
  congr 1
  ext x
  exact ENNReal.ofReal_mul (hh0 _)

lemma ofReal_corr_eq_lintegral {h : ℝ → ℝ} (hh0 : ∀ x, 0 ≤ h x) (hh_l2 : MemLp h 2) (t : ℝ) :
    ENNReal.ofReal (corr h t) = ∫⁻ x, ENNReal.ofReal (h (x + t)) * ENNReal.ofReal (h x) := by
  unfold corr
  rw [ofReal_integral_eq_lintegral_ofReal (corr_integrable_mul hh_l2 t)
    (ae_of_all _ (fun x => mul_nonneg (hh0 _) (hh0 _)))]
  congr 1
  ext x
  exact ENNReal.ofReal_mul (hh0 _)

lemma integral_conv {h : ℝ → ℝ} (hh_meas : Measurable h) (hh0 : ∀ x, 0 ≤ h x)
    (hh_supp : ∀ x, 1 / 4 < |x| → h x = 0) (hh_l2 : MemLp h 2)
    (hh_int : Integrable h) (hh_one : ∫ x, h x = 1) :
    ∫ t, conv h t = 1 := by
  let e : ℝ → ENNReal := fun x => ENNReal.ofReal (h x)
  have he : Measurable e := ENNReal.measurable_ofReal.comp hh_meas
  have he_int : (∫⁻ x, e x) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hh_int (ae_of_all _ hh0), hh_one, ENNReal.ofReal_one]
  have hof : ENNReal.ofReal (∫ t, conv h t) = 1 := by
    rw [ofReal_integral_eq_lintegral_ofReal (conv_integrable hh_meas hh0 hh_supp hh_l2)
      (ae_of_all _ (conv_nonneg hh0))]
    simp_rw [ofReal_conv_eq_lintegral hh0 hh_l2]
    change (∫⁻ t, ∫⁻ x, e (t - x) * e x) = 1
    rw [lintegral_lintegral_swap ((he.comp (measurable_fst.sub measurable_snd)).mul (he.comp measurable_snd)).aemeasurable]
    have hshift : ∀ x, (∫⁻ t, e (t - x) * e x) = (∫⁻ t, e t) * e x := by
      intro x
      have hm : Measurable (fun t => e (t - x)) := he.comp (measurable_sub_const x)
      rw [lintegral_mul_const (e x) hm]
      congr 1
      exact lintegral_sub_right_eq_self e x
    simp_rw [hshift, lintegral_const_mul _ he, he_int, one_mul]
  have h0 : 0 ≤ ∫ t, conv h t := integral_nonneg (conv_nonneg hh0)
  have h1 := congrArg ENNReal.toReal hof
  rw [ENNReal.toReal_ofReal h0, ENNReal.toReal_one] at h1
  exact h1

lemma integral_corr {h : ℝ → ℝ} (hh_meas : Measurable h) (hh0 : ∀ x, 0 ≤ h x)
    (hh_supp : ∀ x, 1 / 4 < |x| → h x = 0) (hh_l2 : MemLp h 2)
    (hh_int : Integrable h) (hh_one : ∫ x, h x = 1) :
    ∫ t, corr h t = 1 := by
  let e : ℝ → ENNReal := fun x => ENNReal.ofReal (h x)
  have he : Measurable e := ENNReal.measurable_ofReal.comp hh_meas
  have he_int : (∫⁻ x, e x) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hh_int (ae_of_all _ hh0), hh_one, ENNReal.ofReal_one]
  have hof : ENNReal.ofReal (∫ t, corr h t) = 1 := by
    rw [ofReal_integral_eq_lintegral_ofReal (corr_integrable hh_meas hh0 hh_supp hh_l2)
      (ae_of_all _ (corr_nonneg hh0))]
    simp_rw [ofReal_corr_eq_lintegral hh0 hh_l2]
    change (∫⁻ t, ∫⁻ x, e (x + t) * e x) = 1
    rw [lintegral_lintegral_swap ((he.comp (measurable_snd.add measurable_fst)).mul (he.comp measurable_snd)).aemeasurable]
    have hshift : ∀ x, (∫⁻ t, e (x + t) * e x) = (∫⁻ t, e t) * e x := by
      intro x
      have hm : Measurable (fun t => e (x + t)) := he.comp (measurable_const_add x)
      rw [lintegral_mul_const (e x) hm]
      congr 1
      exact lintegral_add_left_eq_self e x
    simp_rw [hshift, lintegral_const_mul _ he, he_int, one_mul]
  have h0 : 0 ≤ ∫ t, corr h t := integral_nonneg (corr_nonneg hh0)
  have h1 := congrArg ENNReal.toReal hof
  rw [ENNReal.toReal_ofReal h0, ENNReal.toReal_one] at h1
  exact h1

lemma integral_corr_sq_eq_conv_sq {h : ℝ → ℝ} (hh_meas : Measurable h) (hh0 : ∀ x, 0 ≤ h x)
    (hh_supp : ∀ x, 1 / 4 < |x| → h x = 0) (hh_l2 : MemLp h 2) :
    ∫ t, corr h t ^ 2 = ∫ t, conv h t ^ 2 := by
  let e : ℝ → ENNReal := fun x => ENNReal.ofReal (h x)
  have he : Measurable e := ENNReal.measurable_ofReal.comp hh_meas
  have hconv_of : ENNReal.ofReal (∫ t, conv h t ^ 2) =
      ∫⁻ x, e x * ∫⁻ y, e y * ENNReal.ofReal (corr h (y - x)) := by
    rw [ofReal_integral_eq_lintegral_ofReal (conv_sq_integrable hh_meas hh0 hh_supp hh_l2)
      (ae_of_all _ (fun t => sq_nonneg _))]
    have hsq : ∀ t, ENNReal.ofReal (conv h t ^ 2) =
        ∫⁻ x, ∫⁻ y, (e (t - x) * e (t - y)) * (e x * e y) := by
      intro t
      rw [sq, ENNReal.ofReal_mul (conv_nonneg hh0 t), ofReal_conv_eq_lintegral hh0 hh_l2]
      have hmx : Measurable (fun x => e (t - x) * e x) := (he.comp (measurable_const_sub t)).mul he
      have hmy : Measurable (fun y => e (t - y) * e y) := (he.comp (measurable_const_sub t)).mul he
      change (∫⁻ x, e (t - x) * e x) * (∫⁻ y, e (t - y) * e y) = _
      rw [← lintegral_mul_const (∫⁻ y, e (t - y) * e y) hmx]
      congr 1; ext x
      rw [← lintegral_const_mul (e (t - x) * e x) hmy]
      congr 1; ext y; ring
    simp_rw [hsq]
    have hswap1 : (∫⁻ t, ∫⁻ x, ∫⁻ y, (e (t - x) * e (t - y)) * (e x * e y)) =
        ∫⁻ x, ∫⁻ t, ∫⁻ y, (e (t - x) * e (t - y)) * (e x * e y) := by
      refine lintegral_lintegral_swap ?_
      refine Measurable.lintegral_prod_right ?_ |>.aemeasurable
      exact (((he.comp (measurable_fst.fst.sub measurable_fst.snd)).mul
        (he.comp (measurable_fst.fst.sub measurable_snd))).mul
        ((he.comp measurable_fst.snd).mul (he.comp measurable_snd)))
    rw [hswap1]
    congr 1; ext x
    have hswap2 : (∫⁻ t, ∫⁻ y, (e (t - x) * e (t - y)) * (e x * e y)) =
        ∫⁻ y, ∫⁻ t, (e (t - x) * e (t - y)) * (e x * e y) := by
      refine lintegral_lintegral_swap ?_
      exact (((he.comp (measurable_fst.sub_const x)).mul
        (he.comp (measurable_fst.sub measurable_snd))).mul
        (measurable_const.mul (he.comp measurable_snd))).aemeasurable
    rw [hswap2]
    simp_rw [show ∀ y t, (e (t - x) * e (t - y)) * (e x * e y) =
      e x * (e y * (e (t - x) * e (t - y))) by intro y t; ring]
    have hm_outer : Measurable (fun p : ℝ × ℝ =>
        e p.1 * (e (p.2 - x) * e (p.2 - p.1))) :=
      (he.comp measurable_fst).mul
        ((he.comp (measurable_snd.sub_const x)).mul (he.comp (measurable_snd.sub measurable_fst)))
    have hm_in : Measurable (fun y => ∫⁻ t, e y * (e (t - x) * e (t - y))) :=
      hm_outer.lintegral_prod_right
    have hm_t : ∀ y, Measurable (fun t => e y * (e (t - x) * e (t - y))) := fun y =>
      measurable_const.mul ((he.comp (measurable_sub_const x)).mul (he.comp (measurable_sub_const y)))
    simp_rw [lintegral_const_mul (e x) (hm_t _)]
    rw [lintegral_const_mul (e x) hm_in]
    congr 2; ext y
    have hm1 : Measurable (fun t => e (t - x) * e (t - y)) :=
      (he.comp (measurable_sub_const x)).mul (he.comp (measurable_sub_const y))
    rw [lintegral_const_mul (e y) hm1]
    congr 1
    rw [ofReal_corr_eq_lintegral hh0 hh_l2,
      ← lintegral_add_right_eq_self (fun t => e (t - x) * e (t - y)) y]
    congr 1; ext u
    have h1 : u + y - x = u + (y - x) := by ring
    have h2 : u + y - y = u := by ring
    rw [h1, h2]
  have hcorr_of : ENNReal.ofReal (∫ t, corr h t ^ 2) =
      ∫⁻ x, e x * ∫⁻ y, e y * ENNReal.ofReal (corr h (y - x)) := by
    rw [ofReal_integral_eq_lintegral_ofReal (corr_sq_integrable hh_meas hh0 hh_supp hh_l2)
      (ae_of_all _ (fun t => sq_nonneg _))]
    have hsq : ∀ t, ENNReal.ofReal (corr h t ^ 2) =
        ∫⁻ x, ∫⁻ y, (e (x + t) * e (y + t)) * (e x * e y) := by
      intro t
      rw [sq, ENNReal.ofReal_mul (corr_nonneg hh0 t), ofReal_corr_eq_lintegral hh0 hh_l2]
      have hmx : Measurable (fun x => e (x + t) * e x) := (he.comp (measurable_add_const t)).mul he
      have hmy : Measurable (fun y => e (y + t) * e y) := (he.comp (measurable_add_const t)).mul he
      change (∫⁻ x, e (x + t) * e x) * (∫⁻ y, e (y + t) * e y) = _
      rw [← lintegral_mul_const (∫⁻ y, e (y + t) * e y) hmx]
      congr 1; ext x
      rw [← lintegral_const_mul (e (x + t) * e x) hmy]
      congr 1; ext y; ring
    simp_rw [hsq]
    have hswap1 : (∫⁻ t, ∫⁻ x, ∫⁻ y, (e (x + t) * e (y + t)) * (e x * e y)) =
        ∫⁻ x, ∫⁻ t, ∫⁻ y, (e (x + t) * e (y + t)) * (e x * e y) := by
      refine lintegral_lintegral_swap ?_
      refine Measurable.lintegral_prod_right ?_ |>.aemeasurable
      exact (((he.comp (measurable_fst.snd.add measurable_fst.fst)).mul
        (he.comp (measurable_snd.add measurable_fst.fst))).mul
        ((he.comp measurable_fst.snd).mul (he.comp measurable_snd)))
    rw [hswap1]
    congr 1; ext x
    have hswap2 : (∫⁻ t, ∫⁻ y, (e (x + t) * e (y + t)) * (e x * e y)) =
        ∫⁻ y, ∫⁻ t, (e (x + t) * e (y + t)) * (e x * e y) := by
      refine lintegral_lintegral_swap ?_
      exact (((he.comp (measurable_const.add measurable_fst)).mul
        (he.comp (measurable_snd.add measurable_fst))).mul
        (measurable_const.mul (he.comp measurable_snd))).aemeasurable
    rw [hswap2]
    simp_rw [show ∀ y t, (e (x + t) * e (y + t)) * (e x * e y) =
      e x * (e y * (e (x + t) * e (y + t))) by intro y t; ring]
    have hm_outer : Measurable (fun p : ℝ × ℝ =>
        e p.1 * (e (x + p.2) * e (p.1 + p.2))) :=
      (he.comp measurable_fst).mul
        ((he.comp (measurable_const_add x)).comp measurable_snd |>.mul
          (he.comp (measurable_fst.add measurable_snd)))
    have hm_in : Measurable (fun y => ∫⁻ t, e y * (e (x + t) * e (y + t))) :=
      hm_outer.lintegral_prod_right
    have hm_t : ∀ y, Measurable (fun t => e y * (e (x + t) * e (y + t))) := fun y =>
      measurable_const.mul ((he.comp (measurable_const_add x)).mul (he.comp (measurable_const_add y)))
    simp_rw [lintegral_const_mul (e x) (hm_t _)]
    rw [lintegral_const_mul (e x) hm_in]
    congr 2; ext y
    have hm1 : Measurable (fun t => e (x + t) * e (y + t)) :=
      (he.comp (measurable_const_add x)).mul (he.comp (measurable_const_add y))
    rw [lintegral_const_mul (e y) hm1]
    congr 1
    rw [← corr_even (y - x), neg_sub, ofReal_corr_eq_lintegral hh0 hh_l2,
      ← lintegral_sub_right_eq_self (fun t => e (x + t) * e (y + t)) y]
    congr 1; ext u
    have h1 : x + (u - y) = u + (x - y) := by ring
    have h2 : y + (u - y) = u := by ring
    rw [h1, h2]
  have hofeq : ENNReal.ofReal (∫ t, corr h t ^ 2) = ENNReal.ofReal (∫ t, conv h t ^ 2) :=
    hcorr_of.trans hconv_of.symm
  have h1 := congrArg ENNReal.toReal hofeq
  rwa [ENNReal.toReal_ofReal (integral_nonneg (fun _ => sq_nonneg _)),
    ENNReal.toReal_ofReal (integral_nonneg (fun _ => sq_nonneg _))] at h1

lemma one_le_integral_conv_sq {h : ℝ → ℝ} (hh_meas : Measurable h) (hh0 : ∀ x, 0 ≤ h x)
    (hh_supp : ∀ x, 1 / 4 < |x| → h x = 0) (hh_l2 : MemLp h 2)
    (hh_int : Integrable h) (hh_one : ∫ x, h x = 1) :
    1 ≤ ∫ t, conv h t ^ 2 := by
  let S := Set.Icc (-1 / 2 : ℝ) (1 / 2)
  let ind : ℝ → ℝ := S.indicator (fun _ => (1 : ℝ))
  have hind_int : Integrable ind :=
    (integrableOn_const measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc
  have hind_sq : (fun t => ind t ^ 2) = ind := by
    ext t; by_cases ht : t ∈ S <;> simp [ind, ht]
  have hind_sq_int : Integrable (fun t => ind t ^ 2) := by
    rw [hind_sq]; exact hind_int
  have hconv_ind_eq : (fun t => conv h t * ind t) = conv h := by
    ext t
    by_cases ht : t ∈ S
    · simp [ind, ht]
    · have hlt : 1 / 2 < |t| := by
        simp only [S, Set.mem_Icc, not_and, not_le] at ht
        by_cases h1 : -1 / 2 ≤ t
        · exact (ht h1).trans_le (le_abs_self t)
        · push Not at h1
          exact (by linarith : 1 / 2 < -t).trans_le (neg_le_abs t)
      simp [ind, ht, conv_eq_zero_of_lt hh_supp hlt]
  have hcs := integral_mul_sq_le
    (conv_sq_integrable hh_meas hh0 hh_supp hh_l2)
    hind_sq_int
    (by rw [hconv_ind_eq]; exact conv_integrable hh_meas hh0 hh_supp hh_l2)
  rw [hconv_ind_eq, integral_conv hh_meas hh0 hh_supp hh_l2 hh_int hh_one, one_pow] at hcs
  have hvol : (∫ t, ind t ^ 2) = 1 := by
    rw [hind_sq, integral_indicator measurableSet_Icc, setIntegral_const,
      Real.volume_real_Icc_of_le (by norm_num), smul_eq_mul, mul_one]
    norm_num
  rw [hvol, mul_one] at hcs
  exact hcs

lemma eq1_bound {h K : ℝ → ℝ} (hh0 : ∀ x, 0 ≤ h x)
    (hh_supp : ∀ x, 1 / 4 < |x| → h x = 0)
    (hK0 : ∀ t, 0 ≤ K t) (hK_int : Integrable K) (hK_one : ∫ t, K t = 1)
    {M_sup : ℝ} (hM_bdd : ∀ t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2), conv h t ≤ M_sup)
    (hint : Integrable (fun t => conv h t * K t)) :
    ∫ t, conv h t * K t ≤ M_sup := by
  have hle : ∀ t, conv h t * K t ≤ M_sup * K t := by
    intro t
    by_cases ht : t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)
    · exact mul_le_mul_of_nonneg_right (hM_bdd t ht) (hK0 t)
    · have hlt : 1 / 2 < |t| := by
        simp only [Set.mem_Icc, not_and, not_le] at ht
        by_cases h1 : -1 / 2 ≤ t
        · exact (ht h1).trans_le (le_abs_self t)
        · push Not at h1
          exact (by linarith : 1 / 2 < -t).trans_le (neg_le_abs t)
      rw [conv_eq_zero_of_lt hh_supp hlt, zero_mul]
      have hM0 : 0 ≤ M_sup := (conv_nonneg hh0 0).trans (hM_bdd 0 ⟨by norm_num, by norm_num⟩)
      exact mul_nonneg hM0 (hK0 t)
  calc ∫ t, conv h t * K t
      ≤ ∫ t, M_sup * K t := integral_mono hint (hK_int.const_mul M_sup) hle
    _ = M_sup * ∫ t, K t := integral_const_mul M_sup K
    _ = M_sup := by rw [hK_one, mul_one]

lemma eq2_bound {h K : ℝ → ℝ} (hh_meas : Measurable h) (hh0 : ∀ x, 0 ≤ h x)
    (hh_supp : ∀ x, 1 / 4 < |x| → h x = 0) (hh_l2 : MemLp h 2)
    (hh_int : Integrable h) (hh_one : ∫ x, h x = 1)
    (hK_int : Integrable K) (hK_sq : Integrable (fun t => K t ^ 2))
    (hK_one : ∫ t, K t = 1) (hK_supp : ∀ t, 1 / 2 < |t| → K t = 0)
    (hint : Integrable (fun t => corr h t * K t)) :
    ∫ t, corr h t * K t ≤ 1 + Real.sqrt (((∫ t, conv h t ^ 2) - 1) * ((∫ t, K t ^ 2) - 1)) := by
  let S := Set.Icc (-1 / 2 : ℝ) (1 / 2)
  let u : ℝ → ℝ := S.indicator (fun t => corr h t - 1)
  let v : ℝ → ℝ := S.indicator (fun t => K t - 1)
  let ind : ℝ → ℝ := S.indicator (fun _ => (1 : ℝ))
  have hind_int : Integrable ind :=
    (integrableOn_const measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc
  have hind_val : ∫ t, ind t = 1 := by
    rw [integral_indicator measurableSet_Icc, setIntegral_const,
      Real.volume_real_Icc_of_le (by norm_num), smul_eq_mul, mul_one]
    norm_num
  have hcorr_ind : ∀ t, corr h t * ind t = corr h t := by
    intro t
    by_cases ht : t ∈ S
    · simp [ind, ht]
    · have hlt : 1 / 2 < |t| := by
        simp only [S, Set.mem_Icc, not_and, not_le] at ht
        by_cases h1 : -1 / 2 ≤ t
        · exact (ht h1).trans_le (le_abs_self t)
        · push Not at h1
          exact (by linarith : 1 / 2 < -t).trans_le (neg_le_abs t)
      simp [ind, ht, corr_eq_zero_of_lt hh_supp hlt]
  have hK_ind : ∀ t, K t * ind t = K t := by
    intro t
    by_cases ht : t ∈ S
    · simp [ind, ht]
    · have hlt : 1 / 2 < |t| := by
        simp only [S, Set.mem_Icc, not_and, not_le] at ht
        by_cases h1 : -1 / 2 ≤ t
        · exact (ht h1).trans_le (le_abs_self t)
        · push Not at h1
          exact (by linarith : 1 / 2 < -t).trans_le (neg_le_abs t)
      simp [ind, ht, hK_supp t hlt]
  have hu_eq : u = fun t => corr h t - ind t := by
    ext t
    by_cases ht : t ∈ S
    · simp [u, ind, ht]
    · simp only [u, ind, Set.indicator_of_notMem ht, sub_zero]
      have hlt : 1 / 2 < |t| := by
        simp only [S, Set.mem_Icc, not_and, not_le] at ht
        by_cases h1 : -1 / 2 ≤ t
        · exact (ht h1).trans_le (le_abs_self t)
        · push Not at h1
          exact (by linarith : 1 / 2 < -t).trans_le (neg_le_abs t)
      exact (corr_eq_zero_of_lt hh_supp hlt).symm
  have hv_eq : v = fun t => K t - ind t := by
    ext t
    by_cases ht : t ∈ S
    · simp [v, ind, ht]
    · simp only [v, ind, Set.indicator_of_notMem ht, sub_zero]
      have hlt : 1 / 2 < |t| := by
        simp only [S, Set.mem_Icc, not_and, not_le] at ht
        by_cases h1 : -1 / 2 ≤ t
        · exact (ht h1).trans_le (le_abs_self t)
        · push Not at h1
          exact (by linarith : 1 / 2 < -t).trans_le (neg_le_abs t)
      exact (hK_supp t hlt).symm
  have hu_int : Integrable u := by
    rw [hu_eq]; exact (corr_integrable hh_meas hh0 hh_supp hh_l2).sub hind_int
  have hv_int : Integrable v := by
    rw [hv_eq]; exact hK_int.sub hind_int
  have hind_sq : (fun t => ind t ^ 2) = ind := by
    ext t; by_cases ht : t ∈ S <;> simp [ind, ht]
  have hu_sq_eq : (fun t => u t ^ 2) = fun t => corr h t ^ 2 - 2 * corr h t + ind t := by
    ext t
    rw [hu_eq]
    have hc := hcorr_ind t
    have hi : ind t ^ 2 = ind t := congrFun hind_sq t
    linear_combination -2 * hc + hi
  have hv_sq_eq : (fun t => v t ^ 2) = fun t => K t ^ 2 - 2 * K t + ind t := by
    ext t
    rw [hv_eq]
    have hk := hK_ind t
    have hi : ind t ^ 2 = ind t := congrFun hind_sq t
    linear_combination -2 * hk + hi
  have hu_sq_int : Integrable (fun t => u t ^ 2) := by
    rw [hu_sq_eq]
    exact ((corr_sq_integrable hh_meas hh0 hh_supp hh_l2).sub
      ((corr_integrable hh_meas hh0 hh_supp hh_l2).const_mul 2)).add hind_int
  have hv_sq_int : Integrable (fun t => v t ^ 2) := by
    rw [hv_sq_eq]
    exact (hK_sq.sub (hK_int.const_mul 2)).add hind_int
  have huv_eq : (fun t => u t * v t) = fun t => corr h t * K t - corr h t - K t + ind t := by
    ext t
    rw [hu_eq, hv_eq]
    have hc := hcorr_ind t
    have hk := hK_ind t
    have hi : ind t ^ 2 = ind t := congrFun hind_sq t
    linear_combination -hc - hk + hi
  have huv_int : Integrable (fun t => u t * v t) := by
    rw [huv_eq]
    exact ((hint.sub (corr_integrable hh_meas hh0 hh_supp hh_l2)).sub hK_int).add hind_int
  have hu_sq_val : ∫ t, u t ^ 2 = (∫ t, conv h t ^ 2) - 1 := by
    have hsub : Integrable (fun t => corr h t ^ 2 - 2 * corr h t) :=
      (corr_sq_integrable hh_meas hh0 hh_supp hh_l2).sub
        ((corr_integrable hh_meas hh0 hh_supp hh_l2).const_mul 2)
    rw [hu_sq_eq,
      integral_add (f := fun t => corr h t ^ 2 - 2 * corr h t) (g := ind) hsub hind_int,
      integral_sub (f := fun t => corr h t ^ 2) (g := fun t => 2 * corr h t)
        (corr_sq_integrable hh_meas hh0 hh_supp hh_l2)
        ((corr_integrable hh_meas hh0 hh_supp hh_l2).const_mul 2),
      integral_const_mul, integral_corr hh_meas hh0 hh_supp hh_l2 hh_int hh_one,
      hind_val, integral_corr_sq_eq_conv_sq hh_meas hh0 hh_supp hh_l2]
    ring
  have hv_sq_val : ∫ t, v t ^ 2 = (∫ t, K t ^ 2) - 1 := by
    have hsub : Integrable (fun t => K t ^ 2 - 2 * K t) :=
      hK_sq.sub (hK_int.const_mul 2)
    rw [hv_sq_eq,
      integral_add (f := fun t => K t ^ 2 - 2 * K t) (g := ind) hsub hind_int,
      integral_sub (f := fun t => K t ^ 2) (g := fun t => 2 * K t) hK_sq (hK_int.const_mul 2),
      integral_const_mul, hK_one, hind_val]
    ring
  have huv_val : ∫ t, u t * v t = (∫ t, corr h t * K t) - 1 := by
    have hsub1 : Integrable (fun t => corr h t * K t - corr h t) :=
      hint.sub (corr_integrable hh_meas hh0 hh_supp hh_l2)
    have hsub2 : Integrable (fun t => corr h t * K t - corr h t - K t) :=
      hsub1.sub hK_int
    rw [huv_eq,
      integral_add (f := fun t => corr h t * K t - corr h t - K t) (g := ind) hsub2 hind_int,
      integral_sub (f := fun t => corr h t * K t - corr h t) (g := K) hsub1 hK_int,
      integral_sub (f := fun t => corr h t * K t) (g := corr h) hint
        (corr_integrable hh_meas hh0 hh_supp hh_l2),
      integral_corr hh_meas hh0 hh_supp hh_l2 hh_int hh_one, hK_one, hind_val]
    ring
  have hcs := integral_mul_le_sqrt_mul_sqrt hu_sq_int hv_sq_int huv_int
  rw [huv_val, hu_sq_val, hv_sq_val] at hcs
  linarith

/- ### Block C: Symmetrized Smoothing, Bessel Eq (3), Weighted Cauchy-Schwarz Eq (4), Master Inequality, and Reduction to C1a -/

lemma integrable_comp_neg' {f : ℝ → ℝ} (hf : Integrable f) :
    Integrable (fun x => f (-x)) :=
  (memLp_one_iff_integrable.mp
    ((memLp_one_iff_integrable.mpr hf).comp_measurePreserving (Measure.measurePreserving_neg volume)))

lemma integrable_h_add_neg {h : ℝ → ℝ} (hh_int : Integrable h) :
    Integrable (fun x => h x + h (-x)) :=
  hh_int.add (integrable_comp_neg' hh_int)

lemma integral_h_add_neg {h : ℝ → ℝ} (hh_int : Integrable h) (hh_one : ∫ x, h x = 1) :
    ∫ x, (h x + h (-x)) = 2 := by
  rw [integral_add hh_int (integrable_comp_neg' hh_int), integral_neg_eq_self h volume, hh_one]
  norm_num

noncomputable def symmSmooth (h : ℝ → ℝ) (b t : ℝ) : ℝ :=
  ∫ x, (h x + h (-x)) * box b (t - x)

lemma symmSmooth_nonneg {h : ℝ → ℝ} (hh0 : ∀ x, 0 ≤ h x) {b : ℝ} (hb : 0 < b) (t : ℝ) :
    0 ≤ symmSmooth h b t :=
  integral_nonneg (fun x => mul_nonneg (add_nonneg (hh0 x) (hh0 (-x))) (box_nonneg hb (t - x)))

lemma symmSmooth_measurable {h : ℝ → ℝ} (hh_meas : Measurable h) (b : ℝ) :
    Measurable (symmSmooth h b) := by
  have hm : Measurable (fun p : ℝ × ℝ => (h p.2 + h (-p.2)) * box b (p.1 - p.2)) :=
    ((hh_meas.comp measurable_snd).add (hh_meas.comp measurable_snd.neg)).mul
      ((box_measurable b).comp (measurable_fst.sub measurable_snd))
  exact (hm.stronglyMeasurable.integral_prod_right').measurable

lemma symmSmooth_eq_zero_of_lt {h : ℝ → ℝ} (hh_supp : ∀ x, 1 / 4 < |x| → h x = 0)
    {b : ℝ} (_hb0 : 0 < b) (hb8 : b ≤ 1 / 8) {t : ℝ} (ht : 3 / 8 < |t|) :
    symmSmooth h b t = 0 := by
  unfold symmSmooth
  have hz : (fun x => (h x + h (-x)) * box b (t - x)) = 0 := by
    ext x
    by_cases hx : 1 / 4 < |x|
    · have hnx : 1 / 4 < |-x| := by rwa [abs_neg]
      simp [hh_supp x hx, hh_supp (-x) hnx]
    · push Not at hx
      have htb : b < |t - x| := by
        have htri : |t| ≤ |t - x| + |x| := by
          simpa [sub_add_cancel] using abs_add_le (t - x) x
        linarith
      simp [box_eq_zero_of_lt htb]
  rw [hz]
  simp

lemma box_le_inv {b : ℝ} (hb : 0 < b) (y : ℝ) : box b y ≤ 1 / (2 * b) := by
  unfold box
  by_cases hy : y ∈ Set.Icc (-b) b
  · simp [hy]
  · simp [hy]; positivity

lemma symmSmooth_mul_integrable {h : ℝ → ℝ} (hh0 : ∀ x, 0 ≤ h x)
    (hh_int : Integrable h) {b : ℝ} (hb : 0 < b) (t : ℝ) :
    Integrable (fun x => (h x + h (-x)) * box b (t - x)) := by
  have hdom : Integrable (fun x => (1 / (2 * b)) * (h x + h (-x))) :=
    (integrable_h_add_neg hh_int).const_mul _
  refine hdom.mono
    (((hh_int.aestronglyMeasurable.add
      (integrable_comp_neg' hh_int).aestronglyMeasurable).mul
      ((box_measurable b).comp (measurable_const_sub t)).aestronglyMeasurable)) ?_
  filter_upwards with x
  have h1 : 0 ≤ (h x + h (-x)) * box b (t - x) :=
    mul_nonneg (add_nonneg (hh0 x) (hh0 (-x))) (box_nonneg hb (t - x))
  have h2 : 0 ≤ (1 / (2 * b)) * (h x + h (-x)) :=
    mul_nonneg (by positivity) (add_nonneg (hh0 x) (hh0 (-x)))
  rw [Real.norm_of_nonneg h1, Real.norm_of_nonneg h2]
  calc (h x + h (-x)) * box b (t - x)
      ≤ (h x + h (-x)) * (1 / (2 * b)) :=
        mul_le_mul_of_nonneg_left (box_le_inv hb (t - x)) (add_nonneg (hh0 x) (hh0 (-x)))
    _ = (1 / (2 * b)) * (h x + h (-x)) := mul_comm _ _

lemma symmSmooth_le {h : ℝ → ℝ} (hh0 : ∀ x, 0 ≤ h x) (hh_int : Integrable h)
    (hh_one : ∫ x, h x = 1) {b : ℝ} (hb : 0 < b) (t : ℝ) :
    symmSmooth h b t ≤ 1 / b := by
  unfold symmSmooth
  have hle : ∀ x, (h x + h (-x)) * box b (t - x) ≤ (1 / (2 * b)) * (h x + h (-x)) := by
    intro x
    calc (h x + h (-x)) * box b (t - x)
        ≤ (h x + h (-x)) * (1 / (2 * b)) :=
          mul_le_mul_of_nonneg_left (box_le_inv hb (t - x)) (add_nonneg (hh0 x) (hh0 (-x)))
      _ = (1 / (2 * b)) * (h x + h (-x)) := mul_comm _ _
  calc ∫ x, (h x + h (-x)) * box b (t - x)
      ≤ ∫ x, (1 / (2 * b)) * (h x + h (-x)) :=
        integral_mono (symmSmooth_mul_integrable hh0 hh_int hb t)
          ((integrable_h_add_neg hh_int).const_mul _) hle
    _ = (1 / (2 * b)) * ∫ x, (h x + h (-x)) := integral_const_mul _ _
    _ = (1 / (2 * b)) * 2 := by rw [integral_h_add_neg hh_int hh_one]
    _ = 1 / b := by field_simp

lemma symmSmooth_integrable {h : ℝ → ℝ} (hh_meas : Measurable h) (hh0 : ∀ x, 0 ≤ h x)
    (hh_supp : ∀ x, 1 / 4 < |x| → h x = 0) (hh_int : Integrable h) (hh_one : ∫ x, h x = 1)
    {b : ℝ} (hb0 : 0 < b) (hb8 : b ≤ 1 / 8) :
    Integrable (symmSmooth h b) := by
  have hdom : Integrable (Set.indicator (Set.Icc (-3 / 8 : ℝ) (3 / 8)) (fun _ => 1 / b)) :=
    (integrableOn_const measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc
  refine hdom.mono (symmSmooth_measurable hh_meas b).aestronglyMeasurable ?_
  filter_upwards with t
  rw [Real.norm_of_nonneg (symmSmooth_nonneg hh0 hb0 t)]
  by_cases ht : t ∈ Set.Icc (-3 / 8 : ℝ) (3 / 8)
  · rw [Set.indicator_of_mem ht, Real.norm_of_nonneg (by positivity)]
    exact symmSmooth_le hh0 hh_int hh_one hb0 t
  · have hlt : 3 / 8 < |t| := by
      simp only [Set.mem_Icc, not_and, not_le] at ht
      by_cases h1 : -3 / 8 ≤ t
      · exact (ht h1).trans_le (le_abs_self t)
      · push Not at h1
        exact (by linarith : 3 / 8 < -t).trans_le (neg_le_abs t)
    rw [symmSmooth_eq_zero_of_lt hh_supp hb0 hb8 hlt]
    exact norm_nonneg _

lemma symmSmooth_sq_integrable {h : ℝ → ℝ} (hh_meas : Measurable h) (hh0 : ∀ x, 0 ≤ h x)
    (hh_supp : ∀ x, 1 / 4 < |x| → h x = 0) (hh_int : Integrable h) (hh_one : ∫ x, h x = 1)
    {b : ℝ} (hb0 : 0 < b) (hb8 : b ≤ 1 / 8) :
    Integrable (fun t => symmSmooth h b t ^ 2) := by
  refine ((symmSmooth_integrable hh_meas hh0 hh_supp hh_int hh_one hb0 hb8).const_mul (1 / b)).mono
    ((symmSmooth_measurable hh_meas b).pow_const 2).aestronglyMeasurable ?_
  filter_upwards with t
  have h0 := symmSmooth_nonneg hh0 hb0 t
  have h1 := symmSmooth_le hh0 hh_int hh_one hb0 t
  rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (mul_nonneg (by positivity) h0)]
  nlinarith

lemma symmSmooth_interval_eq_integral {h : ℝ → ℝ} (hh_supp : ∀ x, 1 / 4 < |x| → h x = 0)
    {b : ℝ} (hb0 : 0 < b) (hb8 : b ≤ 1 / 8) (g : ℝ → ℝ) :
    (∫ t in (-3 / 8 : ℝ)..(3 / 8), symmSmooth h b t * g t) =
      ∫ t, symmSmooth h b t * g t := by
  rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  have hlt : 3 / 8 < |t| := by
    simp only [Set.mem_Icc, not_and, not_le] at ht
    by_cases h1 : -3 / 8 ≤ t
    · exact (ht h1).trans_le (le_abs_self t)
    · push Not at h1
      exact (by linarith : 3 / 8 < -t).trans_le (neg_le_abs t)
  rw [symmSmooth_eq_zero_of_lt hh_supp hb0 hb8 hlt, zero_mul]

lemma integral_symmSmooth {h : ℝ → ℝ} (hh_meas : Measurable h) (hh0 : ∀ x, 0 ≤ h x)
    (hh_supp : ∀ x, 1 / 4 < |x| → h x = 0) (hh_int : Integrable h) (hh_one : ∫ x, h x = 1)
    {b : ℝ} (hb0 : 0 < b) (hb8 : b ≤ 1 / 8) :
    ∫ t, symmSmooth h b t = 2 := by
  let eh : ℝ → ENNReal := fun x => ENNReal.ofReal (h x + h (-x))
  let eb : ℝ → ENNReal := fun t => ENNReal.ofReal (box b t)
  have heh : Measurable eh := ENNReal.measurable_ofReal.comp (hh_meas.add (hh_meas.comp measurable_neg))
  have heb : Measurable eb := ENNReal.measurable_ofReal.comp (box_measurable b)
  have heh_int : ∫⁻ x, eh x = 2 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_h_add_neg hh_int)
      (ae_of_all _ (fun x => add_nonneg (hh0 x) (hh0 (-x)))),
      integral_h_add_neg hh_int hh_one]
    norm_num
  have heb_int : ∫⁻ t, eb t = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (box_integrable b) (ae_of_all _ (box_nonneg hb0)),
      integral_box hb0, ENNReal.ofReal_one]
  have hof : ENNReal.ofReal (∫ t, symmSmooth h b t) = 2 := by
    rw [ofReal_integral_eq_lintegral_ofReal
      (symmSmooth_integrable hh_meas hh0 hh_supp hh_int hh_one hb0 hb8)
      (ae_of_all _ (symmSmooth_nonneg hh0 hb0))]
    have hpt : ∀ t, ENNReal.ofReal (symmSmooth h b t) = ∫⁻ x, eh x * eb (t - x) := by
      intro t
      unfold symmSmooth
      rw [ofReal_integral_eq_lintegral_ofReal (symmSmooth_mul_integrable hh0 hh_int hb0 t)
        (ae_of_all _ (fun x => mul_nonneg (add_nonneg (hh0 x) (hh0 (-x))) (box_nonneg hb0 (t - x))))]
      congr 1; ext x
      exact ENNReal.ofReal_mul (add_nonneg (hh0 x) (hh0 (-x)))
    simp_rw [hpt]
    rw [lintegral_lintegral_swap
      ((heh.comp measurable_snd).mul (heb.comp (measurable_fst.sub measurable_snd))).aemeasurable]
    have hshift : ∀ x, (∫⁻ t, eh x * eb (t - x)) = eh x * 1 := by
      intro x
      have hm : Measurable (fun t => eb (t - x)) := heb.comp (measurable_sub_const x)
      rw [lintegral_const_mul (eh x) hm, lintegral_sub_right_eq_self eb x, heb_int]
    simp_rw [hshift, mul_one, heh_int]
  have h1 := congrArg ENNReal.toReal hof
  rwa [ENNReal.toReal_ofReal (integral_nonneg (symmSmooth_nonneg hh0 hb0)),
    show ENNReal.toReal 2 = (2 : ℝ) by norm_num] at h1

lemma conv_tent_integrable {h : ℝ → ℝ} (hh_meas : Measurable h) (hh0 : ∀ x, 0 ≤ h x)
    (hh_supp : ∀ x, 1 / 4 < |x| → h x = 0) (hh_l2 : MemLp h 2) {b : ℝ} (hb0 : 0 < b) :
    Integrable (fun s => conv h s * tent b s) := by
  refine ((conv_integrable hh_meas hh0 hh_supp hh_l2).const_mul (1 / (2 * b))).mono
    ((conv_measurable hh_meas).mul (tent_continuous b).measurable).aestronglyMeasurable ?_
  filter_upwards with s
  have hc0 := conv_nonneg hh0 s
  have ht0 := tent_nonneg hb0 s
  have hle : tent b s ≤ 1 / (2 * b) := by
    unfold tent
    have : max 0 (1 - |s| / (2 * b)) ≤ 1 := max_le zero_le_one (by
      have : 0 ≤ |s| / (2 * b) := by positivity
      linarith)
    calc (1 / (2 * b)) * max 0 (1 - |s| / (2 * b))
        ≤ (1 / (2 * b)) * 1 := mul_le_mul_of_nonneg_left this (by positivity)
      _ = 1 / (2 * b) := mul_one _
  rw [Real.norm_of_nonneg (mul_nonneg hc0 ht0),
    Real.norm_of_nonneg (mul_nonneg (by positivity) hc0)]
  nlinarith

lemma corr_tent_integrable {h : ℝ → ℝ} (hh_meas : Measurable h) (hh0 : ∀ x, 0 ≤ h x)
    (hh_supp : ∀ x, 1 / 4 < |x| → h x = 0) (hh_l2 : MemLp h 2) {b : ℝ} (hb0 : 0 < b) :
    Integrable (fun s => corr h s * tent b s) := by
  refine ((corr_integrable hh_meas hh0 hh_supp hh_l2).const_mul (1 / (2 * b))).mono
    ((corr_measurable hh_meas).mul (tent_continuous b).measurable).aestronglyMeasurable ?_
  filter_upwards with s
  have hc0 := corr_nonneg hh0 s
  have ht0 := tent_nonneg hb0 s
  have hle : tent b s ≤ 1 / (2 * b) := by
    unfold tent
    have : max 0 (1 - |s| / (2 * b)) ≤ 1 := max_le zero_le_one (by
      have : 0 ≤ |s| / (2 * b) := by positivity
      linarith)
    calc (1 / (2 * b)) * max 0 (1 - |s| / (2 * b))
        ≤ (1 / (2 * b)) * 1 := mul_le_mul_of_nonneg_left this (by positivity)
      _ = 1 / (2 * b) := mul_one _
  rw [Real.norm_of_nonneg (mul_nonneg hc0 ht0),
    Real.norm_of_nonneg (mul_nonneg (by positivity) hc0)]
  nlinarith

lemma lintegral_box_conv {b : ℝ} (hb0 : 0 < b) (x y : ℝ) :
    (∫⁻ t, ENNReal.ofReal (box b (t - x)) * ENNReal.ofReal (box b (t - y))) =
      ENNReal.ofReal (tent b (x - y)) := by
  have hshift := lintegral_add_right_eq_self (μ := volume)
    (fun t => ENNReal.ofReal (box b (t - x)) * ENNReal.ofReal (box b (t - y))) y
  rw [← hshift]
  have hpt : (fun u => ENNReal.ofReal (box b (u + y - x)) * ENNReal.ofReal (box b (u + y - y))) =
      fun u => ENNReal.ofReal (box b u * box b ((x - y) - u)) := by
    ext u
    rw [ENNReal.ofReal_mul (box_nonneg hb0 u)]
    have h1 : u + y - x = -((x - y) - u) := by ring
    have h2 : u + y - y = u := by ring
    rw [h1, h2, box_even, mul_comm]
  rw [hpt, ← ofReal_integral_eq_lintegral_ofReal ?_ (ae_of_all _ (fun u => mul_nonneg (box_nonneg hb0 _) (box_nonneg hb0 _))),
    box_conv_box hb0 (x - y)]
  exact (box_integrable b).mul_bdd
    ((box_measurable b).comp (measurable_const_sub (x - y))).aestronglyMeasurable
    (ae_of_all _ (fun u => by
      rw [Real.norm_of_nonneg (box_nonneg hb0 _)]
      exact box_le_inv hb0 _))

lemma integral_symmSmooth_sq {h : ℝ → ℝ} (hh_meas : Measurable h) (hh0 : ∀ x, 0 ≤ h x)
    (hh_supp : ∀ x, 1 / 4 < |x| → h x = 0) (hh_l2 : MemLp h 2) (hh_int : Integrable h)
    (hh_one : ∫ x, h x = 1) {b : ℝ} (hb0 : 0 < b) (hb8 : b ≤ 1 / 8) :
    ∫ t, symmSmooth h b t ^ 2 = 2 * ∫ s, (conv h s + corr h s) * tent b s := by
  let e : ℝ → ENNReal := fun x => ENNReal.ofReal (h x)
  let eh : ℝ → ENNReal := fun x => ENNReal.ofReal (h x + h (-x))
  let eb : ℝ → ENNReal := fun t => ENNReal.ofReal (box b t)
  let et : ℝ → ENNReal := fun s => ENNReal.ofReal (tent b s)
  have he : Measurable e := ENNReal.measurable_ofReal.comp hh_meas
  have heh : Measurable eh := ENNReal.measurable_ofReal.comp (hh_meas.add (hh_meas.comp measurable_neg))
  have heb : Measurable eb := ENNReal.measurable_ofReal.comp (box_measurable b)
  have het : Measurable et := ENNReal.measurable_ofReal.comp (tent_continuous b).measurable
  have heh_eq : ∀ x, eh x = e x + e (-x) := fun x => ENNReal.ofReal_add (hh0 x) (hh0 (-x))
  have hof_lhs : ENNReal.ofReal (∫ t, symmSmooth h b t ^ 2) =
      ∫⁻ x, ∫⁻ y, eh x * eh y * et (x - y) := by
    rw [ofReal_integral_eq_lintegral_ofReal
      (symmSmooth_sq_integrable hh_meas hh0 hh_supp hh_int hh_one hb0 hb8)
      (ae_of_all _ (fun _ => sq_nonneg _))]
    have hsq : ∀ t, ENNReal.ofReal (symmSmooth h b t ^ 2) =
        ∫⁻ x, ∫⁻ y, (eb (t - x) * eb (t - y)) * (eh x * eh y) := by
      intro t
      rw [sq, ENNReal.ofReal_mul (symmSmooth_nonneg hh0 hb0 t)]
      have h1 : ENNReal.ofReal (symmSmooth h b t) = ∫⁻ x, eh x * eb (t - x) := by
        unfold symmSmooth
        rw [ofReal_integral_eq_lintegral_ofReal (symmSmooth_mul_integrable hh0 hh_int hb0 t)
          (ae_of_all _ (fun x => mul_nonneg (add_nonneg (hh0 x) (hh0 (-x))) (box_nonneg hb0 (t - x))))]
        congr 1; ext x
        exact ENNReal.ofReal_mul (add_nonneg (hh0 x) (hh0 (-x)))
      rw [h1]
      have hmx : Measurable (fun x => eh x * eb (t - x)) := heh.mul (heb.comp (measurable_const_sub t))
      have hmy : Measurable (fun y => eh y * eb (t - y)) := heh.mul (heb.comp (measurable_const_sub t))
      rw [← lintegral_mul_const (∫⁻ y, eh y * eb (t - y)) hmx]
      congr 1; ext x
      rw [← lintegral_const_mul (eh x * eb (t - x)) hmy]
      congr 1; ext y; ring
    simp_rw [hsq]
    have hswap1 : (∫⁻ t, ∫⁻ x, ∫⁻ y, (eb (t - x) * eb (t - y)) * (eh x * eh y)) =
        ∫⁻ x, ∫⁻ t, ∫⁻ y, (eb (t - x) * eb (t - y)) * (eh x * eh y) := by
      refine lintegral_lintegral_swap ?_
      refine Measurable.lintegral_prod_right ?_ |>.aemeasurable
      exact (((heb.comp (measurable_fst.fst.sub measurable_fst.snd)).mul
        (heb.comp (measurable_fst.fst.sub measurable_snd))).mul
        ((heh.comp measurable_fst.snd).mul (heh.comp measurable_snd)))
    rw [hswap1]
    congr 1; ext x
    have hswap2 : (∫⁻ t, ∫⁻ y, (eb (t - x) * eb (t - y)) * (eh x * eh y)) =
        ∫⁻ y, ∫⁻ t, (eb (t - x) * eb (t - y)) * (eh x * eh y) := by
      refine lintegral_lintegral_swap ?_
      exact (((heb.comp (measurable_fst.sub_const x)).mul
        (heb.comp (measurable_fst.sub measurable_snd))).mul
        (measurable_const.mul (heh.comp measurable_snd))).aemeasurable
    rw [hswap2]
    congr 1; ext y
    have hm1 : Measurable (fun t => eb (t - x) * eb (t - y)) :=
      (heb.comp (measurable_sub_const x)).mul (heb.comp (measurable_sub_const y))
    rw [lintegral_mul_const (eh x * eh y) hm1, lintegral_box_conv hb0 x y]
    ring
  have hT_even : ∀ s, et (-s) = et s := fun s => by simp [et, tent_even]
  have hm_prod : ∀ {f1 f2 : ℝ → ENNReal} (hf1 : Measurable f1) (hf2 : Measurable f2)
      {g : ℝ × ℝ → ENNReal} (hg : Measurable g),
      Measurable (fun p : ℝ × ℝ => f1 p.1 * f2 p.2 * g p) := by
    intro f1 f2 hf1 hf2 g hg
    exact ((hf1.comp measurable_fst).mul (hf2.comp measurable_snd)).mul hg
  have hT_sub_meas : Measurable (fun p : ℝ × ℝ => et (p.1 - p.2)) :=
    het.comp (measurable_fst.sub measurable_snd)
  have hterm_corr : (∫⁻ x, ∫⁻ y, e x * e y * et (x - y)) =
      ∫⁻ s, ENNReal.ofReal (corr h s * tent b s) := by
    rw [lintegral_lintegral_swap (hm_prod he he hT_sub_meas).aemeasurable]
    have hshift : ∀ y, (∫⁻ x, e x * e y * et (x - y)) =
        ∫⁻ s, e (s + y) * e y * et s := by
      intro y
      rw [← lintegral_add_right_eq_self (fun x => e x * e y * et (x - y)) y]
      congr 1; ext s
      have hsub : s + y - y = s := by ring
      rw [hsub]
    simp_rw [hshift]
    rw [lintegral_lintegral_swap
      ((((he.comp (measurable_snd.add measurable_fst)).mul (he.comp measurable_fst)).mul
        (het.comp measurable_snd))).aemeasurable]
    congr 1; ext s
    have hm_y : Measurable (fun y => e (y + s) * e y) := (he.comp (measurable_add_const s)).mul he
    have hpt : (fun y => e (s + y) * e y * et s) = fun y => (e (y + s) * e y) * et s := by
      ext y; rw [add_comm s y]
    rw [hpt, lintegral_mul_const (et s) hm_y, ← ofReal_corr_eq_lintegral hh0 hh_l2 s,
      ← ENNReal.ofReal_mul (corr_nonneg hh0 s)]
  have hterm_corr_neg : (∫⁻ x, ∫⁻ y, e (-x) * e (-y) * et (x - y)) =
      ∫⁻ s, ENNReal.ofReal (corr h s * tent b s) := by
    rw [← lintegral_neg_eq_self (fun x => ∫⁻ y, e (-x) * e (-y) * et (x - y))]
    have hpt : (fun x => ∫⁻ y, e (- -x) * e (-y) * et (-x - y)) =
        fun x => ∫⁻ y, e x * e y * et (x - y) := by
      ext x
      rw [← lintegral_neg_eq_self (fun y => e (- -x) * e (-y) * et (-x - y))]
      congr 1; ext y
      have heq : -x - -y = -(x - y) := by ring
      rw [neg_neg, neg_neg, heq, hT_even]
    rw [hpt, hterm_corr]
  have hterm_conv : (∫⁻ x, ∫⁻ y, e x * e (-y) * et (x - y)) =
      ∫⁻ s, ENNReal.ofReal (conv h s * tent b s) := by
    have hneg : (∫⁻ x, ∫⁻ y, e x * e (-y) * et (x - y)) =
        ∫⁻ x, ∫⁻ y, e x * e y * et (x + y) := by
      congr 1; ext x
      rw [← lintegral_neg_eq_self (fun y => e x * e (-y) * et (x - y))]
      congr 1; ext y
      rw [neg_neg, sub_neg_eq_add]
    rw [hneg]
    have hT_add_meas : Measurable (fun p : ℝ × ℝ => et (p.1 + p.2)) :=
      het.comp (measurable_fst.add measurable_snd)
    rw [lintegral_lintegral_swap (hm_prod he he hT_add_meas).aemeasurable]
    have hshift : ∀ y, (∫⁻ x, e x * e y * et (x + y)) =
        ∫⁻ s, e (s - y) * e y * et s := by
      intro y
      rw [← lintegral_sub_right_eq_self (fun x => e x * e y * et (x + y)) y]
      congr 1; ext s
      have hsub : s - y + y = s := by ring
      rw [hsub]
    simp_rw [hshift]
    rw [lintegral_lintegral_swap
      ((((he.comp (measurable_snd.sub measurable_fst)).mul (he.comp measurable_fst)).mul
        (het.comp measurable_snd))).aemeasurable]
    congr 1; ext s
    have hm_y : Measurable (fun y => e (s - y) * e y) := (he.comp (measurable_const_sub s)).mul he
    rw [lintegral_mul_const (et s) hm_y, ← ofReal_conv_eq_lintegral hh0 hh_l2 s,
      ← ENNReal.ofReal_mul (conv_nonneg hh0 s)]
  have hterm_conv_neg : (∫⁻ x, ∫⁻ y, e (-x) * e y * et (x - y)) =
      ∫⁻ s, ENNReal.ofReal (conv h s * tent b s) := by
    rw [← lintegral_neg_eq_self (fun x => ∫⁻ y, e (-x) * e y * et (x - y))]
    have hpt : (fun x => ∫⁻ y, e (- -x) * e y * et (-x - y)) =
        fun x => ∫⁻ y, e x * e (-y) * et (x - y) := by
      ext x
      rw [← lintegral_neg_eq_self (fun y => e (- -x) * e y * et (-x - y))]
      congr 1; ext y
      have heq : -x - -y = -(x - y) := by ring
      rw [neg_neg, heq, hT_even]
    rw [hpt, hterm_conv]
  have hm1 : Measurable (fun x => ∫⁻ y, e x * e y * et (x - y)) :=
    (hm_prod he he hT_sub_meas).lintegral_prod_right
  have hm2 : Measurable (fun x => ∫⁻ y, e (-x) * e (-y) * et (x - y)) :=
    (hm_prod (he.comp measurable_neg) (he.comp measurable_neg) hT_sub_meas).lintegral_prod_right
  have hm3 : Measurable (fun x => ∫⁻ y, e x * e (-y) * et (x - y)) :=
    (hm_prod he (he.comp measurable_neg) hT_sub_meas).lintegral_prod_right
  have hm4 : Measurable (fun x => ∫⁻ y, e (-x) * e y * et (x - y)) :=
    (hm_prod (he.comp measurable_neg) he hT_sub_meas).lintegral_prod_right
  have hsplit : (∫⁻ x, ∫⁻ y, eh x * eh y * et (x - y)) =
      (∫⁻ x, ∫⁻ y, e x * e y * et (x - y)) +
      (∫⁻ x, ∫⁻ y, e (-x) * e (-y) * et (x - y)) +
      (∫⁻ x, ∫⁻ y, e x * e (-y) * et (x - y)) +
      (∫⁻ x, ∫⁻ y, e (-x) * e y * et (x - y)) := by
    have hin : ∀ x, (∫⁻ y, eh x * eh y * et (x - y)) =
        (∫⁻ y, e x * e y * et (x - y)) +
        (∫⁻ y, e (-x) * e (-y) * et (x - y)) +
        (∫⁻ y, e x * e (-y) * et (x - y)) +
        (∫⁻ y, e (-x) * e y * et (x - y)) := by
      intro x
      have hexp : ∀ y, eh x * eh y * et (x - y) =
          e x * e y * et (x - y) + e (-x) * e (-y) * et (x - y) +
          e x * e (-y) * et (x - y) + e (-x) * e y * et (x - y) := by
        intro y; rw [heh_eq x, heh_eq y]; ring
      simp_rw [hexp]
      have ma : Measurable (fun y => e x * e y * et (x - y)) :=
        (measurable_const.mul he).mul (het.comp (measurable_const_sub x))
      have mb : Measurable (fun y => e (-x) * e (-y) * et (x - y)) :=
        (measurable_const.mul (he.comp measurable_neg)).mul (het.comp (measurable_const_sub x))
      have mc : Measurable (fun y => e x * e (-y) * et (x - y)) :=
        (measurable_const.mul (he.comp measurable_neg)).mul (het.comp (measurable_const_sub x))
      have md : Measurable (fun y => e (-x) * e y * et (x - y)) :=
        (measurable_const.mul he).mul (het.comp (measurable_const_sub x))
      have mab : Measurable (fun y => e x * e y * et (x - y) + e (-x) * e (-y) * et (x - y)) := ma.add mb
      have mabc : Measurable (fun y => (e x * e y * et (x - y) + e (-x) * e (-y) * et (x - y)) +
          e x * e (-y) * et (x - y)) := mab.add mc
      rw [lintegral_add_left mabc _, lintegral_add_left mab _, lintegral_add_left ma _]
    simp_rw [hin]
    have hm12 : Measurable (fun x => (∫⁻ y, e x * e y * et (x - y)) +
        ∫⁻ y, e (-x) * e (-y) * et (x - y)) := hm1.add hm2
    have hm123 : Measurable (fun x => ((∫⁻ y, e x * e y * et (x - y)) +
        ∫⁻ y, e (-x) * e (-y) * et (x - y)) + ∫⁻ y, e x * e (-y) * et (x - y)) := hm12.add hm3
    rw [lintegral_add_left hm123 _, lintegral_add_left hm12 _, lintegral_add_left hm1 _]
  have hof_rhs : (∫⁻ x, ∫⁻ y, eh x * eh y * et (x - y)) =
      ENNReal.ofReal (2 * ∫ s, (conv h s + corr h s) * tent b s) := by
    rw [hsplit, hterm_corr, hterm_corr_neg, hterm_conv, hterm_conv_neg]
    have hadd_int : Integrable (fun s => (conv h s + corr h s) * tent b s) := by
      have : (fun s => (conv h s + corr h s) * tent b s) =
          fun s => conv h s * tent b s + corr h s * tent b s := by
        ext s; ring
      rw [this]
      exact (conv_tent_integrable hh_meas hh0 hh_supp hh_l2 hb0).add
        (corr_tent_integrable hh_meas hh0 hh_supp hh_l2 hb0)
    rw [ENNReal.ofReal_mul (by norm_num),
      ofReal_integral_eq_lintegral_ofReal hadd_int (ae_of_all _ (fun s =>
        mul_nonneg (add_nonneg (conv_nonneg hh0 s) (corr_nonneg hh0 s)) (tent_nonneg hb0 s)))]
    have hpt : ∀ s, ENNReal.ofReal ((conv h s + corr h s) * tent b s) =
        ENNReal.ofReal (conv h s * tent b s) + ENNReal.ofReal (corr h s * tent b s) := by
      intro s
      rw [add_mul, ENNReal.ofReal_add
        (mul_nonneg (conv_nonneg hh0 s) (tent_nonneg hb0 s))
        (mul_nonneg (corr_nonneg hh0 s) (tent_nonneg hb0 s))]
    simp_rw [hpt]
    have hm_c : Measurable (fun s => ENNReal.ofReal (conv h s * tent b s)) :=
      ENNReal.measurable_ofReal.comp ((conv_measurable hh_meas).mul (tent_continuous b).measurable)
    rw [lintegral_add_left hm_c _, show ENNReal.ofReal 2 = (2 : ENNReal) by norm_num]
    ring
  have hofeq : ENNReal.ofReal (∫ t, symmSmooth h b t ^ 2) =
      ENNReal.ofReal (2 * ∫ s, (conv h s + corr h s) * tent b s) :=
    hof_lhs.trans hof_rhs
  have h1 := congrArg ENNReal.toReal hofeq
  rwa [ENNReal.toReal_ofReal (integral_nonneg (fun _ => sq_nonneg _)),
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (integral_nonneg (fun s =>
      mul_nonneg (add_nonneg (conv_nonneg hh0 s) (corr_nonneg hh0 s)) (tent_nonneg hb0 s))))] at h1

lemma symmSmooth_prod_integrable {h : ℝ → ℝ} (hh_meas : Measurable h) (hh0 : ∀ x, 0 ≤ h x)
    (hh_int : Integrable h) {b : ℝ} (hb0 : 0 < b) :
    Integrable (Function.uncurry fun t x => (h x + h (-x)) * box b (t - x))
      (volume.prod volume) := by
  have hm : Measurable (Function.uncurry fun t x => (h x + h (-x)) * box b (t - x)) :=
    ((hh_meas.comp measurable_snd).add (hh_meas.comp measurable_snd.neg)).mul
      ((box_measurable b).comp (measurable_fst.sub measurable_snd))
  have hm_swap : Measurable (Function.uncurry fun x t => (h x + h (-x)) * box b (t - x)) :=
    ((hh_meas.comp measurable_fst).add (hh_meas.comp measurable_fst.neg)).mul
      ((box_measurable b).comp (measurable_snd.sub measurable_fst))
  have hswap_int : Integrable (Function.uncurry fun x t => (h x + h (-x)) * box b (t - x))
      (volume.prod volume) := by
    rw [integrable_prod_iff hm_swap.aestronglyMeasurable]
    refine ⟨ae_of_all _ (fun x => ?_), ?_⟩
    · exact (((memLp_one_iff_integrable.mp ((memLp_one_iff_integrable.mpr (box_integrable b)).comp_measurePreserving
        (measurePreserving_sub_right volume x)))).const_mul (h x + h (-x)))
    · have hnorm : (fun x => ∫ t, ‖(h x + h (-x)) * box b (t - x)‖) = fun x => h x + h (-x) := by
        ext x
        simp_rw [show ∀ t, ‖(h x + h (-x)) * box b (t - x)‖ = (h x + h (-x)) * box b (t - x) from
          fun t => Real.norm_of_nonneg (mul_nonneg (add_nonneg (hh0 x) (hh0 (-x))) (box_nonneg hb0 (t - x)))]
        rw [integral_const_mul, integral_sub_right_eq_self (box b) x, integral_box hb0, mul_one]
      simp only [Function.uncurry_apply_pair]
      rw [hnorm]
      exact integrable_h_add_neg hh_int
  exact (memLp_one_iff_integrable.mp
    ((memLp_one_iff_integrable.mpr hswap_int).comp_measurePreserving Measure.measurePreserving_swap))

lemma symmSmooth_cos_integral {h : ℝ → ℝ} (hh_meas : Measurable h) (hh0 : ∀ x, 0 ≤ h x)
    (hh_supp : ∀ x, 1 / 4 < |x| → h x = 0) (hh_int : Integrable h)
    {b : ℝ} (hb0 : 0 < b) (hb8 : b ≤ 1 / 8) {ω : ℝ} (hω : ω ≠ 0) :
    (∫ t in (-3 / 8 : ℝ)..(3 / 8), symmSmooth h b t * Real.cos (ω * t)) =
      2 * (Real.sin (ω * b) / (ω * b)) * (∫ x, h x * Real.cos (ω * x)) := by
  rw [symmSmooth_interval_eq_integral hh_supp hb0 hb8]
  have hprod : Integrable (Function.uncurry fun t x =>
      (h x + h (-x)) * box b (t - x) * Real.cos (ω * t)) (volume.prod volume) := by
    have hm : Measurable (Function.uncurry fun t x =>
        (h x + h (-x)) * box b (t - x) * Real.cos (ω * t)) :=
      (((hh_meas.comp measurable_snd).add (hh_meas.comp measurable_snd.neg)).mul
        ((box_measurable b).comp (measurable_fst.sub measurable_snd))).mul
        (Real.continuous_cos.measurable.comp (measurable_const.mul measurable_fst))
    refine (symmSmooth_prod_integrable hh_meas hh0 hh_int hb0).mono hm.aestronglyMeasurable ?_
    filter_upwards with ⟨t, x⟩
    simp only [Function.uncurry_apply_pair, norm_mul, Real.norm_eq_abs]
    rw [abs_of_nonneg (add_nonneg (hh0 x) (hh0 (-x))), abs_of_nonneg (box_nonneg hb0 (t - x))]
    exact mul_le_of_le_one_right (mul_nonneg (add_nonneg (hh0 x) (hh0 (-x))) (box_nonneg hb0 (t - x)))
      (Real.abs_cos_le_one _)
  have h1 : (∫ t, symmSmooth h b t * Real.cos (ω * t)) =
      ∫ t, ∫ x, (h x + h (-x)) * box b (t - x) * Real.cos (ω * t) := by
    congr 1; ext t
    unfold symmSmooth
    rw [← integral_mul_const]
  rw [h1, integral_integral_swap hprod]
  have hinner : ∀ x, (∫ t, (h x + h (-x)) * box b (t - x) * Real.cos (ω * t)) =
      (h x + h (-x)) * ((Real.sin (ω * b) / (ω * b)) * Real.cos (ω * x)) := by
    intro x
    simp_rw [show ∀ t, (h x + h (-x)) * box b (t - x) * Real.cos (ω * t) =
      (h x + h (-x)) * (box b (t - x) * Real.cos (ω * t)) by intro t; ring]
    rw [integral_const_mul]
    have hshift : (∫ t, box b (t - x) * Real.cos (ω * t)) =
        ∫ s, box b s * Real.cos (ω * (x + s)) := by
      rw [← integral_add_right_eq_self (μ := volume) (fun t => box b (t - x) * Real.cos (ω * t)) x]
      congr 1; ext s
      have h1 : s + x - x = s := by ring
      have h2 : ω * (s + x) = ω * (x + s) := by ring
      rw [h1, h2]
    rw [hshift]
    have hexp : (fun s => box b s * Real.cos (ω * (x + s))) =
        fun s => Real.cos (ω * x) * (box b s * Real.cos (ω * s)) -
          Real.sin (ω * x) * (box b s * Real.sin (ω * s)) := by
      ext s; rw [mul_add, Real.cos_add]; ring
    have hint1 : Integrable (fun s => Real.cos (ω * x) * (box b s * Real.cos (ω * s))) :=
      ((box_integrable b).mul_bdd
        (Real.continuous_cos.measurable.comp (measurable_const_mul ω)).aestronglyMeasurable
        (ae_of_all _ (fun s => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _))).const_mul _
    have hint2 : Integrable (fun s => Real.sin (ω * x) * (box b s * Real.sin (ω * s))) :=
      ((box_integrable b).mul_bdd
        (Real.continuous_sin.measurable.comp (measurable_const_mul ω)).aestronglyMeasurable
        (ae_of_all _ (fun s => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _))).const_mul _
    rw [hexp, integral_sub hint1 hint2, integral_const_mul, integral_const_mul,
      box_cos_integral hb0 hω, box_sin_integral hb0, mul_zero, sub_zero]
    ring
  simp_rw [hinner]
  rw [show (fun x => (h x + h (-x)) * ((Real.sin (ω * b) / (ω * b)) * Real.cos (ω * x))) =
    fun x => (Real.sin (ω * b) / (ω * b)) * (h x * Real.cos (ω * x) + h (-x) * Real.cos (ω * x))
    by ext x; ring, integral_const_mul]
  have hc1 : Integrable (fun x => h x * Real.cos (ω * x)) :=
    hh_int.mul_bdd (Real.continuous_cos.measurable.comp (measurable_const_mul ω)).aestronglyMeasurable
      (ae_of_all _ (fun x => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _))
  have hc2 : Integrable (fun x => h (-x) * Real.cos (ω * x)) :=
    (integrable_comp_neg' hh_int).mul_bdd
      (Real.continuous_cos.measurable.comp (measurable_const_mul ω)).aestronglyMeasurable
      (ae_of_all _ (fun x => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _))
  rw [integral_add hc1 hc2]
  have hneg : (∫ x, h (-x) * Real.cos (ω * x)) = ∫ x, h x * Real.cos (ω * x) := by
    rw [← integral_neg_eq_self (fun x => h (-x) * Real.cos (ω * x)) volume]
    congr 1; ext x
    rw [neg_neg, mul_neg, Real.cos_neg]
  rw [hneg]
  ring

noncomputable def modeFreq (j : ℕ) : ℝ := 8 * Real.pi * (j : ℝ) / 3

lemma modeFreq_ne_zero {j : ℕ} (hj : 1 ≤ j) : modeFreq j ≠ 0 := by
  unfold modeFreq
  have hj0 : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hj0) (by norm_num)

lemma cos_modeFreq_orthog {j k : ℕ} (hj : 1 ≤ j) (hk : 1 ≤ k) :
    (∫ t in (-3 / 8 : ℝ)..(3 / 8),
      Real.cos (modeFreq j * t) * Real.cos (modeFreq k * t)) =
      if j = k then 3 / 8 else 0 := by
  have h := cos_orthog (u := 3 / 4) (by norm_num) hj hk
  have hpt : (fun t => Real.cos (modeFreq j * t) * Real.cos (modeFreq k * t)) =
      fun t => Real.cos (2 * Real.pi * (j : ℝ) * t / (3 / 4)) *
        Real.cos (2 * Real.pi * (k : ℝ) * t / (3 / 4)) := by
    ext t; unfold modeFreq; ring_nf
  have ha : (-3 / 8 : ℝ) = -((3 / 4 : ℝ) / 2) := by norm_num
  have hb : (3 / 8 : ℝ) = (3 / 4 : ℝ) / 2 := by norm_num
  rw [hpt, ha, hb, h]

lemma cos_modeFreq_integral_eq_zero {j : ℕ} (hj : 1 ≤ j) :
    (∫ t in (-3 / 8 : ℝ)..(3 / 8), Real.cos (modeFreq j * t)) = 0 := by
  have hk : (j : ℤ) ≠ 0 := by omega
  have h := cos_period_integral_eq_zero (u := 3 / 4) (by norm_num) hk
  have hpt : (fun t => Real.cos (modeFreq j * t)) =
      fun t => Real.cos ((2 * Real.pi * ((j : ℤ) : ℝ) / (3 / 4)) * t) := by
    ext t; unfold modeFreq; simp only [Int.cast_natCast]; ring
  have ha : (-3 / 8 : ℝ) = -((3 / 4 : ℝ) / 2) := by norm_num
  have hb : (3 / 8 : ℝ) = (3 / 4 : ℝ) / 2 := by norm_num
  rw [hpt, ha, hb, h]

noncomputable def tentMix (m : ℕ) (bs lam : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range m, lam i * tent (bs i) t

lemma tentMix_nonneg {m : ℕ} {bs lam : ℕ → ℝ}
    (hbs : ∀ i < m, 0 < bs i) (hlam : ∀ i < m, 0 ≤ lam i) (t : ℝ) :
    0 ≤ tentMix m bs lam t :=
  Finset.sum_nonneg (fun i hi => mul_nonneg (hlam i (Finset.mem_range.mp hi))
    (tent_nonneg (hbs i (Finset.mem_range.mp hi)) t))

lemma tentMix_supp {m : ℕ} {bs lam : ℕ → ℝ}
    (hbs0 : ∀ i < m, 0 < bs i) (hbs8 : ∀ i < m, bs i ≤ 1 / 8)
    {t : ℝ} (ht : 1 / 2 < |t|) : tentMix m bs lam t = 0 := by
  unfold tentMix
  refine Finset.sum_eq_zero (fun i hi => ?_)
  have hi' := Finset.mem_range.mp hi
  have h2b : 2 * bs i ≤ |t| := by linarith [hbs8 i hi']
  rw [tent_eq_zero_of_le (hbs0 i hi') h2b, mul_zero]

lemma tentMix_integrable {m : ℕ} {bs lam : ℕ → ℝ} (hbs0 : ∀ i < m, 0 < bs i) :
    Integrable (tentMix m bs lam) := by
  unfold tentMix
  exact integrable_finsetSum _ (fun i hi => (tent_integrable (hbs0 i (Finset.mem_range.mp hi))).const_mul _)

lemma tentMix_continuous {m : ℕ} (bs lam : ℕ → ℝ) : Continuous (tentMix m bs lam) :=
  continuous_finsetSum _ (fun i _ => continuous_const.mul (tent_continuous (bs i)))

lemma tentMix_sq_integrable {m : ℕ} {bs lam : ℕ → ℝ}
    (hbs0 : ∀ i < m, 0 < bs i) (hbs8 : ∀ i < m, bs i ≤ 1 / 8) :
    Integrable (fun t => tentMix m bs lam t ^ 2) := by
  have heq : (fun t => tentMix m bs lam t ^ 2) =
      Set.indicator (Set.Icc (-1 / 2 : ℝ) (1 / 2)) (fun t => tentMix m bs lam t ^ 2) := by
    ext t
    by_cases ht : t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)
    · rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht]
      have hlt : 1 / 2 < |t| := by
        simp only [Set.mem_Icc, not_and, not_le] at ht
        by_cases h1 : -1 / 2 ≤ t
        · exact (ht h1).trans_le (le_abs_self t)
        · push Not at h1
          exact (by linarith : 1 / 2 < -t).trans_le (neg_le_abs t)
      rw [tentMix_supp hbs0 hbs8 hlt, sq, mul_zero]
  rw [heq]
  exact ((tentMix_continuous bs lam).pow 2).integrableOn_Icc.integrable_indicator measurableSet_Icc

lemma integral_tentMix {m : ℕ} {bs lam : ℕ → ℝ}
    (hbs0 : ∀ i < m, 0 < bs i) (hsum : ∑ i ∈ Finset.range m, lam i = 1) :
    ∫ t, tentMix m bs lam t = 1 := by
  unfold tentMix
  rw [integral_finsetSum _ (fun i hi => (tent_integrable (hbs0 i (Finset.mem_range.mp hi))).const_mul _)]
  simp_rw [integral_const_mul]
  have h1 : ∀ i ∈ Finset.range m, lam i * ∫ t, tent (bs i) t = lam i := fun i hi => by
    rw [integral_tent (hbs0 i (Finset.mem_range.mp hi)), mul_one]
  rw [Finset.sum_congr rfl h1, hsum]

lemma one_le_integral_tentMix_sq {m : ℕ} {bs lam : ℕ → ℝ}
    (hbs0 : ∀ i < m, 0 < bs i) (hbs8 : ∀ i < m, bs i ≤ 1 / 8)
    (hsum : ∑ i ∈ Finset.range m, lam i = 1) :
    1 ≤ ∫ t, tentMix m bs lam t ^ 2 := by
  let S := Set.Icc (-1 / 2 : ℝ) (1 / 2)
  let ind : ℝ → ℝ := S.indicator (fun _ => (1 : ℝ))
  have hind_int : Integrable ind :=
    (integrableOn_const measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc
  have hind_sq : (fun t => ind t ^ 2) = ind := by
    ext t; by_cases ht : t ∈ S <;> simp [ind, ht]
  have hK_ind : (fun t => tentMix m bs lam t * ind t) = tentMix m bs lam := by
    ext t
    by_cases ht : t ∈ S
    · simp [ind, ht]
    · have hlt : 1 / 2 < |t| := by
        simp only [S, Set.mem_Icc, not_and, not_le] at ht
        by_cases h1 : -1 / 2 ≤ t
        · exact (ht h1).trans_le (le_abs_self t)
        · push Not at h1
          exact (by linarith : 1 / 2 < -t).trans_le (neg_le_abs t)
      simp [ind, ht, tentMix_supp hbs0 hbs8 hlt]
  have hcs := integral_mul_sq_le
    (tentMix_sq_integrable hbs0 hbs8)
    (by rw [hind_sq]; exact hind_int)
    (by rw [hK_ind]; exact tentMix_integrable hbs0)
  rw [hK_ind, integral_tentMix hbs0 hsum, one_pow] at hcs
  have hvol : (∫ t, ind t ^ 2) = 1 := by
    rw [hind_sq, integral_indicator measurableSet_Icc, setIntegral_const,
      Real.volume_real_Icc_of_le (by norm_num), smul_eq_mul, mul_one]
    norm_num
  rw [hvol, mul_one] at hcs
  exact hcs

lemma bessel_interval_cosine {F : ℝ → ℝ}
    (hF_ii : IntervalIntegrable F volume (-3 / 8) (3 / 8))
    (hF2_ii : IntervalIntegrable (fun t => F t ^ 2) volume (-3 / 8) (3 / 8))
    (hF_cos_ii : ∀ j : ℕ, IntervalIntegrable (fun t => F t * Real.cos (modeFreq j * t)) volume (-3 / 8) (3 / 8))
    (hF_int : (∫ t in (-3 / 8 : ℝ)..(3 / 8), F t) = 2)
    (N : ℕ) :
    16 / 3 + (8 / 3) * ∑ j ∈ Finset.Icc 1 N,
        (∫ t in (-3 / 8 : ℝ)..(3 / 8), F t * Real.cos (modeFreq j * t)) ^ 2 ≤
      ∫ t in (-3 / 8 : ℝ)..(3 / 8), F t ^ 2 := by
  let S := Finset.Icc 1 N
  let α : ℕ → ℝ := fun j => ∫ t in (-3 / 8 : ℝ)..(3 / 8), F t * Real.cos (modeFreq j * t)
  let g : ℝ → ℝ := fun t => ∑ j ∈ S, (8 / 3) * α j * Real.cos (modeFreq j * t)
  have hg_cont : Continuous g :=
    continuous_finsetSum S (fun j _ =>
      continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
  have hg_ii : IntervalIntegrable g volume (-3 / 8) (3 / 8) := hg_cont.intervalIntegrable _ _
  have hg2_ii : IntervalIntegrable (fun t => g t ^ 2) volume (-3 / 8) (3 / 8) :=
    (hg_cont.pow 2).intervalIntegrable _ _
  have hFg_ii : IntervalIntegrable (fun t => F t * g t) volume (-3 / 8) (3 / 8) := by
    have hpt : (fun t => F t * g t) =
        fun t => ∑ j ∈ S, (8 / 3) * α j * (F t * Real.cos (modeFreq j * t)) := by
      ext t; simp only [g, Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => by ring)
    have hpt' : (fun t => ∑ j ∈ S, (8 / 3) * α j * (F t * Real.cos (modeFreq j * t))) =
        ∑ j ∈ S, fun t => (8 / 3) * α j * (F t * Real.cos (modeFreq j * t)) := by
      ext t; simp only [Finset.sum_apply]
    rw [hpt, hpt']
    exact IntervalIntegrable.sum S (fun j _ => (hF_cos_ii j).const_mul _)
  have hnonneg : 0 ≤ ∫ t in (-3 / 8 : ℝ)..(3 / 8), (F t - 8 / 3 - g t) ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => sq_nonneg _)
  have hexp : (fun t => (F t - 8 / 3 - g t) ^ 2) =
      fun t => ((F t ^ 2 - (16 / 3) * F t + (64 / 9)) + (16 / 3) * g t) - 2 * (F t * g t) + g t ^ 2 := by
    ext t; ring
  have hg_val : (∫ t in (-3 / 8 : ℝ)..(3 / 8), g t) = 0 := by
    rw [intervalIntegral.integral_finsetSum (f := fun j t => (8 / 3) * α j * Real.cos (modeFreq j * t))
      (fun j _ => (continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _)]
    refine Finset.sum_eq_zero (fun j hj => ?_)
    rw [intervalIntegral.integral_const_mul,
      cos_modeFreq_integral_eq_zero (Finset.mem_Icc.mp hj).1, mul_zero]
  have hFg_val : (∫ t in (-3 / 8 : ℝ)..(3 / 8), F t * g t) = ∑ j ∈ S, (8 / 3) * α j ^ 2 := by
    have hpt : (fun t => F t * g t) =
        fun t => ∑ j ∈ S, (8 / 3) * α j * (F t * Real.cos (modeFreq j * t)) := by
      ext t; simp only [g, Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => by ring)
    rw [hpt, intervalIntegral.integral_finsetSum (fun j _ => (hF_cos_ii j).const_mul _)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [intervalIntegral.integral_const_mul]
    change (8 / 3) * α j * α j = (8 / 3) * α j ^ 2
    ring
  have hg2_val : (∫ t in (-3 / 8 : ℝ)..(3 / 8), g t ^ 2) = ∑ j ∈ S, (8 / 3) * α j ^ 2 := by
    have hpt : (fun t => g t ^ 2) = fun t => ∑ j ∈ S, ∑ k ∈ S,
        ((8 / 3) * α j) * ((8 / 3) * α k) * (Real.cos (modeFreq j * t) * Real.cos (modeFreq k * t)) := by
      ext t; rw [sq]; simp only [g, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => by ring))
    rw [hpt, intervalIntegral.integral_finsetSum
      (f := fun j t => ∑ k ∈ S, ((8 / 3) * α j) * ((8 / 3) * α k) * (Real.cos (modeFreq j * t) * Real.cos (modeFreq k * t)))
      (fun j _ => (continuous_finsetSum S (fun k _ => continuous_const.mul
        ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul
          (Real.continuous_cos.comp (continuous_const.mul continuous_id))))).intervalIntegrable _ _)]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [intervalIntegral.integral_finsetSum
      (f := fun k t => ((8 / 3) * α j) * ((8 / 3) * α k) * (Real.cos (modeFreq j * t) * Real.cos (modeFreq k * t)))
      (fun k _ => (continuous_const.mul
        ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul
          (Real.continuous_cos.comp (continuous_const.mul continuous_id)))).intervalIntegrable _ _)]
    have hinner : ∀ k ∈ S, (∫ t in (-3 / 8 : ℝ)..(3 / 8),
        ((8 / 3) * α j) * ((8 / 3) * α k) * (Real.cos (modeFreq j * t) * Real.cos (modeFreq k * t))) =
        if k = j then (8 / 3) * α j ^ 2 else 0 := by
      intro k hk
      rw [intervalIntegral.integral_const_mul,
        cos_modeFreq_orthog (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hk).1]
      by_cases hkj : k = j
      · subst hkj; simp only [ite_true]; ring
      · have hjk : j ≠ k := fun h => hkj h.symm
        simp only [if_neg hjk, if_neg hkj, mul_zero]
    rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq' S j, if_pos hj]
  have hc64 : IntervalIntegrable (fun _ : ℝ => (64 / 9 : ℝ)) volume (-3 / 8) (3 / 8) :=
    intervalIntegrable_const
  have h1 : IntervalIntegrable (fun t => F t ^ 2 - (16 / 3) * F t) volume (-3 / 8) (3 / 8) :=
    hF2_ii.sub (hF_ii.const_mul _)
  have h2 : IntervalIntegrable (fun t => F t ^ 2 - (16 / 3) * F t + (64 / 9)) volume (-3 / 8) (3 / 8) :=
    h1.add hc64
  have h3 : IntervalIntegrable (fun t => (F t ^ 2 - (16 / 3) * F t + (64 / 9)) + (16 / 3) * g t)
      volume (-3 / 8) (3 / 8) := h2.add (hg_ii.const_mul _)
  have h4 : IntervalIntegrable (fun t => ((F t ^ 2 - (16 / 3) * F t + (64 / 9)) + (16 / 3) * g t) - 2 * (F t * g t))
      volume (-3 / 8) (3 / 8) := h3.sub (hFg_ii.const_mul _)
  rw [hexp, intervalIntegral.integral_add h4 hg2_ii, intervalIntegral.integral_sub h3 (hFg_ii.const_mul _),
    intervalIntegral.integral_add h2 (hg_ii.const_mul _), intervalIntegral.integral_add h1 hc64,
    intervalIntegral.integral_sub hF2_ii (hF_ii.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul,
    hF_int, hg_val, hFg_val, hg2_val] at hnonneg
  rw [← Finset.mul_sum] at hnonneg
  norm_num at hnonneg
  dsimp only [S, α] at hnonneg
  simp only [show (-3 / 8 : ℝ) = -(3 / 8) by norm_num] at hnonneg ⊢
  linarith

lemma bessel_symmSmooth {h : ℝ → ℝ} (hh_meas : Measurable h) (hh0 : ∀ x, 0 ≤ h x)
    (hh_supp : ∀ x, 1 / 4 < |x| → h x = 0) (hh_l2 : MemLp h 2) (hh_int : Integrable h)
    (hh_one : ∫ x, h x = 1) {b : ℝ} (hb0 : 0 < b) (hb8 : b ≤ 1 / 8) (N : ℕ) :
    8 / 3 + (16 / 3) * ∑ j ∈ Finset.Icc 1 N,
        (Real.sin (modeFreq j * b) / (modeFreq j * b)) ^ 2 *
          (∫ x, h x * Real.cos (modeFreq j * x)) ^ 2 ≤
      ∫ s, (conv h s + corr h s) * tent b s := by
  let F := symmSmooth h b
  have hF_ii : IntervalIntegrable F volume (-3 / 8) (3 / 8) :=
    (symmSmooth_integrable hh_meas hh0 hh_supp hh_int hh_one hb0 hb8).intervalIntegrable
  have hF2_ii : IntervalIntegrable (fun t => F t ^ 2) volume (-3 / 8) (3 / 8) :=
    (symmSmooth_sq_integrable hh_meas hh0 hh_supp hh_int hh_one hb0 hb8).intervalIntegrable
  have hF_cos_ii : ∀ j : ℕ, IntervalIntegrable (fun t => F t * Real.cos (modeFreq j * t)) volume (-3 / 8) (3 / 8) := by
    intro j
    have hm : Measurable (fun t => Real.cos (modeFreq j * t)) :=
      Real.continuous_cos.measurable.comp (measurable_const_mul (modeFreq j))
    exact ((symmSmooth_integrable hh_meas hh0 hh_supp hh_int hh_one hb0 hb8).mul_bdd
      hm.aestronglyMeasurable
      (ae_of_all _ (fun t => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _))).intervalIntegrable
  have hF_int : (∫ t in (-3 / 8 : ℝ)..(3 / 8), F t) = 2 := by
    have h1 := symmSmooth_interval_eq_integral hh_supp hb0 hb8 (fun _ => (1 : ℝ))
    simp only [mul_one] at h1
    rw [h1, integral_symmSmooth hh_meas hh0 hh_supp hh_int hh_one hb0 hb8]
  have hbes := bessel_interval_cosine hF_ii hF2_ii hF_cos_ii hF_int N
  have hF2_val : (∫ t in (-3 / 8 : ℝ)..(3 / 8), F t ^ 2) =
      2 * ∫ s, (conv h s + corr h s) * tent b s := by
    have hpt : (fun t => F t ^ 2) = fun t => symmSmooth h b t * F t := by ext t; ring
    rw [hpt, symmSmooth_interval_eq_integral hh_supp hb0 hb8 F]
    have hpt2 : (fun t => symmSmooth h b t * F t) = fun t => symmSmooth h b t ^ 2 := by ext t; ring
    rw [hpt2, integral_symmSmooth_sq hh_meas hh0 hh_supp hh_l2 hh_int hh_one hb0 hb8]
  have hcos_val : (∑ j ∈ Finset.Icc 1 N,
      (∫ t in (-3 / 8 : ℝ)..(3 / 8), F t * Real.cos (modeFreq j * t)) ^ 2) =
      4 * ∑ j ∈ Finset.Icc 1 N,
        (Real.sin (modeFreq j * b) / (modeFreq j * b)) ^ 2 *
          (∫ x, h x * Real.cos (modeFreq j * x)) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [symmSmooth_cos_integral hh_meas hh0 hh_supp hh_int hb0 hb8
      (modeFreq_ne_zero (Finset.mem_Icc.mp hj).1)]
    ring
  rw [hF2_val, hcos_val] at hbes
  linarith

lemma eq4_weighted_cs {h : ℝ → ℝ} (hh0 : ∀ x, 0 ≤ h x)
    (hh_supp : ∀ x, 1 / 4 < |x| → h x = 0) (hh_int : Integrable h) (hh_one : ∫ x, h x = 1)
    {N : ℕ} {a ell : ℕ → ℝ} (hell : ∀ j ∈ Finset.Icc 1 N, 0 < ell j)
    {mG S1_up : ℝ} (hmG0 : 0 ≤ mG)
    (hG_lo : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 4),
      mG ≤ ∑ j ∈ Finset.Icc 1 N, a j * Real.cos (modeFreq j * x))
    (hS1 : (∑ j ∈ Finset.Icc 1 N, a j ^ 2 / ell j) ≤ S1_up) (hS1_pos : 0 < S1_up) :
    mG ^ 2 / S1_up ≤ ∑ j ∈ Finset.Icc 1 N, ell j * (∫ x, h x * Real.cos (modeFreq j * x)) ^ 2 := by
  let S := Finset.Icc 1 N
  let G : ℝ → ℝ := fun x => ∑ j ∈ S, a j * Real.cos (modeFreq j * x)
  have hG_even : ∀ x, G (-x) = G x := fun x => by
    dsimp [G]; refine Finset.sum_congr rfl (fun j _ => ?_); rw [mul_neg, Real.cos_neg]
  have hG_all : ∀ x, |x| ≤ 1 / 4 → mG ≤ G x := by
    intro x hx
    rcases le_total 0 x with hx0 | hx0
    · exact hG_lo x ⟨hx0, by rwa [abs_of_nonneg hx0] at hx⟩
    · rw [← hG_even x]
      exact hG_lo (-x) ⟨by linarith, by rwa [abs_of_nonpos hx0] at hx⟩
  have hle : ∀ x, mG * h x ≤ h x * G x := by
    intro x
    by_cases hx : 1 / 4 < |x|
    · simp [hh_supp x hx]
    · push Not at hx
      rw [mul_comm mG (h x)]
      exact mul_le_mul_of_nonneg_left (hG_all x hx) (hh0 x)
  have hcos_int : ∀ j ∈ S, Integrable (fun x => a j * (h x * Real.cos (modeFreq j * x))) := by
    intro j _
    have hm : Measurable (fun x => Real.cos (modeFreq j * x)) :=
      Real.continuous_cos.measurable.comp (measurable_const_mul (modeFreq j))
    exact (hh_int.mul_bdd hm.aestronglyMeasurable
      (ae_of_all _ (fun x => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _))).const_mul _
  have hintG : Integrable (fun x => h x * G x) := by
    have hpt : (fun x => h x * G x) = fun x => ∑ j ∈ S, a j * (h x * Real.cos (modeFreq j * x)) := by
      ext x; simp only [G, Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => by ring)
    rw [hpt]
    exact integrable_finsetSum S hcos_int
  have hmG_le : mG ≤ ∑ j ∈ S, a j * (∫ x, h x * Real.cos (modeFreq j * x)) := by
    calc mG = ∫ x, mG * h x := by rw [integral_const_mul, hh_one, mul_one]
      _ ≤ ∫ x, h x * G x := integral_mono (hh_int.const_mul _) hintG hle
      _ = ∫ x, ∑ j ∈ S, a j * (h x * Real.cos (modeFreq j * x)) := by
          congr 1; ext x; simp only [G, Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => by ring)
      _ = ∑ j ∈ S, a j * (∫ x, h x * Real.cos (modeFreq j * x)) := by
          rw [integral_finsetSum S hcos_int]
          refine Finset.sum_congr rfl (fun j _ => integral_const_mul _ _)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S
    (fun j => a j / Real.sqrt (ell j))
    (fun j => Real.sqrt (ell j) * (∫ x, h x * Real.cos (modeFreq j * x)))
  have hprod_eq : (∑ j ∈ S, (a j / Real.sqrt (ell j)) *
      (Real.sqrt (ell j) * (∫ x, h x * Real.cos (modeFreq j * x)))) =
      ∑ j ∈ S, a j * (∫ x, h x * Real.cos (modeFreq j * x)) := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hsq0 : Real.sqrt (ell j) ≠ 0 := (Real.sqrt_pos.mpr (hell j hj)).ne'
    field_simp
  have hL_eq : (∑ j ∈ S, (a j / Real.sqrt (ell j)) ^ 2) = ∑ j ∈ S, a j ^ 2 / ell j := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [div_pow, Real.sq_sqrt (hell j hj).le]
  have hR_eq : (∑ j ∈ S, (Real.sqrt (ell j) * (∫ x, h x * Real.cos (modeFreq j * x))) ^ 2) =
      ∑ j ∈ S, ell j * (∫ x, h x * Real.cos (modeFreq j * x)) ^ 2 := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [mul_pow, Real.sq_sqrt (hell j hj).le]
  rw [hprod_eq, hL_eq, hR_eq] at hcs
  have hsq : mG ^ 2 ≤ S1_up * ∑ j ∈ S, ell j * (∫ x, h x * Real.cos (modeFreq j * x)) ^ 2 := by
    calc mG ^ 2 ≤ (∑ j ∈ S, a j * (∫ x, h x * Real.cos (modeFreq j * x))) ^ 2 :=
          pow_le_pow_left₀ hmG0 hmG_le 2
      _ ≤ (∑ j ∈ S, a j ^ 2 / ell j) * ∑ j ∈ S, ell j * (∫ x, h x * Real.cos (modeFreq j * x)) ^ 2 := hcs
      _ ≤ S1_up * ∑ j ∈ S, ell j * (∫ x, h x * Real.cos (modeFreq j * x)) ^ 2 :=
          mul_le_mul_of_nonneg_right hS1 (Finset.sum_nonneg (fun j hj =>
            mul_nonneg (hell j hj).le (sq_nonneg _)))
  exact (div_le_iff₀ hS1_pos).mpr (by linarith)

lemma integral_conv_sq_le_M_sup {h : ℝ → ℝ} (hh_meas : Measurable h) (hh0 : ∀ x, 0 ≤ h x)
    (hh_supp : ∀ x, 1 / 4 < |x| → h x = 0) (hh_l2 : MemLp h 2)
    (hh_int : Integrable h) (hh_one : ∫ x, h x = 1)
    {M_sup : ℝ} (hM_bdd : ∀ t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2), conv h t ≤ M_sup) :
    ∫ t, conv h t ^ 2 ≤ M_sup := by
  have hle : ∀ t, conv h t ^ 2 ≤ M_sup * conv h t := by
    intro t
    have hc0 := conv_nonneg hh0 t
    by_cases ht : t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)
    · rw [sq]; exact mul_le_mul_of_nonneg_right (hM_bdd t ht) hc0
    · have hlt : 1 / 2 < |t| := by
        simp only [Set.mem_Icc, not_and, not_le] at ht
        by_cases h1 : -1 / 2 ≤ t
        · exact (ht h1).trans_le (le_abs_self t)
        · push Not at h1
          exact (by linarith : 1 / 2 < -t).trans_le (neg_le_abs t)
      rw [conv_eq_zero_of_lt hh_supp hlt, sq, mul_zero, mul_zero]
  calc ∫ t, conv h t ^ 2
      ≤ ∫ t, M_sup * conv h t :=
        integral_mono (conv_sq_integrable hh_meas hh0 hh_supp hh_l2)
          ((conv_integrable hh_meas hh0 hh_supp hh_l2).const_mul _) hle
    _ = M_sup * ∫ t, conv h t := integral_const_mul _ _
    _ = M_sup := by rw [integral_conv hh_meas hh0 hh_supp hh_l2 hh_int hh_one, mul_one]

lemma master_inequality {h : ℝ → ℝ} (hh_meas : Measurable h) (hh0 : ∀ x, 0 ≤ h x)
    (hh_supp : ∀ x, 1 / 4 < |x| → h x = 0) (hh_l2 : MemLp h 2)
    (hh_int : Integrable h) (hh_one : ∫ x, h x = 1)
    {m : ℕ} {bs lam : ℕ → ℝ} (hbs0 : ∀ i < m, 0 < bs i) (hbs8 : ∀ i < m, bs i ≤ 1 / 8)
    (hlam0 : ∀ i < m, 0 ≤ lam i) (hlam1 : ∑ i ∈ Finset.range m, lam i = 1)
    {N : ℕ} {a ell : ℕ → ℝ} (hell : ∀ j ∈ Finset.Icc 1 N, 0 < ell j)
    (hell_le : ∀ j ∈ Finset.Icc 1 N,
      ell j ≤ ∑ i ∈ Finset.range m, lam i * (Real.sin (modeFreq j * bs i) / (modeFreq j * bs i)) ^ 2)
    {mG S1_up C0 M_sup : ℝ} (hmG0 : 0 ≤ mG)
    (hG_lo : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 4),
      mG ≤ ∑ j ∈ Finset.Icc 1 N, a j * Real.cos (modeFreq j * x))
    (hS1 : (∑ j ∈ Finset.Icc 1 N, a j ^ 2 / ell j) ≤ S1_up) (hS1_pos : 0 < S1_up)
    (hM_bdd : ∀ t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2), conv h t ≤ M_sup)
    (hlt : C0 + 1 < 8 / 3 + (16 / 3) * (mG ^ 2 / S1_up))
    (hsq : (C0 - 1) * ((∫ t, tentMix m bs lam t ^ 2) - 1) <
      ((8 / 3 + (16 / 3) * (mG ^ 2 / S1_up)) - (C0 + 1)) ^ 2) :
    C0 ≤ M_sup := by
  let K := tentMix m bs lam
  let c : ℕ → ℝ := fun j => ∫ x, h x * Real.cos (modeFreq j * x)
  have h1M : 1 ≤ ∫ t, conv h t ^ 2 := one_le_integral_conv_sq hh_meas hh0 hh_supp hh_l2 hh_int hh_one
  have hMM : (∫ t, conv h t ^ 2) ≤ M_sup :=
    integral_conv_sq_le_M_sup hh_meas hh0 hh_supp hh_l2 hh_int hh_one hM_bdd
  have h1K : 1 ≤ ∫ t, K t ^ 2 := one_le_integral_tentMix_sq hbs0 hbs8 hlam1
  have hcs_eq4 := eq4_weighted_cs hh0 hh_supp hh_int hh_one hell hmG0 hG_lo hS1 hS1_pos
  have hbes_mix : 8 / 3 + (16 / 3) * (mG ^ 2 / S1_up) ≤ ∫ s, (conv h s + corr h s) * K s := by
    have hlow : ∀ i ∈ Finset.range m,
        lam i * (8 / 3 + (16 / 3) * ∑ j ∈ Finset.Icc 1 N,
          (Real.sin (modeFreq j * bs i) / (modeFreq j * bs i)) ^ 2 * c j ^ 2) ≤
        lam i * ∫ s, (conv h s + corr h s) * tent (bs i) s := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      exact mul_le_mul_of_nonneg_left
        (bessel_symmSmooth hh_meas hh0 hh_supp hh_l2 hh_int hh_one (hbs0 i hi') (hbs8 i hi') N)
        (hlam0 i hi')
    have hsum_low := Finset.sum_le_sum hlow
    have hL : (∑ i ∈ Finset.range m, lam i * (8 / 3 + (16 / 3) * ∑ j ∈ Finset.Icc 1 N,
        (Real.sin (modeFreq j * bs i) / (modeFreq j * bs i)) ^ 2 * c j ^ 2)) =
        8 / 3 + (16 / 3) * ∑ j ∈ Finset.Icc 1 N,
          (∑ i ∈ Finset.range m, lam i * (Real.sin (modeFreq j * bs i) / (modeFreq j * bs i)) ^ 2) * c j ^ 2 := by
      simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hlam1, one_mul, Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x _ => by ring)
    have hR : (∑ i ∈ Finset.range m, lam i * ∫ s, (conv h s + corr h s) * tent (bs i) s) =
        ∫ s, (conv h s + corr h s) * K s := by
      have hint_i : ∀ i ∈ Finset.range m,
          Integrable (fun s => lam i * ((conv h s + corr h s) * tent (bs i) s)) := by
        intro i hi
        have hi' := Finset.mem_range.mp hi
        have hsum : Integrable (fun s => conv h s * tent (bs i) s + corr h s * tent (bs i) s) :=
          (conv_tent_integrable hh_meas hh0 hh_supp hh_l2 (hbs0 i hi')).add
            (corr_tent_integrable hh_meas hh0 hh_supp hh_l2 (hbs0 i hi'))
        have hsum2 : Integrable (fun s => (conv h s + corr h s) * tent (bs i) s) := by
          have hpt : (fun s => (conv h s + corr h s) * tent (bs i) s) =
              fun s => conv h s * tent (bs i) s + corr h s * tent (bs i) s := by ext s; ring
          rw [hpt]; exact hsum
        exact hsum2.const_mul _
      simp_rw [← integral_const_mul]
      rw [← integral_finsetSum _ hint_i]
      congr 1; ext s
      simp only [K, tentMix, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => by ring)
    rw [hL, hR] at hsum_low
    have hmid : 8 / 3 + (16 / 3) * (mG ^ 2 / S1_up) ≤
        8 / 3 + (16 / 3) * ∑ j ∈ Finset.Icc 1 N,
          (∑ i ∈ Finset.range m, lam i * (Real.sin (modeFreq j * bs i) / (modeFreq j * bs i)) ^ 2) * c j ^ 2 := by
      have hs : ∑ j ∈ Finset.Icc 1 N, ell j * c j ^ 2 ≤
          ∑ j ∈ Finset.Icc 1 N,
            (∑ i ∈ Finset.range m, lam i * (Real.sin (modeFreq j * bs i) / (modeFreq j * bs i)) ^ 2) * c j ^ 2 :=
        Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_right (hell_le j hj) (sq_nonneg _))
      linarith [hcs_eq4, hs]
    exact hmid.trans hsum_low
  have hconv_K : Integrable (fun s => conv h s * K s) := by
    have hpt : (fun s => conv h s * K s) = fun s => ∑ i ∈ Finset.range m, lam i * (conv h s * tent (bs i) s) := by
      ext s; simp only [K, tentMix, Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _ => by ring)
    rw [hpt]
    exact integrable_finsetSum _ (fun i hi =>
      (conv_tent_integrable hh_meas hh0 hh_supp hh_l2 (hbs0 i (Finset.mem_range.mp hi))).const_mul _)
  have hcorr_K : Integrable (fun s => corr h s * K s) := by
    have hpt : (fun s => corr h s * K s) = fun s => ∑ i ∈ Finset.range m, lam i * (corr h s * tent (bs i) s) := by
      ext s; simp only [K, tentMix, Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _ => by ring)
    rw [hpt]
    exact integrable_finsetSum _ (fun i hi =>
      (corr_tent_integrable hh_meas hh0 hh_supp hh_l2 (hbs0 i (Finset.mem_range.mp hi))).const_mul _)
  have hup_eq1 := eq1_bound hh0 hh_supp (tentMix_nonneg hbs0 hlam0)
    (tentMix_integrable hbs0) (integral_tentMix hbs0 hlam1) hM_bdd hconv_K
  have hup_eq2 := eq2_bound hh_meas hh0 hh_supp hh_l2 hh_int hh_one
    (tentMix_integrable hbs0) (tentMix_sq_integrable hbs0 hbs8)
    (integral_tentMix hbs0 hlam1) (fun t ht => tentMix_supp hbs0 hbs8 ht) hcorr_K
  have hsplit_K : (∫ s, (conv h s + corr h s) * K s) =
      (∫ s, conv h s * K s) + (∫ s, corr h s * K s) := by
    have hpt : (fun s => (conv h s + corr h s) * K s) = fun s => conv h s * K s + corr h s * K s := by
      ext s; ring
    rw [hpt, integral_add hconv_K hcorr_K]
  rw [hsplit_K] at hbes_mix
  by_contra hlt_M
  push Not at hlt_M
  have hprod_lt : ((∫ t, conv h t ^ 2) - 1) * ((∫ t, K t ^ 2) - 1) <
      ((8 / 3 + (16 / 3) * (mG ^ 2 / S1_up)) - (C0 + 1)) ^ 2 := by
    have h1 : (∫ t, conv h t ^ 2) - 1 ≤ C0 - 1 := by linarith
    have h2 : ((∫ t, conv h t ^ 2) - 1) * ((∫ t, K t ^ 2) - 1) ≤ (C0 - 1) * ((∫ t, K t ^ 2) - 1) :=
      mul_le_mul_of_nonneg_right h1 (by linarith)
    exact lt_of_le_of_lt h2 hsq
  have hsqrt_lt : Real.sqrt (((∫ t, conv h t ^ 2) - 1) * ((∫ t, K t ^ 2) - 1)) <
      (8 / 3 + (16 / 3) * (mG ^ 2 / S1_up)) - (C0 + 1) :=
    (Real.sqrt_lt' (by linarith)).mpr hprod_lt
  linarith

lemma C1a_set_bddAbove : BddAbove
    {C : ℝ | ∀ ⦃f : ℝ → ℝ⦄, 0 ≤ f → MemLp f 2 →
      C * (∫ x in (-1 / 4 : ℝ)..(1 / 4), f x) ^ 2 ≤
        sSup {∫ x, f (t - x) * f x | t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)}} := by
  refine ⟨2, fun C hC => ?_⟩
  let f0 : ℝ → ℝ := Set.indicator (Set.Icc (-1 / 4 : ℝ) (1 / 4)) (fun _ => (1 : ℝ))
  have hf0_0 : 0 ≤ f0 := fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have hf0_int : Integrable f0 :=
    (integrableOn_const measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc
  have hf0_sq : (fun x => f0 x ^ 2) = f0 := by
    ext x
    by_cases hx : x ∈ Set.Icc (-1 / 4 : ℝ) (1 / 4)
    · simp only [f0, Set.indicator_of_mem hx, one_pow]
    · simp only [f0, Set.indicator_of_notMem hx, zero_pow (by norm_num : 2 ≠ 0)]
  have hf0_l2 : MemLp f0 2 :=
    (memLp_two_iff_integrable_sq (measurable_const.indicator measurableSet_Icc).aestronglyMeasurable).mpr
      (by rw [hf0_sq]; exact hf0_int)
  have hI : (∫ x in (-1 / 4 : ℝ)..(1 / 4), f0 x) = 1 / 2 := by
    rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc,
      setIntegral_indicator measurableSet_Icc, Set.inter_self, setIntegral_const,
      Real.volume_real_Icc_of_le (by norm_num), smul_eq_mul, mul_one]
    norm_num
  have hconv_le : ∀ t, (∫ x, f0 (t - x) * f0 x) ≤ 1 / 2 := by
    intro t
    calc (∫ x, f0 (t - x) * f0 x) ≤ ∫ x, f0 x ^ 2 := conv_le_sq hf0_l2 t
      _ = ∫ x, f0 x := by rw [hf0_sq]
      _ = 1 / 2 := by
          rw [integral_indicator measurableSet_Icc, setIntegral_const,
            Real.volume_real_Icc_of_le (by norm_num), smul_eq_mul, mul_one]
          norm_num
  have hsup_le : sSup {∫ x, f0 (t - x) * f0 x | t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)} ≤ 1 / 2 := by
    have hne : {∫ x, f0 (t - x) * f0 x | t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)}.Nonempty :=
      ⟨∫ x, f0 (0 - x) * f0 x, 0, ⟨by norm_num, by norm_num⟩, rfl⟩
    apply csSup_le hne
    rintro y ⟨t, _, rfl⟩
    exact hconv_le t
  have hC0 := hC hf0_0 hf0_l2
  rw [hI] at hC0
  linarith

lemma C1a_ge_of_normalized_bound {C0 : ℝ} (_hC0_nonneg : 0 ≤ C0)
    (hbound : ∀ h : ℝ → ℝ, Measurable h → (∀ x, 0 ≤ h x) → (∀ x, 1 / 4 < |x| → h x = 0) →
      MemLp h 2 → Integrable h → (∫ x, h x = 1) →
      ∀ M_sup : ℝ, (∀ t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2), conv h t ≤ M_sup) → C0 ≤ M_sup) :
    C0 ≤ Constant1a.C1a := by
  unfold Constant1a.C1a
  apply le_csSup C1a_set_bddAbove
  intro f hf0 hfl2
  let S_f : Set ℝ := {∫ x, f (t - x) * f x | t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)}
  have hSf_ne : S_f.Nonempty := ⟨∫ x, f (0 - x) * f x, 0, ⟨by norm_num, by norm_num⟩, rfl⟩
  have hSf_bdd : BddAbove S_f := by
    refine ⟨∫ x, f x ^ 2, ?_⟩
    rintro y ⟨t, _, rfl⟩
    exact conv_le_sq hfl2 t
  have hSf_nonneg : 0 ≤ sSup S_f := by
    have h0 : 0 ≤ ∫ x, f (0 - x) * f x := integral_nonneg (fun x => mul_nonneg (hf0 _) (hf0 _))
    exact h0.trans (le_csSup hSf_bdd ⟨0, ⟨by norm_num, by norm_num⟩, rfl⟩)
  set I := ∫ x in (-1 / 4 : ℝ)..(1 / 4), f x
  have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg (by norm_num) (fun x _ => hf0 x)
  rcases eq_or_lt_of_le hI0 with hIeq | hIpos
  · rw [← hIeq, zero_pow (by norm_num), mul_zero]
    exact hSf_nonneg
  · let g0 := hfl2.aestronglyMeasurable.mk f
    let g : ℝ → ℝ := fun x => max 0 (g0 x)
    have hg_meas : Measurable g :=
      measurable_const.max hfl2.aestronglyMeasurable.stronglyMeasurable_mk.measurable
    have hfg : f =ᵐ[volume] g := by
      filter_upwards [hfl2.aestronglyMeasurable.ae_eq_mk] with x hx
      dsimp only [g, g0]
      rw [← hx]
      exact (max_eq_right (hf0 x)).symm
    have hgl2 : MemLp g 2 := hfl2.ae_eq hfg
    let h : ℝ → ℝ := Set.indicator (Set.Icc (-1 / 4 : ℝ) (1 / 4)) (fun x => (1 / I) * g x)
    have hh_meas : Measurable h := ((hg_meas.const_mul (1 / I)).indicator measurableSet_Icc)
    have hh0 : ∀ x, 0 ≤ h x := fun x =>
      Set.indicator_nonneg (fun _ _ => mul_nonneg (by positivity) (le_max_left _ _)) x
    have hh_supp : ∀ x, 1 / 4 < |x| → h x = 0 := by
      intro x hx
      have hn : x ∉ Set.Icc (-1 / 4 : ℝ) (1 / 4) := by
        simp only [Set.mem_Icc, not_and, not_le]
        intro _
        rcases le_or_gt 0 x with h1 | h1
        · rwa [abs_of_nonneg h1] at hx
        · rw [abs_of_neg h1] at hx; linarith
      exact Set.indicator_of_notMem hn _
    have hhg_le : ∀ x, h x ≤ (1 / I) * g x := fun x => by
      by_cases hx : x ∈ Set.Icc (-1 / 4 : ℝ) (1 / 4)
      · exact (Set.indicator_of_mem hx _).le
      · rw [show h x = 0 from Set.indicator_of_notMem hx _]
        exact mul_nonneg (by positivity) (le_max_left _ _)
    have hh_l2 : MemLp h 2 :=
      (hgl2.const_mul (1 / I)).mono' hh_meas.aestronglyMeasurable (ae_of_all _ (fun x => by
        rw [Real.norm_of_nonneg (hh0 x)]
        exact hhg_le x))
    have hh_int : Integrable h := by
      let ind : ℝ → ℝ := Set.indicator (Set.Icc (-1 / 4 : ℝ) (1 / 4)) (fun _ => (1 : ℝ))
      have hind_int : Integrable ind :=
        (integrableOn_const measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc
      have hind_add : Integrable (fun x => ind x + h x ^ 2) := hind_int.add hh_l2.integrable_sq
      refine hind_add.mono hh_meas.aestronglyMeasurable ?_
      filter_upwards with x
      rw [Real.norm_of_nonneg (hh0 x)]
      have hsq0 : 0 ≤ h x ^ 2 := sq_nonneg _
      have hind0 : 0 ≤ ind x := Set.indicator_nonneg (fun _ _ => zero_le_one) x
      rw [Real.norm_of_nonneg (add_nonneg hind0 hsq0)]
      by_cases hx : x ∈ Set.Icc (-1 / 4 : ℝ) (1 / 4)
      · have hind_x : ind x = 1 := Set.indicator_of_mem hx _
        rw [hind_x]
        nlinarith [hh0 x]
      · have hx0 : h x = 0 := Set.indicator_of_notMem hx _
        rw [hx0]
        linarith
    have hh_one : ∫ x, h x = 1 := by
      have hg_eq_f : (∫ x in Set.Icc (-1 / 4 : ℝ) (1 / 4), g x) =
          ∫ x in Set.Icc (-1 / 4 : ℝ) (1 / 4), f x :=
        setIntegral_congr_ae measurableSet_Icc (by filter_upwards [hfg] with x hx _; exact hx.symm)
      have hg_int_Icc : (∫ x in Set.Icc (-1 / 4 : ℝ) (1 / 4), g x) = I := by
        rw [hg_eq_f, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
      rw [integral_indicator measurableSet_Icc, integral_const_mul, hg_int_Icc]
      field_simp
    have hM_bdd : ∀ t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2), conv h t ≤ sSup S_f / I ^ 2 := by
      intro t ht
      have hfg_sub : (fun x => f (t - x)) =ᵐ[volume] (fun x => g (t - x)) :=
        (Measure.measurePreserving_sub_left volume t).quasiMeasurePreserving.ae_eq_comp hfg
      have hint_fg : (∫ x, g (t - x) * g x) = ∫ x, f (t - x) * f x :=
        integral_congr_ae (hfg_sub.mul hfg).symm
      have hpt_le : ∀ x, (I * h (t - x)) * (I * h x) ≤ g (t - x) * g x := by
        intro x
        have h1 : I * h (t - x) ≤ g (t - x) := by
          have := mul_le_mul_of_nonneg_left (hhg_le (t - x)) hI0
          rwa [← mul_assoc, mul_one_div_cancel hIpos.ne', one_mul] at this
        have h2 : I * h x ≤ g x := by
          have := mul_le_mul_of_nonneg_left (hhg_le x) hI0
          rwa [← mul_assoc, mul_one_div_cancel hIpos.ne', one_mul] at this
        exact mul_le_mul h1 h2 (mul_nonneg hI0 (hh0 x)) (le_max_left _ _)
      have hint_h : Integrable (fun x => (I * h (t - x)) * (I * h x)) := by
        have : (fun x => (I * h (t - x)) * (I * h x)) = fun x => I ^ 2 * (h (t - x) * h x) := by
          ext x; ring
        rw [this]
        exact (conv_integrable_mul hh_l2 t).const_mul _
      have hint_g : Integrable (fun x => g (t - x) * g x) := conv_integrable_mul hgl2 t
      have hconv_mul : I ^ 2 * conv h t ≤ sSup S_f := by
        calc I ^ 2 * conv h t
            = ∫ x, (I * h (t - x)) * (I * h x) := by
                unfold conv; rw [← integral_const_mul]; congr 1; ext x; ring
          _ ≤ ∫ x, g (t - x) * g x := integral_mono hint_h hint_g hpt_le
          _ = ∫ x, f (t - x) * f x := hint_fg
          _ ≤ sSup S_f := le_csSup hSf_bdd ⟨t, ht, rfl⟩
      exact (le_div_iff₀ (sq_pos_of_pos hIpos)).mpr (by linarith)
    have hC0_le := hbound h hh_meas hh0 hh_supp hh_l2 hh_int hh_one (sSup S_f / I ^ 2) hM_bdd
    exact (le_div_iff₀ (sq_pos_of_pos hIpos)).mp hC0_le

/- ### Block D: Taylor Sin Lower Bound, Rational / Fejer-Riesz Certificate, and Closing Inequality -/

lemma nonneg_of_hasDerivAt_nonneg {f f' : ℝ → ℝ} (hf_cont : Continuous f)
    (hderiv : ∀ x, HasDerivAt f (f' x) x) (hf0 : f 0 = 0) (hf'0 : ∀ x, 0 ≤ x → 0 ≤ f' x)
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have hmono : MonotoneOn f (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) hf_cont.continuousOn
      (fun y _ => (hderiv y).differentiableAt.differentiableWithinAt) (fun y hy => ?_)
    rw [(hderiv y).deriv]
    exact hf'0 y (interior_subset hy)
  have h := hmono (le_refl (0 : ℝ)) hx hx
  simpa [hf0] using h

lemma pow_div_fac_hasDerivAt (n : ℕ) (c : ℝ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => t ^ (n + 1) / c) (((n + 1 : ℕ) : ℝ) * x ^ n / c) x := by
  have h := (hasDerivAt_pow (n + 1) x).div_const c
  simpa only [Nat.add_sub_cancel] using h

lemma one_sub_cos_hasDerivAt (y : ℝ) :
    HasDerivAt (fun s : ℝ => 1 - Real.cos s) (Real.sin y) y := by
  have hc := (hasDerivAt_const y (1 : ℝ)).sub (Real.hasDerivAt_cos y)
  rwa [zero_sub, neg_neg] at hc

lemma pow_fac_hasDerivAt (n : ℕ) (c d : ℝ) (hd0 : d ≠ 0)
    (hcd : c = ((n + 1 : ℕ) : ℝ) * d) (y : ℝ) :
    HasDerivAt (fun s : ℝ => s ^ (n + 1) / c) (y ^ n / d) y := by
  have h := pow_div_fac_hasDerivAt n c y
  rwa [show (((n + 1 : ℕ) : ℝ) * y ^ n / c) = y ^ n / d by rw [hcd]; field_simp] at h

lemma sin_taylor_lower {x : ℝ} (hx : 0 ≤ x) :
    x * (1 - x ^ 2 * (1 / 6 - x ^ 2 * (1 / 120 - x ^ 2 * (1 / 5040)))) ≤ Real.sin x := by
  have hd0 : ∀ t, 0 ≤ t → 0 ≤ 1 - Real.cos t := fun t _ => sub_nonneg.mpr (Real.cos_le_one t)
  have hd1 : ∀ t, 0 ≤ t → 0 ≤ t - Real.sin t := fun t ht =>
    nonneg_of_hasDerivAt_nonneg (continuous_id.sub Real.continuous_sin)
      (fun y => (hasDerivAt_id y).sub (Real.hasDerivAt_sin y)) (by norm_num) hd0 ht
  have d2h : ∀ y, HasDerivAt (fun s : ℝ => s ^ 2 / 2 - (1 - Real.cos s)) (y - Real.sin y) y := fun y =>
    (show HasDerivAt (fun s : ℝ => s ^ 2 / 2) y y by
      simpa using pow_fac_hasDerivAt 1 2 1 (by norm_num) (by norm_num) y).sub
      (one_sub_cos_hasDerivAt y)
  have hd2 : ∀ t, 0 ≤ t → 0 ≤ t ^ 2 / 2 - (1 - Real.cos t) := fun t ht =>
    nonneg_of_hasDerivAt_nonneg
      (((continuous_pow 2).div_const 2).sub (continuous_const.sub Real.continuous_cos))
      d2h (by norm_num) hd1 ht
  have d3h : ∀ y, HasDerivAt (fun s : ℝ => s ^ 3 / 6 - (s - Real.sin s))
      (y ^ 2 / 2 - (1 - Real.cos y)) y := fun y =>
    (pow_fac_hasDerivAt 2 6 2 (by norm_num) (by norm_num) y).sub
      ((hasDerivAt_id y).sub (Real.hasDerivAt_sin y))
  have hd3 : ∀ t, 0 ≤ t → 0 ≤ t ^ 3 / 6 - (t - Real.sin t) := fun t ht =>
    nonneg_of_hasDerivAt_nonneg
      (((continuous_pow 3).div_const 6).sub (continuous_id.sub Real.continuous_sin))
      d3h (by norm_num) hd2 ht
  have d4h : ∀ y, HasDerivAt (fun s : ℝ => s ^ 4 / 24 - (s ^ 2 / 2 - (1 - Real.cos s)))
      (y ^ 3 / 6 - (y - Real.sin y)) y := fun y =>
    (pow_fac_hasDerivAt 3 24 6 (by norm_num) (by norm_num) y).sub (d2h y)
  have hd4 : ∀ t, 0 ≤ t → 0 ≤ t ^ 4 / 24 - (t ^ 2 / 2 - (1 - Real.cos t)) := fun t ht =>
    nonneg_of_hasDerivAt_nonneg
      (((continuous_pow 4).div_const 24).sub
        (((continuous_pow 2).div_const 2).sub (continuous_const.sub Real.continuous_cos)))
      d4h (by norm_num) hd3 ht
  have d5h : ∀ y, HasDerivAt (fun s : ℝ => s ^ 5 / 120 - (s ^ 3 / 6 - (s - Real.sin s)))
      (y ^ 4 / 24 - (y ^ 2 / 2 - (1 - Real.cos y))) y := fun y =>
    (pow_fac_hasDerivAt 4 120 24 (by norm_num) (by norm_num) y).sub (d3h y)
  have hd5 : ∀ t, 0 ≤ t → 0 ≤ t ^ 5 / 120 - (t ^ 3 / 6 - (t - Real.sin t)) := fun t ht =>
    nonneg_of_hasDerivAt_nonneg
      (((continuous_pow 5).div_const 120).sub
        (((continuous_pow 3).div_const 6).sub (continuous_id.sub Real.continuous_sin)))
      d5h (by norm_num) hd4 ht
  have d6h : ∀ y, HasDerivAt
      (fun s : ℝ => s ^ 6 / 720 - (s ^ 4 / 24 - (s ^ 2 / 2 - (1 - Real.cos s))))
      (y ^ 5 / 120 - (y ^ 3 / 6 - (y - Real.sin y))) y := fun y =>
    (pow_fac_hasDerivAt 5 720 120 (by norm_num) (by norm_num) y).sub (d4h y)
  have hd6 : ∀ t, 0 ≤ t → 0 ≤ t ^ 6 / 720 - (t ^ 4 / 24 - (t ^ 2 / 2 - (1 - Real.cos t))) := fun t ht =>
    nonneg_of_hasDerivAt_nonneg
      (((continuous_pow 6).div_const 720).sub
        (((continuous_pow 4).div_const 24).sub
          (((continuous_pow 2).div_const 2).sub (continuous_const.sub Real.continuous_cos))))
      d6h (by norm_num) hd5 ht
  have hd7 := nonneg_of_hasDerivAt_nonneg
    (((continuous_pow 7).div_const 5040).sub
      (((continuous_pow 5).div_const 120).sub
        (((continuous_pow 3).div_const 6).sub (continuous_id.sub Real.continuous_sin))))
    (fun y => (pow_fac_hasDerivAt 6 5040 720 (by norm_num) (by norm_num) y).sub (d5h y))
    (by norm_num) hd6 hx
  simp only [Pi.sub_apply, id_eq] at hd7
  have hpoly : x * (1 - x ^ 2 * (1 / 6 - x ^ 2 * (1 / 120 - x ^ 2 * (1 / 5040)))) =
      x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 := by ring
  linarith

def N_modes : ℕ := 66
def D_a : ℤ := 100000
def D_p : ℤ := 100000
def D_ell : ℚ := 100000000

def E_list : List ℕ := [
  76091979, 35921028, 19140762, 17919210, 13681447, 9824868, 9717953, 8633700, 6975560, 6563202, 5781653, 5024789, 5251788, 5253985, 4973638, 5000009, 4732687, 4315870, 4230082, 3995432, 3617585, 3436061, 3168699, 2891712, 2867872, 2805873, 2673880, 2648032, 2537045, 2376721, 2339569, 2252066, 2108439, 2043542, 1942137, 1833428, 1835840, 1820753, 1770358, 1767676, 1719524, 1640946, 1619795, 1567533, 1479625, 1428594, 1352653, 1267771, 1241861, 1203758, 1143330, 1109674, 1048710, 969367, 925486, 864153, 782582, 726215, 657024, 585168, 554583, 520041, 474733, 450671, 412141, 364497
]

def A_list : List ℤ := [
  174609, -110944, 39067, 11264, -26831, 15320, 3666, -13277, 9163, 1322, -7848, 5870, 1075, -5976, 4877, 322, -4466, 4095, -189, -3321, 3402, -461, -2462, 2735, -437, -2035, 2392, -520, -1645, 2089, -570, -1330, 1828, -595, -1070, 1582, -560, -922, 1450, -600, -743, 1306, -631, -568, 1154, -644, -404, 989, -618, -288, 861, -613, -156, 709, -581, -40, 552, -524, 53, 397, -451, 127, 252, -395, 278, -91
]

def P_list : List ℤ := [
  3274, -2811, 2722, -2420, 2059, -1684, 1216, -779, 330, 96, -485, 854, -1191, 1481, -1722, 1894, -1980, 1979, -1845, 1633, -1331, 941, -509, 58, 339, -645, 803, -774, 602, -306, -56, 365, -507, 485, -272, -25, 293, -400, 277, -4, -247, 306, -129, -119, 258, -139, -125, 206, -37, -156, 109, 97, -113, -80, 78, 84, -19, -79, -68, -34, -12, -3, -1, 0, 0, 0, 0
]

def piLo : ℚ := 3141592 / 1000000
def piHi : ℚ := 3141593 / 1000000

def sinPolyQ (x : ℚ) : ℚ :=
  let x2 := x * x
  x * (1 - x2 * (1 / 6 - x2 * (1 / 120 - x2 * (1 / 5040))))

def absQ (r : ℚ) : ℚ := if r < 0 then -r else r

def nearestIntQ (q : ℚ) : ℤ :=
  (2 * q.num + (q.den : ℤ)) / (2 * (q.den : ℤ))

def sincSqLoQ (q : ℚ) : ℚ :=
  let k := nearestIntQ q
  let r := absQ (q - k)
  let s := sinPolyQ (r * piLo)
  let d := q * piHi
  let s' := if 0 < s then s else 0
  (s' / d) * (s' / d)

def tentPairs : List (ℚ × ℚ) :=
  [(1/8, 7136/10000), (1/16, 1277/10000), (1/32, 956/10000), (1/90, 313/10000), (1/240, 318/10000)]

def checkKtildeLoop (j : ℕ) : List ℕ → Bool
  | [] => true
  | e :: es =>
    let pairsOk := tentPairs.all (fun ⟨b, _⟩ =>
      let q : ℚ := ((8 * j : ℚ) / 3) * b
      absQ (q - nearestIntQ q) ≤ 1 / 2)
    let sumQ : ℚ := tentPairs.foldl (fun acc ⟨b, lam⟩ =>
      let q : ℚ := ((8 * j : ℚ) / 3) * b
      acc + lam * sincSqLoQ q) 0
    (pairsOk && 0 < e && (e : ℚ) / D_ell ≤ sumQ) && checkKtildeLoop (j + 1) es

theorem checkKtilde_ok : checkKtildeLoop 1 E_list = true := by decide +kernel

lemma absQ_cast (r : ℚ) : ((absQ r : ℚ) : ℝ) = |(r : ℝ)| := by
  unfold absQ
  split_ifs with h
  · rw [Rat.cast_neg, abs_of_neg (by exact_mod_cast h)]
  · rw [abs_of_nonneg (by exact_mod_cast (not_lt.mp h))]

lemma sincSqLoQ_le {q : ℚ} (hq : 0 < q) (hr : absQ (q - nearestIntQ q) ≤ 1 / 2) :
    ((sincSqLoQ q : ℚ) : ℝ) ≤ (Real.sin ((q : ℝ) * Real.pi) / ((q : ℝ) * Real.pi)) ^ 2 := by
  dsimp only [sincSqLoQ]
  set k := nearestIntQ q
  set r := absQ (q - k)
  set s := sinPolyQ (r * piLo)
  set d := q * piHi
  set s' := if 0 < s then s else 0
  have hpi_lo : (piLo : ℝ) < Real.pi := by
    have : (piLo : ℝ) = 3.141592 := by unfold piLo; norm_num
    rw [this]; exact Real.pi_gt_d6
  have hpi_hi : Real.pi < (piHi : ℝ) := by
    have : (piHi : ℝ) = 3.141593 := by unfold piHi; norm_num
    rw [this]; exact Real.pi_lt_d6
  have hpi_lo_pos : (0 : ℝ) < (piLo : ℝ) := by unfold piLo; norm_num
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hd_pos : (0 : ℝ) < (d : ℝ) := by
    dsimp only [d]; push_cast; exact mul_pos hqR (lt_trans Real.pi_pos hpi_hi)
  have hqpi_pos : 0 < (q : ℝ) * Real.pi := mul_pos hqR Real.pi_pos
  have hqpi_le_d : (q : ℝ) * Real.pi ≤ (d : ℝ) := by
    have : (d : ℝ) = (q : ℝ) * (piHi : ℝ) := by push_cast [d]; rfl
    rw [this]; exact mul_le_mul_of_nonneg_left hpi_hi.le hqR.le
  rw [Rat.cast_mul, Rat.cast_div]
  rcases le_or_gt s 0 with hs0 | hs0
  · have hs'_zero : s' = 0 := if_neg (not_lt.mpr hs0)
    rw [hs'_zero, Rat.cast_zero, zero_div, mul_zero]
    exact sq_nonneg _
  · have hs'_eq : s' = s := if_pos hs0
    rw [hs'_eq, ← sq]
    have hr_cast : (r : ℝ) = |(q : ℝ) - (k : ℝ)| := by
      have := absQ_cast (q - k)
      push_cast at this
      exact this
    have hr0 : 0 ≤ (r : ℝ) := hr_cast ▸ abs_nonneg _
    have hr_half : (r : ℝ) ≤ 1 / 2 := by simpa using Rat.cast_le (K := ℝ).mpr hr
    have hr_piLo_nonneg : 0 ≤ (r : ℝ) * (piLo : ℝ) := mul_nonneg hr0 hpi_lo_pos.le
    have hs_taylor : (s : ℝ) ≤ Real.sin ((r : ℝ) * (piLo : ℝ)) := by
      have hcast : (s : ℝ) = ((r : ℝ) * (piLo : ℝ)) *
          (1 - ((r : ℝ) * (piLo : ℝ)) ^ 2 *
            (1 / 6 - ((r : ℝ) * (piLo : ℝ)) ^ 2 * (1 / 120 - ((r : ℝ) * (piLo : ℝ)) ^ 2 * (1 / 5040)))) := by
        dsimp only [s, sinPolyQ]; push_cast; ring
      rw [hcast]
      exact sin_taylor_lower hr_piLo_nonneg
    have hsin_mono : Real.sin ((r : ℝ) * (piLo : ℝ)) ≤ Real.sin ((r : ℝ) * Real.pi) := by
      refine Real.sin_le_sin_of_le_of_le_pi_div_two ?_ ?_ (mul_le_mul_of_nonneg_left hpi_lo.le hr0)
      · linarith
      · calc (r : ℝ) * Real.pi ≤ (1 / 2) * Real.pi := mul_le_mul_of_nonneg_right hr_half Real.pi_pos.le
          _ = Real.pi / 2 := by ring
    have hsin_abs : Real.sin ((r : ℝ) * Real.pi) = |Real.sin ((q : ℝ) * Real.pi)| := by
      have hshift : |Real.sin (((q : ℝ) - (k : ℝ)) * Real.pi)| = |Real.sin ((q : ℝ) * Real.pi)| := by
        rw [sub_mul, Real.sin_sub_int_mul_pi, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
      rw [← hshift, hr_cast]
      rcases le_total 0 ((q : ℝ) - (k : ℝ)) with hqk | hqk
      · rw [abs_of_nonneg hqk]
        have hsin0 : 0 ≤ Real.sin (((q : ℝ) - (k : ℝ)) * Real.pi) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg hqk Real.pi_pos.le) (by
            have hle : (q : ℝ) - (k : ℝ) ≤ 1 / 2 := by rwa [← abs_of_nonneg hqk, ← hr_cast]
            nlinarith [Real.pi_pos])
        exact (abs_of_nonneg hsin0).symm
      · rw [abs_of_nonpos hqk, neg_mul, Real.sin_neg]
        have hsin0 : Real.sin (((q : ℝ) - (k : ℝ)) * Real.pi) ≤ 0 :=
          Real.sin_nonpos_of_nonpos_of_neg_pi_le (mul_nonpos_of_nonpos_of_nonneg hqk Real.pi_pos.le) (by
            have hle : -((q : ℝ) - (k : ℝ)) ≤ 1 / 2 := by rwa [← abs_of_nonpos hqk, ← hr_cast]
            nlinarith [Real.pi_pos])
        exact (abs_of_nonpos hsin0).symm
    have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs0
    have hfrac : (s : ℝ) / (d : ℝ) ≤ |Real.sin ((q : ℝ) * Real.pi)| / ((q : ℝ) * Real.pi) := by
      calc (s : ℝ) / (d : ℝ) ≤ |Real.sin ((q : ℝ) * Real.pi)| / (d : ℝ) := by
            apply div_le_div_of_nonneg_right _ hd_pos.le
            exact hsin_abs ▸ hs_taylor.trans hsin_mono
        _ ≤ |Real.sin ((q : ℝ) * Real.pi)| / ((q : ℝ) * Real.pi) :=
            div_le_div_of_nonneg_left (abs_nonneg _) hqpi_pos hqpi_le_d
    calc ((s : ℝ) / (d : ℝ)) ^ 2
        ≤ (|Real.sin ((q : ℝ) * Real.pi)| / ((q : ℝ) * Real.pi)) ^ 2 :=
          pow_le_pow_left₀ (div_nonneg hs_pos.le hd_pos.le) hfrac 2
      _ = (Real.sin ((q : ℝ) * Real.pi) / ((q : ℝ) * Real.pi)) ^ 2 := by
          rw [div_pow, sq_abs, ← div_pow]

noncomputable def bs5 (i : ℕ) : ℝ := (((tentPairs.getD i (0, 0)).1 : ℚ) : ℝ)
noncomputable def lam5 (i : ℕ) : ℝ := (((tentPairs.getD i (0, 0)).2 : ℚ) : ℝ)
noncomputable def ell5 (j : ℕ) : ℝ := ((E_list.getD (j - 1) 0 : ℕ) : ℝ) / (D_ell : ℝ)

lemma foldl_tentPairs_le (j : ℕ) (hj : 1 ≤ j) (ps : List (ℚ × ℚ)) (acc : ℚ)
    (hbs : ∀ p ∈ ps, 0 < p.1) (hlam : ∀ p ∈ ps, 0 ≤ p.2)
    (hpairs : ps.all (fun p => absQ (((8 * j : ℚ) / 3) * p.1 - nearestIntQ (((8 * j : ℚ) / 3) * p.1)) ≤ 1 / 2) = true) :
    ((ps.foldl (fun a p => a + p.2 * sincSqLoQ (((8 * j : ℚ) / 3) * p.1)) acc : ℚ) : ℝ) ≤
      (acc : ℝ) + (ps.map (fun p => (p.2 : ℝ) * (Real.sin (modeFreq j * (p.1 : ℝ)) / (modeFreq j * (p.1 : ℝ))) ^ 2)).sum := by
  induction ps generalizing acc with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hpairs ⊢
    have hp_b : 0 < p.1 := hbs p (by simp)
    have hp_lam : 0 ≤ p.2 := hlam p (by simp)
    have hq_pos : 0 < ((8 * j : ℚ) / 3) * p.1 :=
      mul_pos (div_pos (mul_pos (by norm_num) (by exact_mod_cast (by omega : 0 < j))) (by norm_num)) hp_b
    have hsinc := sincSqLoQ_le hq_pos hpairs.1
    have hfreq : (((((8 * j : ℚ) / 3) * p.1 : ℚ) : ℝ) * Real.pi) = modeFreq j * (p.1 : ℝ) := by
      unfold modeFreq; push_cast; ring
    rw [hfreq] at hsinc
    have hstep : ((acc + p.2 * sincSqLoQ (((8 * j : ℚ) / 3) * p.1) : ℚ) : ℝ) ≤
        (acc : ℝ) + (p.2 : ℝ) * (Real.sin (modeFreq j * (p.1 : ℝ)) / (modeFreq j * (p.1 : ℝ))) ^ 2 := by
      push_cast
      linarith [mul_le_mul_of_nonneg_left hsinc (Rat.cast_nonneg.mpr hp_lam)]
    have hrec := ih (acc + p.2 * sincSqLoQ (((8 * j : ℚ) / 3) * p.1))
      (fun x hx => hbs x (by simp [hx])) (fun x hx => hlam x (by simp [hx])) hpairs.2
    linarith

lemma checkKtildeLoop_sound : ∀ (j : ℕ) (es : List ℕ), 1 ≤ j → checkKtildeLoop j es = true →
    ∀ idx < es.length,
      0 < (((es.getD idx 0 : ℕ) : ℝ) / (D_ell : ℝ)) ∧
      (((es.getD idx 0 : ℕ) : ℝ) / (D_ell : ℝ)) ≤
        ∑ i ∈ Finset.range 5, lam5 i * (Real.sin (modeFreq (j + idx) * bs5 i) / (modeFreq (j + idx) * bs5 i)) ^ 2 := by
  intro j es
  induction es generalizing j with
  | nil => intro _ _ idx hidx; simp at hidx
  | cons e es ih =>
    intro hj hloop idx hidx
    simp only [checkKtildeLoop, Bool.and_eq_true, decide_eq_true_eq] at hloop
    rcases hloop with ⟨⟨⟨hpairs, he0⟩, he_le⟩, htail⟩
    cases idx with
    | zero =>
      simp only [List.getD_cons_zero, Nat.add_zero]
      have hDell : (0 : ℝ) < (D_ell : ℝ) := by unfold D_ell; norm_num
      have he_pos : 0 < ((e : ℝ) / (D_ell : ℝ)) := div_pos (Nat.cast_pos.mpr he0) hDell
      have hbs_pos : ∀ p ∈ tentPairs, 0 < p.1 := by decide +kernel
      have hlam_nn : ∀ p ∈ tentPairs, 0 ≤ p.2 := by decide +kernel
      have hfold := foldl_tentPairs_le j hj tentPairs 0 hbs_pos hlam_nn hpairs
      rw [Rat.cast_zero, zero_add] at hfold
      have hmap_eq : (tentPairs.map (fun p => (p.2 : ℝ) *
          (Real.sin (modeFreq j * (p.1 : ℝ)) / (modeFreq j * (p.1 : ℝ))) ^ 2)).sum =
          ∑ i ∈ Finset.range 5, lam5 i * (Real.sin (modeFreq j * bs5 i) / (modeFreq j * bs5 i)) ^ 2 := by
        simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
        simp only [tentPairs, bs5, lam5, List.getD_cons_zero, List.getD_cons_succ, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        norm_num
        ring
      have he_leR : ((e : ℝ) / (D_ell : ℝ)) ≤
          ((tentPairs.foldl (fun acc ⟨b, lam⟩ => acc + lam * sincSqLoQ (((8 * j : ℚ) / 3) * b)) 0 : ℚ) : ℝ) := by
        have : (((e : ℚ) / D_ell : ℚ) : ℝ) ≤ _ := Rat.cast_le.mpr he_le
        push_cast at this
        exact this
      exact ⟨he_pos, he_leR.trans (hfold.trans_eq hmap_eq)⟩
    | succ k =>
      simp only [List.getD_cons_succ, List.length_cons, Nat.add_lt_add_iff_right] at hidx ⊢
      have := ih (j + 1) (by omega) htail k hidx
      rwa [show j + 1 + k = j + (k + 1) by omega] at this

lemma ell5_ok : ∀ j ∈ Finset.Icc 1 N_modes,
    0 < ell5 j ∧ ell5 j ≤ ∑ i ∈ Finset.range 5, lam5 i * (Real.sin (modeFreq j * bs5 i) / (modeFreq j * bs5 i)) ^ 2 := by
  intro j hj
  rcases Finset.mem_Icc.mp hj with ⟨hj1, hjN⟩
  have hlen : E_list.length = N_modes := by decide
  have h := checkKtildeLoop_sound 1 E_list (le_refl 1) checkKtilde_ok (j - 1) (by omega)
  rwa [show 1 + (j - 1) = j by omega] at h

def addPoly : List ℤ → List ℤ → List ℤ
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x + y) :: addPoly xs ys

def scalePoly (c : ℤ) : List ℤ → List ℤ := List.map (c * ·)

def subPoly : List ℤ → List ℤ → List ℤ
  | [], ys => scalePoly (-1) ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x - y) :: subPoly xs ys

def mul6CosPlus2 (u : List ℤ) : List ℤ :=
  let twoU := scalePoly 2 u
  let up := match u with
    | [] => []
    | u0 :: rest => 0 :: (2 * u0) :: rest
  let down := match u with
    | [] => []
    | _ :: rest => rest
  addPoly twoU (addPoly (scalePoly 3 up) (scalePoly 3 down))

def dotOverlap : List ℤ → List ℤ → ℤ
  | x :: xs, y :: ys => x * y + dotOverlap xs ys
  | _, _ => 0

def fejerGo : ℕ → List ℤ → List ℤ → List ℤ
  | _, _, [] => []
  | d, p, cur@(_ :: rest) =>
    (if d = 0 then dotOverlap p p else 2 * dotOverlap p cur) :: fejerGo (d + 1) p rest

def fejerAll (p : List ℤ) : List ℤ := fejerGo 0 p p

def absPolySum : List ℤ → ℤ
  | [] => 0
  | x :: xs => (if x < 0 then -x else x) + absPolySum xs

def gScaledGo (uPrev uCurr acc : List ℤ) : List ℤ → List ℤ
  | [] => acc
  | aj :: rest =>
    let acc' := addPoly (scalePoly 4 acc) (scalePoly aj uCurr)
    let uNext := addPoly (mul6CosPlus2 uCurr) (scalePoly (-16) uPrev)
    gScaledGo uCurr uNext acc' rest

def gScaledPoly : List ℤ := gScaledGo [1] [1, 3] [] A_list

def checkFejer : Bool :=
  let pow4N : ℤ := (4 : ℤ) ^ N_modes
  let scaleG : ℤ := D_p * D_p
  let scaleF : ℤ := D_a * pow4N
  let scaleMCert : ℤ := (D_a / 10000) * pow4N * D_p * D_p
  let target := subPoly (scalePoly scaleG gScaledPoly) [9997 * scaleMCert]
  let fScaled := scalePoly scaleF (fejerAll P_list)
  let residScaled := absPolySum (subPoly target fScaled)
  1000000 * residScaled ≤ 25 * D_a * pow4N * D_p * D_p

theorem checkFejer_ok : checkFejer = true := by decide +kernel

noncomputable def evalCosShift : ℕ → List ℤ → ℝ → ℝ
  | _, [], _ => 0
  | m, c :: cs, φ => (c : ℝ) * Real.cos ((m : ℝ) * φ) + evalCosShift (m + 1) cs φ

noncomputable def evalSinShift : ℕ → List ℤ → ℝ → ℝ
  | _, [], _ => 0
  | m, c :: cs, φ => (c : ℝ) * Real.sin ((m : ℝ) * φ) + evalSinShift (m + 1) cs φ

lemma evalCosShift_addPoly : ∀ (m : ℕ) (xs ys : List ℤ) (φ : ℝ),
    evalCosShift m (addPoly xs ys) φ = evalCosShift m xs φ + evalCosShift m ys φ
  | _, [], ys, _ => by simp [addPoly, evalCosShift]
  | _, x :: xs, [], _ => by simp [addPoly, evalCosShift]
  | m, x :: xs, y :: ys, φ => by
    simp only [addPoly, evalCosShift, Int.cast_add]
    rw [evalCosShift_addPoly (m + 1) xs ys φ]
    ring

lemma evalCosShift_scalePoly : ∀ (m : ℕ) (c : ℤ) (xs : List ℤ) (φ : ℝ),
    evalCosShift m (scalePoly c xs) φ = (c : ℝ) * evalCosShift m xs φ
  | _, _, [], _ => by simp [scalePoly, evalCosShift]
  | m, c, x :: xs, φ => by
    have hrec := evalCosShift_scalePoly (m + 1) c xs φ
    unfold scalePoly at hrec ⊢
    simp only [List.map_cons, evalCosShift, Int.cast_mul]
    rw [hrec]
    ring

lemma evalCosShift_subPoly : ∀ (m : ℕ) (xs ys : List ℤ) (φ : ℝ),
    evalCosShift m (subPoly xs ys) φ = evalCosShift m xs φ - evalCosShift m ys φ
  | _, [], ys, φ => by
    simp only [subPoly, evalCosShift_scalePoly, evalCosShift, Int.cast_neg, Int.cast_one]
    ring
  | _, x :: xs, [], _ => by simp [subPoly, evalCosShift]
  | m, x :: xs, y :: ys, φ => by
    simp only [subPoly, evalCosShift, Int.cast_sub]
    rw [evalCosShift_subPoly (m + 1) xs ys φ]
    ring

lemma abs_evalCosShift_le : ∀ (m : ℕ) (cs : List ℤ) (φ : ℝ),
    |evalCosShift m cs φ| ≤ (absPolySum cs : ℝ)
  | _, [], _ => by simp [evalCosShift, absPolySum]
  | m, c :: cs, φ => by
    simp only [evalCosShift, absPolySum, Int.cast_add]
    have hrec := abs_evalCosShift_le (m + 1) cs φ
    have hterm : |(c : ℝ) * Real.cos ((m : ℝ) * φ)| ≤ ((if c < 0 then -c else c : ℤ) : ℝ) := by
      rw [abs_mul]
      have h1 := mul_le_of_le_one_right (abs_nonneg (c : ℝ)) (Real.abs_cos_le_one ((m : ℝ) * φ))
      have habs : |(c : ℝ)| = ((if c < 0 then -c else c : ℤ) : ℝ) := by
        split_ifs with hc
        · rw [Int.cast_neg, abs_of_neg (Int.cast_lt_zero.mpr hc)]
        · rw [abs_of_nonneg (Int.cast_nonneg (not_lt.mp hc))]
      rw [← habs]
      exact h1
    exact (abs_add_le _ _).trans (add_le_add hterm hrec)

lemma two_cos_mul_evalCosShift : ∀ (m : ℕ) (_hm : 1 ≤ m) (cs : List ℤ) (φ : ℝ),
    2 * Real.cos φ * evalCosShift m cs φ = evalCosShift (m + 1) cs φ + evalCosShift (m - 1) cs φ
  | _, _, [], _ => by simp [evalCosShift]
  | m, hm, c :: cs, φ => by
    simp only [evalCosShift]
    have hrec := two_cos_mul_evalCosShift (m + 1) (by omega) cs φ
    rw [show m + 1 - 1 = m by omega] at hrec
    rw [show m - 1 + 1 = m by omega]
    have htrig : 2 * Real.cos φ * Real.cos ((m : ℝ) * φ) =
        Real.cos (((m + 1 : ℕ) : ℝ) * φ) + Real.cos (((m - 1 : ℕ) : ℝ) * φ) := by
      have hm1 : ((m + 1 : ℕ) : ℝ) * φ = (m : ℝ) * φ + φ := by push_cast; ring
      have hm2 : ((m - 1 : ℕ) : ℝ) * φ = (m : ℝ) * φ - φ := by
        have hnat : (m : ℝ) = ((m - 1 : ℕ) : ℝ) + 1 := by exact_mod_cast (by omega : m = m - 1 + 1)
        rw [hnat]; ring
      rw [hm1, hm2, Real.cos_add, Real.cos_sub]
      ring
    linear_combination (c : ℝ) * htrig + hrec

lemma evalCosShift_mul6CosPlus2 (u : List ℤ) (φ : ℝ) :
    evalCosShift 0 (mul6CosPlus2 u) φ = (2 + 6 * Real.cos φ) * evalCosShift 0 u φ := by
  cases u with
  | nil => simp [mul6CosPlus2, addPoly, scalePoly, evalCosShift]
  | cons u0 rest =>
    simp only [mul6CosPlus2, evalCosShift_addPoly, evalCosShift_scalePoly]
    have hup : evalCosShift 0 (0 :: (2 * u0) :: rest) φ =
        2 * (u0 : ℝ) * Real.cos φ + evalCosShift 2 rest φ := by
      simp [evalCosShift]
    have h2 : 2 * Real.cos φ * evalCosShift 1 rest φ =
        evalCosShift 2 rest φ + evalCosShift 0 rest φ := by
      simpa using two_cos_mul_evalCosShift 1 (le_refl 1) rest φ
    rw [hup]
    simp only [evalCosShift, Nat.cast_zero, zero_mul, Real.cos_zero, mul_one, zero_add]
    push_cast
    linear_combination -3 * h2

lemma fejerGo_pos : ∀ (d : ℕ), 1 ≤ d → ∀ (p cur : List ℤ),
    fejerGo d p cur = fejerGo 1 p cur
  | _, _, _, [] => rfl
  | d, hd, p, q :: qs => by
    simp only [fejerGo, if_neg (by omega : d ≠ 0), if_neg (by omega : (1 : ℕ) ≠ 0)]
    congr 1
    rw [fejerGo_pos (d + 1) (by omega) p qs, fejerGo_pos (1 + 1) (by omega) p qs]

lemma fejerGo_one_cons : ∀ (p0 : ℤ) (ps cur : List ℤ),
    fejerGo 1 (p0 :: ps) cur = addPoly (scalePoly (2 * p0) cur) (fejerGo 1 ps (cur.drop 1))
  | _, _, [] => by simp [fejerGo, scalePoly, addPoly]
  | p0, ps, q :: qs => by
    simp only [fejerGo, if_neg (by omega : (1 : ℕ) ≠ 0), dotOverlap, scalePoly, List.map_cons,
      List.drop_succ_cons, List.drop_zero]
    rw [fejerGo_pos 2 (by omega), fejerGo_one_cons p0 ps qs]
    cases qs with
    | nil =>
      have hdot : dotOverlap ps [] = 0 := by cases ps <;> rfl
      simp [fejerGo, addPoly, scalePoly, hdot]
      ring
    | cons q' qs' =>
      simp only [fejerGo, if_neg (by omega : (1 : ℕ) ≠ 0), addPoly, List.drop_succ_cons,
        List.drop_zero, List.cons.injEq]
      refine ⟨by ring, ?_⟩
      change addPoly (scalePoly (2 * p0) (q' :: qs')) (fejerGo 1 ps qs') =
        addPoly (scalePoly (2 * p0) (q' :: qs')) (fejerGo (1 + 1) ps qs')
      rw [fejerGo_pos (1 + 1) (by omega)]

lemma fejerAll_cons (p0 : ℤ) (ps : List ℤ) :
    fejerAll (p0 :: ps) = addPoly (p0 * p0 :: scalePoly (2 * p0) ps) (fejerAll ps) := by
  cases ps with
  | nil => simp [fejerAll, fejerGo, dotOverlap, scalePoly, addPoly]
  | cons q qs =>
    change dotOverlap (p0 :: q :: qs) (p0 :: q :: qs) :: fejerGo 1 (p0 :: q :: qs) (q :: qs) =
      addPoly (p0 * p0 :: scalePoly (2 * p0) (q :: qs))
        (dotOverlap (q :: qs) (q :: qs) :: fejerGo 1 (q :: qs) qs)
    simp only [dotOverlap, addPoly, List.cons.injEq]
    exact ⟨trivial, fejerGo_one_cons p0 (q :: qs) (q :: qs)⟩

lemma evalCosShift_succ : ∀ (m : ℕ) (cs : List ℤ) (φ : ℝ),
    evalCosShift (m + 1) cs φ = Real.cos φ * evalCosShift m cs φ - Real.sin φ * evalSinShift m cs φ
  | _, [], _ => by simp [evalCosShift, evalSinShift]
  | m, c :: cs, φ => by
    simp only [evalCosShift, evalSinShift]
    have hrec := evalCosShift_succ (m + 1) cs φ
    have htrig : Real.cos (((m + 1 : ℕ) : ℝ) * φ) =
        Real.cos φ * Real.cos ((m : ℝ) * φ) - Real.sin φ * Real.sin ((m : ℝ) * φ) := by
      have hm : ((m + 1 : ℕ) : ℝ) * φ = (m : ℝ) * φ + φ := by push_cast; ring
      rw [hm, Real.cos_add]; ring
    linear_combination (c : ℝ) * htrig + hrec

lemma evalSinShift_succ : ∀ (m : ℕ) (cs : List ℤ) (φ : ℝ),
    evalSinShift (m + 1) cs φ = Real.sin φ * evalCosShift m cs φ + Real.cos φ * evalSinShift m cs φ
  | _, [], _ => by simp [evalCosShift, evalSinShift]
  | m, c :: cs, φ => by
    simp only [evalCosShift, evalSinShift]
    have hrec := evalSinShift_succ (m + 1) cs φ
    have htrig : Real.sin (((m + 1 : ℕ) : ℝ) * φ) =
        Real.sin φ * Real.cos ((m : ℝ) * φ) + Real.cos φ * Real.sin ((m : ℝ) * φ) := by
      have hm : ((m + 1 : ℕ) : ℝ) * φ = (m : ℝ) * φ + φ := by push_cast; ring
      rw [hm, Real.sin_add]; ring
    linear_combination (c : ℝ) * htrig + hrec

lemma evalCosShift_sq_add_sin_sq (ps : List ℤ) (φ : ℝ) :
    evalCosShift 1 ps φ ^ 2 + evalSinShift 1 ps φ ^ 2 =
      evalCosShift 0 ps φ ^ 2 + evalSinShift 0 ps φ ^ 2 := by
  rw [evalCosShift_succ 0 ps φ, evalSinShift_succ 0 ps φ]
  have h1 := Real.cos_sq_add_sin_sq φ
  linear_combination (evalCosShift 0 ps φ ^ 2 + evalSinShift 0 ps φ ^ 2) * h1

lemma evalCosShift_fejerAll : ∀ (p : List ℤ) (φ : ℝ),
    evalCosShift 0 (fejerAll p) φ = evalCosShift 0 p φ ^ 2 + evalSinShift 0 p φ ^ 2
  | [], _ => by simp [fejerAll, fejerGo, evalCosShift, evalSinShift]
  | p0 :: ps, φ => by
    rw [fejerAll_cons, evalCosShift_addPoly, evalCosShift_fejerAll ps φ]
    simp only [evalCosShift, evalSinShift, Int.cast_mul, Nat.cast_zero, zero_mul,
      Real.cos_zero, Real.sin_zero, mul_one, mul_zero, zero_add]
    rw [evalCosShift_scalePoly]
    have hsq := evalCosShift_sq_add_sin_sq ps φ
    push_cast
    linarith

noncomputable def evalCosModes : ℕ → List ℤ → ℝ → ℝ
  | _, [], _ => 0
  | j, a :: as, θ => (a : ℝ) * Real.cos ((j : ℝ) * θ) + evalCosModes (j + 1) as θ

lemma evalCosShift_gScaledGo (θ φ : ℝ) (hcos : Real.cos θ = (1 + 3 * Real.cos φ) / 4) :
    ∀ (rest : List ℤ) (j : ℕ), 1 ≤ j → ∀ (uPrev uCurr acc : List ℤ),
      evalCosShift 0 uPrev φ = (4 : ℝ) ^ (j - 1) * Real.cos (((j - 1 : ℕ) : ℝ) * θ) →
      evalCosShift 0 uCurr φ = (4 : ℝ) ^ j * Real.cos ((j : ℝ) * θ) →
      evalCosShift 0 (gScaledGo uPrev uCurr acc rest) φ =
        (4 : ℝ) ^ rest.length * evalCosShift 0 acc φ +
          (4 : ℝ) ^ (j + rest.length - 1) * evalCosModes j rest θ
  | [], j, _, _, _, _, _, _ => by simp [gScaledGo, evalCosModes]
  | aj :: rest, j, hj, uPrev, uCurr, acc, hu0, hu1 => by
    simp only [gScaledGo, List.length_cons]
    have huNext : evalCosShift 0 (addPoly (mul6CosPlus2 uCurr) (scalePoly (-16) uPrev)) φ =
        (4 : ℝ) ^ (j + 1) * Real.cos (((j + 1 : ℕ) : ℝ) * θ) := by
      rw [evalCosShift_addPoly, evalCosShift_mul6CosPlus2, evalCosShift_scalePoly, hu0, hu1]
      have hcos_eq : 2 + 6 * Real.cos φ = 8 * Real.cos θ := by linarith
      have htrig : 2 * Real.cos θ * Real.cos ((j : ℝ) * θ) - Real.cos (((j - 1 : ℕ) : ℝ) * θ) =
          Real.cos (((j + 1 : ℕ) : ℝ) * θ) := by
        have hp1 : ((j + 1 : ℕ) : ℝ) * θ = (j : ℝ) * θ + θ := by push_cast; ring
        have hm1 : ((j - 1 : ℕ) : ℝ) * θ = (j : ℝ) * θ - θ := by
          have hj_eq : (j : ℝ) = ((j - 1 : ℕ) : ℝ) + 1 := by exact_mod_cast (by omega : j = j - 1 + 1)
          rw [hj_eq]; ring
        rw [hp1, hm1, Real.cos_add, Real.cos_sub]; ring
      have hj_pow : (4 : ℝ) ^ j = 4 * (4 : ℝ) ^ (j - 1) := by
        conv_lhs => rw [show j = j - 1 + 1 by omega, pow_succ']
      rw [hcos_eq, ← htrig]
      push_cast
      rw [pow_succ', hj_pow]
      ring
    have hrec := evalCosShift_gScaledGo θ φ hcos rest (j + 1) (by omega) uCurr
      (addPoly (mul6CosPlus2 uCurr) (scalePoly (-16) uPrev))
      (addPoly (scalePoly 4 acc) (scalePoly aj uCurr))
      (by simpa using hu1) huNext
    rw [hrec, evalCosShift_addPoly, evalCosShift_scalePoly, evalCosShift_scalePoly, hu1]
    simp only [evalCosModes]
    push_cast
    have hpow1 : (4 : ℝ) ^ (j + rest.length) = (4 : ℝ) ^ rest.length * (4 : ℝ) ^ j := by
      rw [← pow_add, add_comm]
    have hpow2 : j + 1 + rest.length - 1 = j + rest.length := by omega
    have hpow3 : j + (rest.length + 1) - 1 = j + rest.length := by omega
    rw [hpow2, hpow3, hpow1, pow_succ']
    ring

lemma evalCosModes_eq_sum : ∀ (j : ℕ) (xs : List ℤ) (θ : ℝ),
    evalCosModes j xs θ = ∑ k ∈ Finset.range xs.length,
      ((xs.getD k 0 : ℤ) : ℝ) * Real.cos (((j + k : ℕ) : ℝ) * θ)
  | _, [], _ => by simp [evalCosModes]
  | j, x :: xs, θ => by
    simp only [evalCosModes, List.length_cons, Finset.sum_range_succ',
      List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero]
    rw [evalCosModes_eq_sum (j + 1) xs θ]
    have hshift : (∑ k ∈ Finset.range xs.length, ((xs.getD k 0 : ℤ) : ℝ) *
        Real.cos (((j + 1 + k : ℕ) : ℝ) * θ)) =
        ∑ k ∈ Finset.range xs.length, ((xs.getD k 0 : ℤ) : ℝ) *
          Real.cos (((j + (k + 1) : ℕ) : ℝ) * θ) := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [show j + 1 + k = j + (k + 1) by omega]
    rw [hshift]
    ring

noncomputable def a5 (j : ℕ) : ℝ := ((A_list.getD (j - 1) 0 : ℤ) : ℝ) / (D_a : ℝ)

lemma G_lower_bound : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 4),
    (999675 / 1000000 : ℝ) ≤ ∑ j ∈ Finset.Icc 1 N_modes, a5 j * Real.cos (modeFreq j * x) := by
  intro x hx
  let θ : ℝ := 8 * Real.pi * x / 3
  have hθ0 : 0 ≤ θ := by dsimp [θ]; nlinarith [hx.1, Real.pi_pos]
  have hθpi : θ ≤ 2 * Real.pi / 3 := by dsimp [θ]; nlinarith [hx.2, Real.pi_pos]
  have hcos23 : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
    ring
  have hcos_lo : -1 / 2 ≤ Real.cos θ := by
    rw [← hcos23]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hθ0 (by linarith [Real.pi_pos]) hθpi
  have hcos_hi : Real.cos θ ≤ 1 := Real.cos_le_one θ
  let y : ℝ := (4 * Real.cos θ - 1) / 3
  have hy_lo : -1 ≤ y := by dsimp [y]; linarith
  have hy_hi : y ≤ 1 := by dsimp [y]; linarith
  let φ : ℝ := Real.arccos y
  have hφ : Real.cos φ = y := Real.cos_arccos hy_lo hy_hi
  have hcos : Real.cos θ = (1 + 3 * Real.cos φ) / 4 := by dsimp [y] at hφ; linarith
  have hg := evalCosShift_gScaledGo θ φ hcos A_list 1 (le_refl 1) [1] [1, 3] []
    (by simp [evalCosShift]) (by simp [evalCosShift]; linarith)
  have hlenA : A_list.length = N_modes := by decide
  have hg_val : evalCosShift 0 gScaledPoly φ =
      (4 : ℝ) ^ N_modes * (D_a : ℝ) * ∑ j ∈ Finset.Icc 1 N_modes, a5 j * Real.cos (modeFreq j * x) := by
    change evalCosShift 0 (gScaledGo [1] [1, 3] [] A_list) φ = _
    rw [hg, hlenA, evalCosShift, mul_zero, zero_add, evalCosModes_eq_sum, hlenA]
    have hsum_eq : (∑ k ∈ Finset.range N_modes,
        ((A_list.getD k 0 : ℤ) : ℝ) * Real.cos (((1 + k : ℕ) : ℝ) * θ)) =
        (D_a : ℝ) * ∑ j ∈ Finset.Icc 1 N_modes, a5 j * Real.cos (modeFreq j * x) := by
      rw [Finset.mul_sum]
      refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
      · intro k hk; rw [Finset.mem_Icc]; rw [Finset.mem_range] at hk; omega
      · intro k1 _ k2 _ h; omega
      · intro j hj; rw [Finset.mem_Icc] at hj
        exact ⟨j - 1, Finset.mem_range.mpr (by omega), by omega⟩
      · intro k _
        have hfreq : (((1 + k : ℕ) : ℝ) * θ) = modeFreq (k + 1) * x := by
          dsimp [θ, modeFreq]; push_cast; ring
        have hDa : (D_a : ℝ) ≠ 0 := by unfold D_a; norm_num
        simp only [a5, Nat.add_sub_cancel, hfreq]
        field_simp
    rw [hsum_eq, show 1 + N_modes - 1 = N_modes by omega]
    ring
  have hchk := checkFejer_ok
  unfold checkFejer at hchk
  simp only [decide_eq_true_eq] at hchk
  let pow4N : ℤ := (4 : ℤ) ^ N_modes
  let scaleG : ℤ := D_p * D_p
  let scaleF : ℤ := D_a * pow4N
  let scaleMCert : ℤ := (D_a / 10000) * pow4N * D_p * D_p
  let target := subPoly (scalePoly scaleG gScaledPoly) [9997 * scaleMCert]
  let fScaled := scalePoly scaleF (fejerAll P_list)
  let resid := subPoly target fScaled
  have hchkR : (1000000 : ℝ) * (absPolySum resid : ℝ) ≤ (25 * D_a * pow4N * D_p * D_p : ℝ) := by
    have h1 : ((1000000 * absPolySum resid : ℤ) : ℝ) ≤ ((25 * D_a * pow4N * D_p * D_p : ℤ) : ℝ) :=
      Int.cast_le.mpr hchk
    push_cast at h1
    exact h1
  have hres_le : -(absPolySum resid : ℝ) ≤ evalCosShift 0 resid φ :=
    (abs_le.mp (abs_evalCosShift_le 0 resid φ)).1
  have hres_eq : evalCosShift 0 resid φ =
      (scaleG : ℝ) * evalCosShift 0 gScaledPoly φ - (9997 * scaleMCert : ℝ) -
        (scaleF : ℝ) * evalCosShift 0 (fejerAll P_list) φ := by
    simp only [resid, target, fScaled, evalCosShift_subPoly, evalCosShift_scalePoly]
    simp only [evalCosShift, Nat.cast_zero, zero_mul, Real.cos_zero, mul_one, add_zero]
    push_cast
    ring
  have hfejer_nn : 0 ≤ evalCosShift 0 (fejerAll P_list) φ := by
    rw [evalCosShift_fejerAll]
    exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hscaleF_nn : 0 ≤ (scaleF : ℝ) := by
    dsimp only [scaleF, pow4N]; push_cast; unfold D_a; positivity
  have hcomb : (9997 * scaleMCert : ℝ) - (absPolySum resid : ℝ) ≤
      (scaleG : ℝ) * evalCosShift 0 gScaledPoly φ := by
    have hmul_nn := mul_nonneg hscaleF_nn hfejer_nn
    linarith [hres_le, hres_eq, hmul_nn]
  rw [hg_val] at hcomb
  have hden : (0 : ℝ) < (D_p : ℝ) ^ 2 * (4 : ℝ) ^ N_modes * (D_a : ℝ) := by
    unfold D_p D_a; positivity
  have hDa_div : ((D_a / 10000 : ℤ) : ℝ) = (D_a : ℝ) / 10000 := by unfold D_a; norm_num
  have hnum_check : ((D_p : ℝ) ^ 2 * (4 : ℝ) ^ N_modes * (D_a : ℝ)) * (999675 / 1000000 : ℝ) =
      (9997 * scaleMCert : ℝ) - (25 * D_a * pow4N * D_p * D_p : ℝ) / 1000000 := by
    dsimp only [scaleMCert, pow4N]
    push_cast
    rw [hDa_div]
    ring
  have hsg : (scaleG : ℝ) * ((4 : ℝ) ^ N_modes * (D_a : ℝ) *
      ∑ j ∈ Finset.Icc 1 N_modes, a5 j * Real.cos (modeFreq j * x)) =
      ((D_p : ℝ) ^ 2 * (4 : ℝ) ^ N_modes * (D_a : ℝ)) *
        ∑ j ∈ Finset.Icc 1 N_modes, a5 j * Real.cos (modeFreq j * x) := by
    dsimp [scaleG]; push_cast; ring
  rw [hsg] at hcomb
  have hfinal : ((D_p : ℝ) ^ 2 * (4 : ℝ) ^ N_modes * (D_a : ℝ)) * (999675 / 1000000 : ℝ) ≤
      ((D_p : ℝ) ^ 2 * (4 : ℝ) ^ N_modes * (D_a : ℝ)) *
        ∑ j ∈ Finset.Icc 1 N_modes, a5 j * Real.cos (modeFreq j * x) := by
    linarith [hcomb, hchkR, hnum_check]
  exact le_of_mul_le_mul_left hfinal hden

lemma tent_inner_symm {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t, tent a t * tent b t) =
      if a ≤ b then (1 / (2 * b)) * (1 - a / (3 * b)) else (1 / (2 * a)) * (1 - b / (3 * a)) := by
  split_ifs with h
  · exact tent_inner ha h
  · have hba : b ≤ a := le_of_not_ge h
    rw [show (fun t => tent a t * tent b t) = fun t => tent b t * tent a t by ext t; ring]
    exact tent_inner hb hba

lemma integral_tentMix5_sq : ∫ t, tentMix 5 bs5 lam5 t ^ 2 = 731120377 / 200000000 := by
  have hbs0 : ∀ i < 5, 0 < bs5 i := by
    intro i hi; interval_cases i <;> norm_num [tentPairs, bs5]
  have hint : ∀ i < 5, ∀ j < 5, Integrable (fun t => tent (bs5 i) t * tent (bs5 j) t) := by
    intro i hi j hj
    have hj0 : 0 < bs5 j := hbs0 j hj
    refine (tent_integrable (hbs0 i hi)).mul_bdd
      (tent_continuous (bs5 j)).measurable.aestronglyMeasurable
      (ae_of_all _ (fun t => by
        rw [Real.norm_of_nonneg (tent_nonneg hj0 t)]
        unfold tent
        have h1 : max 0 (1 - |t| / (2 * bs5 j)) ≤ 1 := max_le zero_le_one (by
          have : 0 ≤ |t| / (2 * bs5 j) := by positivity
          linarith)
        calc (1 / (2 * bs5 j)) * max 0 (1 - |t| / (2 * bs5 j))
            ≤ (1 / (2 * bs5 j)) * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = 1 / (2 * bs5 j) := mul_one _))
  have hpt : (fun t => tentMix 5 bs5 lam5 t ^ 2) = fun t =>
      ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (lam5 i * lam5 j) * (tent (bs5 i) t * tent (bs5 j) t) := by
    ext t; rw [sq]; simp only [tentMix, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  rw [hpt, integral_finsetSum _ (fun i hi =>
    integrable_finsetSum _ (fun j hj =>
      (hint i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)).const_mul _))]
  have hsum_in : ∀ i ∈ Finset.range 5,
      (∫ t, ∑ j ∈ Finset.range 5, (lam5 i * lam5 j) * (tent (bs5 i) t * tent (bs5 j) t)) =
      ∑ j ∈ Finset.range 5, (lam5 i * lam5 j) * ∫ t, tent (bs5 i) t * tent (bs5 j) t := by
    intro i hi
    rw [integral_finsetSum _ (fun j hj =>
      (hint i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)).const_mul _)]
    refine Finset.sum_congr rfl (fun j _ => integral_const_mul _ _)
  rw [Finset.sum_congr rfl hsum_in]
  have hval : ∀ i ∈ Finset.range 5, ∀ j ∈ Finset.range 5,
      ∫ t, tent (bs5 i) t * tent (bs5 j) t =
        if bs5 i ≤ bs5 j then (1 / (2 * bs5 j)) * (1 - bs5 i / (3 * bs5 j))
        else (1 / (2 * bs5 i)) * (1 - bs5 j / (3 * bs5 i)) := fun i hi j hj =>
    tent_inner_symm (hbs0 i (Finset.mem_range.mp hi)) (hbs0 j (Finset.mem_range.mp hj))
  simp_rw [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  repeat rw [tent_inner_symm (by norm_num [tentPairs, bs5]) (by norm_num [tentPairs, bs5])]
  norm_num [tentPairs, bs5, lam5]

def S1_up_Q : ℚ :=
  ((A_list.zip E_list).map (fun p => ((p.1 : ℚ) / D_a) ^ 2 / ((p.2 : ℚ) / D_ell))).sum

def K2_Q : ℚ := 731120377 / 200000000
def mG_lo_Q : ℚ := 999675 / 1000000
def tau_Q : ℚ := 8 / 3 + (16 / 3) * (mG_lo_Q ^ 2 / S1_up_Q)

theorem cert_ineq1 : (0 : ℚ) < S1_up_Q := by decide +kernel
theorem cert_ineq2 : (13 / 10 : ℚ) + 1 < tau_Q := by decide +kernel
theorem cert_ineq3 : ((13 / 10 : ℚ) - 1) * (K2_Q - 1) < (tau_Q - ((13 / 10 : ℚ) + 1)) ^ 2 := by
  decide +kernel

lemma zip_sum_eq : ∀ (as : List ℤ) (es : List ℕ), as.length = es.length →
    ∑ k ∈ Finset.range as.length,
      (((as.getD k 0 : ℤ) : ℝ) / (D_a : ℝ)) ^ 2 / (((es.getD k 0 : ℕ) : ℝ) / (D_ell : ℝ)) =
    (((as.zip es).map (fun p => ((p.1 : ℚ) / D_a) ^ 2 / ((p.2 : ℚ) / D_ell))).sum : ℝ)
  | [], [], _ => by simp
  | a :: as, e :: es, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [List.length_cons, Finset.sum_range_succ', List.getD_cons_zero,
      List.getD_cons_succ, List.zip_cons_cons, List.map_cons, List.sum_cons, Rat.cast_add]
    rw [zip_sum_eq as es h]
    push_cast
    ring

theorem C1a_ge_13_div_10 : (13 / 10 : ℝ) ≤ Constant1a.C1a := by
  refine C1a_ge_of_normalized_bound (by norm_num) ?_
  intro h hh_meas hh0 hh_supp hh_l2 hh_int hh_one M_sup hM_bdd
  have hbs0 : ∀ i < 5, 0 < bs5 i := fun i hi => by interval_cases i <;> norm_num [tentPairs, bs5]
  have hbs8 : ∀ i < 5, bs5 i ≤ 1 / 8 := fun i hi => by interval_cases i <;> norm_num [tentPairs, bs5]
  have hlam0 : ∀ i < 5, 0 ≤ lam5 i := fun i hi => by interval_cases i <;> norm_num [tentPairs, lam5]
  have hlam1 : ∑ i ∈ Finset.range 5, lam5 i = 1 := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
    norm_num [tentPairs, lam5]
  have hS1_eq : (∑ j ∈ Finset.Icc 1 N_modes, a5 j ^ 2 / ell5 j) = (S1_up_Q : ℝ) := by
    have hlenA : A_list.length = N_modes := by decide
    have hlenE : E_list.length = N_modes := by decide
    have hbij : (∑ j ∈ Finset.Icc 1 N_modes, a5 j ^ 2 / ell5 j) =
        ∑ k ∈ Finset.range A_list.length,
          (((A_list.getD k 0 : ℤ) : ℝ) / (D_a : ℝ)) ^ 2 /
            (((E_list.getD k 0 : ℕ) : ℝ) / (D_ell : ℝ)) := by
      refine Finset.sum_bij (fun j _ => j - 1) ?_ ?_ ?_ ?_
      · intro j hj; rw [Finset.mem_Icc] at hj; rw [Finset.mem_range]; omega
      · intro j1 hj1 j2 hj2 h; rw [Finset.mem_Icc] at hj1 hj2; omega
      · intro k hk; rw [Finset.mem_range] at hk
        exact ⟨k + 1, Finset.mem_Icc.mpr (by omega), by omega⟩
      · intro j _; simp [a5, ell5]
    rw [hbij, zip_sum_eq A_list E_list (hlenA.trans hlenE.symm)]
    rfl
  have hS1_pos : (0 : ℝ) < (S1_up_Q : ℝ) := by exact_mod_cast cert_ineq1
  have hlt : (13 / 10 : ℝ) + 1 < 8 / 3 + (16 / 3) * ((999675 / 1000000 : ℝ) ^ 2 / (S1_up_Q : ℝ)) := by
    have := Rat.cast_lt (K := ℝ).mpr cert_ineq2
    push_cast [tau_Q, mG_lo_Q] at this
    exact this
  have hsq : ((13 / 10 : ℝ) - 1) * ((∫ t, tentMix 5 bs5 lam5 t ^ 2) - 1) <
      ((8 / 3 + (16 / 3) * ((999675 / 1000000 : ℝ) ^ 2 / (S1_up_Q : ℝ))) - ((13 / 10 : ℝ) + 1)) ^ 2 := by
    rw [integral_tentMix5_sq]
    have := Rat.cast_lt (K := ℝ).mpr cert_ineq3
    push_cast [K2_Q, tau_Q, mG_lo_Q] at this
    exact this
  exact master_inequality hh_meas hh0 hh_supp hh_l2 hh_int hh_one hbs0 hbs8 hlam0 hlam1
    (fun j hj => (ell5_ok j hj).1) (fun j hj => (ell5_ok j hj).2)
    (by norm_num) G_lower_bound hS1_eq.le hS1_pos hM_bdd hlt hsq

end C1aLower

noncomputable def OMA.answer : ℝ := 13 / 10

theorem OMA.solution :
    Constant1a.mem_Ioc_c1a.answer = OMA.answer → type_of% @Constant1a.mem_Ioc_c1a := by
  intro h
  rw [h]
  exact ⟨by norm_num [OMA.answer], C1aLower.C1a_ge_13_div_10⟩
