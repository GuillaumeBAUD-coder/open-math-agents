import FormalConjectures.Books.BugeaudDistributionModuloOne.Problem10_61
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

open Complex MeasureTheory Filter Topology Finset intervalIntegral
open scoped Interval

noncomputable def OMA.centeredInd (a b x : ℝ) : ℝ :=
  (if Int.fract x ∈ Set.Ico a b then (1 : ℝ) else 0) - (b - a)

lemma OMA.centeredInd_periodic (a b : ℝ) : Function.Periodic (OMA.centeredInd a b) 1 := by
  intro x
  simp [OMA.centeredInd]

lemma OMA.abs_centeredInd_le_one {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (x : ℝ) :
    |OMA.centeredInd a b x| ≤ 1 := by
  unfold OMA.centeredInd
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

lemma OMA.measurable_centeredInd (a b : ℝ) : Measurable (OMA.centeredInd a b) := by
  unfold OMA.centeredInd
  refine Measurable.sub ?_ measurable_const
  exact Measurable.ite (measurable_fract measurableSet_Ico) measurable_const measurable_const

noncomputable def OMA.weylTerm (α : ℝ) (h : ℕ) (ξ : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (h : ℝ) * ξ * α ^ (n + 1))

noncomputable def OMA.weylMean (α : ℝ) (h : ℕ) (ξ : ℝ) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, OMA.weylTerm α h ξ n

lemma OMA.weylTerm_norm (α : ℝ) (h : ℕ) (ξ : ℝ) (n : ℕ) :
    ‖OMA.weylTerm α h ξ n‖ = 1 := by
  unfold OMA.weylTerm
  have harg :
      (2 * Real.pi * Complex.I * (h : ℝ) * ξ * α ^ (n + 1) : ℂ) =
        ((2 * Real.pi * (h : ℝ) * ξ * α ^ (n + 1) : ℝ) : ℂ) * Complex.I := by
    simp [mul_assoc, mul_left_comm, mul_comm]
  rw [harg]
  exact Complex.norm_exp_ofReal_mul_I _

lemma OMA.weylTerm_norm_le (α : ℝ) (h : ℕ) (ξ : ℝ) (n : ℕ) :
    ‖OMA.weylTerm α h ξ n‖ ≤ 1 :=
  (OMA.weylTerm_norm α h ξ n).le

lemma OMA.alpha_pow_diff_ge (α : ℝ) (hα : 1 < α) {n m : ℕ} (hnm : n < m) :
    (α - 1) * α ^ m ≤ α ^ (m + 1) - α ^ (n + 1) := by
  have hα0 : (0 : ℝ) < α := zero_lt_one.trans hα
  have hnm' : n + 1 ≤ m := Nat.succ_le_of_lt hnm
  have hle : α ^ (n + 1) ≤ α ^ m :=
    pow_le_pow_right₀ (le_of_lt hα) hnm'
  calc
    (α - 1) * α ^ m = α ^ (m + 1) - α ^ m := by ring
    _ ≤ α ^ (m + 1) - α ^ (n + 1) := by gcongr

lemma OMA.alpha_pow_diff_pos (α : ℝ) (hα : 1 < α) {n m : ℕ} (hnm : n < m) :
    0 < α ^ (m + 1) - α ^ (n + 1) := by
  have hα0 : (0 : ℝ) < α := zero_lt_one.trans hα
  have hpos : 0 < (α - 1) * α ^ m :=
    mul_pos (sub_pos.mpr hα) (pow_pos hα0 m)
  exact hpos.trans_le (OMA.alpha_pow_diff_ge α hα hnm)

lemma OMA.summable_nat_div_alpha_pow (α : ℝ) (hα : 1 < α) :
    Summable fun m : ℕ => (m : ℝ) / α ^ m := by
  have hα0 : (0 : ℝ) < α := zero_lt_one.trans hα
  have hr : ‖(α⁻¹ : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hα0)]
    exact inv_lt_one_of_one_lt₀ hα
  simpa [pow_one, div_eq_mul_inv, inv_pow] using
    (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr)

lemma OMA.cexp_two_pi_I_mul_eq (t : ℝ) :
    (2 * Real.pi * Complex.I * t : ℂ) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by
  simp [mul_left_comm, mul_comm]

lemma OMA.norm_cexp_two_pi_I_mul (t : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * t)‖ = 1 := by
  rw [OMA.cexp_two_pi_I_mul_eq, Complex.norm_exp_ofReal_mul_I]

lemma OMA.norm_cexp_two_pi_I_mul_real (lam x : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * lam * x)‖ = 1 := by
  rw [mul_assoc (2 * Real.pi * Complex.I), ← Complex.ofReal_mul]
  exact OMA.norm_cexp_two_pi_I_mul (lam * x)

lemma OMA.interval_integral_exp_eq (lam : ℝ) (a : ℝ) (hlam : lam ≠ 0) :
    (∫ x in a..(a + 1), Complex.exp (2 * Real.pi * Complex.I * lam * x)) =
      (Complex.exp (2 * Real.pi * Complex.I * lam * (a + 1)) -
        Complex.exp (2 * Real.pi * Complex.I * lam * a)) /
        (2 * Real.pi * Complex.I * lam) := by
  have hc : (2 * Real.pi * Complex.I * lam : ℂ) ≠ 0 := by
    simp [Complex.I_ne_zero, Real.pi_ne_zero, hlam]
  have hfun :
      (fun x : ℝ => Complex.exp (2 * Real.pi * Complex.I * lam * x)) =
        fun x : ℝ => Complex.exp ((2 * Real.pi * Complex.I * lam) * x) := by
    funext x
    ring
  rw [hfun, integral_exp_mul_complex hc]
  simp [mul_assoc]

lemma OMA.interval_integral_exp_bound (lam : ℝ) (a : ℝ) :
    ‖∫ x in a..(a + 1), Complex.exp (2 * Real.pi * Complex.I * lam * x)‖ ≤ 1 := by
  have hnorm : ∀ x ∈ Set.uIoc a (a + 1),
      ‖Complex.exp (2 * Real.pi * Complex.I * lam * x)‖ ≤ 1 := by
    intro x hx
    exact (OMA.norm_cexp_two_pi_I_mul_real lam x).le
  have := intervalIntegral.norm_integral_le_of_norm_le_const hnorm
  simpa [abs_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)] using this

lemma OMA.off_diag_lambda_ge (α : ℝ) (hα : 1 < α) (h : ℕ) (hh : 0 < h)
    {n m : ℕ} (hnm : n < m) :
    (h : ℝ) * (α - 1) * α ^ m ≤ |(h : ℝ) * (α ^ (n + 1) - α ^ (m + 1))| := by
  have hdiff := OMA.alpha_pow_diff_ge α hα hnm
  have hpos := OMA.alpha_pow_diff_pos α hα hnm
  have hh0 : (0 : ℝ) < h := Nat.cast_pos.mpr hh
  have hneg : α ^ (n + 1) - α ^ (m + 1) < 0 := by linarith
  rw [abs_mul, abs_of_pos hh0, abs_of_neg hneg, neg_sub, mul_assoc]
  exact mul_le_mul_of_nonneg_left hdiff hh0.le

lemma OMA.weylMean_eq_weyl_sum (α : ℝ) (h : ℕ) (ξ : ℝ) (N : ℕ) :
    OMA.weylMean α h ξ N =
      (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
        Complex.exp (2 * Real.pi * Complex.I * (h : ℝ) * (ξ * α ^ (n + 1))) := by
  unfold OMA.weylMean OMA.weylTerm
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  congr 1
  simp [mul_assoc]

lemma OMA.mem_unit_interval (ξ : ℝ) :
    ξ ∈ Set.Ico (⌊ξ⌋ : ℝ) (⌊ξ⌋ + 1) :=
  ⟨Int.floor_le ξ, Int.lt_floor_add_one ξ⟩

-- Fourier-free piecewise-constant correlation route

lemma OMA.intervalIntegrable_of_measurable_bounded {f : ℝ → ℝ} (hf : Measurable f)
    {C : ℝ} (hb : ∀ x, |f x| ≤ C) (u v : ℝ) : IntervalIntegrable f volume u v := by
  rw [intervalIntegrable_iff]
  haveI : IsFiniteMeasure (volume.restrict (Set.uIoc u v)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_uIoc]; exact ENNReal.ofReal_lt_top⟩
  refine (integrable_const C).mono' hf.aestronglyMeasurable ?_
  filter_upwards with x
  simpa [Real.norm_eq_abs] using hb x

lemma OMA.intervalIntegrable_centeredInd {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (u v : ℝ) :
    IntervalIntegrable (OMA.centeredInd 0 t) volume u v :=
  OMA.intervalIntegrable_of_measurable_bounded (OMA.measurable_centeredInd 0 t)
    (OMA.abs_centeredInd_le_one le_rfl ht0 ht1) u v

lemma OMA.intervalIntegrable_centeredInd_mul {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (c u v : ℝ) :
    IntervalIntegrable (fun x => OMA.centeredInd 0 t (x * c)) volume u v :=
  OMA.intervalIntegrable_of_measurable_bounded
    ((OMA.measurable_centeredInd 0 t).comp (measurable_id.mul_const c))
    (fun x => OMA.abs_centeredInd_le_one le_rfl ht0 ht1 (x * c)) u v

lemma OMA.intervalIntegrable_centeredInd_prod {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (c₁ c₂ u v : ℝ) :
    IntervalIntegrable (fun x => OMA.centeredInd 0 t (x * c₁) * OMA.centeredInd 0 t (x * c₂))
      volume u v := by
  refine OMA.intervalIntegrable_of_measurable_bounded ?_ (C := 1) ?_ u v
  · exact ((OMA.measurable_centeredInd 0 t).comp (measurable_id.mul_const c₁)).mul
      ((OMA.measurable_centeredInd 0 t).comp (measurable_id.mul_const c₂))
  · intro x
    rw [abs_mul]
    have h1 := OMA.abs_centeredInd_le_one le_rfl ht0 ht1 (x * c₁)
    have h2 := OMA.abs_centeredInd_le_one le_rfl ht0 ht1 (x * c₂)
    nlinarith [abs_nonneg (OMA.centeredInd 0 t (x * c₁)),
      abs_nonneg (OMA.centeredInd 0 t (x * c₂))]

lemma OMA.integral_centeredInd_zero_one {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫ x in (0 : ℝ)..1, OMA.centeredInd 0 t x) = 0 := by
  have hsplit : (∫ x in (0 : ℝ)..t, OMA.centeredInd 0 t x) +
      (∫ x in t..1, OMA.centeredInd 0 t x) = ∫ x in (0 : ℝ)..1, OMA.centeredInd 0 t x :=
    intervalIntegral.integral_add_adjacent_intervals
      (OMA.intervalIntegrable_centeredInd ht0 ht1 0 t)
      (OMA.intervalIntegrable_centeredInd ht0 ht1 t 1)
  have h1 : (∫ x in (0 : ℝ)..t, OMA.centeredInd 0 t x) = t * (1 - t) := by
    rw [intervalIntegral.integral_of_le ht0, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    have hcongr : (∫ x in Set.Ioo (0 : ℝ) t, OMA.centeredInd 0 t x) =
        ∫ x in Set.Ioo (0 : ℝ) t, (1 - t : ℝ) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
      have hfx : Int.fract x = x := Int.fract_eq_self.mpr ⟨hx.1.le, hx.2.trans_le ht1⟩
      have hmem : Int.fract x ∈ Set.Ico (0 : ℝ) t := by
        rw [hfx]
        exact ⟨hx.1.le, hx.2⟩
      simp [OMA.centeredInd, hmem]
    rw [hcongr, ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht0,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  have h2 : (∫ x in t..1, OMA.centeredInd 0 t x) = (1 - t) * (-t) := by
    rw [intervalIntegral.integral_of_le ht1, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    have hcongr : (∫ x in Set.Ioo t 1, OMA.centeredInd 0 t x) =
        ∫ x in Set.Ioo t 1, (-t : ℝ) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
      have hfx : Int.fract x = x := Int.fract_eq_self.mpr ⟨ht0.trans hx.1.le, hx.2⟩
      have hmem : Int.fract x ∉ Set.Ico (0 : ℝ) t := by
        rw [hfx, Set.mem_Ico]
        intro h
        linarith [hx.1, h.2]
      simp [OMA.centeredInd, hmem]
    rw [hcongr, ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht1,
      intervalIntegral.integral_const, smul_eq_mul]
  rw [← hsplit, h1, h2]
  ring

lemma OMA.integral_centeredInd_unit {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (u : ℝ) :
    (∫ x in u..(u + 1), OMA.centeredInd 0 t x) = 0 := by
  rw [(OMA.centeredInd_periodic 0 t).intervalIntegral_add_eq u 0, zero_add]
  exact OMA.integral_centeredInd_zero_one ht0 ht1

lemma OMA.integral_centeredInd_nat {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (u : ℝ) (k : ℕ) :
    (∫ x in u..(u + (k : ℝ)), OMA.centeredInd 0 t x) = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hadd : u + ((k + 1 : ℕ) : ℝ) = (u + (k : ℝ)) + 1 := by
      push_cast
      ring
    rw [hadd, ← intervalIntegral.integral_add_adjacent_intervals
      (OMA.intervalIntegrable_centeredInd ht0 ht1 u (u + k))
      (OMA.intervalIntegrable_centeredInd ht0 ht1 (u + k) (u + k + 1)),
      ih, OMA.integral_centeredInd_unit ht0 ht1 (u + k), add_zero]

lemma OMA.abs_integral_centeredInd_le_one {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {u v : ℝ} (huv : u ≤ v) :
    |∫ x in u..v, OMA.centeredInd 0 t x| ≤ 1 := by
  set k : ℕ := Int.toNat ⌊v - u⌋
  have hfl_nonneg : (0 : ℤ) ≤ ⌊v - u⌋ := Int.floor_nonneg.mpr (sub_nonneg.mpr huv)
  have hk_eq : (k : ℝ) = (⌊v - u⌋ : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hfl_nonneg
  have hsplit : (∫ x in u..(u + (k : ℝ)), OMA.centeredInd 0 t x) +
      (∫ x in (u + (k : ℝ))..v, OMA.centeredInd 0 t x) =
        ∫ x in u..v, OMA.centeredInd 0 t x :=
    intervalIntegral.integral_add_adjacent_intervals
      (OMA.intervalIntegrable_centeredInd ht0 ht1 u (u + k))
      (OMA.intervalIntegrable_centeredInd ht0 ht1 (u + k) v)
  rw [← hsplit, OMA.integral_centeredInd_nat ht0 ht1 u k, zero_add]
  have hle1 : u + (k : ℝ) ≤ v := by
    rw [hk_eq]
    linarith [Int.floor_le (v - u)]
  have hle2 : v - (u + (k : ℝ)) ≤ 1 := by
    rw [hk_eq]
    linarith [Int.lt_floor_add_one (v - u)]
  have hbound : ‖∫ x in (u + (k : ℝ))..v, OMA.centeredInd 0 t x‖ ≤
      1 * |v - (u + (k : ℝ))| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun x _ => by
      simpa [Real.norm_eq_abs] using OMA.abs_centeredInd_le_one le_rfl ht0 ht1 x
  rw [Real.norm_eq_abs, one_mul, abs_of_nonneg (sub_nonneg.mpr hle1)] at hbound
  exact hbound.trans hle2

lemma OMA.abs_integral_centeredInd_mul_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {c : ℝ} (hc : 0 < c) {u v : ℝ} (huv : u ≤ v) :
    |∫ ξ in u..v, OMA.centeredInd 0 t (ξ * c)| ≤ c⁻¹ := by
  rw [intervalIntegral.integral_comp_mul_right (f := OMA.centeredInd 0 t) hc.ne', smul_eq_mul,
    abs_mul, abs_of_pos (inv_pos.mpr hc)]
  have h1 := OMA.abs_integral_centeredInd_le_one ht0 ht1 (mul_le_mul_of_nonneg_right huv hc.le)
  calc
    c⁻¹ * |∫ x in u * c..v * c, OMA.centeredInd 0 t x| ≤ c⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hc.le)
    _ = c⁻¹ := mul_one _

lemma OMA.abs_integral_centeredInd_prod_unit_sub {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {r : ℝ} (hr : 0 < r) (k : ℤ) {u v : ℝ}
    (hku : (k : ℝ) ≤ u) (huv : u ≤ v) (hvk : v ≤ (k : ℝ) + 1) :
    |∫ x in u..v, OMA.centeredInd 0 t x * OMA.centeredInd 0 t (x * r)| ≤ r⁻¹ := by
  set w : ℝ := max u (min v ((k : ℝ) + t))
  have huw : u ≤ w := le_max_left _ _
  have hwv : w ≤ v := max_le huv (min_le_left _ _)
  have hint_uw : IntervalIntegrable
      (fun x => OMA.centeredInd 0 t x * OMA.centeredInd 0 t (x * r)) volume u w := by
    simpa [mul_one] using OMA.intervalIntegrable_centeredInd_prod ht0 ht1 1 r u w
  have hint_wv : IntervalIntegrable
      (fun x => OMA.centeredInd 0 t x * OMA.centeredInd 0 t (x * r)) volume w v := by
    simpa [mul_one] using OMA.intervalIntegrable_centeredInd_prod ht0 ht1 1 r w v
  have hsplit : (∫ x in u..w, OMA.centeredInd 0 t x * OMA.centeredInd 0 t (x * r)) +
      (∫ x in w..v, OMA.centeredInd 0 t x * OMA.centeredInd 0 t (x * r)) =
        ∫ x in u..v, OMA.centeredInd 0 t x * OMA.centeredInd 0 t (x * r) :=
    intervalIntegral.integral_add_adjacent_intervals hint_uw hint_wv
  have h1 : (∫ x in u..w, OMA.centeredInd 0 t x * OMA.centeredInd 0 t (x * r)) =
      (1 - t) * ∫ x in u..w, OMA.centeredInd 0 t (x * r) := by
    rw [intervalIntegral.integral_of_le huw, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    have hcongr : (∫ x in Set.Ioo u w, OMA.centeredInd 0 t x * OMA.centeredInd 0 t (x * r)) =
        ∫ x in Set.Ioo u w, (1 - t) * OMA.centeredInd 0 t (x * r) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
      have hxk1 : (k : ℝ) ≤ x := hku.trans hx.1.le
      have hxk2 : x < (k : ℝ) + 1 := hx.2.trans_le (hwv.trans hvk)
      have hfl : ⌊x⌋ = k := Int.floor_eq_iff.mpr ⟨hxk1, hxk2⟩
      have hfr : Int.fract x = x - (k : ℝ) := by
        rw [Int.fract, hfl]
      have hxlt : x < (k : ℝ) + t := by
        have hlt_max : u < max u (min v ((k : ℝ) + t)) := hx.1.trans hx.2
        have hw_le : w ≤ (k : ℝ) + t := by
          unfold w
          rcases le_total u (min v ((k : ℝ) + t)) with h | h
          · rw [max_eq_right h]
            exact min_le_right _ _
          · exfalso
            rw [max_eq_left h] at hlt_max
            exact lt_irrefl _ hlt_max
        exact hx.2.trans_le hw_le
      have hmem : Int.fract x ∈ Set.Ico (0 : ℝ) t := by
        rw [hfr, Set.mem_Ico]
        exact ⟨sub_nonneg.mpr hxk1, sub_lt_iff_lt_add'.mpr hxlt⟩
      simp [OMA.centeredInd, hmem]
    rw [hcongr, ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le huw,
      intervalIntegral.integral_const_mul]
  have h2 : (∫ x in w..v, OMA.centeredInd 0 t x * OMA.centeredInd 0 t (x * r)) =
      (-t) * ∫ x in w..v, OMA.centeredInd 0 t (x * r) := by
    rw [intervalIntegral.integral_of_le hwv, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    have hcongr : (∫ x in Set.Ioo w v, OMA.centeredInd 0 t x * OMA.centeredInd 0 t (x * r)) =
        ∫ x in Set.Ioo w v, (-t) * OMA.centeredInd 0 t (x * r) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
      have hxk1 : (k : ℝ) ≤ x := (hku.trans huw).trans hx.1.le
      have hxk2 : x < (k : ℝ) + 1 := hx.2.trans_le hvk
      have hfl : ⌊x⌋ = k := Int.floor_eq_iff.mpr ⟨hxk1, hxk2⟩
      have hfr : Int.fract x = x - (k : ℝ) := by
        rw [Int.fract, hfl]
      have hxgt : (k : ℝ) + t < x := by
        have hlt_v : min v ((k : ℝ) + t) < v := (le_max_right _ _).trans_lt (hx.1.trans hx.2)
        have hmin_eq : min v ((k : ℝ) + t) = (k : ℝ) + t := by
          rcases le_total v ((k : ℝ) + t) with h | h
          · exfalso
            rw [min_eq_left h] at hlt_v
            exact lt_irrefl _ hlt_v
          · exact min_eq_right h
        have hle_w : (k : ℝ) + t ≤ w := by
          rw [← hmin_eq]
          exact le_max_right _ _
        exact hle_w.trans_lt hx.1
      have hmem : Int.fract x ∉ Set.Ico (0 : ℝ) t := by
        rw [hfr, Set.mem_Ico]
        intro h
        linarith [hxgt, h.2]
      simp [OMA.centeredInd, hmem]
    rw [hcongr, ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hwv,
      intervalIntegral.integral_const_mul]
  rw [← hsplit, h1, h2]
  have hb1 := OMA.abs_integral_centeredInd_mul_le ht0 ht1 hr huw
  have hb2 := OMA.abs_integral_centeredInd_mul_le ht0 ht1 hr hwv
  calc
    |(1 - t) * (∫ x in u..w, OMA.centeredInd 0 t (x * r)) +
        (-t) * (∫ x in w..v, OMA.centeredInd 0 t (x * r))|
        ≤ |(1 - t) * (∫ x in u..w, OMA.centeredInd 0 t (x * r))| +
          |(-t) * (∫ x in w..v, OMA.centeredInd 0 t (x * r))| := abs_add_le _ _
    _ = (1 - t) * |∫ x in u..w, OMA.centeredInd 0 t (x * r)| +
          t * |∫ x in w..v, OMA.centeredInd 0 t (x * r)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr ht1), abs_neg, abs_of_nonneg ht0]
    _ ≤ (1 - t) * r⁻¹ + t * r⁻¹ := by
        gcongr
    _ = r⁻¹ := by ring

lemma OMA.abs_integral_centeredInd_prod_le_aux {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {r : ℝ} (hr : 0 < r) (N : ℕ) :
    ∀ A B : ℝ, A ≤ B → ⌊B⌋ - ⌊A⌋ ≤ (N : ℤ) →
      |∫ x in A..B, OMA.centeredInd 0 t x * OMA.centeredInd 0 t (x * r)| ≤
        ((N : ℝ) + 1) * r⁻¹ := by
  induction N with
  | zero =>
    intro A B hAB hfl
    have hfl_eq : ⌊B⌋ = ⌊A⌋ := by
      have hle : ⌊A⌋ ≤ ⌊B⌋ := Int.floor_mono hAB
      omega
    have hBk : B ≤ (⌊A⌋ : ℝ) + 1 := by
      rw [← hfl_eq]
      exact (Int.lt_floor_add_one B).le
    simpa using OMA.abs_integral_centeredInd_prod_unit_sub ht0 ht1 hr ⌊A⌋
      (Int.floor_le A) hAB hBk
  | succ N ih =>
    intro A B hAB hfl
    by_cases hfl_eq : ⌊B⌋ = ⌊A⌋
    · have hBk : B ≤ (⌊A⌋ : ℝ) + 1 := by
        rw [← hfl_eq]
        exact (Int.lt_floor_add_one B).le
      have h0 := OMA.abs_integral_centeredInd_prod_unit_sub ht0 ht1 hr ⌊A⌋
        (Int.floor_le A) hAB hBk
      have hr0 : 0 ≤ r⁻¹ := inv_nonneg.mpr hr.le
      calc
        |∫ x in A..B, OMA.centeredInd 0 t x * OMA.centeredInd 0 t (x * r)| ≤ r⁻¹ := h0
        _ = 1 * r⁻¹ := (one_mul _).symm
        _ ≤ (((N + 1 : ℕ) : ℝ) + 1) * r⁻¹ := by
            refine mul_le_mul_of_nonneg_right ?_ hr0
            push_cast
            linarith [Nat.cast_nonneg (α := ℝ) N]
    · have hfl_lt : ⌊A⌋ < ⌊B⌋ := lt_of_le_of_ne (Int.floor_mono hAB) (Ne.symm hfl_eq)
      set M : ℝ := (⌊A⌋ : ℝ) + 1
      have hAM : A ≤ M := (Int.lt_floor_add_one A).le
      have hMB : M ≤ B := by
        have h1 : ⌊A⌋ + 1 ≤ ⌊B⌋ := hfl_lt
        have h2 : ((⌊A⌋ + 1 : ℤ) : ℝ) ≤ (⌊B⌋ : ℝ) := by exact_mod_cast h1
        have h3 : (⌊B⌋ : ℝ) ≤ B := Int.floor_le B
        simpa [M] using h2.trans h3
      have hflM : ⌊M⌋ = ⌊A⌋ + 1 := by
        have hM_cast : M = ((⌊A⌋ + 1 : ℤ) : ℝ) := by push_cast [M]; rfl
        rw [hM_cast, Int.floor_intCast]
      have hint1 : IntervalIntegrable
          (fun x => OMA.centeredInd 0 t x * OMA.centeredInd 0 t (x * r)) volume A M := by
        simpa [mul_one] using OMA.intervalIntegrable_centeredInd_prod ht0 ht1 1 r A M
      have hint2 : IntervalIntegrable
          (fun x => OMA.centeredInd 0 t x * OMA.centeredInd 0 t (x * r)) volume M B := by
        simpa [mul_one] using OMA.intervalIntegrable_centeredInd_prod ht0 ht1 1 r M B
      have hsplit : (∫ x in A..M, OMA.centeredInd 0 t x * OMA.centeredInd 0 t (x * r)) +
          (∫ x in M..B, OMA.centeredInd 0 t x * OMA.centeredInd 0 t (x * r)) =
            ∫ x in A..B, OMA.centeredInd 0 t x * OMA.centeredInd 0 t (x * r) :=
        intervalIntegral.integral_add_adjacent_intervals hint1 hint2
      have hb1 := OMA.abs_integral_centeredInd_prod_unit_sub ht0 ht1 hr ⌊A⌋
        (Int.floor_le A) hAM le_rfl
      have hb2 := ih M B hMB (by omega)
      rw [← hsplit]
      calc
        |(∫ x in A..M, OMA.centeredInd 0 t x * OMA.centeredInd 0 t (x * r)) +
            (∫ x in M..B, OMA.centeredInd 0 t x * OMA.centeredInd 0 t (x * r))|
            ≤ |∫ x in A..M, OMA.centeredInd 0 t x * OMA.centeredInd 0 t (x * r)| +
              |∫ x in M..B, OMA.centeredInd 0 t x * OMA.centeredInd 0 t (x * r)| := abs_add_le _ _
        _ ≤ r⁻¹ + ((N : ℝ) + 1) * r⁻¹ := add_le_add hb1 hb2
        _ = (((N + 1 : ℕ) : ℝ) + 1) * r⁻¹ := by push_cast; ring

lemma OMA.abs_integral_centeredInd_prod_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {r : ℝ} (hr : 0 < r) {A B : ℝ} (hAB : A ≤ B) :
    |∫ x in A..B, OMA.centeredInd 0 t x * OMA.centeredInd 0 t (x * r)| ≤
      (B - A + 2) * r⁻¹ := by
  set N : ℕ := Int.toNat (⌊B⌋ - ⌊A⌋)
  have hnonneg : (0 : ℤ) ≤ ⌊B⌋ - ⌊A⌋ := sub_nonneg.mpr (Int.floor_mono hAB)
  have hN_int : (N : ℤ) = ⌊B⌋ - ⌊A⌋ := Int.toNat_of_nonneg hnonneg
  have hN_real : (N : ℝ) = (⌊B⌋ : ℝ) - (⌊A⌋ : ℝ) := by exact_mod_cast hN_int
  have haux := OMA.abs_integral_centeredInd_prod_le_aux ht0 ht1 hr N A B hAB (le_of_eq hN_int.symm)
  have hbound : (N : ℝ) + 1 ≤ B - A + 2 := by
    rw [hN_real]
    linarith [Int.floor_le B, Int.lt_floor_add_one A]
  exact haux.trans (mul_le_mul_of_nonneg_right hbound (inv_nonneg.mpr hr.le))

lemma OMA.abs_integral_centeredInd_alpha_prod_le {α t : ℝ} (hα : 1 < α)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (M : ℤ) {n m : ℕ} (hnm : n < m) :
    |∫ ξ in (M : ℝ)..(M + 1),
        OMA.centeredInd 0 t (ξ * α ^ (n + 1)) * OMA.centeredInd 0 t (ξ * α ^ (m + 1))| ≤
      3 * α⁻¹ ^ (m - n) := by
  have hα0 : 0 < α := zero_lt_one.trans hα
  have hc : 0 < α ^ (n + 1) := pow_pos hα0 (n + 1)
  have hr : 0 < α ^ (m - n) := pow_pos hα0 (m - n)
  have hpow : ∀ ξ : ℝ, ξ * α ^ (m + 1) = (ξ * α ^ (n + 1)) * α ^ (m - n) := by
    intro ξ
    rw [mul_assoc, ← pow_add]
    congr 2
    omega
  have hfun : (fun ξ : ℝ =>
      OMA.centeredInd 0 t (ξ * α ^ (n + 1)) * OMA.centeredInd 0 t (ξ * α ^ (m + 1))) =
      fun ξ : ℝ =>
        (fun x : ℝ => OMA.centeredInd 0 t x * OMA.centeredInd 0 t (x * α ^ (m - n)))
          (ξ * α ^ (n + 1)) := by
    funext ξ
    rw [hpow ξ]
  rw [hfun, intervalIntegral.integral_comp_mul_right
    (f := fun x : ℝ => OMA.centeredInd 0 t x * OMA.centeredInd 0 t (x * α ^ (m - n))) hc.ne',
    smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hc)]
  have hAB : (M : ℝ) * α ^ (n + 1) ≤ ((M : ℝ) + 1) * α ^ (n + 1) :=
    mul_le_mul_of_nonneg_right (by linarith) hc.le
  have hprod := OMA.abs_integral_centeredInd_prod_le ht0 ht1 hr hAB
  have hdiff : ((M : ℝ) + 1) * α ^ (n + 1) - (M : ℝ) * α ^ (n + 1) = α ^ (n + 1) := by ring
  rw [hdiff] at hprod
  have hge1 : 1 ≤ α ^ (n + 1) := one_le_pow₀ hα.le
  have hinv_le : (α ^ (n + 1))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hge1
  calc
    (α ^ (n + 1))⁻¹ *
        |∫ x in (M : ℝ) * α ^ (n + 1)..((M : ℝ) + 1) * α ^ (n + 1),
          OMA.centeredInd 0 t x * OMA.centeredInd 0 t (x * α ^ (m - n))|
        ≤ (α ^ (n + 1))⁻¹ * ((α ^ (n + 1) + 2) * (α ^ (m - n))⁻¹) :=
          mul_le_mul_of_nonneg_left hprod (inv_nonneg.mpr hc.le)
    _ = (1 + 2 * (α ^ (n + 1))⁻¹) * (α ^ (m - n))⁻¹ := by
          field_simp [hc.ne']
    _ ≤ (1 + 2 * 1) * (α ^ (m - n))⁻¹ := by
          gcongr
    _ = 3 * α⁻¹ ^ (m - n) := by
          rw [inv_pow]
          ring

lemma OMA.geom_sum_inv_le {α : ℝ} (hα : 1 < α) (N : ℕ) :
    (∑ d ∈ Finset.range N, α⁻¹ ^ d) ≤ (1 - α⁻¹)⁻¹ := by
  have hα0 : 0 < α := zero_lt_one.trans hα
  have hinv0 : 0 ≤ α⁻¹ := inv_nonneg.mpr hα0.le
  have hinv1 : α⁻¹ < 1 := inv_lt_one_of_one_lt₀ hα
  have hden : 0 < 1 - α⁻¹ := sub_pos.mpr hinv1
  rw [geom_sum_eq (ne_of_lt hinv1)]
  have hdiv : (α⁻¹ ^ N - 1) / (α⁻¹ - 1) = (1 - α⁻¹ ^ N) / (1 - α⁻¹) := by
    rw [← neg_div_neg_eq, neg_sub, neg_sub]
  rw [hdiv, div_eq_mul_inv]
  have hpow0 : 0 ≤ α⁻¹ ^ N := pow_nonneg hinv0 N
  have hle1 : 1 - α⁻¹ ^ N ≤ 1 := by linarith
  calc
    (1 - α⁻¹ ^ N) * (1 - α⁻¹)⁻¹ ≤ 1 * (1 - α⁻¹)⁻¹ :=
      mul_le_mul_of_nonneg_right hle1 (inv_nonneg.mpr hden.le)
    _ = (1 - α⁻¹)⁻¹ := one_mul _

lemma OMA.centeredInd_cesaro_l2_bound {α t : ℝ} (hα : 1 < α)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (M : ℤ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      (∫ ξ in (M : ℝ)..(M + 1),
        ((N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
          OMA.centeredInd 0 t (ξ * α ^ (n + 1))) ^ 2) ≤ C / N := by
  have hα0 : 0 < α := zero_lt_one.trans hα
  have hinv0 : 0 ≤ α⁻¹ := inv_nonneg.mpr hα0.le
  have hinv1 : α⁻¹ < 1 := inv_lt_one_of_one_lt₀ hα
  have hden : 0 < 1 - α⁻¹ := sub_pos.mpr hinv1
  refine ⟨1 + 6 * (1 - α⁻¹)⁻¹, by positivity, fun N hN => ?_⟩
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  set g : ℕ → ℝ → ℝ := fun n ξ => OMA.centeredInd 0 t (ξ * α ^ (n + 1))
  have hexpand : ∀ ξ : ℝ,
      ((N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, g n ξ) ^ 2 =
        (N : ℝ)⁻¹ ^ 2 * ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, g n ξ * g m ξ := by
    intro ξ
    rw [mul_pow]
    congr 1
    rw [sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.mul_sum]
  have hint_prod : ∀ n m : ℕ,
      IntervalIntegrable (fun ξ => g n ξ * g m ξ) volume (M : ℝ) (M + 1) :=
    fun n m => OMA.intervalIntegrable_centeredInd_prod ht0 ht1 (α ^ (n + 1)) (α ^ (m + 1)) M (M + 1)
  have hint_sum : ∀ n : ℕ,
      IntervalIntegrable (fun ξ => ∑ m ∈ Finset.range N, g n ξ * g m ξ) volume (M : ℝ) (M + 1) := by
    intro n
    have hfun : (fun ξ => ∑ m ∈ Finset.range N, g n ξ * g m ξ) =
        ∑ m ∈ Finset.range N, fun ξ => g n ξ * g m ξ := by
      funext ξ
      simp
    rw [hfun]
    exact IntervalIntegrable.sum (Finset.range N) fun m _ => hint_prod n m
  have hrew : (∫ ξ in (M : ℝ)..(M + 1), ((N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, g n ξ) ^ 2) =
      (N : ℝ)⁻¹ ^ 2 * ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ∫ ξ in (M : ℝ)..(M + 1), g n ξ * g m ξ := by
    simp_rw [hexpand]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum fun n _ => hint_sum n]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    exact intervalIntegral.integral_finsetSum fun m _ => hint_prod n m
  rw [hrew]
  have hrow : ∀ n ∈ Finset.range N,
      (∑ m ∈ Finset.range N, ∫ ξ in (M : ℝ)..(M + 1), g n ξ * g m ξ) ≤
        1 + 6 * (1 - α⁻¹)⁻¹ := by
    intro n hn
    have hn_lt : n < N := Finset.mem_range.mp hn
    have hterm : ∀ m ∈ Finset.range N,
        (∫ ξ in (M : ℝ)..(M + 1), g n ξ * g m ξ) ≤
          (if m = n then (1 : ℝ) else 0) +
          (if n < m then 3 * α⁻¹ ^ (m - n) else 0) +
          (if m < n then 3 * α⁻¹ ^ (n - m) else 0) := by
      intro m _
      rcases lt_trichotomy n m with hnm | rfl | hmn
      · have h1 : m ≠ n := ne_of_gt hnm
        have h2 : ¬ m < n := not_lt.mpr hnm.le
        simp only [h1, hnm, h2, ↓reduceIte, zero_add, add_zero]
        exact (le_abs_self _).trans (OMA.abs_integral_centeredInd_alpha_prod_le hα ht0 ht1 M hnm)
      · simp only [↓reduceIte, lt_irrefl, add_zero]
        have hnorm : ‖∫ ξ in (M : ℝ)..(M + 1), g n ξ * g n ξ‖ ≤ 1 * |(M : ℝ) + 1 - M| :=
          intervalIntegral.norm_integral_le_of_norm_le_const fun ξ _ => by
            rw [Real.norm_eq_abs, abs_mul]
            have hle := OMA.abs_centeredInd_le_one le_rfl ht0 ht1 (ξ * α ^ (n + 1))
            nlinarith [abs_nonneg (g n ξ)]
        have hval : (1 : ℝ) * |(M : ℝ) + 1 - M| = 1 := by
          have : (M : ℝ) + 1 - M = 1 := by ring
          rw [this, abs_one, mul_one]
        rw [hval, Real.norm_eq_abs] at hnorm
        exact (le_abs_self _).trans hnorm
      · have h1 : m ≠ n := ne_of_lt hmn
        have h2 : ¬ n < m := not_lt.mpr hmn.le
        simp only [h1, h2, hmn, ↓reduceIte, zero_add]
        have hcomm : (∫ ξ in (M : ℝ)..(M + 1), g n ξ * g m ξ) =
            ∫ ξ in (M : ℝ)..(M + 1), g m ξ * g n ξ := by
          congr 1; funext ξ; ring
        rw [hcomm]
        exact (le_abs_self _).trans (OMA.abs_integral_centeredInd_alpha_prod_le hα ht0 ht1 M hmn)
    have hsum1 : (∑ m ∈ Finset.range N, if m = n then (1 : ℝ) else 0) = 1 := by
      rw [Finset.sum_ite_eq' (Finset.range N) n (fun _ => (1 : ℝ)), if_pos hn]
    have hsum2 : (∑ m ∈ Finset.range N, if n < m then 3 * α⁻¹ ^ (m - n) else 0) ≤
        3 * (1 - α⁻¹)⁻¹ := by
      rw [← Finset.sum_filter, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      have hinj : Set.InjOn (fun m => m - n)
          (((Finset.range N).filter (fun m => n < m) : Finset ℕ) : Set ℕ) := by
        intro a ha b hb hab
        simp only [Finset.mem_coe, Finset.mem_filter] at ha hb
        dsimp only at hab
        omega
      have hsub : ((Finset.range N).filter (fun m => n < m)).image (fun m => m - n) ⊆
          Finset.range N := by
        intro d hd
        rcases Finset.mem_image.mp hd with ⟨m, hm, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢
        omega
      calc
        (∑ m ∈ (Finset.range N).filter (fun m => n < m), α⁻¹ ^ (m - n))
            = ∑ d ∈ ((Finset.range N).filter (fun m => n < m)).image (fun m => m - n),
                α⁻¹ ^ d := (Finset.sum_image hinj).symm
        _ ≤ ∑ d ∈ Finset.range N, α⁻¹ ^ d :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun d _ _ => pow_nonneg hinv0 d
        _ ≤ (1 - α⁻¹)⁻¹ := OMA.geom_sum_inv_le hα N
    have hsum3 : (∑ m ∈ Finset.range N, if m < n then 3 * α⁻¹ ^ (n - m) else 0) ≤
        3 * (1 - α⁻¹)⁻¹ := by
      rw [← Finset.sum_filter, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      have hinj : Set.InjOn (fun m => n - m)
          (((Finset.range N).filter (fun m => m < n) : Finset ℕ) : Set ℕ) := by
        intro a ha b hb hab
        simp only [Finset.mem_coe, Finset.mem_filter] at ha hb
        dsimp only at hab
        omega
      have hsub : ((Finset.range N).filter (fun m => m < n)).image (fun m => n - m) ⊆
          Finset.range N := by
        intro d hd
        rcases Finset.mem_image.mp hd with ⟨m, hm, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢
        omega
      calc
        (∑ m ∈ (Finset.range N).filter (fun m => m < n), α⁻¹ ^ (n - m))
            = ∑ d ∈ ((Finset.range N).filter (fun m => m < n)).image (fun m => n - m),
                α⁻¹ ^ d := (Finset.sum_image hinj).symm
        _ ≤ ∑ d ∈ Finset.range N, α⁻¹ ^ d :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun d _ _ => pow_nonneg hinv0 d
        _ ≤ (1 - α⁻¹)⁻¹ := OMA.geom_sum_inv_le hα N
    calc
      (∑ m ∈ Finset.range N, ∫ ξ in (M : ℝ)..(M + 1), g n ξ * g m ξ)
          ≤ ∑ m ∈ Finset.range N,
              ((if m = n then (1 : ℝ) else 0) +
                (if n < m then 3 * α⁻¹ ^ (m - n) else 0) +
                (if m < n then 3 * α⁻¹ ^ (n - m) else 0)) := Finset.sum_le_sum hterm
      _ = (∑ m ∈ Finset.range N, if m = n then (1 : ℝ) else 0) +
          (∑ m ∈ Finset.range N, if n < m then 3 * α⁻¹ ^ (m - n) else 0) +
          (∑ m ∈ Finset.range N, if m < n then 3 * α⁻¹ ^ (n - m) else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ ≤ 1 + 3 * (1 - α⁻¹)⁻¹ + 3 * (1 - α⁻¹)⁻¹ := by linarith
      _ = 1 + 6 * (1 - α⁻¹)⁻¹ := by ring
  have hdouble : (∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
      ∫ ξ in (M : ℝ)..(M + 1), g n ξ * g m ξ) ≤ (N : ℝ) * (1 + 6 * (1 - α⁻¹)⁻¹) := by
    calc
      (∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, ∫ ξ in (M : ℝ)..(M + 1), g n ξ * g m ξ)
          ≤ ∑ _n ∈ Finset.range N, (1 + 6 * (1 - α⁻¹)⁻¹) := Finset.sum_le_sum hrow
      _ = (N : ℝ) * (1 + 6 * (1 - α⁻¹)⁻¹) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc
    (N : ℝ)⁻¹ ^ 2 * ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ∫ ξ in (M : ℝ)..(M + 1), g n ξ * g m ξ
        ≤ (N : ℝ)⁻¹ ^ 2 * ((N : ℝ) * (1 + 6 * (1 - α⁻¹)⁻¹)) :=
          mul_le_mul_of_nonneg_left hdouble (sq_nonneg _)
    _ = (1 + 6 * (1 - α⁻¹)⁻¹) / N := by
          field_simp [hN0.ne']

lemma OMA.centeredInd_cesaro_sq_subseq_ae {α t : ℝ} (hα : 1 < α)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (M : ℤ) :
    ∀ᵐ ξ : ℝ, ξ ∈ Set.Ioc (M : ℝ) (M + 1) →
      Tendsto (fun k : ℕ => (((k + 1) ^ 2 : ℕ) : ℝ)⁻¹ *
        ∑ n ∈ Finset.range ((k + 1) ^ 2), OMA.centeredInd 0 t (ξ * α ^ (n + 1)))
        atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := OMA.centeredInd_cesaro_l2_bound hα ht0 ht1 M
  set μ : Measure ℝ := volume.restrict (Set.Ioc (M : ℝ) (M + 1))
  set S : ℕ → ℝ → ℝ := fun k ξ =>
    (((k + 1) ^ 2 : ℕ) : ℝ)⁻¹ *
      ∑ n ∈ Finset.range ((k + 1) ^ 2), OMA.centeredInd 0 t (ξ * α ^ (n + 1))
  have hS_meas : ∀ k, Measurable (S k) := fun k => by
    refine measurable_const.mul ?_
    refine Finset.measurable_sum _ fun n _ => ?_
    exact (OMA.measurable_centeredInd 0 t).comp (measurable_id.mul_const _)
  have hS_bd : ∀ k ξ, |S k ξ| ≤ 1 := fun k ξ => by
    have hpos : (0 : ℝ) < ((k + 1) ^ 2 : ℕ) := by positivity
    rw [abs_mul, abs_of_pos (inv_pos.mpr hpos)]
    have hsum : |∑ n ∈ Finset.range ((k + 1) ^ 2), OMA.centeredInd 0 t (ξ * α ^ (n + 1))| ≤
        (((k + 1) ^ 2 : ℕ) : ℝ) := by
      calc
        |∑ n ∈ Finset.range ((k + 1) ^ 2), OMA.centeredInd 0 t (ξ * α ^ (n + 1))|
            ≤ ∑ n ∈ Finset.range ((k + 1) ^ 2), |OMA.centeredInd 0 t (ξ * α ^ (n + 1))| :=
              Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _n ∈ Finset.range ((k + 1) ^ 2), (1 : ℝ) :=
              Finset.sum_le_sum fun n _ => OMA.abs_centeredInd_le_one le_rfl ht0 ht1 _
        _ = (((k + 1) ^ 2 : ℕ) : ℝ) := by simp
    calc
      (((k + 1) ^ 2 : ℕ) : ℝ)⁻¹ *
          |∑ n ∈ Finset.range ((k + 1) ^ 2), OMA.centeredInd 0 t (ξ * α ^ (n + 1))|
          ≤ (((k + 1) ^ 2 : ℕ) : ℝ)⁻¹ * (((k + 1) ^ 2 : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hpos.le)
      _ = 1 := inv_mul_cancel₀ hpos.ne'
  have hlint_k : ∀ k : ℕ,
      (∫⁻ ξ, ENNReal.ofReal ((S k ξ) ^ 2) ∂μ) ≤
        ENNReal.ofReal (C / (((k + 1 : ℕ) : ℝ) ^ 2)) := by
    intro k
    have hint : Integrable (fun ξ => (S k ξ) ^ 2) μ := by
      refine (integrable_const (1 : ℝ)).mono' ((hS_meas k).pow_const 2).aestronglyMeasurable ?_
      filter_upwards with ξ
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [hS_bd k ξ, abs_nonneg (S k ξ), sq_abs (S k ξ)]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun ξ => sq_nonneg (S k ξ))]
    apply ENNReal.ofReal_le_ofReal
    have hle : (M : ℝ) ≤ (M : ℝ) + 1 := by linarith
    have heq : (∫ ξ, (S k ξ) ^ 2 ∂μ) = ∫ ξ in (M : ℝ)..(M + 1), (S k ξ) ^ 2 :=
      (intervalIntegral.integral_of_le hle).symm
    rw [heq]
    have h1 : 1 ≤ (k + 1) ^ 2 := Nat.one_le_pow 2 (k + 1) (Nat.succ_pos k)
    have hbound := hC ((k + 1) ^ 2) h1
    simpa [S] using hbound
  have hsum_real : Summable (fun k : ℕ => C / (((k + 1 : ℕ) : ℝ) ^ 2)) := by
    have hbase : Summable (fun k : ℕ => (1 : ℝ) / ((k : ℝ) ^ 2)) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have hshift : Summable (fun k : ℕ => (1 : ℝ) / (((k + 1 : ℕ) : ℝ) ^ 2)) :=
      (summable_nat_add_iff 1).mpr hbase
    have hfun : (fun k : ℕ => C / (((k + 1 : ℕ) : ℝ) ^ 2)) =
        fun k : ℕ => C * ((1 : ℝ) / (((k + 1 : ℕ) : ℝ) ^ 2)) := by
      funext k
      ring
    rw [hfun]
    exact hshift.mul_left C
  have htsum_ne_top :
      (∫⁻ ξ, ∑' k : ℕ, ENNReal.ofReal ((S k ξ) ^ 2) ∂μ) ≠ ⊤ := by
    have hlt_eq : (∫⁻ ξ, ∑' k : ℕ, ENNReal.ofReal ((S k ξ) ^ 2) ∂μ) =
        ∑' k : ℕ, ∫⁻ ξ, ENNReal.ofReal ((S k ξ) ^ 2) ∂μ :=
      MeasureTheory.lintegral_tsum fun k =>
        (ENNReal.measurable_ofReal.comp ((hS_meas k).pow_const 2)).aemeasurable
    rw [hlt_eq]
    have hle_tsum : (∑' k : ℕ, ∫⁻ ξ, ENNReal.ofReal ((S k ξ) ^ 2) ∂μ) ≤
        ∑' k : ℕ, ENNReal.ofReal (C / (((k + 1 : ℕ) : ℝ) ^ 2)) :=
      ENNReal.tsum_le_tsum hlint_k
    have hfin : (∑' k : ℕ, ENNReal.ofReal (C / (((k + 1 : ℕ) : ℝ) ^ 2))) < ⊤ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum_real]
      exact ENNReal.ofReal_lt_top
    exact (hle_tsum.trans_lt hfin).ne
  have hae_lt : ∀ᵐ ξ ∂μ, (∑' k : ℕ, ENNReal.ofReal ((S k ξ) ^ 2)) < ⊤ :=
    MeasureTheory.ae_lt_top
      (Measurable.ennreal_tsum fun k => ENNReal.measurable_ofReal.comp ((hS_meas k).pow_const 2))
      htsum_ne_top
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc] at hae_lt
  filter_upwards [hae_lt] with ξ hξ hmem
  have hne : (∑' k : ℕ, ENNReal.ofReal ((S k ξ) ^ 2)) ≠ ⊤ := (hξ hmem).ne
  have hsummable_toReal : Summable (fun k : ℕ => (ENNReal.ofReal ((S k ξ) ^ 2)).toReal) :=
    ENNReal.summable_toReal hne
  have hsummable_sq : Summable (fun k : ℕ => (S k ξ) ^ 2) := by
    simpa [ENNReal.toReal_ofReal (sq_nonneg _)] using hsummable_toReal
  have htend_sq : Tendsto (fun k : ℕ => (S k ξ) ^ 2) atTop (𝓝 0) :=
    hsummable_sq.tendsto_atTop_zero
  have htend_abs : Tendsto (fun k : ℕ => |S k ξ|) atTop (𝓝 0) := by
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp htend_sq
    simpa [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] using hsqrt
  have htend_norm : Tendsto (fun k : ℕ => ‖S k ξ‖) atTop (𝓝 0) := by
    simpa only [Real.norm_eq_abs] using htend_abs
  exact tendsto_zero_iff_norm_tendsto_zero.mpr htend_norm

lemma OMA.real_cesaro_tendsto_of_sq_subseq {u : ℕ → ℝ} (hu : ∀ n, |u n| ≤ 1)
    (hsq : Tendsto (fun k : ℕ => (((k + 1) ^ 2 : ℕ) : ℝ)⁻¹ *
      ∑ n ∈ Finset.range ((k + 1) ^ 2), u n) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, u n) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop] at hsq ⊢
  intro ε hε
  obtain ⟨K₀, hK₀⟩ := hsq (ε / 2) (half_pos hε)
  obtain ⟨K₁, hK₁⟩ := exists_nat_gt (4 / ε)
  set K : ℕ := max K₀ K₁
  refine ⟨(K + 1) ^ 2, fun N hN => ?_⟩
  rw [Real.dist_eq, sub_zero]
  set m : ℕ := Nat.sqrt N
  have hm_ge : K + 1 ≤ m := by
    have := Nat.sqrt_le_sqrt hN
    rwa [sq, Nat.sqrt_eq] at this
  have hm_pos : 0 < m := by omega
  set k : ℕ := m - 1
  have hk_succ : k + 1 = m := Nat.sub_add_cancel hm_pos
  have hk_ge0 : K₀ ≤ k := by omega
  have hk_ge1 : K₁ ≤ k := by omega
  have hsq_le : (k + 1) ^ 2 ≤ N := by
    rw [hk_succ]
    exact Nat.sqrt_le' N
  have hlt_sq : N < (k + 2) ^ 2 := by
    have h := Nat.lt_succ_sqrt' N
    change N < (m + 1) ^ 2 at h
    rw [← hk_succ] at h
    exact h
  have hdiff_le : N - (k + 1) ^ 2 ≤ 2 * (k + 1) := by
    have h1 : (k + 2) ^ 2 = (k + 1) ^ 2 + 2 * (k + 1) + 1 := by ring
    omega
  have hN_pos : (0 : ℝ) < N := by
    have : 0 < N := lt_of_lt_of_le (by positivity) hN
    exact Nat.cast_pos.mpr this
  have hk1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hsplit : ∑ n ∈ Finset.range N, u n =
      (∑ n ∈ Finset.range ((k + 1) ^ 2), u n) +
        (∑ n ∈ Finset.Ico ((k + 1) ^ 2) N, u n) :=
    (Finset.sum_range_add_sum_Ico u hsq_le).symm
  have htail : |∑ n ∈ Finset.Ico ((k + 1) ^ 2) N, u n| ≤ 2 * ((k + 1 : ℕ) : ℝ) := by
    calc
      |∑ n ∈ Finset.Ico ((k + 1) ^ 2) N, u n|
          ≤ ∑ n ∈ Finset.Ico ((k + 1) ^ 2) N, |u n| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ Finset.Ico ((k + 1) ^ 2) N, (1 : ℝ) := Finset.sum_le_sum fun n _ => hu n
      _ = ((N - (k + 1) ^ 2 : ℕ) : ℝ) := by simp [Nat.card_Ico]
      _ ≤ ((2 * (k + 1) : ℕ) : ℝ) := by exact_mod_cast hdiff_le
      _ = 2 * ((k + 1 : ℕ) : ℝ) := by push_cast; ring
  have hhead : |(((k + 1) ^ 2 : ℕ) : ℝ)⁻¹ * ∑ n ∈ Finset.range ((k + 1) ^ 2), u n| < ε / 2 := by
    have := hK₀ k hk_ge0
    rwa [Real.dist_eq, sub_zero] at this
  have hhead_mul : |∑ n ∈ Finset.range ((k + 1) ^ 2), u n| <
      (((k + 1) ^ 2 : ℕ) : ℝ) * (ε / 2) := by
    have hpos : (0 : ℝ) < ((k + 1) ^ 2 : ℕ) := by positivity
    rw [abs_mul, abs_of_pos (inv_pos.mpr hpos)] at hhead
    have := mul_lt_mul_of_pos_left hhead hpos
    rwa [mul_inv_cancel_left₀ hpos.ne'] at this
  have hratio_le : (((k + 1) ^ 2 : ℕ) : ℝ) / (N : ℝ) ≤ 1 := by
    rw [div_le_one hN_pos]
    exact_mod_cast hsq_le
  have htail_div : 2 * ((k + 1 : ℕ) : ℝ) / (N : ℝ) < ε / 2 := by
    have hN_ge_sq : (((k + 1 : ℕ) : ℝ) ^ 2) ≤ (N : ℝ) := by exact_mod_cast hsq_le
    have h1 : 2 * ((k + 1 : ℕ) : ℝ) / (N : ℝ) ≤ 2 / ((k + 1 : ℕ) : ℝ) := by
      rw [div_le_div_iff₀ hN_pos hk1_pos]
      have : 2 * ((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) = 2 * ((k + 1 : ℕ) : ℝ) ^ 2 := by ring
      rw [this]
      nlinarith
    have h2 : 2 / ((k + 1 : ℕ) : ℝ) < ε / 2 := by
      have hk1_gt : 4 / ε < ((k + 1 : ℕ) : ℝ) := by
        have : (K₁ : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (show K₁ ≤ k + 1 by omega)
        exact hK₁.trans_le this
      rw [div_lt_iff₀ hk1_pos]
      have := (div_lt_iff₀ hε).mp hk1_gt
      linarith
    exact h1.trans_lt h2
  rw [hsplit, mul_add]
  calc
    |(N : ℝ)⁻¹ * (∑ n ∈ Finset.range ((k + 1) ^ 2), u n) +
        (N : ℝ)⁻¹ * (∑ n ∈ Finset.Ico ((k + 1) ^ 2) N, u n)|
        ≤ |(N : ℝ)⁻¹ * (∑ n ∈ Finset.range ((k + 1) ^ 2), u n)| +
          |(N : ℝ)⁻¹ * (∑ n ∈ Finset.Ico ((k + 1) ^ 2) N, u n)| := abs_add_le _ _
    _ = (N : ℝ)⁻¹ * |∑ n ∈ Finset.range ((k + 1) ^ 2), u n| +
          (N : ℝ)⁻¹ * |∑ n ∈ Finset.Ico ((k + 1) ^ 2) N, u n| := by
          rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hN_pos)]
    _ < (N : ℝ)⁻¹ * ((((k + 1) ^ 2 : ℕ) : ℝ) * (ε / 2)) +
          (N : ℝ)⁻¹ * (2 * ((k + 1 : ℕ) : ℝ)) := by
          have hlt1 := mul_lt_mul_of_pos_left hhead_mul (inv_pos.mpr hN_pos)
          have hle2 := mul_le_mul_of_nonneg_left htail (inv_nonneg.mpr hN_pos.le)
          linarith
    _ = ((((k + 1) ^ 2 : ℕ) : ℝ) / (N : ℝ)) * (ε / 2) +
          (2 * ((k + 1 : ℕ) : ℝ) / (N : ℝ)) := by ring
    _ < 1 * (ε / 2) + ε / 2 := by
          have hle1 : ((((k + 1) ^ 2 : ℕ) : ℝ) / (N : ℝ)) * (ε / 2) ≤ 1 * (ε / 2) :=
            mul_le_mul_of_nonneg_right hratio_le (half_pos hε).le
          linarith
    _ = ε := by ring

lemma OMA.count_Ico_tendsto_of_centeredInd {x : ℕ → ℝ} {t : ℝ}
    (h : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, OMA.centeredInd 0 t (x n))
      atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      (((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico 0 t).card : ℝ) / (N : ℝ))
      atTop (𝓝 t) := by
  have hev : (fun N : ℕ =>
      (((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico 0 t).card : ℝ) / (N : ℝ))
      =ᶠ[atTop]
      fun N : ℕ =>
        (N : ℝ)⁻¹ * (∑ n ∈ Finset.range N, OMA.centeredInd 0 t (x n)) + t := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hsum : (∑ n ∈ Finset.range N, OMA.centeredInd 0 t (x n)) =
        (((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico 0 t).card : ℝ) -
          (N : ℝ) * t := by
      simp only [OMA.centeredInd, sub_zero, Finset.sum_sub_distrib, Finset.sum_boole,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hsum]
    field_simp [hN0]
    ring
  refine Tendsto.congr' hev.symm ?_
  simpa using h.add_const t

lemma OMA.equidistributed_of_rat_centeredInd {x : ℕ → ℝ}
    (hrat : ∀ q : ℚ, (0 : ℝ) ≤ (q : ℝ) → (q : ℝ) ≤ 1 →
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, OMA.centeredInd 0 (q : ℝ) (x n))
        atTop (𝓝 0)) :
    IsEquidistributedModuloOne x := by
  intro c d hcd hsub
  have hc0 : 0 ≤ c := (hsub ⟨le_rfl, hcd⟩).1
  have hd1 : d ≤ 1 := (hsub ⟨hcd, le_rfl⟩).2
  have hgoal_eq : (d - c) / (1 - 0 : ℝ) = d - c := by ring
  rw [hgoal_eq, Metric.tendsto_atTop]
  intro ε hε
  set F : ℝ → ℕ → ℝ := fun t N =>
    (((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico 0 t).card : ℝ) / (N : ℝ)
  set C_cnt : ℕ → ℝ := fun N =>
    (((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Icc c d).card : ℝ) / (N : ℝ)
  have hF_tend : ∀ q : ℚ, (0 : ℝ) ≤ (q : ℝ) → (q : ℝ) ≤ 1 →
      Tendsto (F (q : ℝ)) atTop (𝓝 (q : ℝ)) :=
    fun q hq0 hq1 => OMA.count_Ico_tendsto_of_centeredInd (hrat q hq0 hq1)
  have hsub_cnt : ∀ (a b : ℝ) (N : ℕ), a ≤ b →
      (((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b).card : ℝ) / (N : ℝ) =
        F b N - F a N := by
    intro a b N hab
    have hdisj : Disjoint
        ((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico 0 a)
        ((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b) := by
      rw [Finset.disjoint_filter]
      intro n _ h1 h2
      linarith [h1.2, h2.1]
    have hunion :
        ((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico 0 a) ∪
          ((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b) =
        ((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico 0 b) := by
      ext n
      simp only [Finset.mem_union, Finset.mem_filter, Set.mem_Ico]
      constructor
      · rintro (⟨hn, h0, ha⟩ | ⟨hn, ha, hb⟩)
        · exact ⟨hn, h0, ha.trans_le hab⟩
        · exact ⟨hn, Int.fract_nonneg _, hb⟩
      · rintro ⟨hn, h0, hb⟩
        rcases lt_or_ge (Int.fract (x n)) a with h | h
        · exact Or.inl ⟨hn, h0, h⟩
        · exact Or.inr ⟨hn, h, hb⟩
    have hcard :
        (((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico 0 a).card : ℝ) +
          (((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b).card : ℝ) =
        (((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico 0 b).card : ℝ) := by
      exact_mod_cast (by rw [← Finset.card_union_of_disjoint hdisj, hunion])
    simp only [F]
    rw [← sub_div, ← hcard]
    ring
  -- Upper bound
  have hp1_ex : ∃ p1 : ℚ, (0 : ℝ) ≤ p1 ∧ (p1 : ℝ) ≤ c ∧ c - (p1 : ℝ) < ε / 4 := by
    by_cases hc : c = 0
    · refine ⟨0, by simp, by simp [hc], by simp [hc]; linarith⟩
    · have hcpos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hc)
      have hlt : max 0 (c - ε / 4) < c := max_lt hcpos (by linarith)
      obtain ⟨p1, hp1_gt, hp1_lt⟩ := exists_rat_btwn hlt
      exact ⟨p1, (le_max_left _ _).trans hp1_gt.le, hp1_lt.le,
        by linarith [(le_max_right _ _).trans_lt hp1_gt]⟩
  have hq2_ex : ∃ q2 : ℚ, d ≤ (q2 : ℝ) ∧ (q2 : ℝ) ≤ 1 ∧ (q2 : ℝ) - d < ε / 4 ∧
      ∀ y : ℝ, y < 1 → y ≤ d → y < (q2 : ℝ) := by
    by_cases hd : d = 1
    · refine ⟨1, by simp [hd], by simp, by simp [hd]; linarith, fun y hy _ => by simpa using hy⟩
    · have hdlt : d < 1 := lt_of_le_of_ne hd1 hd
      have hlt : d < min 1 (d + ε / 4) := lt_min hdlt (by linarith)
      obtain ⟨q2, hq2_gt, hq2_lt⟩ := exists_rat_btwn hlt
      exact ⟨q2, hq2_gt.le, hq2_lt.le.trans (min_le_left _ _),
        by linarith [hq2_lt.trans_le (min_le_right _ _)], fun y _ hyd => hyd.trans_lt hq2_gt⟩
  obtain ⟨p1, hp1_0, hp1_c, hp1_eps⟩ := hp1_ex
  obtain ⟨q2, hq2_d, hq2_1, hq2_eps, hq2_strict⟩ := hq2_ex
  have hupper_ev : ∀ᶠ N in atTop, C_cnt N < (d - c) + ε := by
    have htend_u : Tendsto (fun N => F (q2 : ℝ) N - F (p1 : ℝ) N) atTop
        (𝓝 ((q2 : ℝ) - (p1 : ℝ))) :=
      (hF_tend q2 (hc0.trans (hcd.trans hq2_d)) hq2_1).sub
        (hF_tend p1 hp1_0 (hp1_c.trans (hcd.trans hd1)))
    have hlt_lim : (q2 : ℝ) - (p1 : ℝ) < (d - c) + ε := by linarith
    filter_upwards [htend_u.eventually (gt_mem_nhds hlt_lim)] with N hN
    have hle : C_cnt N ≤ F (q2 : ℝ) N - F (p1 : ℝ) N := by
      rw [← hsub_cnt (p1 : ℝ) (q2 : ℝ) N (hp1_c.trans (hcd.trans hq2_d))]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
      have hcard :
          ((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Icc c d).card ≤
            ((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico (p1 : ℝ) (q2 : ℝ)).card := by
        refine Finset.card_le_card fun n hn => ?_
        simp only [Finset.mem_filter, Set.mem_Icc, Set.mem_Ico] at hn ⊢
        exact ⟨hn.1, hp1_c.trans hn.2.1, hq2_strict _ (Int.fract_lt_one _) hn.2.2⟩
      exact_mod_cast hcard
    exact hle.trans_lt hN
  -- Lower bound
  have hlower_ev : ∀ᶠ N in atTop, (d - c) - ε < C_cnt N := by
    by_cases hsmall : d - c < ε / 2
    · filter_upwards with N
      have hnonneg : 0 ≤ C_cnt N := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      linarith
    · push Not at hsmall
      obtain ⟨p2, hp2_gt, hp2_lt⟩ := exists_rat_btwn (show c < c + ε / 4 by linarith)
      obtain ⟨q1, hq1_gt, hq1_lt⟩ := exists_rat_btwn (show d - ε / 4 < d by linarith)
      have hp2_le_q1 : (p2 : ℝ) ≤ (q1 : ℝ) := by linarith
      have htend_l : Tendsto (fun N => F (q1 : ℝ) N - F (p2 : ℝ) N) atTop
          (𝓝 ((q1 : ℝ) - (p2 : ℝ))) :=
        (hF_tend q1 (by linarith) (hq1_lt.le.trans hd1)).sub
          (hF_tend p2 (hc0.trans hp2_gt.le) (by linarith))
      have hgt_lim : (d - c) - ε < (q1 : ℝ) - (p2 : ℝ) := by linarith
      filter_upwards [htend_l.eventually (lt_mem_nhds hgt_lim)] with N hN
      have hle : F (q1 : ℝ) N - F (p2 : ℝ) N ≤ C_cnt N := by
        rw [← hsub_cnt (p2 : ℝ) (q1 : ℝ) N hp2_le_q1]
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
        have hcard :
            ((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico (p2 : ℝ) (q1 : ℝ)).card ≤
              ((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Icc c d).card := by
          refine Finset.card_le_card fun n hn => ?_
          simp only [Finset.mem_filter, Set.mem_Icc, Set.mem_Ico] at hn ⊢
          exact ⟨hn.1, hp2_gt.le.trans hn.2.1, hn.2.2.le.trans hq1_lt.le⟩
        exact_mod_cast hcard
      exact hN.trans_le hle
  obtain ⟨N₀, hN₀⟩ := (Filter.eventually_atTop.mp (hupper_ev.and hlower_ev))
  refine ⟨N₀, fun N hN => ?_⟩
  rcases hN₀ N hN with ⟨hu, hl⟩
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith, by linarith⟩

theorem OMA.solution : type_of% @Bugeaud61.problem_10_61.variants.almost_every := by
  intro α hα
  have hqM : ∀ (M : ℤ) (q : ℚ),
      ∀ᵐ ξ : ℝ, ξ ∈ Set.Ioc (M : ℝ) (M + 1) →
        (0 : ℝ) ≤ (q : ℝ) → (q : ℝ) ≤ 1 →
        Tendsto (fun N : ℕ => (N : ℝ)⁻¹ *
          ∑ n ∈ Finset.range N, OMA.centeredInd 0 (q : ℝ) (ξ * α ^ (n + 1)))
          atTop (𝓝 0) := by
    intro M q
    by_cases hq : (0 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) ≤ 1
    · filter_upwards [OMA.centeredInd_cesaro_sq_subseq_ae hα hq.1 hq.2 M] with ξ hξ hmem _ _
      exact OMA.real_cesaro_tendsto_of_sq_subseq
        (fun n => OMA.abs_centeredInd_le_one le_rfl hq.1 hq.2 _) (hξ hmem)
    · filter_upwards with ξ _ hq0 hq1
      exact (hq ⟨hq0, hq1⟩).elim
  have hall : ∀ᵐ ξ : ℝ, ∀ (M : ℤ) (q : ℚ),
      ξ ∈ Set.Ioc (M : ℝ) (M + 1) →
      (0 : ℝ) ≤ (q : ℝ) → (q : ℝ) ≤ 1 →
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ *
        ∑ n ∈ Finset.range N, OMA.centeredInd 0 (q : ℝ) (ξ * α ^ (n + 1)))
        atTop (𝓝 0) := by
    rw [MeasureTheory.ae_all_iff]
    intro M
    rw [MeasureTheory.ae_all_iff]
    exact hqM M
  filter_upwards [hall] with ξ hξ
  refine OMA.equidistributed_of_rat_centeredInd fun q hq0 hq1 => ?_
  have hmem : ξ ∈ Set.Ioc (((⌈ξ⌉ - 1 : ℤ) : ℝ)) (((⌈ξ⌉ - 1 : ℤ) : ℝ) + 1) := by
    push_cast
    exact ⟨by linarith [Int.ceil_lt_add_one ξ], by linarith [Int.le_ceil ξ]⟩
  exact hξ (⌈ξ⌉ - 1) q hmem hq0 hq1
