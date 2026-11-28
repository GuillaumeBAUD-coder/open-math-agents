import OMAStatements.S_mo_475957
import Mathlib

open MeasureTheory Set
open scoped Interval

namespace OMA.H475
open OMA.S_mo_475957

noncomputable def step3 (a b v1 v2 v3 : ℝ) (x : ℝ) : ℝ :=
  if x ≤ a then v1 else if x ≤ b then v2 else v3

lemma step3_meas (a b v1 v2 v3 : ℝ) : Measurable (step3 a b v1 v2 v3) := by
  unfold step3
  exact Measurable.ite (measurableSet_Iic : MeasurableSet {x : ℝ | x ≤ a}) measurable_const
    (Measurable.ite (measurableSet_Iic : MeasurableSet {x : ℝ | x ≤ b}) measurable_const
      measurable_const)

lemma const_on (f : ℝ → ℝ) (c lo hi : ℝ) (hlh : lo ≤ hi) (h : ∀ x ∈ Ioc lo hi, f x = c) :
    IntervalIntegrable f volume lo hi ∧ ∫ x in lo..hi, f x = (hi - lo) * c := by
  have h1 : ∫ x in lo..hi, f x = ∫ x in lo..hi, c := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    rw [uIoc_of_le hlh] at hx
    exact h x hx
  refine ⟨?_, by rw [h1, intervalIntegral.integral_const, smul_eq_mul]⟩
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hlh]
  exact (integrableOn_const (C := c) measure_Ioc_lt_top.ne).congr_fun (fun x hx => (h x hx).symm) measurableSet_Ioc

lemma step3_int (a b v1 v2 v3 : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    IntervalIntegrable (step3 a b v1 v2 v3) volume 0 1 ∧
    ∫ x in (0:ℝ)..1, step3 a b v1 v2 v3 x = a * v1 + (b - a) * v2 + (1 - b) * v3 := by
  obtain ⟨i1, e1⟩ := const_on (step3 a b v1 v2 v3) v1 0 a ha
    (fun x hx => by simp [step3, hx.2])
  obtain ⟨i2, e2⟩ := const_on (step3 a b v1 v2 v3) v2 a b hab
    (fun x hx => by simp [step3, not_le.2 hx.1, hx.2])
  obtain ⟨i3, e3⟩ := const_on (step3 a b v1 v2 v3) v3 b 1 hb (fun x hx => by
    have : a < x := lt_of_le_of_lt hab hx.1
    simp [step3, not_le.2 hx.1, not_le.2 this])
  refine ⟨(i1.trans i2).trans i3, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals (i1.trans i2) i3,
    ← intervalIntegral.integral_add_adjacent_intervals i1 i2, e1, e2, e3]
  ring

lemma comp_step3 (g : ℝ → ℝ) (a b v1 v2 v3 x : ℝ) :
    g (step3 a b v1 v2 v3 x) = step3 a b (g v1) (g v2) (g v3) x := by
  unfold step3; split_ifs <;> rfl

noncomputable def lam (c : ℝ) : ℝ := 4 * c * (1 - c)
noncomputable def mixv (c y x : ℝ) : ℝ := (1 - lam c) * y + lam c * x
noncomputable def fam (c : ℝ) : ℝ → ℝ :=
  step3 (8/15) (6/7) (mixv c (1/8) (1/2)) (mixv c 2 (1/2)) (mixv c 2 4)

lemma lam_bounds (c : ℝ) (hc : c ∈ unitI) : 0 ≤ lam c ∧ lam c ≤ 1 := by
  obtain ⟨h0, h1⟩ := hc
  unfold lam
  constructor
  · nlinarith
  · nlinarith [sq_nonneg (2 * c - 1)]

lemma mixv_pos (c y x : ℝ) (hc : c ∈ unitI) (hy : 1/8 ≤ y) (hx : 1/8 ≤ x) :
    0 < mixv c y x := by
  obtain ⟨l0, l1⟩ := lam_bounds c hc
  unfold mixv
  nlinarith [mul_le_mul_of_nonneg_left hy (sub_nonneg.2 l1), mul_le_mul_of_nonneg_left hx l0]

lemma cost_fam (φ : ℝ → ℝ) (c : ℝ) : cost φ (fam c) =
    8/15 * φ (mixv c (1/8) (1/2)) + (6/7 - 8/15) * φ (mixv c 2 (1/2)) +
      (1 - 6/7) * φ (mixv c 2 4) := by
  unfold cost fam
  simp_rw [comp_step3 φ]
  exact (step3_int _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num)).2

lemma ii_fam (φ : ℝ → ℝ) (c : ℝ) :
    IntervalIntegrable (fun x => φ (fam c x)) volume 0 1 := by
  unfold fam
  simp_rw [comp_step3 φ]
  exact (step3_int _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num)).1

lemma mixv_half (y x : ℝ) : mixv (1/2) y x = x := by
  unfold mixv lam; ring

lemma mixv_zero (y x : ℝ) : mixv 0 y x = y := by
  unfold mixv lam; ring

lemma part1 : ∃ p : ℝ → ℝ → ℝ,
      (∀ x, Continuous (fun c => p c x)) ∧
      (∀ c ∈ unitI, Measurable (p c) ∧ (∀ x ∈ unitI, 0 < p c x) ∧
        (∫ x in (0:ℝ)..1, p c x) = 1 ∧
        (∀ m : ℕ, IntervalIntegrable (fun x => p c x ^ m) volume 0 1) ∧
        IntervalIntegrable (fun x => p c x * Real.log (p c x)) volume 0 1) ∧
      (∀ m : ℕ, 0 < m → ∀ c ∈ unitI, power m (p c) ≤ power m (p (1/2))) ∧
      (∀ m : ℕ, 2 ≤ m → ∀ c ∈ unitI, c ≠ 1/2 → power m (p c) < power m (p (1/2))) ∧
      info (p (1/2)) < info (p 0) := by
  have hstrict : ∀ m : ℕ, 2 ≤ m → ∀ c ∈ unitI, c ≠ 1/2 →
      power m (fam c) < power m (fam (1/2)) := by
    intro m hm c hc hne
    obtain ⟨l0, l1⟩ := lam_bounds c hc
    have llt : lam c < 1 := by
      unfold lam
      have : 2 * c - 1 ≠ 0 := by
        intro h; apply hne; linarith
      have := pow_pos (abs_pos.2 this) 2
      rw [sq_abs] at this
      nlinarith
    have cv : ∀ y x : ℝ, 0 ≤ y → 0 ≤ x →
        mixv c y x ^ m ≤ (1 - lam c) * y ^ m + lam c * x ^ m := by
      intro y x hy hx
      have := (convexOn_pow m).2 (show y ∈ Ici (0:ℝ) from hy) (show x ∈ Ici (0:ℝ) from hx)
        (sub_nonneg.2 l1) l0 (by ring)
      simpa [mixv, smul_eq_mul] using this
    unfold power
    rw [cost_fam, cost_fam]
    simp only [mixv_half]
    have c1 := cv (1/8) (1/2) (by norm_num) (by norm_num)
    have c2 := cv 2 (1/2) (by norm_num) (by norm_num)
    have c3 := cv 2 4 (by norm_num) (by norm_num)
    have t4 : (4:ℝ) ^ m = 2 ^ m * 2 ^ m := by
      rw [← mul_pow]; norm_num
    have t2 : (4:ℝ) ≤ 2 ^ m := by
      calc (4:ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
    have s0 : (0:ℝ) < (1/2) ^ m := by positivity
    have r8 : ((1:ℝ)/8) ^ m ≤ (1/2) ^ m := pow_le_pow_left₀ (by norm_num) (by norm_num) m
    have key : 8/15 * ((1:ℝ)/8) ^ m + (6/7 - 8/15) * 2 ^ m + (1 - 6/7) * 2 ^ m <
        8/15 * ((1:ℝ)/2) ^ m + (6/7 - 8/15) * (1/2) ^ m + (1 - 6/7) * 4 ^ m := by
      rw [t4]; nlinarith
    nlinarith
  refine ⟨fam, ?_, ?_, ?_, hstrict, ?_⟩
  · intro x
    have hc : ∀ y z : ℝ, Continuous (fun c => mixv c y z) := by
      intro y z; unfold mixv lam; fun_prop
    unfold fam step3
    split_ifs
    · exact hc _ _
    · exact hc _ _
    · exact hc _ _
  · intro c hc
    refine ⟨step3_meas _ _ _ _ _, ?_, ?_, ?_, ?_⟩
    · intro x _
      unfold fam step3
      split_ifs
      · exact mixv_pos _ _ _ hc (by norm_num) (by norm_num)
      · exact mixv_pos _ _ _ hc (by norm_num) (by norm_num)
      · exact mixv_pos _ _ _ hc (by norm_num) (by norm_num)
    · have := cost_fam (fun z => z) c
      unfold cost at this
      rw [this]; unfold mixv; ring
    · intro m; exact ii_fam (fun z => z ^ m) c
    · exact ii_fam (fun z => z * Real.log z) c
  · intro m hm c hc
    rcases Nat.lt_or_ge m 2 with h | h
    · have : m = 1 := by omega
      subst this
      unfold power
      rw [cost_fam, cost_fam]
      apply le_of_eq
      unfold mixv lam; ring
    · by_cases hne : c = 1/2
      · rw [hne]
      · exact (hstrict m h c hc hne).le
  · unfold info
    rw [cost_fam, cost_fam]
    simp only [mixv_half, mixv_zero]
    have l2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have h8 : Real.log (1/8) = -(3 * Real.log 2) := by
      rw [one_div, Real.log_inv, show (8:ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
    have h12 : Real.log (1/2) = -Real.log 2 := by rw [one_div, Real.log_inv]
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    rw [h8, h12, h4]
    nlinarith

lemma part2 (q φ : ℝ → ℝ) (hq : ContinuousOn q unitI) (hq0 : ∀ x ∈ unitI, 0 ≤ q x)
    (hq1 : ∫ x in (0:ℝ)..1, q x = 1) (hφ : Continuous φ) (hcv : ConvexOn ℝ (Ici 0) φ)
    (c : ℝ) (hc : c ∈ unitI) : cost φ (mix c (fun _ => 1) q) ≤ cost φ q := by
  have hqi : IntervalIntegrable q volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]; exact hq
  have hi2 : IntervalIntegrable (fun x => φ (q x)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact hφ.comp_continuousOn hq
  have hi1 : IntervalIntegrable (fun x => φ (mix c (fun _ => 1) q x)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    unfold mix
    exact hφ.comp_continuousOn (continuousOn_const.add (continuousOn_const.mul hq))
  have hJ : φ 1 ≤ ∫ x in (0:ℝ)..1, φ (q x) := by
    rw [intervalIntegral.integral_of_le zero_le_one] at hq1 ⊢
    have : IsProbabilityMeasure (volume.restrict (Ioc (0:ℝ) 1)) :=
      ⟨by simp [Real.volume_Ioc]⟩
    have hfs : ∀ᵐ x ∂(volume.restrict (Ioc (0:ℝ) 1)), q x ∈ Ici (0:ℝ) := by
      rw [ae_restrict_iff' measurableSet_Ioc]
      exact Filter.Eventually.of_forall (fun x hx => hq0 x ⟨hx.1.le, hx.2⟩)
    have := hcv.map_integral_le hφ.continuousOn isClosed_Ici hfs
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hqi)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hi2)
    rwa [hq1] at this
  have hpt : ∀ x ∈ Icc (0:ℝ) 1, φ (mix c (fun _ => 1) q x) ≤ (1 - c) * φ 1 + c * φ (q x) := by
    intro x hx
    have := hcv.2 (show (1:ℝ) ∈ Ici 0 by simp) (show q x ∈ Ici 0 from hq0 x hx)
      (sub_nonneg.2 hc.2) hc.1 (by ring)
    simpa [mix, smul_eq_mul] using this
  unfold cost
  calc ∫ x in (0:ℝ)..1, φ (mix c (fun _ => 1) q x)
      ≤ ∫ x in (0:ℝ)..1, ((1 - c) * φ 1 + c * φ (q x)) :=
        intervalIntegral.integral_mono_on zero_le_one hi1
          (intervalIntegrable_const.add (hi2.const_mul c)) hpt
    _ = (1 - c) * φ 1 + c * ∫ x in (0:ℝ)..1, φ (q x) := by
        rw [intervalIntegral.integral_add intervalIntegrable_const (hi2.const_mul c),
          intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
        simp
    _ ≤ _ := by nlinarith [hc.1, hc.2]

lemma part3 (φ : ℝ → ℝ) (hφ : Continuous φ) (hcv : ConvexOn ℝ (Ici 0) φ) (c : ℝ)
    (hc : c ∈ unitI) : cost φ (cosine c) ≤ cost φ (cosine (1/2)) := by
  obtain ⟨c0, c1⟩ := hc
  have hsq : Real.sqrt (c * (1 - c)) ≤ 1/2 := by
    rw [show (1:ℝ)/2 = Real.sqrt (1/4) by
      rw [show (1:ℝ)/4 = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num)] ]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (2 * c - 1)])
  set a := 2 * Real.sqrt (c * (1 - c)) with ha
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 := by linarith
  have hhalf : cosine (1/2) = fun x => 1 + Real.cos (2 * Real.pi * x) := by
    funext x; unfold cosine
    rw [show (1:ℝ)/2 * (1 - 1/2) = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num)]
    ring
  have cont1 : Continuous (fun x => φ (1 + Real.cos (2 * Real.pi * x))) := by fun_prop
  have cont2 : Continuous (fun x => φ (1 - Real.cos (2 * Real.pi * x))) := by fun_prop
  have hsym : ∫ x in (0:ℝ)..1, φ (1 - Real.cos (2 * Real.pi * x)) =
      ∫ x in (0:ℝ)..1, φ (1 + Real.cos (2 * Real.pi * x)) := by
    have hper : Function.Periodic (fun x => φ (1 + Real.cos (2 * Real.pi * x))) 1 := by
      intro x; simp only
      rw [show 2 * Real.pi * (x + 1) = 2 * Real.pi * x + 2 * Real.pi by ring, Real.cos_add_two_pi]
    have e1 : ∀ x, φ (1 - Real.cos (2 * Real.pi * x)) =
        φ (1 + Real.cos (2 * Real.pi * (x + 1/2))) := by
      intro x
      rw [show 2 * Real.pi * (x + 1/2) = 2 * Real.pi * x + Real.pi by ring, Real.cos_add_pi]
      ring_nf
    simp_rw [e1]
    rw [intervalIntegral.integral_comp_add_right
      (fun x => φ (1 + Real.cos (2 * Real.pi * x))) (1/2)]
    have := hper.intervalIntegral_add_eq (1/2) 0
    norm_num at this ⊢
    exact this
  have hpt : ∀ x ∈ Icc (0:ℝ) 1, φ (cosine c x) ≤
      (1 + a) / 2 * φ (1 + Real.cos (2 * Real.pi * x)) +
        (1 - a) / 2 * φ (1 - Real.cos (2 * Real.pi * x)) := by
    intro x _
    have hc1 := Real.neg_one_le_cos (2 * Real.pi * x)
    have hc2 := Real.cos_le_one (2 * Real.pi * x)
    have := hcv.2 (show 1 + Real.cos (2 * Real.pi * x) ∈ Ici (0:ℝ) by simp; linarith)
      (show 1 - Real.cos (2 * Real.pi * x) ∈ Ici (0:ℝ) by simp; linarith)
      (show (0:ℝ) ≤ (1 + a) / 2 by linarith) (show (0:ℝ) ≤ (1 - a) / 2 by linarith) (by ring)
    simp only [smul_eq_mul] at this
    have e : (1 + a) / 2 * (1 + Real.cos (2 * Real.pi * x)) +
        (1 - a) / 2 * (1 - Real.cos (2 * Real.pi * x)) = cosine c x := by
      unfold cosine; rw [ha]; ring
    rw [e] at this
    exact this
  have hi1 : IntervalIntegrable (fun x => φ (cosine c x)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    unfold cosine; fun_prop
  have I1 := cont1.intervalIntegrable (μ := volume) 0 1
  have I2 := cont2.intervalIntegrable (μ := volume) 0 1
  unfold cost
  rw [hhalf]
  calc ∫ x in (0:ℝ)..1, φ (cosine c x)
      ≤ ∫ x in (0:ℝ)..1, ((1 + a) / 2 * φ (1 + Real.cos (2 * Real.pi * x)) +
        (1 - a) / 2 * φ (1 - Real.cos (2 * Real.pi * x))) :=
        intervalIntegral.integral_mono_on zero_le_one hi1
          ((I1.const_mul _).add (I2.const_mul _)) hpt
    _ = ∫ x in (0:ℝ)..1, φ (1 + Real.cos (2 * Real.pi * x)) := by
        rw [intervalIntegral.integral_add (I1.const_mul _) (I2.const_mul _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hsym]
        ring

end OMA.H475

theorem OMA.solution : type_of% @OMA.S_mo_475957.main := by
  refine ⟨OMA.H475.part1, fun q φ hq hq0 hq1 hφ hcv c hc =>
    OMA.H475.part2 q φ hq hq0 hq1 hφ hcv c hc, ?_⟩
  intro c hc
  exact ⟨OMA.H475.part3 _ Real.continuous_mul_log Real.convexOn_mul_log c hc,
    fun m => OMA.H475.part3 _ (continuous_pow m) (convexOn_pow m) c hc⟩
