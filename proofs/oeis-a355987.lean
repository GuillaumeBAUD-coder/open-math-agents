import OMAStatements.S_oeis_a355987

/-!
# Proof of Kotesovec's conjecture for OEIS A355987

Source: https://oeis.org/A355987
Credit: @bmendonca3

`a(n) = n! * Sum_{k=1..n} 1/floor(n/k)!` satisfies `a(n) ~ S * n! * n` with
`S = Sum_{k>=1} 1/((k+1)!*k)`, and `S = 2 - e - gamma + Ei(1)`.

Outline.
* Part A. The number of `k` in `1..n` with `floor(n/k) = m` is `floor(n/m) - floor(n/(m+1))`
  for `m ≥ 1`. So `a(n) / (n! * n) = ∑_m (A_cnt n m / n) / m!`. Each term is at most `1/m!`
  and tends to `(1/m - 1/(m+1)) / m!`. Tannery's theorem gives the limit
  `∑_{m≥1} 1/(m (m+1) m!) = S`, and `S > 0`.
* Part B. The substitution `t ↦ -t` and an integration by parts on `(ε, ∞)` give, for `ε > 0`,
  `EiOneCut ε = (e^{-ε} - 1) log ε - ∫_ε^∞ log x e^{-x} dx + ∫_ε^1 (e^x - 1)/x dx`.
  As `ε → 0+` the first term tends to `0`, the second integral tends to
  `∫_0^∞ log x e^{-x} dx = Γ'(1) = -γ`, and the third tends to
  `∫_0^1 (e^x - 1)/x dx = ∑_{k≥1} 1/(k k!)` (termwise integration of the exponential series).
  So `Ei(1) = γ + ∑_{k≥1} 1/(k k!)`. The identity `1/(k k!) - 1/(k+1)! = 1/(k (k+1)!)` and
  `∑_{k≥1} 1/(k+1)! = e - 2` finish the proof.
-/

namespace OMA.A355987Proof

open OMA.S_oeis_a355987 Filter Asymptotics Topology MeasureTheory
open scoped Nat

/-! ## Part A: the asymptotic formula -/

/-- The series of reciprocal factorials converges. -/
lemma A_summable_inv_factorial : Summable (fun m : ℕ => 1 / (m ! : ℝ)) := by
  simpa using Real.summable_pow_div_factorial 1

/-- The series that defines `S` converges. -/
lemma summable_S_term :
    Summable (fun k : ℕ => 1 / ((((k + 1) + 1)! : ℝ) * ((k + 1 : ℕ) : ℝ))) := by
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((summable_nat_add_iff 2).mpr A_summable_inv_factorial)
  apply one_div_le_one_div_of_le (by positivity)
  exact le_mul_of_one_le_right (by positivity) (by exact_mod_cast Nat.succ_pos k)

/-- `S` is positive. -/
lemma S_pos : 0 < S :=
  summable_S_term.tsum_pos (fun k => by positivity) 0 (by positivity)

/-- The number of `k` in `1..n` with `⌊n/k⌋ = m`. -/
def A_cnt (n m : ℕ) : ℕ := ((Finset.Icc 1 n).filter (fun k => n / k = m)).card

/-- For `m ≥ 1` the indices `k` with `⌊n/k⌋ = m` are those with `n/(m+1) < k ≤ n/m`. -/
lemma A_cnt_eq (n m : ℕ) (hm : 1 ≤ m) : A_cnt n m = n / m - n / (m + 1) := by
  have h : (Finset.Icc 1 n).filter (fun k => n / k = m) = Finset.Ioc (n / (m + 1)) (n / m) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hk1, -⟩, rfl⟩
      exact ⟨(Nat.div_lt_iff_lt_mul (by omega)).mpr (Nat.lt_mul_div_succ n (by omega)),
        (Nat.le_div_iff_mul_le (by omega)).mpr (Nat.mul_div_le n k)⟩
    · rintro ⟨h1, h2⟩
      have hk : 0 < k := lt_of_le_of_lt (Nat.zero_le _) h1
      rw [Nat.div_lt_iff_lt_mul (by omega)] at h1
      rw [Nat.le_div_iff_mul_le (by omega)] at h2
      have h3 : m ≤ n / k := (Nat.le_div_iff_mul_le hk).mpr (by linarith [mul_comm k m])
      have h4 : n / k < m + 1 := (Nat.div_lt_iff_lt_mul hk).mpr (by linarith [mul_comm k (m + 1)])
      exact ⟨⟨hk, by nlinarith⟩, by omega⟩
  rw [A_cnt, h, Nat.card_Ioc]

/-- No index `k` in `1..n` has `⌊n/k⌋ = 0`. -/
lemma A_cnt_zero (n : ℕ) : A_cnt n 0 = 0 := by
  rw [A_cnt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro k hk
  have := Nat.div_pos (Finset.mem_Icc.mp hk).2 (Finset.mem_Icc.mp hk).1
  omega

/-- At most `n` indices are counted. -/
lemma A_cnt_le (n m : ℕ) : A_cnt n m ≤ n := by
  simpa [A_cnt] using Finset.card_filter_le (Finset.Icc 1 n) (fun k => n / k = m)

/-- The sum over `k` regrouped by the value `m = ⌊n/k⌋`. -/
lemma A_regroup (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, 1 / ((n / k)! : ℝ) = ∑' m : ℕ, (A_cnt n m : ℝ) / (m ! : ℝ) := by
  have h0 : ∀ m ∉ Finset.range (n + 1), (A_cnt n m : ℝ) / (m ! : ℝ) = 0 := by
    intro m hm
    have h : A_cnt n m = 0 := by
      rw [A_cnt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k _ hk
      have := Nat.div_le_self n k
      simp only [Finset.mem_range] at hm
      omega
    simp [h]
  rw [tsum_eq_sum h0, ← Finset.sum_fiberwise_of_maps_to (g := fun k => n / k)
    (t := Finset.range (n + 1))
    (fun k _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_self n k)))]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have h : ∑ k ∈ Finset.Icc 1 n with n / k = m, 1 / ((n / k)! : ℝ)
      = ∑ k ∈ Finset.Icc 1 n with n / k = m, 1 / (m ! : ℝ) :=
    Finset.sum_congr rfl (fun k hk => by rw [(Finset.mem_filter.mp hk).2])
  rw [h, Finset.sum_const, A_cnt, nsmul_eq_mul]
  ring

/-- `⌊n/d⌋ / n` tends to `1/d`. -/
lemma A_tendsto_div (d : ℕ) :
    Tendsto (fun n : ℕ => ((n / d : ℕ) : ℝ) / n) atTop (𝓝 (1 / (d : ℝ))) := by
  have h := (tendsto_nat_floor_mul_div_atTop (R := ℝ) (a := 1 / (d : ℝ)) (by positivity)).comp
    tendsto_natCast_atTop_atTop
  refine h.congr (fun n => ?_)
  simp only [Function.comp]
  rw [show 1 / (d : ℝ) * (n : ℝ) = (n : ℝ) / (d : ℝ) by ring, Nat.floor_div_eq_div]

/-- The termwise limit in Tannery's theorem. -/
noncomputable def A_lim (m : ℕ) : ℝ :=
  if m = 0 then 0 else (1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ)) / (m ! : ℝ)

/-- Each term of the regrouped sum converges. -/
lemma A_tendsto_term (m : ℕ) :
    Tendsto (fun n : ℕ => (A_cnt n m : ℝ) / n / (m ! : ℝ)) atTop (𝓝 (A_lim m)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [A_cnt_zero, A_lim]
  · rw [A_lim, if_neg (by omega)]
    refine (((A_tendsto_div m).sub (A_tendsto_div (m + 1))).div_const _).congr (fun n => ?_)
    rw [A_cnt_eq n m hm, Nat.cast_sub (Nat.div_le_div_left (by omega) hm)]
    ring

/-- `a(n) / (n! * n)` tends to `S`. -/
lemma A_tendsto_ratio :
    Tendsto (fun n : ℕ => ∑' m : ℕ, (A_cnt n m : ℝ) / n / (m ! : ℝ)) atTop (𝓝 S) := by
  have hS : ∑' m : ℕ, A_lim m = S := by
    have hterm : ∀ k : ℕ, A_lim (k + 1) = 1 / ((((k + 1) + 1)! : ℝ) * ((k + 1 : ℕ) : ℝ)) := by
      intro k
      rw [A_lim, if_neg (by omega), Nat.factorial_succ (k + 1)]
      push_cast
      field_simp
      ring
    rw [tsum_eq_zero_add' (by simpa only [hterm] using summable_S_term)]
    simp only [hterm, S]
    simp [A_lim]
  rw [← hS]
  refine tendsto_tsum_of_dominated_convergence A_summable_inv_factorial A_tendsto_term
    (Eventually.of_forall (fun n m => ?_))
  rw [Real.norm_of_nonneg (by positivity)]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact div_le_one_of_le₀ (by exact_mod_cast A_cnt_le n m) (by positivity)

/-- Part A: `a(n) ~ S * n! * n`. -/
theorem partA :
    (fun n : ℕ => (a n : ℝ)) ~[atTop] (fun n : ℕ => S * (n ! : ℝ) * (n : ℝ)) := by
  refine isEquivalent_iff_exists_eq_mul.mpr
    ⟨fun n => (∑' m : ℕ, (A_cnt n m : ℝ) / n / (m ! : ℝ)) / S, ?_, ?_⟩
  · simpa [S_pos.ne'] using A_tendsto_ratio.div_const S
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have h1 : (a n : ℝ) = (n ! : ℝ) * ∑ k ∈ Finset.Icc 1 n, 1 / ((n / k)! : ℝ) := by
      simp [a]
    have h2 : ∑' m : ℕ, (A_cnt n m : ℝ) / n / (m ! : ℝ)
        = (∑' m : ℕ, (A_cnt n m : ℝ) / (m ! : ℝ)) / n := by
      rw [← tsum_div_const]
      exact tsum_congr (fun m => by ring)
    simp only [Pi.mul_apply]
    rw [h1, A_regroup, h2]
    field_simp [S_pos.ne']

/-! ## Part B: the closed form with the principal value `Ei(1)` -/

/-- `∫_0^∞ log t e^{-t} dt = Γ'(1) = -γ`. -/
lemma B_integral_log_exp :
    ∫ t in Set.Ioi (0 : ℝ), Real.log t * Real.exp (-t) = -Real.eulerMascheroniConstant := by
  have h1 : HasDerivAt Complex.GammaIntegral (-(Real.eulerMascheroniConstant : ℂ)) 1 := by
    refine Complex.hasDerivAt_Gamma_one.congr_of_eventuallyEq ?_
    have h : ∀ᶠ s : ℂ in 𝓝 1, 0 < s.re :=
      Complex.continuous_re.continuousAt.eventually (lt_mem_nhds (by simp))
    filter_upwards [h] with s hs
    exact (Complex.Gamma_eq_integral hs).symm
  have h3 := (Complex.hasDerivAt_GammaIntegral (s := 1) (by simp)).unique h1
  have h4 : ∫ t in Set.Ioi (0 : ℝ), ((Real.log t * Real.exp (-t) : ℝ) : ℂ)
      = -(Real.eulerMascheroniConstant : ℂ) := by
    rw [← h3]
    congr 1
    ext t
    simp
  rw [integral_complex_ofReal] at h4
  exact_mod_cast h4

/-- `log t e^{-t}` is integrable on `(0, ∞)`: its integral is not zero. -/
lemma B_integrableOn_log_exp :
    IntegrableOn (fun t : ℝ => Real.log t * Real.exp (-t)) (Set.Ioi 0) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [B_integral_log_exp]
  linarith [Real.one_half_lt_eulerMascheroniConstant]

/-- `e^{-x} / x` is integrable on `(ε, ∞)` for `ε > 0`. -/
lemma B_integrableOn_exp_div {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun x : ℝ => Real.exp (-x) / x) (Set.Ioi ε) := by
  refine Integrable.mono' ((integrableOn_exp_neg_Ioi ε).const_mul ε⁻¹)
    ((Real.measurable_exp.comp measurable_neg).div measurable_id).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx' : 0 < x := hε.trans hx
  rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_eq_inv_mul]
  gcongr
  exact hx.le

/-- Integration by parts on `(ε, ∞)`. -/
lemma B_integral_exp_div {ε : ℝ} (hε : 0 < ε) :
    ∫ x in Set.Ioi ε, Real.exp (-x) / x
      = -(Real.log ε * Real.exp (-ε)) + ∫ x in Set.Ioi ε, Real.log x * Real.exp (-x) := by
  have hg : IntegrableOn (fun t : ℝ => Real.log t * Real.exp (-t)) (Set.Ioi ε) :=
    B_integrableOn_log_exp.mono_set (Set.Ioi_subset_Ioi hε.le)
  have hlim : Tendsto (fun x : ℝ => Real.log x * Real.exp (-x)) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1)
    · filter_upwards [eventually_ge_atTop 1] with x hx
      exact mul_nonneg (Real.log_nonneg hx) (Real.exp_pos _).le
    · filter_upwards [eventually_ge_atTop 1] with x hx
      rw [pow_one]
      gcongr
      exact Real.log_le_self (by linarith)
  have key := integral_Ioi_of_hasDerivAt_of_tendsto' (a := ε)
    (f := fun x : ℝ => Real.log x * Real.exp (-x))
    (f' := fun x : ℝ => Real.exp (-x) / x - Real.log x * Real.exp (-x)) (m := 0)
    (fun x hx => by
      have hx' : 0 < x := hε.trans_le hx
      have h := (Real.hasDerivAt_log hx'.ne').fun_mul ((hasDerivAt_neg x).exp)
      exact h.congr_deriv (by ring))
    ((B_integrableOn_exp_div hε).sub hg) hlim
  rw [integral_sub (B_integrableOn_exp_div hε) hg] at key
  linarith

/-- The part of the cut integral on the negative axis. -/
lemma B_integral_Iic {ε : ℝ} :
    ∫ t in Set.Iic (-ε), Real.exp t / t = -∫ x in Set.Ioi ε, Real.exp (-x) / x := by
  rw [← integral_comp_neg_Ioi ε (fun t => Real.exp t / t), ← integral_neg]
  congr 1
  ext x
  rw [div_neg]

/-- The part of the cut integral on the positive axis. -/
lemma B_integral_pos {ε : ℝ} (hε : 0 < ε) :
    ∫ x in ε..1, Real.exp x / x = (∫ x in ε..1, (Real.exp x - 1) / x) - Real.log ε := by
  have hpos : ∀ x ∈ Set.uIcc ε 1, x ≠ 0 := fun x hx =>
    (lt_of_lt_of_le (lt_min hε one_pos) hx.1).ne'
  have h1 : IntervalIntegrable (fun x : ℝ => (Real.exp x - 1) / x) volume ε 1 :=
    ContinuousOn.intervalIntegrable
      (ContinuousOn.div (by fun_prop) continuousOn_id hpos)
  have h2 : IntervalIntegrable (fun x : ℝ => 1 / x) volume ε 1 :=
    ContinuousOn.intervalIntegrable
      (ContinuousOn.div (by fun_prop) continuousOn_id hpos)
  have h3 : ∫ x in ε..1, Real.exp x / x
      = (∫ x in ε..1, (Real.exp x - 1) / x) + ∫ x in ε..1, 1 / x := by
    rw [← intervalIntegral.integral_add h1 h2]
    congr 1
    ext x
    ring
  rw [h3, integral_one_div_of_pos hε one_pos, one_div, Real.log_inv]
  ring

/-- `(e^x - 1) / x = ∑ x^n / (n+1)!` for `x ≠ 0`. -/
lemma B_hasSum_phi {x : ℝ} (hx : x ≠ 0) :
    HasSum (fun n : ℕ => x ^ n / ((n + 1)! : ℝ)) ((Real.exp x - 1) / x) := by
  have h := NormedSpace.expSeries_div_hasSum_exp x
  rw [← Real.exp_eq_exp_ℝ] at h
  have h2 := ((hasSum_nat_add_iff' 1).mpr h).div_const x
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one,
    div_one] at h2
  have e : (fun n : ℕ => x ^ n / ((n + 1)! : ℝ))
      = fun n : ℕ => x ^ (n + 1) / ((n + 1)! : ℝ) / x := by
    funext n
    field_simp
    ring
  rw [e]
  exact h2

/-- `∫_0^1 (e^x - 1) / x dx = ∑ 1 / ((k+1) (k+1)!)`. -/
lemma B_hasSum_integral_phi :
    HasSum (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ) * ((k + 1)! : ℝ)))
      (∫ x in (0 : ℝ)..1, (Real.exp x - 1) / x) := by
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (a := 0) (b := 1) (f := fun x : ℝ => (Real.exp x - 1) / x)
    (F := fun (n : ℕ) (x : ℝ) => x ^ n / ((n + 1)! : ℝ))
    (fun (n : ℕ) (_ : ℝ) => 1 / ((n + 1)! : ℝ))
    (fun n => by fun_prop)
    (fun n => Eventually.of_forall fun t ht => by
      rw [Set.uIoc_of_le zero_le_one] at ht
      rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht.1.le n),
        Nat.abs_cast]
      gcongr
      exact pow_le_one₀ ht.1.le ht.2)
    (Eventually.of_forall fun t _ => by
      have := (summable_nat_add_iff 1).mpr (Real.summable_pow_div_factorial 1)
      simpa using this)
    intervalIntegrable_const
    (Eventually.of_forall fun t ht => by
      rw [Set.uIoc_of_le zero_le_one] at ht
      exact B_hasSum_phi ht.1.ne')
  have e : (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ) * ((k + 1)! : ℝ)))
      = fun n : ℕ => ∫ t in (0 : ℝ)..1, t ^ n / ((n + 1)! : ℝ) := by
    funext n
    rw [intervalIntegral.integral_div, integral_pow]
    simp
    ring
  rw [e]
  exact h

/-- `(e^x - 1) / x` is integrable on `[0, 1]`: it is bounded by `e` there. -/
lemma B_intervalIntegrable_phi :
    IntervalIntegrable (fun x : ℝ => (Real.exp x - 1) / x) volume 0 1 := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le zero_le_one]
  refine Measure.integrableOn_of_bounded (M := Real.exp 1) (by simp)
    ((Real.measurable_exp.sub measurable_const).div measurable_id).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have h1 : 0 ≤ Real.exp x - 1 := by linarith [Real.add_one_le_exp x, hx.1]
  have h2 : Real.exp x - 1 ≤ x * Real.exp 1 := by
    have h3 := Real.add_one_le_exp (-x)
    have h4 : (-x + 1) * Real.exp x ≤ Real.exp (-x) * Real.exp x :=
      mul_le_mul_of_nonneg_right h3 (Real.exp_pos x).le
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h4
    have h5 : x * Real.exp x ≤ x * Real.exp 1 :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hx.2) hx.1.le
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg h1 hx.1.le), div_le_iff₀ hx.1]
  linarith

/-- `(e^{-ε} - 1) log ε → 0` as `ε → 0+`. -/
lemma B_tendsto_boundary :
    Tendsto (fun ε : ℝ => (Real.exp (-ε) - 1) * Real.log ε) (𝓝[>] 0) (𝓝 0) := by
  have h0 : Tendsto (fun ε : ℝ => |ε * Real.log ε|) (𝓝[>] 0) (𝓝 0) := by
    have h := (Real.continuous_mul_log.abs.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using h
  refine squeeze_zero_norm' ?_ h0
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (0 : ℝ) < ε := hε
  have h1 : Real.exp (-ε) - 1 ≤ 0 := by
    have := Real.exp_le_exp.mpr (neg_nonpos.mpr hε'.le)
    rw [Real.exp_zero] at this
    linarith
  have h2 : |Real.exp (-ε) - 1| ≤ |ε| := by
    rw [abs_of_nonpos h1, abs_of_pos hε']
    linarith [Real.add_one_le_exp (-ε)]
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_right h2 (abs_nonneg _)

/-- `∫_ε^1 (e^x - 1) / x dx → ∫_0^1 (e^x - 1) / x dx` as `ε → 0+`. -/
lemma B_tendsto_phi :
    Tendsto (fun ε : ℝ => ∫ x in ε..1, (Real.exp x - 1) / x) (𝓝[>] 0)
      (𝓝 (∫ x in (0 : ℝ)..1, (Real.exp x - 1) / x)) := by
  have h := intervalIntegral.continuousWithinAt_primitive (μ := volume) (a := 1) (b₀ := 0)
    (b₁ := 0) (b₂ := 1) (f := fun x : ℝ => (Real.exp x - 1) / x) (by simp)
    (by simpa using B_intervalIntegrable_phi)
  have h2 := (h.mono Set.Ioc_subset_Icc_self).tendsto
  rw [nhdsWithin_Ioc_eq_nhdsGT zero_lt_one] at h2
  have h3 := h2.neg
  simp only [← intervalIntegral.integral_symm] at h3
  exact h3

/-- `∫_ε^∞ log x e^{-x} dx → -γ` as `ε → 0+`. -/
lemma B_tendsto_log_exp :
    Tendsto (fun ε : ℝ => ∫ x in Set.Ioi ε, Real.log x * Real.exp (-x)) (𝓝[>] 0)
      (𝓝 (-Real.eulerMascheroniConstant)) := by
  have hint : IntervalIntegrable (fun t : ℝ => Real.log t * Real.exp (-t)) volume 0 1 := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le zero_le_one]
    exact B_integrableOn_log_exp.mono_set Set.Ioc_subset_Ioi_self
  have h := intervalIntegral.continuousWithinAt_primitive (μ := volume) (a := 0) (b₀ := 0)
    (b₁ := 0) (b₂ := 1) (f := fun t : ℝ => Real.log t * Real.exp (-t)) (by simp)
    (by simpa using hint)
  have h2 := (h.mono Set.Ioc_subset_Icc_self).tendsto
  rw [nhdsWithin_Ioc_eq_nhdsGT zero_lt_one, intervalIntegral.integral_same] at h2
  have h3 := (tendsto_const_nhds (x := -Real.eulerMascheroniConstant)).sub h2
  rw [sub_zero] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (0 : ℝ) < ε := hε
  rw [← B_integral_log_exp, ← intervalIntegral.integral_interval_add_Ioi B_integrableOn_log_exp
    (B_integrableOn_log_exp.mono_set (Set.Ioi_subset_Ioi hε'.le))]
  ring

/-- The principal value: `Ei(1) = γ + ∑ 1 / ((k+1) (k+1)!)`. -/
lemma B_tendsto_EiOneCut :
    Tendsto EiOneCut (𝓝[>] 0)
      (𝓝 (Real.eulerMascheroniConstant + ∫ x in (0 : ℝ)..1, (Real.exp x - 1) / x)) := by
  have h := (B_tendsto_boundary.sub B_tendsto_log_exp).add B_tendsto_phi
  rw [zero_sub, neg_neg] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (0 : ℝ) < ε := hε
  rw [EiOneCut, B_integral_Iic, B_integral_exp_div hε', B_integral_pos hε']
  ring

/-- `∑ 1 / (k+2)! = e - 2`. -/
lemma B_hasSum_factorial :
    HasSum (fun k : ℕ => 1 / (((k + 1) + 1)! : ℝ)) (Real.exp 1 - 2) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (1 : ℝ)
  rw [← Real.exp_eq_exp_ℝ] at h
  have h2 := (hasSum_nat_add_iff' 2).mpr h
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, one_pow,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, div_one, zero_add] at h2
  have e : Real.exp 1 - 2 = Real.exp 1 - (1 + 1) := by ring
  rw [e]
  exact h2

/-- Part B: the principal value exists and `S = 2 - e - γ + Ei(1)`. -/
theorem partB : ∃ Ei1 : ℝ, Tendsto EiOneCut (𝓝[>] 0) (𝓝 Ei1) ∧
    S = 2 - Real.exp 1 - Real.eulerMascheroniConstant + Ei1 := by
  refine ⟨_, B_tendsto_EiOneCut, ?_⟩
  have h := B_hasSum_integral_phi.sub B_hasSum_factorial
  have e : (fun k : ℕ => 1 / ((((k + 1) + 1)! : ℝ) * ((k + 1 : ℕ) : ℝ)))
      = fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ) * ((k + 1)! : ℝ)) - 1 / (((k + 1) + 1)! : ℝ) := by
    funext k
    rw [Nat.factorial_succ (k + 1)]
    push_cast
    field_simp
    ring
  rw [S, e, h.tsum_eq]
  ring

end OMA.A355987Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a355987.main := by
  exact ⟨OMA.A355987Proof.partA, OMA.A355987Proof.partB⟩
