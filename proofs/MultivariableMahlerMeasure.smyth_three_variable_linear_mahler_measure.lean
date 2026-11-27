import FormalConjectures.Wikipedia.MultivariableMahlerMeasure
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Smyth's three-variable linear Mahler measure

A measure-preserving torus shear and Jensen's formula reduce the
three-variable integral to the average of a maximum of two linear
magnitudes. Reflection and Fubini give a weighted log-sine integral.
Integrate its damped cosine modes, then take the limit and sum the
odd reciprocal cubes.

See Smyth's calculation in Boyd (1981), Appendix 1,
https://doi.org/10.4153/CMB-1981-069-5.
-/

/-
# The logarithm series on a damped circle

The Taylor series gives the real Fourier coefficients. A uniform bound by an integrable
logarithmic function permits passage to the undamped weighted integral.
-/

open Filter MeasureTheory
open scoped Topology

namespace SmythFourier

noncomputable def rotation (t : ℝ) : ℂ :=
  Complex.exp (((2*t : ℝ) : ℂ)*Complex.I)

noncomputable def damped (r t : ℝ) : ℝ :=
  Real.log ‖(1:ℂ)-(r:ℂ)*rotation t‖

theorem norm_rotation (t : ℝ) : ‖rotation t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem rotation_pow (t : ℝ) (n : ℕ) :
    rotation t ^ n = Complex.exp (((2*(n : ℝ)*t : ℝ) : ℂ)*Complex.I) := by
  unfold rotation
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem re_exp_rotation (x : ℝ) :
    (Complex.exp ((x : ℂ)*Complex.I)).re = Real.cos x := by
  rw [Complex.exp_re]
  simp [Complex.mul_re, Complex.mul_im]

theorem hasSum_damped {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    HasSum (fun n : ℕ => r^n * Real.cos (2*(n : ℝ)*t)/(n : ℝ)) (-damped r t) := by
  let z := (r : ℂ)*rotation t
  have hz : ‖z‖ < 1 := by
    simpa [z, norm_mul, norm_rotation, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0] using hr1
  have h := Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log hz)
  simp only [Complex.neg_re, Complex.log_re] at h
  change HasSum _ (-Real.log ‖1-z‖)
  convert h using 1
  ext n
  simp only [z, mul_pow, rotation_pow, ← Complex.ofReal_pow,
    Complex.div_natCast_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, re_exp_rotation]

theorem norm_damped_sq (r t : ℝ) :
    ‖(1:ℂ)-(r:ℂ)*rotation t‖^2 = (1-r)^2+4*r*(Real.sin t)^2 := by
  have hn : ‖(r:ℂ)*rotation t‖ = |r| := by
    rw [norm_mul, norm_rotation, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hre : ((r:ℂ)*rotation t).re = r*Real.cos (2*t) := by
    simp only [rotation, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, re_exp_rotation]
  rw [Complex.sq_norm, Complex.normSq_sub]
  simp only [one_mul, Complex.conj_re, Complex.normSq_eq_norm_sq, norm_one,
    hn, sq_abs, hre]
  rw [Real.cos_two_mul_eq_one_sub]
  ring

theorem norm_damped_ge_sin {r t : ℝ} (hr : 1/2 ≤ r) :
    Real.sin t ≤ ‖(1:ℂ)-(r:ℂ)*rotation t‖ := by
  apply le_of_sq_le_sq
  · rw [norm_damped_sq]
    have h := mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ 4*r by linarith)
      (sq_nonneg (Real.sin t))
    nlinarith [sq_nonneg (1-r)]
  · positivity

theorem norm_damped_le_two {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (t : ℝ) :
    ‖(1:ℂ)-(r:ℂ)*rotation t‖ ≤ 2 := by
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0,
    norm_rotation, mul_one]
  linarith

theorem continuous_damped {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (damped r) := by
  have hcont : Continuous (fun t => (1:ℂ)-(r:ℂ)*rotation t) := by
    unfold rotation
    fun_prop
  apply hcont.norm.log
  intro t h
  have hterm : (1:ℂ) = (r:ℂ)*rotation t := sub_eq_zero.1 (norm_eq_zero.1 h)
  have hn := congrArg (fun z : ℂ => ‖z‖) hterm
  rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0,
    norm_rotation, mul_one] at hn
  exact hr1.ne' hn

theorem norm_damped_one {t : ℝ} (ht : 0 ≤ Real.sin t) :
    ‖(1:ℂ)-(1:ℂ)*rotation t‖ = 2*Real.sin t := by
  rw [one_mul, norm_sub_rev]
  unfold rotation
  rw [mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one,
    show (2*t)/2 = t by ring, Real.norm_of_nonneg (by positivity)]

theorem weighted_bound {r t : ℝ} (hr0 : 1/2 ≤ r) (hr1 : r ≤ 1)
    (ht0 : 0 < t) (ht1 : t ≤ Real.pi/2) :
    ‖t*damped r t‖ ≤ (Real.pi/2)*(Real.log 2 + |Real.log (Real.sin t)|) := by
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith [Real.pi_pos])
  have hnlo := norm_damped_ge_sin (t := t) hr0
  have hn := hs.trans_le hnlo
  have hnhi := norm_damped_le_two (by linarith : 0 ≤ r) hr1 t
  have hlo : Real.log (Real.sin t) ≤ damped r t := Real.log_le_log hs hnlo
  have hhi : damped r t ≤ Real.log 2 := Real.log_le_log hn hnhi
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hb : |damped r t| ≤ Real.log 2 + |Real.log (Real.sin t)| := by
    apply abs_le.2
    constructor
    · linarith [neg_abs_le (Real.log (Real.sin t))]
    · exact hhi.trans (le_add_of_nonneg_right (abs_nonneg _))
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos ht0]
  exact (mul_le_mul_of_nonneg_left hb ht0.le).trans
    (mul_le_mul_of_nonneg_right ht1 (add_nonneg hlog2 (abs_nonneg _)))

theorem weighted_integral_tendsto :
    Tendsto (fun r : ℝ => ∫ t in (0:ℝ)..Real.pi/2, t*damped r t)
      (𝓝[<] (1 : ℝ))
      (𝓝 (∫ t in (0:ℝ)..Real.pi/2, t*Real.log (2*Real.sin t))) := by
  have hr0 : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), 1/2 ≤ r :=
    (eventually_ge_nhds (by norm_num : (1/2 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  have hr1 : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), r < 1 := self_mem_nhdsWithin
  have hI : Set.uIoc (0 : ℝ) (Real.pi/2) = Set.Ioc 0 (Real.pi/2) :=
    Set.uIoc_of_le (by positivity)
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun t => (Real.pi/2)*(Real.log 2 + |Real.log (Real.sin t)|))
  · filter_upwards [hr0, hr1] with r h₀ h₁
    exact (continuous_id.mul (continuous_damped (by linarith) h₁)).aestronglyMeasurable
  · filter_upwards [hr0, hr1] with r h₀ h₁
    exact .of_forall (fun t ht => by
      rw [hI] at ht
      exact weighted_bound h₀ h₁.le ht.1 ht.2)
  · exact (intervalIntegrable_const.add intervalIntegrable_log_sin.abs).const_mul _
  · exact .of_forall (fun t ht => by
      rw [hI] at ht
      have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
        (by linarith [ht.2, Real.pi_pos])
      have hnorm : Continuous (fun r : ℝ => ‖(1:ℂ)-(r:ℂ)*rotation t‖) := by fun_prop
      have hlim : Tendsto (fun r : ℝ => ‖(1:ℂ)-(r:ℂ)*rotation t‖) (𝓝[<] (1:ℝ))
          (𝓝 (2*Real.sin t)) := by
        simpa only [Complex.ofReal_one, norm_damped_one hs.le] using
          (hnorm.continuousAt.continuousWithinAt
            (x := (1:ℝ)) (s := Set.Iio 1)).tendsto
      exact (hlim.log (by positivity)).const_mul t)

end SmythFourier

/- Summing the weighted cosine modes in Smyth's Mahler measure. -/

noncomputable section

namespace SmythModes

open Set Filter MeasureTheory
open scoped Topology BigOperators

private theorem primitive_derivative {k : ℝ} (hk : k ≠ 0) (x : ℝ) :
    HasDerivAt (fun t : ℝ => t * (Real.sin (k*t) / k) + Real.cos (k*t) / k^2)
      (x * Real.cos (k*x)) x := by
  have hlinear : HasDerivAt (fun t : ℝ => k * t) k x := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul k
  have hs := hlinear.sin.div_const k
  have hc := hlinear.cos.div_const (k^2)
  have h := ((hasDerivAt_id x).mul hs).add hc
  change HasDerivAt (fun t : ℝ => t * (Real.sin (k*t) / k) + Real.cos (k*t) / k^2)
    (1 * (Real.sin (k*x) / k) + x * (Real.cos (k*x) * k / k) +
      (-Real.sin (k*x) * k / k^2)) x at h
  have hrate : 1 * (Real.sin (k*x) / k) + x * (Real.cos (k*x) * k / k) +
      (-Real.sin (k*x) * k / k^2) = x * Real.cos (k*x) := by
    field_simp
    ring
  rwa [hrate] at h

private theorem integral_weighted_cos {n : ℕ} (hn : n ≠ 0) :
    (∫ t in (0 : ℝ)..(Real.pi/2), t * Real.cos (2 * (n : ℝ) * t)) =
      ((-1 : ℝ)^n - 1) / (4 * (n : ℝ)^2) := by
  let k := 2 * (n : ℝ)
  have hk : k ≠ 0 := by
    dsimp [k]
    exact mul_ne_zero (by norm_num) (by exact_mod_cast hn)
  have hc : Continuous (fun t : ℝ => t * Real.cos (k*t)) := by fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := Real.pi/2) (fun x _ => primitive_derivative hk x)
    (hc.intervalIntegrable _ _)
  have hangle : k * (Real.pi/2) = n * Real.pi := by dsimp [k]; ring
  rw [hangle, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi] at h
  simp only [zero_div, mul_zero, zero_add, Real.cos_zero] at h
  change (∫ t in (0 : ℝ)..(Real.pi/2), t * Real.cos (k*t)) = _
  rw [h]
  dsimp [k]
  ring

private def mode (r : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  -(r^n / (n : ℝ)) * (t * Real.cos (2 * (n : ℝ) * t))

private def weight (n : ℕ) : ℝ := (1 - (-1 : ℝ)^n) / (4 * (n : ℝ)^3)

private theorem integral_mode (r : ℝ) (n : ℕ) :
    (∫ t in (0 : ℝ)..(Real.pi/2), mode r n t) = r^n * weight n := by
  cases eq_or_ne n 0 with
  | inl h => subst n; simp [mode, weight]
  | inr hn =>
    simp only [mode, intervalIntegral.integral_const_mul, integral_weighted_cos hn, weight]
    have h : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp
    ring

private theorem summable_integral_mode {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1) :
    Summable (fun n : ℕ => ∫ t in Ioc (0 : ℝ) (Real.pi/2), ‖mode r n t‖) := by
  refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) ?_
    ((summable_geometric_of_lt_one hr₀ hr₁).mul_left ((Real.pi/2)^2))
  intro n
  have hpi : 0 < Real.pi/2 := by positivity
  have hinv : ((n : ℝ)⁻¹) ≤ 1 := by
    cases n with
    | zero => simp
    | succ n =>
      exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.succ_pos n)
  have hbound (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) (Real.pi/2)) :
      ‖mode r n t‖ ≤ r^n * (Real.pi/2) := by
    unfold mode
    simp only [norm_mul, norm_neg, Real.norm_eq_abs, abs_div, abs_of_nonneg (pow_nonneg hr₀ n),
      abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) by positivity), abs_of_nonneg ht.1.le]
    rw [div_eq_mul_inv]
    calc
      _ ≤ r^n * t :=
        mul_le_mul (mul_le_of_le_one_right (pow_nonneg hr₀ n) hinv)
          (mul_le_of_le_one_right ht.1.le (Real.abs_cos_le_one _))
          (mul_nonneg ht.1.le (abs_nonneg _)) (pow_nonneg hr₀ n)
      _ ≤ _ := mul_le_mul_of_nonneg_left ht.2 (pow_nonneg hr₀ n)
  have hi := norm_integral_le_of_norm_le_const
    (μ := volume.restrict (Ioc (0 : ℝ) (Real.pi/2)))
    (f := fun t => ‖mode r n t‖)
    ((ae_restrict_iff' measurableSet_Ioc).2
      (ae_of_all volume (fun t ht => by simpa only [Real.norm_of_nonneg (norm_nonneg _)] using hbound t ht)))
  have hVol : (volume.restrict (Ioc (0 : ℝ) (Real.pi/2))).real univ = Real.pi/2 := by
    rw [Measure.real, Measure.restrict_apply_univ]
    exact (Real.volume_real_Ioc_of_le hpi.le).trans (sub_zero _)
  rw [hVol] at hi
  calc
    _ ≤ ‖∫ t in Ioc (0 : ℝ) (Real.pi/2), ‖mode r n t‖‖ := Real.le_norm_self _
    _ ≤ _ := by simpa only [pow_two, mul_assoc, mul_left_comm, mul_comm] using hi

theorem weighted_damped_sum {d : ℝ → ℝ} {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1)
    (hd : ∀ t, HasSum (fun n : ℕ => r^n * Real.cos (2 * (n : ℝ) * t) / (n : ℝ)) (-d t)) :
    (∫ t in (0 : ℝ)..(Real.pi/2), t * d t) = ∑' n, r^n * weight n := by
  have hpi : 0 ≤ Real.pi/2 := by positivity
  have hm (n : ℕ) : Integrable (mode r n) (volume.restrict (Ioc (0 : ℝ) (Real.pi/2))) := by
    have hc : Continuous (mode r n) := by unfold mode; fun_prop
    exact (hc.intervalIntegrable 0 (Real.pi/2)).1
  have h (t : ℝ) : (∑' n, mode r n t) = t * d t := by
    have hs := (hd t).mul_left (-t)
    have hmodes : (fun n : ℕ => -t * (r^n * Real.cos (2 * (n : ℝ) * t) / (n : ℝ))) =
        (fun n => mode r n t) := by
      funext n
      unfold mode
      ring
    rw [hmodes, neg_mul_neg] at hs
    exact hs.tsum_eq
  rw [intervalIntegral.integral_of_le hpi]
  simp_rw [← h]
  rw [← integral_tsum_of_summable_integral_norm hm (summable_integral_mode hr₀ hr₁)]
  apply tsum_congr
  intro n
  rw [← intervalIntegral.integral_of_le hpi, integral_mode]

private def invCube (n : ℕ) : ℝ := 1 / (n : ℝ)^3

private theorem summable_invCube : Summable invCube := by
  change Summable (fun n : ℕ => 1 / (n : ℝ)^3)
  simpa only [one_div] using (Real.summable_nat_pow_inv (p := 3)).mpr (by decide)

private theorem invCube_sum : (∑' n, invCube n) = (riemannZeta 3).re := by
  have h := (Complex.ofRealCLM.hasSum summable_invCube.hasSum).tsum_eq
  have hZ := zeta_nat_eq_tsum_of_gt_one (k := 3) (by decide)
  have hcast (n : ℕ) : (↑(invCube n) : ℂ) = 1 / (n : ℂ)^3 := by
    simp only [invCube, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_one,
      Complex.ofReal_natCast]
  change (∑' n, (↑(invCube n) : ℂ)) = (↑(∑' n, invCube n) : ℂ) at h
  simp only [hcast] at h
  rw [h] at hZ
  exact (by simpa only [Nat.cast_ofNat, Complex.ofReal_re] using congrArg Complex.re hZ.symm)

private theorem weight_nonneg (n : ℕ) : 0 ≤ weight n := by
  unfold weight
  apply div_nonneg ?_ (by positivity)
  have h := le_abs_self ((-1 : ℝ)^n)
  rw [abs_pow, abs_neg, abs_one, one_pow] at h
  linarith

private theorem weight_le_invCube (n : ℕ) : weight n ≤ invCube n := by
  unfold weight invCube
  have h := neg_abs_le ((-1 : ℝ)^n)
  rw [abs_pow, abs_neg, abs_one, one_pow] at h
  have hsplit : (1 - (-1 : ℝ)^n) / (4 * (n : ℝ)^3) =
      ((1 - (-1 : ℝ)^n) / 4) * (1 / (n : ℝ)^3) := by
    rw [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hsplit]
  exact mul_le_of_le_one_left (by positivity) (by linarith)

private theorem weight_sum : (∑' n, weight n) = (7/16 : ℝ) * (riemannZeta 3).re := by
  have hE : Function.Injective (fun n : ℕ => 2*n) := by intro a b h; change 2*a = 2*b at h; omega
  have hO : Function.Injective (fun n : ℕ => 2*n+1) := by intro a b h; change 2*a+1 = 2*b+1 at h; omega
  have haE := summable_invCube.comp_injective hE
  have haO := summable_invCube.comp_injective hO
  have hEven (n : ℕ) : invCube (2*n) = (1/8 : ℝ) * invCube n := by
    simp only [invCube, Nat.cast_mul, Nat.cast_ofNat, mul_pow]
    rw [show (2 : ℝ)^3 = 8 by norm_num]
    rw [div_eq_mul_inv, mul_inv_rev]
    ring
  have ha := tsum_even_add_odd haE haO
  simp_rw [hEven] at ha
  rw [tsum_mul_left, invCube_sum] at ha
  have hb : Summable weight :=
    Summable.of_nonneg_of_le weight_nonneg weight_le_invCube summable_invCube
  have hWeightEven (n : ℕ) : weight (2*n) = 0 := by
    simp [weight, pow_mul]
  have hWeightOdd (n : ℕ) : weight (2*n+1) = (1/2 : ℝ) * invCube (2*n+1) := by
    simp only [weight, invCube, pow_succ, pow_mul]
    rw [div_eq_mul_inv, mul_inv_rev]
    ring
  have hb' := tsum_even_add_odd (hb.comp_injective hE) (hb.comp_injective hO)
  simp_rw [hWeightEven, hWeightOdd] at hb'
  rw [tsum_zero, zero_add, tsum_mul_left] at hb'
  linarith

theorem integral_log_sin_weighted {d : ℝ → ℝ → ℝ}
    (hd : ∀ r : ℝ, 0 ≤ r → r < 1 → ∀ t,
      HasSum (fun n : ℕ => r^n * Real.cos (2 * (n : ℝ) * t) / (n : ℝ)) (-d r t))
    (hlim : Tendsto (fun r : ℝ => ∫ t in (0 : ℝ)..(Real.pi/2), t * d r t)
      (𝓝[<] (1 : ℝ)) (𝓝 (∫ t in (0 : ℝ)..(Real.pi/2), t * Real.log (2 * Real.sin t)))) :
    (∫ t in (0 : ℝ)..(Real.pi/2), t * Real.log (2 * Real.sin t)) =
      (7/16 : ℝ) * (riemannZeta 3).re := by
  have hr₀ : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), 0 ≤ r :=
    mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds zero_lt_one)
  have hr₁ : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), r < 1 := self_mem_nhdsWithin
  have hSum : Tendsto (fun r : ℝ => ∑' n, r^n * weight n) (𝓝[<] (1 : ℝ))
      (𝓝 (∑' n, weight n)) := by
    refine tendsto_tsum_of_dominated_convergence (bound := invCube) summable_invCube
      (fun n => ?_) ?_
    · have hc : Continuous (fun r : ℝ => r^n * weight n) := by fun_prop
      have h := hc.continuousAt (x := (1 : ℝ))
      have hh := h.tendsto.mono_left
        (show 𝓝[<] (1 : ℝ) ≤ 𝓝 (1 : ℝ) from nhdsWithin_le_nhds)
      simpa only [one_pow, one_mul] using hh
    · filter_upwards [hr₀, hr₁] with r h₀ h₁ n
      rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg h₀ n) (weight_nonneg n))]
      exact (mul_le_of_le_one_left (weight_nonneg n) (pow_le_one₀ h₀ h₁.le)).trans
        (weight_le_invCube n)
  have hSum' : Tendsto (fun r : ℝ => ∫ t in (0 : ℝ)..(Real.pi/2), t * d r t)
      (𝓝[<] (1 : ℝ)) (𝓝 (∑' n, weight n)) := by
    apply hSum.congr'
    filter_upwards [hr₀, hr₁] with r h₀ h₁
    exact (weighted_damped_sum h₀ h₁ (hd r h₀ h₁)).symm
  exact (tendsto_nhds_unique hlim hSum').trans weight_sum

end SmythModes

/- A real integral reduction in Smyth's Mahler measure computation. -/

namespace SmythSquare

open Set MeasureTheory Filter intervalIntegral

private noncomputable def lower (f : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  {q : ℝ × ℝ | q.2 ≤ q.1}.indicator (fun q => f q.1) p

private noncomputable def upper (f : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  {q : ℝ × ℝ | q.1 < q.2}.indicator (fun q => f q.2) p

private lemma split_max (f : ℝ → ℝ) (x y : ℝ) :
    f (max x y) = lower f (x,y) + upper f (x,y) := by
  by_cases h : y ≤ x
  · simp [lower, upper, h, not_lt_of_ge h]
  · have h' : x < y := lt_of_not_ge h
    simp [lower, upper, h, h', max_eq_right h'.le]

private lemma max_section {f : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hf : IntervalIntegrable f volume 0 a) (x : ℝ) :
    IntervalIntegrable (fun y => f (max x y)) volume 0 a := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha] at hf ⊢
  let μ : Measure ℝ := volume.restrict (Ioc 0 a)
  have : IsFiniteMeasure μ := ⟨by simp [μ, Real.volume_Ioc]⟩
  have hf' : Integrable f μ := hf
  have h₁ : Integrable (fun y => lower f (x,y)) μ :=
    (integrable_const (f x)).indicator measurableSet_Iic
  have h₂ : Integrable (fun y => upper f (x,y)) μ :=
    hf'.indicator measurableSet_Ioi
  exact (h₁.add h₂).congr (Eventually.of_forall (fun y => (split_max f x y).symm))

private lemma square_max {f : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hf : IntervalIntegrable f volume 0 a) :
    IntervalIntegrable (fun x => ∫ y in (0 : ℝ)..a, f (max x y)) volume 0 a ∧
      (∫ x in (0 : ℝ)..a, ∫ y in (0 : ℝ)..a, f (max x y)) =
        2 * ∫ x in (0 : ℝ)..a, x * f x := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 a)
  have : IsFiniteMeasure μ := ⟨by simp [μ, Real.volume_Ioc]⟩
  have hf' : Integrable f μ := (intervalIntegrable_iff_integrableOn_Ioc_of_le ha).mp hf
  have hLo : Integrable (lower f) (μ.prod μ) :=
    (hf'.comp_fst μ).indicator (measurableSet_le measurable_snd measurable_fst)
  have hHi : Integrable (upper f) (μ.prod μ) :=
    (hf'.comp_snd μ).indicator (measurableSet_lt measurable_fst measurable_snd)
  have hFull : Integrable (fun p : ℝ × ℝ => f (max p.1 p.2)) (μ.prod μ) :=
    (hLo.add hHi).congr (Eventually.of_forall (fun p => (split_max f p.1 p.2).symm))
  constructor
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha]
    simp only [integral_of_le ha]
    exact hFull.integral_prod_left
  · simp only [integral_of_le ha]
    change (∫ x, ∫ y, f (max x y) ∂μ ∂μ) = 2 * ∫ x, x * f x ∂μ
    have hRow (x : ℝ) : (∫ y, f (max x y) ∂μ) =
        (∫ y, lower f (x,y) ∂μ) + (∫ y, upper f (x,y) ∂μ) := by
      have h₁ : Integrable (fun y => lower f (x,y)) μ :=
        (integrable_const (f x)).indicator measurableSet_Iic
      have h₂ : Integrable (fun y => upper f (x,y)) μ :=
        hf'.indicator measurableSet_Ioi
      rw [← integral_add h₁ h₂]
      exact MeasureTheory.integral_congr_ae (Eventually.of_forall (split_max f x))
    have hLower : (∫ x, ∫ y, lower f (x,y) ∂μ ∂μ) = ∫ x, x * f x ∂μ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [ae_restrict_mem (μ := volume) (s := Ioc 0 a) measurableSet_Ioc] with x hx
      change (∫ y, (Iic x).indicator (fun _ => f x) y ∂μ) = x * f x
      rw [MeasureTheory.integral_indicator measurableSet_Iic, show μ = volume.restrict (Ioc 0 a) by rfl,
        Measure.restrict_restrict measurableSet_Iic]
      have hs : Iic x ∩ Ioc 0 a = Ioc 0 x := by
        ext y
        simp only [mem_inter_iff, mem_Iic, mem_Ioc]
        constructor
        · exact fun hh => ⟨hh.2.1,hh.1⟩
        · exact fun hh => ⟨hh.2,hh.1,hh.2.trans hx.2⟩
      rw [hs, setIntegral_const]
      simp [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal hx.1.le]
    have hUpper : (∫ x, ∫ y, upper f (x,y) ∂μ ∂μ) = ∫ y, y * f y ∂μ := by
      rw [integral_integral_swap (f := fun x y => upper f (x,y)) hHi]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [ae_restrict_mem (μ := volume) (s := Ioc 0 a) measurableSet_Ioc] with y hy
      change (∫ x, (Iio y).indicator (fun _ => f y) x ∂μ) = y * f y
      rw [MeasureTheory.integral_indicator measurableSet_Iio, show μ = volume.restrict (Ioc 0 a) by rfl,
        Measure.restrict_restrict measurableSet_Iio]
      have hs : Iio y ∩ Ioc 0 a = Ioo 0 y := by
        ext x
        simp only [mem_inter_iff, mem_Iio, mem_Ioc, mem_Ioo]
        constructor
        · exact fun hh => ⟨hh.2.1,hh.1⟩
        · exact fun hh => ⟨hh.2,hh.1,hh.2.le.trans hy.2⟩
      rw [hs, setIntegral_const]
      simp [Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal hy.1.le]
    simp_rw [hRow]
    rw [integral_add hLo.integral_prod_left hHi.integral_prod_left, hLower, hUpper, two_mul]

private noncomputable def fold (x : ℝ) : ℝ := Real.pi * |x - 1 / 2|

private lemma fold_range {x : ℝ} (hx : x ∈ Icc 0 1) :
    fold x ∈ Icc 0 (Real.pi / 2) := by
  have hAbs : |x - 1 / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  exact ⟨mul_nonneg Real.pi_pos.le (abs_nonneg _),
    by simpa [fold, div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hAbs Real.pi_pos.le⟩

private lemma fold_integral {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume 0 (Real.pi / 2)) :
    (∫ x in (0 : ℝ)..1, g (fold x)) =
      (2 / Real.pi) * ∫ t in (0 : ℝ)..(Real.pi / 2), g t := by
  have hHalf : Real.pi / 2 / Real.pi = (1 / 2 : ℝ) := by
    field_simp [Real.pi_ne_zero]
  have hScale : IntervalIntegrable (fun x => g (Real.pi * x)) volume 0 (1 / 2) := by
    simpa only [zero_div,hHalf] using hg.comp_mul_left (c := Real.pi)
  have leftEq : EqOn (fun x => g (Real.pi * (1 / 2 - x))) (fun x => g (fold x)) (uIcc 0 (1 / 2)) := by
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hx
    change g (Real.pi * (1 / 2 - x)) = g (fold x)
    rw [fold, abs_of_nonpos (sub_nonpos.mpr hx.2), neg_sub]
  have rightEq : EqOn (fun x => g (Real.pi * (x - 1 / 2))) (fun x => g (fold x)) (uIcc (1 / 2) 1) := by
    intro x hx
    rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at hx
    change g (Real.pi * (x - 1 / 2)) = g (fold x)
    rw [fold, abs_of_nonneg (sub_nonneg.mpr hx.1)]
  have hL : IntervalIntegrable (fun x => g (fold x)) volume 0 (1 / 2) := by
    have h : IntervalIntegrable (fun x => g (Real.pi * (1 / 2 - x))) volume 0 (1 / 2) := by
      simpa only [sub_self, sub_zero] using (hScale.comp_sub_left (1 / 2)).symm
    apply h.congr
    exact leftEq.mono uIoc_subset_uIcc
  have hR : IntervalIntegrable (fun x => g (fold x)) volume (1 / 2) 1 := by
    have h : IntervalIntegrable (fun x => g (Real.pi * (x - 1 / 2))) volume (1 / 2) 1 := by
      simpa only [zero_add, add_halves] using hScale.comp_sub_right (1 / 2)
    apply h.congr
    exact rightEq.mono uIoc_subset_uIcc
  rw [← integral_add_adjacent_intervals hL hR, integral_congr leftEq.symm, integral_congr rightEq.symm]
  rw [integral_comp_sub_left (fun x => g (Real.pi * x)),
    integral_comp_sub_right (fun x => g (Real.pi * x))]
  norm_num
  rw [show Real.pi * (1 / 2) = Real.pi / 2 by ring]
  ring

private lemma norm_one_add_exp (x : ℝ) :
    ‖1 + Complex.exp ((↑(2 * x) : ℂ) * Complex.I)‖ = 2 * |Real.cos x| := by
  have h : 1 + Complex.exp ((↑(2 * x) : ℂ) * Complex.I) =
      Complex.exp ((x : ℂ) * Complex.I) * (2 * Complex.cos x) := by
    rw [Complex.two_cos, mul_add, ← Complex.exp_add, ← Complex.exp_add]
    rw [show (x : ℂ) * Complex.I + (- (x : ℂ)) * Complex.I = 0 by ring,
      show (x : ℂ) * Complex.I + (x : ℂ) * Complex.I = (↑(2*x) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_zero, add_comm]
  have hcos : ‖Complex.cos (x : ℂ)‖ = |Real.cos x| := by
    rw [← Complex.ofReal_cos, Complex.norm_real, Real.norm_eq_abs]
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_mul, hcos]
  norm_num

private lemma norm_fold {x : ℝ} (hx : x ∈ Icc 0 1) :
    ‖1 + Complex.exp ((↑(2 * Real.pi * x) : ℂ) * Complex.I)‖ = 2 * Real.sin (fold x) := by
  have hAbs : |Real.pi / 2 - Real.pi * x| = fold x := by
    rw [show Real.pi / 2 - Real.pi * x = -(Real.pi * (x - 1 / 2)) by ring,
      abs_neg, abs_mul, abs_of_pos Real.pi_pos, fold]
  have hLe : |Real.pi / 2 - Real.pi * x| ≤ Real.pi := by
    rw [hAbs]
    linarith [(fold_range hx).2, Real.pi_pos]
  rw [show 2 * Real.pi * x = 2 * (Real.pi * x) by ring, norm_one_add_exp,
    ← Real.sin_pi_div_two_sub (Real.pi * x), Real.abs_sin_eq_sin_abs_of_abs_le_pi hLe, hAbs]

private lemma max_sin {t u : ℝ} (ht : t ∈ Icc 0 (Real.pi / 2))
    (hu : u ∈ Icc 0 (Real.pi / 2)) :
    max (2 * Real.sin t) (2 * Real.sin u) = 2 * Real.sin (max t u) := by
  have t' : t ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith [ht.1, Real.pi_pos],ht.2⟩
  have u' : u ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith [hu.1, Real.pi_pos],hu.2⟩
  rcases le_total t u with h | h
  · rw [max_eq_right h, max_eq_right (mul_le_mul_of_nonneg_left
      (Real.strictMonoOn_sin.monotoneOn t' u' h) (by norm_num))]
  · rw [max_eq_left h, max_eq_left (mul_le_mul_of_nonneg_left
      (Real.strictMonoOn_sin.monotoneOn u' t' h) (by norm_num))]

private lemma logSin_integrable :
    IntervalIntegrable (fun t => Real.log (2 * Real.sin t)) volume 0 (Real.pi / 2) := by
  have h : AnalyticOnNhd ℝ (fun t : ℝ => 2 * Real.sin t) (uIcc 0 (Real.pi / 2)) :=
    analyticOnNhd_const.mul Real.analyticOnNhd_sin
  exact h.meromorphicOn.intervalIntegrable_log

/-- The norm-max average on the unit square reduces to the weighted log-sine integral. -/
theorem reduction :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
      Real.log (max ‖1 + Complex.exp ((↑(2 * Real.pi * x) : ℂ) * Complex.I)‖
        ‖1 + Complex.exp ((↑(2 * Real.pi * y) : ℂ) * Complex.I)‖)) =
      (8 / Real.pi ^ 2) * ∫ t in (0 : ℝ)..(Real.pi / 2), t * Real.log (2 * Real.sin t) := by
  let f (t : ℝ) := Real.log (2 * Real.sin t)
  let g (t : ℝ) := ∫ u in (0 : ℝ)..(Real.pi / 2), f (max t u)
  have h := square_max (half_pos Real.pi_pos).le logSin_integrable
  have hInner (t : ℝ) : (∫ y in (0 : ℝ)..1, f (max t (fold y))) = (2 / Real.pi) * g t :=
    fold_integral (max_section (half_pos Real.pi_pos).le logSin_integrable t)
  calc
    _ = ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, f (max (fold x) (fold y)) := by
      apply integral_congr
      intro x hx
      apply integral_congr
      intro y hy
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx hy
      dsimp only
      rw [norm_fold hx, norm_fold hy, max_sin (fold_range hx) (fold_range hy)]
    _ = ∫ x in (0 : ℝ)..1, (2 / Real.pi) * g (fold x) := by simp_rw [hInner]
    _ = (2 / Real.pi) * ((2 / Real.pi) * ∫ t in (0 : ℝ)..(Real.pi / 2), g t) := by
      rw [intervalIntegral.integral_const_mul, fold_integral h.1]
    _ = _ := by
      change (2 / Real.pi) * ((2 / Real.pi) * ∫ t in (0 : ℝ)..(Real.pi / 2),
        ∫ u in (0 : ℝ)..(Real.pi / 2), f (max t u)) = _
      rw [h.2]
      field_simp [Real.pi_ne_zero]
      ring

end SmythSquare

/-
# Jensen reduction for Smyth's linear Mahler measure

Fiberwise Jensen's formula gives integrability before the phase change.
A measure-preserving shear then turns the remaining one-variable integral
into the logarithm of the maximum of two linear magnitudes. See Borwein
and Straub, Log-sine evaluations of Mahler measures, Example 1.2,
https://arxiv.org/abs/1103.3893.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace SmythJensen

private noncomputable def phase (x : UnitAddCircle) : ℂ := AddCircle.toCircle x

private lemma continuous_phase : Continuous phase :=
  continuous_subtype_val.comp AddCircle.continuous_toCircle

private lemma phase_norm (x : UnitAddCircle) : ‖phase x‖ = 1 := Circle.norm_coe _

private lemma phase_add (x y : UnitAddCircle) : phase (x + y) = phase x * phase y := by
  simp only [phase, AddCircle.toCircle_add, Circle.coe_mul]

private lemma phase_real (t : ℝ) :
    phase (t : UnitAddCircle) = Complex.exp ((↑(2 * Real.pi * t) : ℂ) * Complex.I) := by
  rw [phase, AddCircle.toCircle_apply_mk, Circle.coe_exp, div_one]

private lemma phase_eq_circleMap (t : ℝ) :
    phase (t : UnitAddCircle) = circleMap 0 1 (2 * Real.pi * t) := by
  simp only [phase_real, circleMap, Complex.ofReal_one, one_mul, zero_add]

private lemma linear_integrable (a b : ℂ) :
    Integrable (fun z : UnitAddCircle => Real.log ‖b + a * phase z‖) := by
  let p : Polynomial ℂ := Polynomial.C a * Polynomial.X + Polynomial.C b
  let g (t : ℝ) := Real.log ‖p.eval (circleMap 0 1 t)‖
  let f (z : UnitAddCircle) := Real.log ‖b + a * phase z‖
  have hf : Measurable f :=
    Real.measurable_log.comp (measurable_const.add (measurable_const.mul continuous_phase.measurable)).norm
  have hEq (t : ℝ) : f (t : UnitAddCircle) = g (2 * Real.pi * t) := by
    simp [f, g, p, phase_eq_circleMap, add_comm]
  have hgi : IntervalIntegrable (fun t => g (2 * Real.pi * t)) volume 0 1 := by
    have h := p.intervalIntegrable_mahlerMeasure.comp_mul_left (c := 2 * Real.pi)
    simpa only [g, zero_div, div_self (mul_ne_zero two_ne_zero Real.pi_ne_zero)] using h
  apply ((UnitAddCircle.measurePreserving_mk 0).integrable_comp hf.aestronglyMeasurable).mp
  change Integrable (f ∘ (fun t : ℝ => (t : UnitAddCircle)))
    (volume.restrict (Ioc 0 (0 + 1)))
  rw [show f ∘ (fun t : ℝ => (t : UnitAddCircle)) = fun t => g (2 * Real.pi * t) from
    funext hEq, zero_add]
  exact hgi.1

private lemma linear_average (a b : ℂ) :
    (∫ z : UnitAddCircle, Real.log ‖b + a * phase z‖) =
      Real.log (max ‖b‖ ‖a‖) := by
  let p : Polynomial ℂ := Polynomial.C a * Polynomial.X + Polynomial.C b
  let g (t : ℝ) := Real.log ‖p.eval (circleMap 0 1 t)‖
  let f (z : UnitAddCircle) := Real.log ‖b + a * phase z‖
  have hEq (t : ℝ) : f (t : UnitAddCircle) = g (2 * Real.pi * t) := by
    simp [f, g, p, phase_eq_circleMap, add_comm]
  change (∫ z : UnitAddCircle, f z) = _
  calc
    _ = p.logMahlerMeasure := by
      rw [← UnitAddCircle.intervalIntegral_preimage 0 f]
      simp only [zero_add, hEq]
      rw [intervalIntegral.integral_comp_mul_left g (mul_ne_zero two_ne_zero Real.pi_ne_zero)]
      simp [Polynomial.logMahlerMeasure_def, Real.circleAverage_def, g]
    _ = _ := by
      by_cases ha : a = 0
      · simp [p, ha]
      · rw [Polynomial.logMahlerMeasure_eq_log_MahlerMeasure]
        simp [p, ha, max_comm]

private abbrev Pair := UnitAddCircle × UnitAddCircle
private abbrev Triple := Pair × UnitAddCircle

private noncomputable def pairMeasure : Measure Pair :=
  (volume : Measure UnitAddCircle).prod volume

local instance pairMeasureFinite : IsFiniteMeasure pairMeasure := by
  unfold pairMeasure
  infer_instance

local instance pairMeasureSFinite : SFinite pairMeasure := by
  unfold pairMeasure
  infer_instance

private noncomputable def tripleMeasure : Measure Triple := pairMeasure.prod volume

private noncomputable def original (q : Triple) : ℝ :=
  Real.log ‖1 + phase q.1.1 + phase q.1.2 + phase q.2‖

private noncomputable def shifted (q : Triple) : ℝ :=
  Real.log ‖(1 + phase q.1.1) + (1 + phase q.1.2) * phase q.2‖

private noncomputable def double (q : Pair) : ℝ :=
  Real.log (max ‖1 + phase q.1‖ ‖1 + phase q.2‖)

private lemma original_measurable : Measurable original := by
  apply Real.measurable_log.comp
  exact (measurable_const.add
    (continuous_phase.measurable.comp (measurable_fst.comp measurable_fst)) |>.add
      (continuous_phase.measurable.comp (measurable_snd.comp measurable_fst)) |>.add
      (continuous_phase.measurable.comp measurable_snd)).norm

private lemma original_integrable : Integrable original tripleMeasure := by
  have hgi (p : Pair) : Integrable (fun z => original (p, z)) := by
    simpa only [original, one_mul] using linear_integrable 1 (1 + phase p.1 + phase p.2)
  change Integrable original (pairMeasure.prod volume)
  refine (integrable_prod_iff original_measurable.aestronglyMeasurable).mpr
    ⟨Eventually.of_forall hgi, ?_⟩
  refine (integrable_const (2 * Real.log 4)).mono'
    original_measurable.aestronglyMeasurable.norm.integral_prod_right' ?_
  refine Eventually.of_forall (fun p => ?_)
  let g (z : UnitAddCircle) := original (p, z)
  have hInt : Integrable g := hgi p
  have hPos : 0 ≤ ∫ z, g z := by
    have h := linear_average 1 (1 + phase p.1 + phase p.2)
    have h' : (∫ z, g z) = Real.log (max ‖1 + phase p.1 + phase p.2‖ 1) := by
      simpa only [g, original, one_mul, norm_one] using h
    rw [h']
    exact Real.log_nonneg (le_max_right _ _)
  have hBound (z : UnitAddCircle) : ‖g z‖ + g z ≤ 2 * Real.log 4 := by
    by_cases hn : 0 ≤ g z
    · rw [Real.norm_of_nonneg hn]
      have h1 := norm_add_le (1 : ℂ) (phase p.1)
      have h2 := norm_add_le (1 + phase p.1) (phase p.2)
      have h3 := norm_add_le (1 + phase p.1 + phase p.2) (phase z)
      simp only [norm_one, phase_norm] at h1 h2 h3
      have hNorm : ‖1 + phase p.1 + phase p.2 + phase z‖ ≤ 4 := by
        linarith only [h1, h2, h3]
      have hLog : g z ≤ Real.log 4 := by
        by_cases hz : ‖1 + phase p.1 + phase p.2 + phase z‖ = 0
        · simp [g, original, hz, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
        · exact Real.log_le_log (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)) hNorm
      linarith only [hLog]
    · rw [Real.norm_of_nonpos (le_of_not_ge hn), neg_add_cancel]
      positivity
  have h := integral_mono (hInt.norm.add hInt) (integrable_const (2 * Real.log 4)) hBound
  change (∫ z : UnitAddCircle, ‖g z‖ + g z) ≤
    (∫ _ : UnitAddCircle, 2 * Real.log 4) at h
  rw [integral_add hInt.norm hInt, integral_const] at h
  simp only [Measure.real, UnitAddCircle.measure_univ, ENNReal.toReal_one, one_smul] at h
  change ‖∫ z : UnitAddCircle, ‖g z‖‖ ≤ 2 * Real.log 4
  rw [Real.norm_of_nonneg (integral_nonneg (fun z => norm_nonneg (g z)))]
  linarith only [h, hPos]


private def tuples : UnitAddTorus (Fin 3) ≃ᵐ Triple :=
  ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => UnitAddCircle) 0).trans
    ((MeasurableEquiv.refl UnitAddCircle).prodCongr MeasurableEquiv.finTwoArrow)).trans
      MeasurableEquiv.prodAssoc.symm

private lemma tuples_apply (x : UnitAddTorus (Fin 3)) :
    tuples x = ((x 0, x 1), x 2) := rfl

private lemma tuples_preserving : MeasurePreserving tuples volume tripleMeasure := by
  let μ : Measure UnitAddCircle := volume
  have h₀ := measurePreserving_piFinSuccAbove (fun _ : Fin 3 => μ) 0
  have h₁ := (MeasurePreserving.id μ).prod (measurePreserving_finTwoArrow μ)
  have h₂ := (measurePreserving_prodAssoc μ μ μ).symm MeasurableEquiv.prodAssoc
  exact h₂.comp (h₁.comp h₀)

private def shiftPair : Pair ≃ᵐ Pair :=
  MeasurableEquiv.prodComm.trans (MeasurableEquiv.shearAddRight UnitAddCircle)

private def shift : Triple ≃ᵐ Triple :=
  MeasurableEquiv.prodAssoc.trans
    (((MeasurableEquiv.refl UnitAddCircle).prodCongr shiftPair).trans MeasurableEquiv.prodAssoc.symm)

private lemma shift_apply (q : Triple) : shift q = ((q.1.1, q.2), q.2 + q.1.2) := rfl

private lemma shift_preserving : MeasurePreserving shift tripleMeasure tripleMeasure := by
  let μ : Measure UnitAddCircle := volume
  have h := measurePreserving_prodAssoc μ μ μ
  have hPair : MeasurePreserving shiftPair (μ.prod μ) (μ.prod μ) :=
    measurePreserving_prod_add_swap μ μ
  have h₂ := (MeasurePreserving.id μ).prod hPair
  exact (h.symm MeasurableEquiv.prodAssoc).comp (h₂.comp h)

private lemma original_shift (q : Triple) : original (shift q) = shifted q := by
  rw [original, shifted, shift_apply, phase_add]
  congr 2
  ring

private lemma shifted_integrable : Integrable shifted tripleMeasure := by
  have h := shift_preserving.integrable_comp_of_integrable original_integrable
  exact h.congr (Eventually.of_forall original_shift)

private lemma integral_cube (f : UnitAddTorus (Fin 3) → ℝ) :
    (∫ t in Icc (0 : Fin 3 → ℝ) 1, f (fun j => (t j : UnitAddCircle))) =
      ∫ x, f x := by
  have h := UnitAddTorus.integral_preimage f (0 : Fin 3 → ℝ)
  simp only [Pi.zero_apply, zero_add] at h
  have hSet :
      univ.pi (fun i : Fin 3 => Ioc ((0 : Fin 3 → ℝ) i) ((1 : Fin 3 → ℝ) i)) =
        {x : Fin 3 → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) 1} := by
    ext x
    simp only [mem_univ_pi, Pi.zero_apply, Pi.one_apply, Set.mem_ofPred_eq]
  have hAE : {x : Fin 3 → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) 1} =ᵐ[(volume : Measure (Fin 3 → ℝ))]
      Icc 0 1 := by
    rw [← hSet, volume_pi]
    exact Measure.univ_pi_Ioc_ae_eq_Icc
  have hVol : (volume : Measure (UnitAddTorus (Fin 3))) =
      Measure.pi (fun _ : Fin 3 => (AddCircle.haarAddCircle : Measure UnitAddCircle)) := by
    rw [volume_pi]
    congr 1
    funext i
    simp only [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]
  rw [setIntegral_congr_set hAE.symm, hVol]
  exact h.symm

private noncomputable def linear : MvPolynomial (Fin 3) ℂ :=
  1 + MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 2

private lemma linear_eq_original :
    MvPolynomial.logMahlerMeasure linear = ∫ q, original q ∂tripleMeasure := by
  calc
    _ = ∫ t in Icc (0 : Fin 3 → ℝ) 1, original (tuples (fun j => (t j : UnitAddCircle))) := by
      unfold MvPolynomial.logMahlerMeasure
      apply integral_congr_ae
      refine Eventually.of_forall fun t => ?_
      simp only [linear, tuples_apply, original, phase_real, map_one, map_add, MvPolynomial.eval_X,
        MvPolynomial.torusPoint, Complex.ofReal_mul, Complex.ofReal_ofNat]
    _ = ∫ x : UnitAddTorus (Fin 3), original (tuples x) :=
      integral_cube (fun x => original (tuples x))
    _ = _ := tuples_preserving.integral_comp' original

private lemma shifted_average (p : Pair) :
    (∫ z : UnitAddCircle, shifted (p, z)) = double p := by
  exact linear_average (1 + phase p.2) (1 + phase p.1)

private lemma double_integrable : Integrable double pairMeasure := by
  exact shifted_integrable.integral_prod_left.congr (Eventually.of_forall shifted_average)

private lemma reduction_torus :
    MvPolynomial.logMahlerMeasure linear = ∫ p, double p ∂pairMeasure := by
  rw [linear_eq_original, ← shift_preserving.integral_comp' original]
  simp_rw [original_shift]
  rw [tripleMeasure, integral_prod _ shifted_integrable]
  simp_rw [shifted_average]

/-- Smyth's three-variable linear Mahler measure as the double integral of the
logarithm of the maximum of two linear magnitudes. -/
theorem reduction :
    MvPolynomial.logMahlerMeasure
      (1 + MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 2 : MvPolynomial (Fin 3) ℂ) =
    ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
      Real.log (max ‖1 + Complex.exp ((↑(2 * Real.pi * x) : ℂ) * Complex.I)‖
        ‖1 + Complex.exp ((↑(2 * Real.pi * y) : ℂ) * Complex.I)‖) := by
  change MvPolynomial.logMahlerMeasure linear = _
  rw [reduction_torus, pairMeasure, integral_prod _ double_integrable]
  let f (x : UnitAddCircle) : ℝ := ∫ y : UnitAddCircle, double (x, y)
  change (∫ x : UnitAddCircle, f x) = _
  rw [← UnitAddCircle.intervalIntegral_preimage 0 f, zero_add]
  apply intervalIntegral.integral_congr
  intro x _
  have h := UnitAddCircle.intervalIntegral_preimage 0 (fun y => double ((x : UnitAddCircle), y))
  simpa only [zero_add, double, phase_real, f] using h.symm

end SmythJensen

theorem OMA.solution : type_of% @MultivariableMahlerMeasure.smyth_three_variable_linear_mahler_measure := by
  rw [SmythJensen.reduction, SmythSquare.reduction,
    SmythModes.integral_log_sin_weighted
      (fun _ h₀ h₁ t => SmythFourier.hasSum_damped h₀ h₁ t) SmythFourier.weighted_integral_tendsto]
  ring