import OMAReductions.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1
import Mathlib

namespace TunnellCMGoodDescent
end TunnellCMGoodDescent
namespace TunnellCMLocalUnit
end TunnellCMLocalUnit
namespace TunnellCMNormDistribution
end TunnellCMNormDistribution
namespace TunnellCMRegularized
end TunnellCMRegularized
namespace TunnellCMToricDivision
end TunnellCMToricDivision
namespace TunnellCMTraceDistribution
end TunnellCMTraceDistribution
namespace TunnellCMUnitCriterion
end TunnellCMUnitCriterion
namespace TunnellEllipticZeta
end TunnellEllipticZeta

/- EllipticCurves.VariableChange -/
section
namespace WeierstrassCurve.Affine
variable {F : Type*} [Field F] (W : WeierstrassCurve F) (C : VariableChange F)
namespace Point
variable [W.IsElliptic]
variable [DecidableEq F]
 
def equivOfEq {V V' : WeierstrassCurve F} (h : V = V') :
    V.toAffine.Point ≃+ V'.toAffine.Point := by
  subst h; exact AddEquiv.refl _
@[simp] lemma equivOfEq_some {V V' : WeierstrassCurve F} (h : V = V') {x y : F}
    (hns : V.toAffine.Nonsingular x y) :
    equivOfEq h (some x y hns) = some x y (h ▸ hns) := by
  subst h; rfl
end Point
end WeierstrassCurve.Affine
end

/- LSG.LemniscateIndep.Integral -/
section
noncomputable section
open MeasureTheory Set Real
namespace LSG.LemniscateIndep
 
noncomputable def varpi : ℝ := Real.Gamma (1 / 4) ^ 2 / (2 * Real.sqrt (2 * π))
 
def lemInt (t : ℝ) : ℝ := 1 / Real.sqrt (1 - t ^ 4)
 
def betaInt (u : ℝ) : ℝ := u ^ (-(3 / 4 : ℝ)) * (1 - u) ^ (-(1 / 2 : ℝ))
lemma image_pow_four_Ioo : (fun t : ℝ => t ^ 4) '' Ioo 0 1 = Ioo 0 1 := by
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨pow_pos ht.1 4, pow_lt_one₀ ht.1.le ht.2 (by norm_num)⟩
  · intro hu
    refine ⟨u ^ (1 / 4 : ℝ), ⟨Real.rpow_pos_of_pos hu.1 _,
      Real.rpow_lt_one hu.1.le hu.2 (by norm_num)⟩, ?_⟩
    dsimp only
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu.1.le]
    norm_num
 
lemma setIntegral_betaInt :
    ∫ u in Ioo (0 : ℝ) 1, betaInt u = 4 * ∫ t in Ioo (0 : ℝ) 1, lemInt t := by
  have hinj : InjOn (fun t : ℝ => t ^ 4) (Ioo 0 1) := fun a ha b hb h =>
    (pow_left_inj₀ ha.1.le hb.1.le (by norm_num)).mp h
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun t _ => (hasDerivAt_pow 4 t).hasDerivWithinAt) hinj betaInt
  rw [image_pow_four_Ioo] at h
  rw [h, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
  have ht0 : 0 < t := ht.1
  have h1 : 0 < 1 - t ^ 4 := sub_pos.2 (pow_lt_one₀ ht.1.le ht.2 (by norm_num))
  have hpow : (t ^ 4) ^ (-(3 / 4 : ℝ)) = (t ^ 3)⁻¹ := by
    rw [← Real.rpow_natCast t 4, ← Real.rpow_mul ht0.le,
      show ((4 : ℕ) : ℝ) * (-(3 / 4 : ℝ)) = -((3 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg ht0.le, Real.rpow_natCast]
  have hsq : (1 - t ^ 4) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (1 - t ^ 4))⁻¹ := by
    rw [Real.rpow_neg h1.le, Real.sqrt_eq_rpow]
  simp only [betaInt, smul_eq_mul, hpow, hsq, lemInt]
  rw [abs_of_pos (by positivity)]
  have : (t ^ 3) ≠ 0 := by positivity
  field_simp
  ring
 
lemma betaIntegral_quarter_half' :
    Complex.betaIntegral (1 / 4) (1 / 2) = ((∫ u in Ioo (0 : ℝ) 1, betaInt u : ℝ) : ℂ) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    ← intervalIntegral.integral_ofReal, Complex.betaIntegral]
  refine intervalIntegral.integral_congr (fun x hx => ?_)
  rw [uIcc_of_le zero_le_one] at hx
  simp only [betaInt, Complex.ofReal_mul]
  rw [Complex.ofReal_cpow hx.1, Complex.ofReal_cpow (sub_nonneg.2 hx.2)]
  push_cast
  norm_num
 
theorem varpi_eq_integral : varpi = 2 * ∫ t in (0 : ℝ)..1, lemInt t := by
  
  have hBG := Complex.Gamma_mul_Gamma_eq_betaIntegral
    (s := 1 / 4) (t := 1 / 2) (by norm_num) (by norm_num)
  rw [betaIntegral_quarter_half', setIntegral_betaInt] at hBG
  have hc : ∀ x : ℝ, Complex.Gamma (x : ℂ) = (Real.Gamma x : ℂ) := Complex.Gamma_ofReal
  have hBG' : Real.Gamma (1 / 4) * Real.Gamma (1 / 2) =
      Real.Gamma (3 / 4) * (4 * ∫ t in Ioo (0 : ℝ) 1, lemInt t) := by
    have e1 : (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) := by push_cast; ring
    have e2 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
    have e3 : (1 / 4 + 1 / 2 : ℂ) = ((3 / 4 : ℝ) : ℂ) := by push_cast; ring
    rw [e3, e1, e2, hc, hc, hc] at hBG
    exact_mod_cast hBG
  
  have hrefl := Real.Gamma_mul_Gamma_one_sub (1 / 4)
  rw [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num, show π * (1 / 4) = π / 4 by ring,
    Real.sin_pi_div_four] at hrefl
  rw [Real.Gamma_one_half_eq] at hBG'
  have hI : ∫ t in (0 : ℝ)..1, lemInt t = ∫ t in Ioo (0 : ℝ) 1, lemInt t := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  set J := ∫ t in Ioo (0 : ℝ) 1, lemInt t
  set g1 := Real.Gamma (1 / 4)
  set g3 := Real.Gamma (3 / 4)
  have hs : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  have hq : 0 < √2 := by positivity
  have hq2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2 : √π ^ 2 = π := Real.sq_sqrt Real.pi_pos.le
  have h2π : √(2 * π) = √2 * √π := Real.sqrt_mul (by norm_num) π
  have hg3 : 0 < g3 := Real.Gamma_pos_of_pos (by norm_num)
  unfold varpi
  rw [hI, h2π]
  have hrefl' : g1 * g3 * √2 = 2 * π := by
    rw [hrefl]; field_simp
  rw [← hs2] at hrefl'
  have key : 2 * J * (2 * √2 * √π) * g3 = g1 ^ 2 * g3 := by
    have h4 : 4 * g3 * J = g1 * √π := by linarith [hBG']
    have hL : 2 * J * (2 * √2 * √π) * g3 * √2 = 2 * g1 * √π ^ 2 := by
      calc _ = (4 * g3 * J) * √π * √2 ^ 2 := by ring
        _ = _ := by rw [h4, hq2]; ring
    have hR : g1 ^ 2 * g3 * √2 = 2 * g1 * √π ^ 2 := by
      calc _ = g1 * (g1 * g3 * √2) := by ring
        _ = _ := by rw [hrefl']; ring
    exact mul_right_cancel₀ hq.ne' (hL.trans hR.symm)
  have hJ : 2 * J * (2 * √2 * √π) = g1 ^ 2 := mul_right_cancel₀ hg3.ne' key
  field_simp
  linarith [hJ]
lemma varpi_pos : 0 < varpi := by
  unfold varpi
  have := Real.Gamma_pos_of_pos (show (0 : ℝ) < 1 / 4 by norm_num)
  positivity
 
lemma intervalIntegrable_lemInt : IntervalIntegrable lemInt volume 0 1 := by
  by_contra h
  have h0 := intervalIntegral.integral_undef h
  have := varpi_eq_integral
  rw [h0] at this
  linarith [varpi_pos]
 
def lemF (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, lemInt t
lemma lemF_zero : lemF 0 = 0 := by simp [lemF]
lemma lemF_one : lemF 1 = varpi / 2 := by
  rw [lemF, varpi_eq_integral]; ring
lemma continuousOn_lemF : ContinuousOn lemF (Icc 0 1) := by
  have := intervalIntegral.continuousOn_primitive_interval' intervalIntegrable_lemInt
    (left_mem_uIcc (a := (0 : ℝ)) (b := 1))
  rwa [uIcc_of_le zero_le_one] at this
lemma continuousOn_lemInt : ContinuousOn lemInt (Ioo 0 1) := by
  refine continuousOn_const.div (by fun_prop) (fun t ht => ?_)
  have : t ^ 4 < 1 := pow_lt_one₀ ht.1.le ht.2 (by norm_num)
  exact (Real.sqrt_pos.2 (by linarith)).ne'
lemma hasDerivAt_lemF {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt lemF (lemInt x) x := by
  have hint : IntervalIntegrable lemInt volume 0 x :=
    intervalIntegrable_lemInt.mono_set (by
      rw [uIcc_of_le hx.1.le, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl hx.2.le)
  exact intervalIntegral.integral_hasDerivAt_right hint
    (continuousOn_lemInt.stronglyMeasurableAtFilter isOpen_Ioo x hx)
    (continuousOn_lemInt.continuousAt (isOpen_Ioo.mem_nhds hx))
end LSG.LemniscateIndep
end
end

/- LSG.Weierstrass.ZetaDef -/
section
open Module Filter
open scoped Topology
noncomputable section
namespace LSG.Weierstrass
open PeriodPair
variable (L : PeriodPair)
 

def zetaSummand (l z : ℂ) : ℂ := 1 / (z - l) + 1 / l + z / l ^ 2
lemma zetaSummand_eq (l z : ℂ) (hl : l ≠ 0) (hz : z ≠ l) :
    zetaSummand l z = z ^ 2 / (l ^ 2 * (z - l)) := by
  have : z - l ≠ 0 := sub_ne_zero.mpr hz
  unfold zetaSummand
  field_simp
  ring
 
lemma zetaSummand_bound (r : ℝ) (hr : 0 < r) (z : ℂ) (hz : ‖z‖ < r) (l : ℂ)
    (h : 2 * r ≤ ‖l‖) : ‖zetaSummand l z‖ ≤ 2 * r ^ 2 * ‖l‖ ^ (-3 : ℝ) := by
  have hl0 : 0 < ‖l‖ := by linarith
  have hl : l ≠ 0 := norm_pos_iff.mp hl0
  have hzl : z ≠ l := by rintro rfl; linarith
  have hzl' : ‖l‖ / 2 ≤ ‖z - l‖ := by
    rw [norm_sub_rev]
    have := norm_sub_norm_le l z
    linarith
  rw [zetaSummand_eq l z hl hzl, Real.rpow_neg hl0.le, norm_div, norm_mul, norm_pow, norm_pow]
  have h3 : ‖l‖ ^ (3 : ℝ) = ‖l‖ ^ 3 := by norm_cast
  rw [h3, div_le_iff₀ (mul_pos (by positivity) (by linarith))]
  have hz2 : ‖z‖ ^ 2 ≤ r ^ 2 := by gcongr
  calc ‖z‖ ^ 2 ≤ r ^ 2 := hz2
    _ = 2 * r ^ 2 * (‖l‖ ^ 3)⁻¹ * (‖l‖ ^ 2 * (‖l‖ / 2)) := by field_simp
    _ ≤ 2 * r ^ 2 * (‖l‖ ^ 3)⁻¹ * (‖l‖ ^ 2 * ‖z - l‖) := by gcongr
 
def zeta (z : ℂ) : ℂ := ∑' l : L.lattice, zetaSummand l z
lemma hasSumLocallyUniformly_zeta :
    HasSumLocallyUniformly (fun (l : L.lattice) (z : ℂ) ↦ zetaSummand l z) (zeta L) := by
  refine PeriodPair.hasSumLocallyUniformly_aux L (u := fun r l ↦ 2 * r ^ 2 * ‖(l : ℂ)‖ ^ (-3 : ℝ)) _
    (fun _ _ ↦ (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _) fun r hr ↦
    Filter.eventually_atTop.mpr ⟨2 * r, ?_⟩
  rintro _ h s hs l rfl
  exact zetaSummand_bound r hr s hs l h
lemma hasSum_zeta (z : ℂ) : HasSum (fun l : L.lattice ↦ zetaSummand l z) (zeta L z) :=
  (hasSumLocallyUniformly_zeta L).hasSum
lemma summable_zetaSummand (z : ℂ) : Summable (fun l : L.lattice ↦ zetaSummand l z) :=
  (hasSum_zeta L z).summable
lemma isOpen_compl_coe_lattice : IsOpen (L.latticeᶜ : Set ℂ) :=
  L.isClosed_lattice.isOpen_compl
lemma hasDerivAt_zetaSummand (l x : ℂ) (hxl : x - l ≠ 0) :
    HasDerivAt (zetaSummand l) (-(1 / (x - l) ^ 2 - 1 / l ^ 2)) x := by
  have h1 : HasDerivAt (fun y : ℂ ↦ y - l) 1 x := (hasDerivAt_id x).sub_const _
  have h2 : HasDerivAt (fun y : ℂ ↦ 1 / (y - l)) (-(1 : ℂ) / (x - l) ^ 2) x := by
    simpa only [one_div] using! h1.inv hxl
  have h3 : HasDerivAt (fun y : ℂ ↦ y / l ^ 2) (1 / l ^ 2) x :=
    (hasDerivAt_id x).div_const _
  have h4 : HasDerivAt (fun y ↦ 1 / (y - l) + 1 / l + y / l ^ 2)
      (-(1 : ℂ) / (x - l) ^ 2 + 0 + 1 / l ^ 2) x :=
    (h2.add (hasDerivAt_const x (1 / l))).add h3
  have : zetaSummand l = fun y ↦ 1 / (y - l) + 1 / l + y / l ^ 2 := rfl
  rw [this]
  convert h4 using 1
  ring
lemma sub_coe_ne_zero {x : ℂ} (hx : x ∉ L.lattice) (l : L.lattice) : x - l ≠ 0 :=
  fun e ↦ hx (by rw [sub_eq_zero.mp e]; exact l.2)
lemma differentiableOn_zetaSummand (l : L.lattice) :
    DifferentiableOn ℂ (zetaSummand l) L.latticeᶜ := fun x hx ↦
  (hasDerivAt_zetaSummand l x (sub_coe_ne_zero L hx l)).differentiableAt.differentiableWithinAt
lemma deriv_zetaSummand (l : L.lattice) (x : ℂ) (hx : x ∉ L.lattice) :
    deriv (zetaSummand l) x = -(1 / (x - l) ^ 2 - 1 / (l : ℂ) ^ 2) :=
  (hasDerivAt_zetaSummand l x (sub_coe_ne_zero L hx l)).deriv
 
lemma differentiableOn_zeta : DifferentiableOn ℂ (zeta L) L.latticeᶜ := by
  refine (hasSumLocallyUniformly_zeta L).hasSumLocallyUniformlyOn.differentiableOn
    (.of_forall fun s ↦ .fun_sum fun i _ ↦ differentiableOn_zetaSummand L i)
    (isOpen_compl_coe_lattice L)
lemma hasSumLocallyUniformly_neg_weierstrassP :
    HasSumLocallyUniformly (fun (l : L.lattice) (z : ℂ) ↦ -(1 / (z - l) ^ 2 - 1 / (l : ℂ) ^ 2))
      (fun z ↦ -℘[L] z) := by
  have := PeriodPair.hasSumLocallyUniformly_aux L
    (fun (l : L.lattice) (z : ℂ) ↦ -(1 / (z - l) ^ 2 - 1 / (l : ℂ) ^ 2))
    (u := fun r l ↦ 10 * r * ‖(l : ℂ)‖ ^ (-3 : ℝ))
    (fun _ _ ↦ (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _) fun r hr ↦
    Filter.eventually_atTop.mpr ⟨2 * r, by
      rintro _ h s hs l rfl
      rw [norm_neg]
      exact PeriodPair.weierstrassP_bound r hr s hs l h⟩
  convert this using 2 with z
  rw [tsum_neg, PeriodPair.weierstrassP]
 
lemma eqOn_deriv_zeta : Set.EqOn (deriv (zeta L)) (fun z ↦ -℘[L] z) L.latticeᶜ := by
  refine ((hasSumLocallyUniformly_zeta L).tendstoLocallyUniformlyOn.deriv
    (.of_forall fun s ↦ ?_) (isOpen_compl_coe_lattice L)).unique ?_
  · exact .fun_sum fun i _ ↦ differentiableOn_zetaSummand L i
  · have := (hasSumLocallyUniformly_neg_weierstrassP L).tendstoLocallyUniformlyOn
      (s := L.latticeᶜ)
    refine this.congr ?_
    intro s x hx
    simp only [Function.comp_apply]
    rw [deriv_fun_sum (fun i _ ↦ (differentiableOn_zetaSummand L i x hx).differentiableAt
      ((isOpen_compl_coe_lattice L).mem_nhds hx))]
    exact Finset.sum_congr rfl fun i _ ↦ (deriv_zetaSummand L i x hx).symm
 
lemma hasDerivAt_zeta {z : ℂ} (hz : z ∉ L.lattice) : HasDerivAt (zeta L) (-℘[L] z) z := by
  have hd : DifferentiableAt ℂ (zeta L) z :=
    (differentiableOn_zeta L z hz).differentiableAt ((isOpen_compl_coe_lattice L).mem_nhds hz)
  have := hd.hasDerivAt
  rwa [eqOn_deriv_zeta L hz] at this
end LSG.Weierstrass
end
end

/- LSG.Weierstrass.SigmaDef -/
section
open Module Filter Complex
open scoped Topology
noncomputable section
namespace LSG.Weierstrass
open PeriodPair
 
def weierstrassFactor (u : ℂ) : ℂ := (1 - u) * exp (u + u ^ 2 / 2)
@[simp] lemma weierstrassFactor_zero : weierstrassFactor 0 = 1 := by
  simp [weierstrassFactor]
@[simp] lemma weierstrassFactor_one : weierstrassFactor 1 = 0 := by
  simp [weierstrassFactor]
lemma weierstrassFactor_eq_zero_iff {u : ℂ} : weierstrassFactor u = 0 ↔ u = 1 := by
  rw [weierstrassFactor, mul_eq_zero, sub_eq_zero, or_iff_left (exp_ne_zero _), eq_comm]
lemma differentiable_weierstrassFactor : Differentiable ℂ weierstrassFactor := by
  unfold weierstrassFactor; fun_prop
 
lemma hasDerivAt_weierstrassFactor (u : ℂ) :
    HasDerivAt weierstrassFactor (-u ^ 2 * exp (u + u ^ 2 / 2)) u := by
  have h1 : HasDerivAt (fun v : ℂ ↦ v + v ^ 2 / 2) (1 + u) u :=
    ((hasDerivAt_id' u).add ((hasDerivAt_pow 2 u).div_const 2)).congr_deriv (by norm_num)
  have h2 : HasDerivAt (fun v : ℂ ↦ (1 - v) * exp (v + v ^ 2 / 2))
      ((0 - 1) * exp (u + u ^ 2 / 2) + (1 - u) * (exp (u + u ^ 2 / 2) * (1 + u))) u :=
    ((hasDerivAt_const u (1 : ℂ)).sub (hasDerivAt_id' u)).mul h1.cexp
  exact h2.congr_deriv (by ring)
lemma logTaylor_three (z : ℂ) : logTaylor 3 z = z - z ^ 2 / 2 := by
  simp [logTaylor, Finset.sum_range_succ]
  ring
 
lemma norm_weierstrassFactor_sub_one_le {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) :
    ‖weierstrassFactor u - 1‖ ≤ 2 * ‖u‖ ^ 3 := by
  have hu1 : ‖-u‖ < 1 := by rw [norm_neg]; linarith
  have hne : (1 : ℂ) - u ≠ 0 := by
    intro h
    have : u = 1 := by linear_combination -h
    rw [this] at hu; norm_num at hu
  set w := log (1 + -u) - logTaylor (2 + 1) (-u) with hw
  have hwb := norm_log_sub_logTaylor_le 2 hu1
  rw [← hw, norm_neg] at hwb
  have hw' : w = log (1 - u) + (u + u ^ 2 / 2) := by
    rw [hw, show (2 + 1 : ℕ) = 3 from rfl, logTaylor_three, ← sub_eq_add_neg]; ring
  have hinv : (1 - ‖u‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hwle : ‖w‖ ≤ ‖u‖ ^ 3 := by
    calc ‖w‖ ≤ ‖u‖ ^ (2 + 1) * (1 - ‖u‖)⁻¹ / (2 + 1) := by exact_mod_cast hwb
      _ ≤ ‖u‖ ^ 3 * 2 / 3 := by
          norm_num
          gcongr
      _ ≤ ‖u‖ ^ 3 := by nlinarith [pow_nonneg (norm_nonneg u) 3]
  have hu3 : ‖u‖ ^ 3 ≤ 1 := by
    calc ‖u‖ ^ 3 ≤ (1 / 2) ^ 3 := by gcongr
      _ ≤ 1 := by norm_num
  have hexp : weierstrassFactor u = exp w := by
    rw [hw', exp_add, exp_log hne, weierstrassFactor]
  rw [hexp]
  calc ‖exp w - 1‖ ≤ 2 * ‖w‖ := norm_exp_sub_one_le (hwle.trans hu3)
    _ ≤ 2 * ‖u‖ ^ 3 := by gcongr
variable (L : PeriodPair)
 
lemma eventually_le_norm (R : ℝ) : ∀ᶠ l : L.lattice in cofinite, R ≤ ‖(l : ℂ)‖ := by
  rw [Filter.eventually_cofinite]
  refine (isCompact_iff_finite.mp (isCompact_closedBall (0 : L.lattice) R)).subset ?_
  intro l hl
  simp only [Set.mem_ofPred_eq, not_le] at hl
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact hl.le
lemma summable_norm_rpow_neg_three :
    Summable (fun l : L.lattice ↦ ‖(l : ℂ)‖ ^ (-3 : ℝ)) :=
  ZLattice.summable_norm_rpow _ _ (by simp; norm_num)
 
lemma norm_weierstrassFactor_div_sub_one_le {r : ℝ} (hr : 0 < r) {z l : ℂ} (hz : ‖z‖ ≤ r)
    (hl : 2 * r ≤ ‖l‖) : ‖weierstrassFactor (z / l) - 1‖ ≤ 2 * r ^ 3 * ‖l‖ ^ (-3 : ℝ) := by
  have hl0 : 0 < ‖l‖ := by linarith
  have hzl : ‖z / l‖ ≤ r / ‖l‖ := by rw [norm_div]; gcongr
  have hrl : r / ‖l‖ ≤ 1 / 2 := by rw [div_le_iff₀ hl0]; linarith
  refine (norm_weierstrassFactor_sub_one_le (hzl.trans hrl)).trans ?_
  rw [Real.rpow_neg hl0.le, show ‖l‖ ^ (3 : ℝ) = ‖l‖ ^ 3 by norm_cast]
  calc 2 * ‖z / l‖ ^ 3 ≤ 2 * (r / ‖l‖) ^ 3 := by gcongr
    _ = 2 * r ^ 3 * (‖l‖ ^ 3)⁻¹ := by field_simp
lemma summable_norm_weierstrassFactor_div_sub_one (z : ℂ) :
    Summable (fun l : L.lattice ↦ ‖weierstrassFactor (z / l) - 1‖) := by
  set r := ‖z‖ + 1
  have hr : 0 < r := by positivity
  refine ((summable_norm_rpow_neg_three L).mul_left (2 * r ^ 3)).of_norm_bounded_eventually ?_
  filter_upwards [eventually_le_norm L (2 * r)] with l hl
  rw [norm_norm]
  exact norm_weierstrassFactor_div_sub_one_le hr (by simp [r]) hl
 
def sigmaProd (z : ℂ) : ℂ := ∏' l : L.lattice, weierstrassFactor (z / l)
 
def sigma (z : ℂ) : ℂ := z * sigmaProd L z
lemma hasProdLocallyUniformlyOn_sigmaProd :
    HasProdLocallyUniformlyOn (fun (l : L.lattice) (z : ℂ) ↦ weierstrassFactor (z / l))
      (sigmaProd L) Set.univ := by
  have key : HasProdLocallyUniformlyOn
      (fun (l : L.lattice) (z : ℂ) ↦ 1 + (weierstrassFactor (z / l) - 1))
      (fun z ↦ ∏' l : L.lattice, (1 + (weierstrassFactor (z / l) - 1))) Set.univ := by
    refine hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ fun K _ hK ↦ ?_
    obtain ⟨r₀, hr₀⟩ := hK.isBounded.subset_closedBall 0
    set r := max r₀ 1
    have hr : 0 < r := lt_of_lt_of_le one_pos (le_max_right _ _)
    refine Summable.hasProdUniformlyOn_one_add hK
      ((summable_norm_rpow_neg_three L).mul_left (2 * r ^ 3)) ?_ fun l ↦ ?_
    · filter_upwards [eventually_le_norm L (2 * r)] with l hl x hx
      refine norm_weierstrassFactor_div_sub_one_le hr ?_ hl
      have := hr₀ hx
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact this.trans (le_max_left _ _)
    · exact ((differentiable_weierstrassFactor.comp (differentiable_id.div_const _)).sub_const
        _).continuous.continuousOn
  rw [show sigmaProd L = fun z ↦ ∏' l : L.lattice, weierstrassFactor (z / l) from rfl]
  simpa only [add_sub_cancel] using key
 
lemma differentiable_sigmaProd : Differentiable ℂ (sigmaProd L) := by
  have := (hasProdLocallyUniformlyOn_sigmaProd L).differentiableOn
    (.of_forall fun s ↦ ?_) isOpen_univ
  · exact fun x ↦ (this x (Set.mem_univ x)).differentiableAt (isOpen_univ.mem_nhds trivial)
  · simpa [Finset.prod_fn] using DifferentiableOn.finsetProd (fun i _ ↦
      (differentiable_weierstrassFactor.comp (differentiable_id.div_const _)).differentiableOn)
 
lemma differentiable_sigma : Differentiable ℂ (sigma L) :=
  differentiable_id.mul (differentiable_sigmaProd L)
lemma weierstrassFactor_div_ne_zero {z : ℂ} (hz : z ∉ L.lattice) (l : L.lattice) :
    weierstrassFactor (z / l) ≠ 0 := by
  rw [Ne, weierstrassFactor_eq_zero_iff]
  intro h
  have hl : (l : ℂ) ≠ 0 := by rintro h'; rw [h', div_zero] at h; exact zero_ne_one h
  rw [div_eq_one_iff_eq hl] at h
  exact hz (h ▸ l.2)
lemma sigmaProd_ne_zero {z : ℂ} (hz : z ∉ L.lattice) : sigmaProd L z ≠ 0 := by
  have := tprod_one_add_ne_zero_of_summable
    (f := fun l : L.lattice ↦ weierstrassFactor (z / l) - 1)
    (fun l ↦ by simpa using weierstrassFactor_div_ne_zero L hz l)
    (summable_norm_weierstrassFactor_div_sub_one L z)
  simpa only [add_sub_cancel, sigmaProd] using this
lemma sigmaProd_coe (l : L.lattice) (hl : (l : ℂ) ≠ 0) : sigmaProd L l = 0 :=
  tprod_of_exists_eq_zero ⟨l, by simp [div_self hl]⟩
@[simp] lemma sigmaProd_zero : sigmaProd L 0 = 1 := by
  simp [sigmaProd]
 
lemma sigma_eq_zero_iff {z : ℂ} : sigma L z = 0 ↔ z ∈ L.lattice := by
  constructor
  · intro h
    by_contra hz
    have hz0 : z ≠ 0 := fun h0 ↦ hz (h0 ▸ L.lattice.zero_mem)
    exact mul_ne_zero hz0 (sigmaProd_ne_zero L hz) h
  · intro hz
    by_cases hz0 : z = 0
    · simp [sigma, hz0]
    · simp [sigma, sigmaProd_coe L ⟨z, hz⟩ hz0]
lemma sigma_ne_zero {z : ℂ} (hz : z ∉ L.lattice) : sigma L z ≠ 0 :=
  fun h ↦ hz ((sigma_eq_zero_iff L).mp h)
@[simp] lemma sigma_zero : sigma L 0 = 0 := by simp [sigma]
lemma sigma_coe (l : L.lattice) : sigma L l = 0 := (sigma_eq_zero_iff L).mpr l.2
lemma sigmaProd_neg (z : ℂ) : sigmaProd L (-z) = sigmaProd L z := by
  unfold sigmaProd
  rw [← (Equiv.neg L.lattice).tprod_eq]
  congr 1 with l
  simp [neg_div, div_neg]
 
lemma sigma_neg (z : ℂ) : sigma L (-z) = -sigma L z := by
  simp [sigma, sigmaProd_neg]
 
lemma hasDerivAt_sigma_zero : HasDerivAt (sigma L) 1 0 := by
  have := (hasDerivAt_id' (0 : ℂ)).mul (differentiable_sigmaProd L 0).hasDerivAt
  simpa only [mul_one,one_mul,zero_mul,add_zero,sigmaProd_zero] using! this
lemma deriv_sigma_zero : deriv (sigma L) 0 = 1 := (hasDerivAt_sigma_zero L).deriv
lemma hasDerivAt_weierstrassFactor_div (l x : ℂ) :
    HasDerivAt (fun z ↦ weierstrassFactor (z / l))
      (-(x / l) ^ 2 * exp (x / l + (x / l) ^ 2 / 2) * (1 / l)) x := by
  have h := (hasDerivAt_weierstrassFactor (x / l)).comp x ((hasDerivAt_id' x).div_const l)
  exact h
lemma logDeriv_weierstrassFactor_div (l x : ℂ) (hx : x ≠ l) :
    logDeriv (fun z ↦ weierstrassFactor (z / l)) x = if l = 0 then 0 else zetaSummand l x := by
  rw [logDeriv_apply, (hasDerivAt_weierstrassFactor_div l x).deriv]
  split_ifs with hl
  · simp [hl]
  · rw [zetaSummand_eq l x hl hx, weierstrassFactor]
    have h1 : (1 : ℂ) - x / l ≠ 0 := by
      rw [sub_ne_zero, ne_eq, eq_div_iff hl, one_mul]; exact fun h ↦ hx h.symm
    have h2 : x - l ≠ 0 := sub_ne_zero.mpr hx
    have h3 : (1 : ℂ) - x / l = -(x - l) / l := by field_simp; ring
    rw [h3]
    field_simp
lemma summable_logDeriv_weierstrassFactor_div {x : ℂ} (hx : x ∉ L.lattice) :
    Summable fun l : L.lattice ↦ logDeriv (fun z ↦ weierstrassFactor (z / l)) x := by
  have hxl : ∀ l : L.lattice, x ≠ l := fun l h ↦ hx (h ▸ l.2)
  simp_rw [logDeriv_weierstrassFactor_div _ _ (hxl _)]
  refine (summable_zetaSummand L x).congr_cofinite ?_
  filter_upwards [eventually_le_norm L 1] with l hl
  have : (l : ℂ) ≠ 0 := by rintro h; rw [h, norm_zero] at hl; norm_num at hl
  simp [this]
lemma tsum_logDeriv_weierstrassFactor_div {x : ℂ} (hx : x ∉ L.lattice) :
    ∑' l : L.lattice, logDeriv (fun z ↦ weierstrassFactor (z / l)) x = zeta L x - 1 / x := by
  have hxl : ∀ l : L.lattice, x ≠ l := fun l h ↦ hx (h ▸ l.2)
  simp_rw [logDeriv_weierstrassFactor_div _ _ (hxl _)]
  have hs := summable_zetaSummand L x
  have e : ∀ l : L.lattice, (if (l : ℂ) = 0 then 0 else zetaSummand l x) =
      zetaSummand l x - if l = 0 then 1 / x else 0 := by
    intro l
    by_cases hl : l = 0
    · simp [hl, zetaSummand]
    · have : (l : ℂ) ≠ 0 := fun h ↦ hl (Subtype.ext h)
      simp [hl, this]
  simp_rw [e]
  rw [hs.tsum_sub (summable_of_hasFiniteSupport ((Set.finite_singleton 0).subset (by
    intro l hl; by_contra h; simp_all))), tsum_ite_eq]
  rfl
lemma logDeriv_sigmaProd {x : ℂ} (hx : x ∉ L.lattice) :
    logDeriv (sigmaProd L) x = zeta L x - 1 / x := by
  have h := logDeriv_tprod_eq_tsum (isOpen_compl_coe_lattice L) hx
    (f := fun (l : L.lattice) (z : ℂ) ↦ weierstrassFactor (z / l))
    (weierstrassFactor_div_ne_zero L hx)
    (fun l ↦
      (differentiable_weierstrassFactor.comp (differentiable_id.div_const _)).differentiableOn)
    (summable_logDeriv_weierstrassFactor_div L hx)
    ((hasProdLocallyUniformlyOn_sigmaProd L).multipliableLocallyUniformlyOn.mono
      (Set.subset_univ _))
    (sigmaProd_ne_zero L hx)
  rw [← tsum_logDeriv_weierstrassFactor_div L hx, ← h]
  rfl
 
lemma logDeriv_sigma {x : ℂ} (hx : x ∉ L.lattice) : logDeriv (sigma L) x = zeta L x := by
  have hx0 : x ≠ 0 := fun h ↦ hx (h ▸ L.lattice.zero_mem)
  have := logDeriv_mul (f := id) (g := sigmaProd L) x hx0 (sigmaProd_ne_zero L hx)
    differentiableAt_id (differentiable_sigmaProd L x)
  rw [show sigma L = (fun z => id z * sigmaProd L z) from rfl, this, logDeriv_id, logDeriv_sigmaProd L hx]
  ring
 
lemma deriv_sigma {x : ℂ} (hx : x ∉ L.lattice) : deriv (sigma L) x = zeta L x * sigma L x := by
  have := logDeriv_sigma L hx
  rw [logDeriv_apply, div_eq_iff (sigma_ne_zero L hx)] at this
  exact this
end LSG.Weierstrass
end
end

/- LSG.Weierstrass.SigmaQuasiPeriod -/
section
open Module Filter Complex
open scoped Topology
noncomputable section
namespace LSG.Weierstrass
open PeriodPair
variable (L : PeriodPair)
lemma countable_lattice : (L.lattice : Set ℂ).Countable := by
  have : Countable L.lattice := L.latticeEquivProd.injective.countable
  exact Set.countable_coe_iff.mp this
 
lemma isConnected_compl_lattice : IsConnected (L.lattice : Set ℂ)ᶜ :=
  Set.Countable.isConnected_compl_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)
    (countable_lattice L)
lemma add_notMem_lattice {z ω : ℂ} (hz : z ∉ L.lattice) (hω : ω ∈ L.lattice) :
    z + ω ∉ L.lattice := fun h ↦ hz ((Submodule.add_mem_iff_left _ hω).mp h)
 
lemma eq_of_hasDerivAt_zero {g : ℂ → ℂ} (hg : ∀ z ∉ L.lattice, HasDerivAt g 0 z) {z w : ℂ}
    (hz : z ∉ L.lattice) (hw : w ∉ L.lattice) : g z = g w :=
  (isOpen_compl_coe_lattice L).is_const_of_deriv_eq_zero
    (isConnected_compl_lattice L).isPreconnected
    (fun x hx ↦ (hg x hx).differentiableAt.differentiableWithinAt) (fun x hx ↦ (hg x hx).deriv)
    hz hw
 

def eta (ω : ℂ) : ℂ := zeta L (L.ω₁ / 2 + ω) - zeta L (L.ω₁ / 2)
lemma hasDerivAt_zeta_add_sub {ω : ℂ} (hω : ω ∈ L.lattice) {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt (fun z ↦ zeta L (z + ω) - zeta L z) 0 z := by
  have h1 := (hasDerivAt_zeta L (add_notMem_lattice L hz hω)).comp_add_const z ω
  have h2 : HasDerivAt (fun z ↦ zeta L (z + ω) - zeta L z) (-℘[L] (z + ω) - -℘[L] z) z :=
    h1.sub (hasDerivAt_zeta L hz)
  have hp : ℘[L] (z + ω) = ℘[L] z := L.weierstrassP_add_coe z ⟨ω, hω⟩
  rwa [hp, sub_self] at h2
 
lemma zeta_add_eta {ω : ℂ} (hω : ω ∈ L.lattice) {z : ℂ} (hz : z ∉ L.lattice) :
    zeta L (z + ω) = zeta L z + eta L ω := by
  have : zeta L (z + ω) - zeta L z = zeta L (L.ω₁ / 2 + ω) - zeta L (L.ω₁ / 2) :=
    eq_of_hasDerivAt_zero L (g := fun z ↦ zeta L (z + ω) - zeta L z)
      (fun x hx ↦ hasDerivAt_zeta_add_sub L hω hx) hz L.ω₁_div_two_notMem_lattice
  rw [eta]
  linear_combination this
@[simp] lemma eta_zero : eta L 0 = 0 := by simp [eta]
 
lemma eta_add {ω ω' : ℂ} (hω : ω ∈ L.lattice) (hω' : ω' ∈ L.lattice) :
    eta L (ω + ω') = eta L ω + eta L ω' := by
  have h0 := L.ω₁_div_two_notMem_lattice
  have h1 := zeta_add_eta L (add_mem hω hω') h0
  have h2 := zeta_add_eta L hω' (add_notMem_lattice L h0 hω)
  have h3 := zeta_add_eta L hω h0
  rw [← add_assoc, h2, h3] at h1
  linear_combination -h1
lemma hasDerivAt_sigma (z : ℂ) : HasDerivAt (sigma L) (deriv (sigma L) z) z :=
  (differentiable_sigma L z).hasDerivAt
 
lemma exists_sigma_add {ω : ℂ} (hω : ω ∈ L.lattice) :
    ∃ c : ℂ, ∀ z, sigma L (z + ω) = c * exp (eta L ω * z) * sigma L z := by
  let G : ℂ → ℂ := fun z ↦ sigma L (z + ω) * exp (-(eta L ω * z)) / sigma L z
  have hG : ∀ z ∉ L.lattice, HasDerivAt G 0 z := by
    intro z hz
    have hz' := add_notMem_lattice L hz hω
    have h1 := (hasDerivAt_sigma L (z + ω)).comp_add_const z ω
    have h2 : HasDerivAt (fun z ↦ exp (-(eta L ω * z))) (exp (-(eta L ω * z)) * -(eta L ω * 1))
        z := ((hasDerivAt_id' z).const_mul (eta L ω)).neg.cexp
    have h3 := (h1.mul h2).div (hasDerivAt_sigma L z) (sigma_ne_zero L hz)
    refine h3.congr_deriv ?_
    rw [deriv_sigma L hz', deriv_sigma L hz, zeta_add_eta L hω hz]
    simp only [Pi.mul_apply]
    ring
  refine ⟨G (L.ω₁ / 2), fun z ↦ ?_⟩
  by_cases hz : z ∈ L.lattice
  · rw [sigma_coe L ⟨z, hz⟩, sigma_coe L ⟨z + ω, add_mem hz hω⟩, mul_zero]
  · have := eq_of_hasDerivAt_zero L hG hz L.ω₁_div_two_notMem_lattice
    have h1 := sigma_ne_zero L hz
    have h2 : exp (-(eta L ω * z)) * exp (eta L ω * z) = 1 := by rw [← exp_add]; simp
    have h3 : sigma L (z + ω) * exp (-(eta L ω * z)) = G (L.ω₁ / 2) * sigma L z := by
      rw [← this]; simp only [G]; rw [div_mul_cancel₀ _ h1]
    calc sigma L (z + ω) = sigma L (z + ω) * (exp (-(eta L ω * z)) * exp (eta L ω * z)) := by
          rw [h2, mul_one]
      _ = (sigma L (z + ω) * exp (-(eta L ω * z))) * exp (eta L ω * z) := by ring
      _ = _ := by rw [h3]; ring
 
lemma sigma_add_of_half_notMem {ω : ℂ} (hω : ω ∈ L.lattice) (hω2 : ω / 2 ∉ L.lattice) (z : ℂ) :
    sigma L (z + ω) = -exp (eta L ω * (z + ω / 2)) * sigma L z := by
  obtain ⟨c, hc⟩ := exists_sigma_add L hω
  set e := eta L ω
  have hs := sigma_ne_zero L hω2
  have h := hc (-(ω / 2))
  rw [show -(ω / 2) + ω = ω / 2 by ring, sigma_neg] at h
  have he : exp (e * -(ω / 2)) * exp (e * (ω / 2)) = 1 := by rw [← exp_add]; ring_nf; simp
  have hce : c * exp (e * -(ω / 2)) = -1 := by
    have : sigma L (ω / 2) * (c * exp (e * -(ω / 2)) + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hs
    · linear_combination h'
  have hc' : c = -exp (e * (ω / 2)) := by linear_combination exp (e * (ω / 2)) * hce - c * he
  rw [hc z, hc', mul_add, exp_add]
  ring
end LSG.Weierstrass
end
end

/- LSG.Weierstrass.ZetaQuasiPeriod -/
section
open Module Filter Complex
open scoped Topology
noncomputable section
namespace LSG.Weierstrass
open PeriodPair
variable (L : PeriodPair)
 
def zetaExcept (l₀ : L.lattice) (z : ℂ) : ℂ :=
  ∑' l : L.lattice, if l = l₀ then 0 else zetaSummand l z
lemma hasSumLocallyUniformly_zetaExcept (l₀ : L.lattice) :
    HasSumLocallyUniformly (fun (l : L.lattice) (z : ℂ) ↦ if l = l₀ then 0 else zetaSummand l z)
      (zetaExcept L l₀) := by
  refine PeriodPair.hasSumLocallyUniformly_aux L (u := fun r l ↦ 2 * r ^ 2 * ‖(l : ℂ)‖ ^ (-3 : ℝ))
    _ (fun _ _ ↦ (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _) fun r hr ↦
    Filter.eventually_atTop.mpr ⟨2 * r, ?_⟩
  rintro _ h s hs l rfl
  split_ifs
  · rw [norm_zero]; positivity
  · exact zetaSummand_bound r hr s hs l h
lemma zeta_eq_zetaExcept_add (l₀ : L.lattice) (z : ℂ) :
    zeta L z = zetaExcept L l₀ z + zetaSummand l₀ z := by
  have h := ((hasSumLocallyUniformly_zetaExcept L l₀).hasSum (x := z)).add
    (hasSum_ite_eq l₀ (zetaSummand l₀ z))
  refine (hasSum_zeta L z).unique ?_
  convert h using 1
  funext l
  by_cases hl : l = l₀
  · simp [hl]
  · simp [hl]
lemma continuousAt_zetaExcept (l₀ : L.lattice) : ContinuousAt (zetaExcept L l₀) l₀ := by
  have hU : IsOpen (L.lattice \ {(l₀ : ℂ)} : Set ℂ)ᶜ := L.isOpen_compl_lattice_sdiff
  have hd : DifferentiableOn ℂ (zetaExcept L l₀) (L.lattice \ {(l₀ : ℂ)} : Set ℂ)ᶜ := by
    refine (hasSumLocallyUniformly_zetaExcept L l₀).tendstoLocallyUniformlyOn.differentiableOn
      (.of_forall fun s ↦ .fun_sum fun l _ ↦ ?_) hU
    intro x hx
    split_ifs with hl
    · exact differentiableWithinAt_const _
    · have hxl : x - l ≠ 0 := by
        intro e
        have hxe : x = l := sub_eq_zero.mp e
        apply hx
        refine ⟨hxe ▸ l.2, ?_⟩
        rw [Set.mem_singleton_iff, hxe]
        exact fun h' ↦ hl (Subtype.ext h')
      exact (hasDerivAt_zetaSummand l x hxl).differentiableAt.differentiableWithinAt
  exact ((hd _ (by simp)).differentiableAt (hU.mem_nhds (by simp))).continuousAt
 

theorem zeta_add {ω : ℂ} (hω : ω ∈ L.lattice) (z : ℂ) :
    zeta L (z + ω) = zeta L z + eta L ω := by
  by_cases hz : z ∉ L.lattice
  · exact zeta_add_eta L hω hz
  replace hz := not_not.mp hz
  set l₀ : L.lattice := ⟨z, hz⟩
  set l₁ : L.lattice := ⟨z + ω, add_mem hz hω⟩
  let G : ℂ → ℂ := fun w ↦ zetaExcept L l₁ (w + ω) - zetaExcept L l₀ w +
    (1 / (z + ω) + (w + ω) / (z + ω) ^ 2 - 1 / z - w / z ^ 2) - eta L ω
  have hG : ∀ w, zeta L (w + ω) - zeta L w - eta L ω = G w := by
    intro w
    rw [zeta_eq_zetaExcept_add L l₁ (w + ω), zeta_eq_zetaExcept_add L l₀ w]
    simp only [G, zetaSummand, l₀, l₁]
    rw [show w + ω - (z + ω) = w - z by ring]
    ring
  have hc : ContinuousAt G z := by
    have h1 : ContinuousAt (fun w ↦ zetaExcept L l₁ (w + ω)) z :=
      (continuousAt_zetaExcept L l₁).comp (f := fun w ↦ w + ω) (continuousAt_id.add_const ω)
    have h2 : ContinuousAt (zetaExcept L l₀) z := continuousAt_zetaExcept L l₀
    exact ((h1.sub h2).add (by fun_prop)).sub continuousAt_const
  have hev : G =ᶠ[𝓝[≠] z] fun _ ↦ 0 := by
    have := L.compl_lattice_sdiff_singleton_mem_nhds z
    filter_upwards [nhdsWithin_le_nhds this, self_mem_nhdsWithin] with w hw hwz
    have hw' : w ∉ L.lattice := fun h ↦ hw ⟨h, hwz⟩
    rw [← hG, zeta_add_eta L hω hw']
    ring
  have hlim : Tendsto G (𝓝[≠] z) (𝓝 (G z)) := hc.tendsto.mono_left nhdsWithin_le_nhds
  have h0 : G z = 0 := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hev.symm)
  have := hG z
  rw [h0] at this
  linear_combination this
end LSG.Weierstrass
end
end

/- LSG.Weierstrass.RectInv -/
section
open Complex MeasureTheory intervalIntegral Set
open scoped Real ComplexConjugate Interval
noncomputable section
namespace LSG.Weierstrass
 

def rectIntegral (F : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, F (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, F (x + w.im * I)) +
    I • (∫ y : ℝ in z.im..w.im, F (w.re + y * I)) - I • (∫ y : ℝ in z.im..w.im, F (z.re + y * I))
 
lemma rectIntegral_eq_zero {F : ℂ → ℂ} {z w : ℂ}
    (H : DifferentiableOn ℂ F ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) : rectIntegral F z w = 0 :=
  Complex.integral_boundary_rect_eq_zero_of_differentiableOn F z w H
lemma intervalIntegrable_comp {F : ℂ → ℂ} {s t : ℝ} {g : ℝ → ℂ} (hg : Continuous g)
    (hF : ∀ x ∈ [[s, t]], ContinuousAt F (g x)) :
    IntervalIntegrable (fun x => F (g x)) volume s t :=
  ContinuousOn.intervalIntegrable fun x hx => ((hF x hx).comp hg.continuousAt).continuousWithinAt
 
lemma rectIntegral_add {F₁ F₂ : ℂ → ℂ} {z w : ℂ}
    (h₁ : ∀ p ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]],
      (p.re = z.re ∨ p.re = w.re ∨ p.im = z.im ∨ p.im = w.im) → ContinuousAt F₁ p)
    (h₂ : ∀ p ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]],
      (p.re = z.re ∨ p.re = w.re ∨ p.im = z.im ∨ p.im = w.im) → ContinuousAt F₂ p) :
    rectIntegral (fun p => F₁ p + F₂ p) z w = rectIntegral F₁ z w + rectIntegral F₂ z w := by
  have hz : z.im ∈ [[z.im, w.im]] := left_mem_uIcc
  have hw : w.im ∈ [[z.im, w.im]] := right_mem_uIcc
  have hz' : z.re ∈ [[z.re, w.re]] := left_mem_uIcc
  have hw' : w.re ∈ [[z.re, w.re]] := right_mem_uIcc
  have hor : ∀ (F : ℂ → ℂ), (∀ p ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]],
      (p.re = z.re ∨ p.re = w.re ∨ p.im = z.im ∨ p.im = w.im) → ContinuousAt F p) →
      ∀ c ∈ ({z.im, w.im} : Set ℝ),
      IntervalIntegrable (fun x : ℝ => F (x + c * I)) volume z.re w.re := by
    intro F hF c hc
    refine intervalIntegrable_comp (g := fun x : ℝ => (x : ℂ) + c * I) (by fun_prop) ?_
    intro x hx
    rcases hc with rfl | rfl
    · exact hF _ (by simp [mem_reProdIm, hx, hz]) (by simp)
    · exact hF _ (by simp [mem_reProdIm, hx, hw]) (by simp)
  have ver : ∀ (F : ℂ → ℂ), (∀ p ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]],
      (p.re = z.re ∨ p.re = w.re ∨ p.im = z.im ∨ p.im = w.im) → ContinuousAt F p) →
      ∀ c ∈ ({z.re, w.re} : Set ℝ),
      IntervalIntegrable (fun y : ℝ => F (c + y * I)) volume z.im w.im := by
    intro F hF c hc
    refine intervalIntegrable_comp (g := fun y : ℝ => (c : ℂ) + y * I) (by fun_prop) ?_
    intro y hy
    rcases hc with rfl | rfl
    · exact hF _ (by simp [mem_reProdIm, hy, hz']) (by simp)
    · exact hF _ (by simp [mem_reProdIm, hy, hw']) (by simp)
  unfold rectIntegral
  rw [integral_add (hor F₁ h₁ _ (by simp)) (hor F₂ h₂ _ (by simp)),
    integral_add (hor F₁ h₁ _ (by simp)) (hor F₂ h₂ _ (by simp)),
    integral_add (ver F₁ h₁ _ (by simp)) (ver F₂ h₂ _ (by simp)),
    integral_add (ver F₁ h₁ _ (by simp)) (ver F₂ h₂ _ (by simp))]
  simp only [smul_add]
  ring
lemma hasDerivAt_log_line {c d : ℂ} {x : ℝ} (h : c + x * d ∈ slitPlane) :
    HasDerivAt (fun t : ℝ => log (c + t * d)) ((c + x * d)⁻¹ * d) x := by
  have h1 : HasDerivAt (fun w : ℂ => log (c + w * d)) ((c + x * d)⁻¹ * d) (x : ℂ) := by
    have := (hasDerivAt_log h).comp (x : ℂ) (((hasDerivAt_id (x : ℂ)).mul_const d).const_add c)
    simpa [Function.comp_def] using this
  exact h1.comp_ofReal
lemma integral_inv_line {c d : ℂ} {s t : ℝ} (hd : d ≠ 0)
    (h : ∀ x ∈ [[s, t]], c + x * d ∈ slitPlane) :
    ∫ x : ℝ in s..t, (c + x * d)⁻¹ = d⁻¹ * (log (c + t * d) - log (c + s * d)) := by
  have hcont : ∀ x ∈ [[s, t]], c + x * d ≠ 0 := fun x hx => slitPlane_ne_zero (h x hx)
  have := integral_eq_sub_of_hasDerivAt (fun x hx => hasDerivAt_log_line (h x hx))
    (ContinuousOn.intervalIntegrable (u := fun x : ℝ => (c + x * d)⁻¹ * d) (by
      refine ContinuousOn.mul ?_ continuousOn_const
      exact ContinuousOn.inv₀ (by fun_prop) hcont))
  rw [intervalIntegral.integral_mul_const] at this
  rw [← this, mul_comm _ d, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]
 
theorem rectIntegral_inv {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    rectIntegral (fun z => z⁻¹) ⟨-a, -b⟩ ⟨a, b⟩ = 2 * π * I := by
  unfold rectIntegral
  simp only
  
  have hB : ∫ x : ℝ in (-a)..a, ((x : ℂ) + ((-b : ℝ) : ℂ) * I)⁻¹ =
      log (((-b : ℝ) : ℂ) * I + a) - log (((-b : ℝ) : ℂ) * I + (-a : ℝ)) := by
    have := integral_inv_line (c := ((-b : ℝ) : ℂ) * I) (d := 1) (s := -a) (t := a) one_ne_zero
      (fun x _ => by rw [mem_slitPlane_iff]; right; simp; linarith)
    simpa [add_comm] using this
  have hT : ∫ x : ℝ in (-a)..a, ((x : ℂ) + (b : ℂ) * I)⁻¹ =
      log ((b : ℂ) * I + a) - log ((b : ℂ) * I + (-a : ℝ)) := by
    have := integral_inv_line (c := (b : ℂ) * I) (d := 1) (s := -a) (t := a) one_ne_zero
      (fun x _ => by rw [mem_slitPlane_iff]; right; simp; linarith)
    simpa [add_comm] using this
  have hR : ∫ y : ℝ in (-b)..b, ((a : ℂ) + y * I)⁻¹ =
      I⁻¹ * (log ((a : ℂ) + b * I) - log ((a : ℂ) + (-b : ℝ) * I)) :=
    integral_inv_line I_ne_zero (fun x _ => by rw [mem_slitPlane_iff]; left; simpa using ha)
  have hL : ∫ y : ℝ in (-b)..b, (((-a : ℝ) : ℂ) + y * I)⁻¹ =
      I⁻¹ * (log ((a : ℂ) + (-b : ℝ) * I) - log ((a : ℂ) + b * I)) := by
    have := integral_inv_line (c := (a : ℂ)) (d := -I) (s := -b) (t := b) (neg_ne_zero.mpr I_ne_zero)
      (fun x _ => by rw [mem_slitPlane_iff]; left; simpa using ha)
    have e : ∀ y : ℝ, (((-a : ℝ) : ℂ) + y * I)⁻¹ = -((a : ℂ) + y * -I)⁻¹ := by
      intro y; rw [← inv_neg]; congr 1; push_cast; ring
    simp_rw [e, intervalIntegral.integral_neg, this]
    push_cast
    rw [inv_neg]
    ring_nf
  rw [hB, hT, hR, hL]
  
  set p : ℂ := (a : ℂ) + b * I with hp
  have hpre : p.re = a := by simp [hp]
  have hpim : p.im = b := by simp [hp]
  have e1 : ((-b : ℝ) : ℂ) * I + a = conj p := by
    apply Complex.ext <;> simp [hp]
  have e2 : ((-b : ℝ) : ℂ) * I + (-a : ℝ) = -p := by
    apply Complex.ext <;> simp [hp]
  have e3 : (b : ℂ) * I + a = p := by rw [hp]; ring
  have e4 : (b : ℂ) * I + (-a : ℝ) = -conj p := by
    apply Complex.ext <;> simp [hp]
  have e5 : (a : ℂ) + (-b : ℝ) * I = conj p := by
    apply Complex.ext <;> simp [hp]
  rw [e1, e2, e3, e4, e5]
  have hargp : arg p ≠ π := by
    intro h
    have := Complex.arg_eq_pi_iff.mp h
    linarith [this.2, hpim]
  have harg1 : arg (conj p) = -arg p := by rw [arg_conj, ite_eq_right_iff.mpr (fun h => absurd h hargp)]
  have harg2 : arg (-p) = arg p - π := arg_neg_eq_arg_sub_pi_of_im_pos (by rw [hpim]; exact hb)
  have harg3 : arg (-conj p) = -arg p + π := by
    rw [arg_neg_eq_arg_add_pi_of_im_neg (by simp [hpim, hb]), harg1]
  have hn1 : ‖conj p‖ = ‖p‖ := Complex.norm_conj p
  have hn2 : ‖-p‖ = ‖p‖ := norm_neg p
  have hn3 : ‖-conj p‖ = ‖p‖ := by rw [norm_neg, hn1]
  have key : log (-conj p) - log (-p) + log p - log (conj p) = 2 * π * I := by
    apply Complex.ext
    · simp only [sub_re, add_re, log_re, hn1, hn2, hn3]
      simp
    · simp only [sub_im, add_im, log_im, harg1, harg2, harg3]
      simp
      ring
  simp only [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ I_ne_zero, one_mul]
  linear_combination key
end LSG.Weierstrass
end
end

/- LSG.Weierstrass.Basic -/
section
open Complex Filter Topology PeriodPair Real
namespace LSG.Weierstrass
variable (L : PeriodPair)
lemma ω₁_ne_zero : L.ω₁ ≠ 0 := by simpa using L.indep.ne_zero 0
 
lemma int_coords_eq {a b c d : ℤ} (h : (a : ℂ) * L.ω₁ + b * L.ω₂ = c * L.ω₁ + d * L.ω₂) :
    a = c ∧ b = d := by
  have := LinearIndependent.pair_iff.mp L.indep ((a : ℝ) - c) ((b : ℝ) - d)
    (by simp only [Complex.real_smul]; push_cast; linear_combination h)
  constructor
  · have h1 := this.1; rw [sub_eq_zero] at h1; exact_mod_cast h1
  · have h2 := this.2; rw [sub_eq_zero] at h2; exact_mod_cast h2
lemma lattice_countable : (L.lattice : Set ℂ).Countable := by
  have : (L.lattice : Set ℂ) ⊆ Set.range (fun p : ℤ × ℤ => (p.1 : ℂ) * L.ω₁ + p.2 * L.ω₂) := by
    intro x hx
    obtain ⟨m, n, h⟩ := PeriodPair.mem_lattice.mp hx
    exact ⟨(m, n), h⟩
  exact (Set.countable_range _).mono this
lemma isPreconnected_compl_lattice : IsPreconnected (L.lattice : Set ℂ)ᶜ :=
  ((lattice_countable L).isConnected_compl_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num)).isPreconnected
lemma isOpen_compl_lattice : IsOpen (L.lattice : Set ℂ)ᶜ := L.isClosed_lattice.isOpen_compl
 
lemma exists_norm_weierstrassP_gt (M : ℝ) : ∃ z, z ∉ L.lattice ∧ M < ‖℘[L] z‖ := by
  have hc : ContinuousAt (L.weierstrassPExcept 0) 0 :=
    (L.analyticAt_weierstrassPExcept 0).continuousAt
  obtain ⟨δ₁, hδ₁, hb⟩ := Metric.continuousAt_iff.mp hc 1 one_pos
  obtain ⟨δ₂, hδ₂, hball⟩ := Metric.mem_nhds_iff.mp (L.compl_lattice_sdiff_singleton_mem_nhds 0)
  set B := ‖(L.weierstrassPExcept 0) 0‖ + 1
  have hB : 0 ≤ B := by positivity
  set A := |M| + B + 2
  have hA : 2 ≤ A := by have := abs_nonneg M; linarith
  set t : ℝ := min (min δ₁ δ₂ / 2) (1 / A)
  have hδ : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  have ht0 : 0 < t := lt_min (by positivity) (by positivity)
  have htδ : t < min δ₁ δ₂ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htA : t ≤ 1 / A := min_le_right _ _
  have htn : ‖(t : ℂ)‖ = t := by simp [abs_of_pos ht0]
  have ht1 : ‖(t : ℂ)‖ < δ₁ := by rw [htn]; exact lt_of_lt_of_le htδ (min_le_left _ _)
  have ht2 : ‖(t : ℂ)‖ < δ₂ := by rw [htn]; exact lt_of_lt_of_le htδ (min_le_right _ _)
  have hnot : (t : ℂ) ∉ L.lattice := by
    have := hball (show (t : ℂ) ∈ Metric.ball 0 δ₂ by
      rw [Metric.mem_ball, dist_zero_right]; exact ht2)
    simp only [Set.mem_compl_iff, Set.mem_sdiff, Set.mem_singleton_iff, not_and, not_not] at this
    intro hm
    have := this hm
    exact (ne_of_gt ht0) (by exact_mod_cast this)
  refine ⟨t, hnot, ?_⟩
  have hbd : ‖(L.weierstrassPExcept 0) t‖ ≤ B := by
    have := hb (x := (t : ℂ)) (by rw [dist_zero_right]; exact ht1)
    rw [dist_eq_norm] at this
    have := norm_le_norm_add_norm_sub' (L.weierstrassPExcept 0 t) (L.weierstrassPExcept 0 0)
    simp only [B]
    linarith
  have hdecomp : ℘[L] t = (L.weierstrassPExcept 0) t + 1 / (t : ℂ) ^ 2 := by
    rw [← L.weierstrassPExcept_add ⟨0, L.lattice.zero_mem⟩]; simp
  have hinv : A ≤ 1 / t ^ 2 := by
    have h1 : A * t ≤ 1 := by rw [le_div_iff₀ (by linarith)] at htA; linarith
    have ht1' : t ≤ 1 := by
      have : 1 / A ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      linarith
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hnorm : ‖1 / (t : ℂ) ^ 2‖ = 1 / t ^ 2 := by
    simp [norm_pow, abs_of_pos ht0]
  rw [hdecomp]
  have := norm_sub_norm_le (1 / (t : ℂ) ^ 2) (-(L.weierstrassPExcept 0) t)
  rw [sub_neg_eq_add, norm_neg, hnorm, add_comm] at this
  have hM := le_abs_self M
  linarith
lemma hasDerivAt_weierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt ℘[L] (℘'[L] z) z := by
  have := (L.differentiableOn_weierstrassP.differentiableAt
    ((isOpen_compl_lattice L).mem_nhds hz)).hasDerivAt
  rwa [L.deriv_weierstrassP] at this
lemma differentiableAt_derivWeierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    DifferentiableAt ℂ ℘'[L] z :=
  L.differentiableOn_derivWeierstrassP.differentiableAt ((isOpen_compl_lattice L).mem_nhds hz)
 
lemma derivWeierstrassP_not_eventually_zero {z₀ : ℂ} (hz₀ : z₀ ∉ L.lattice) :
    ¬ (℘'[L] =ᶠ[𝓝 z₀] 0) := by
  intro h
  have hEq := L.analyticOnNhd_derivWeierstrassP.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (isPreconnected_compl_lattice L) hz₀ h
  have hconst : ∀ x ∈ (L.lattice : Set ℂ)ᶜ, ℘[L] x = ℘[L] z₀ := fun x hx =>
    (isOpen_compl_lattice L).is_const_of_deriv_eq_zero (isPreconnected_compl_lattice L)
      L.differentiableOn_weierstrassP (by intro y hy; simp [hEq hy]) hx hz₀
  obtain ⟨z, hz, hM⟩ := (exists_norm_weierstrassP_gt L) ‖℘[L] z₀‖
  rw [hconst z hz] at hM
  exact lt_irrefl _ hM
 
theorem hasDerivAt_derivWeierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt ℘'[L] (6 * ℘[L] z ^ 2 - L.g₂ / 2) z := by
  
  have key : ∀ w, w ∉ L.lattice →
      ℘'[L] w * (deriv ℘'[L] w - (6 * ℘[L] w ^ 2 - L.g₂ / 2)) = 0 := by
    intro w hw
    have h1 : HasDerivAt (fun x => ℘'[L] x ^ 2) (↑2 * ℘'[L] w ^ (2 - 1) * deriv ℘'[L] w) w :=
      ((differentiableAt_derivWeierstrassP L) hw).hasDerivAt.pow 2
    have hP := (hasDerivAt_weierstrassP L) hw
    have h2 : HasDerivAt (fun x => 4 * ℘[L] x ^ 3 - L.g₂ * ℘[L] x - L.g₃)
        (4 * (↑3 * ℘[L] w ^ (3 - 1) * ℘'[L] w) - L.g₂ * ℘'[L] w) w :=
      (((hP.pow 3).const_mul 4).sub (hP.const_mul L.g₂)).sub_const L.g₃
    have hev : (fun x => ℘'[L] x ^ 2) =ᶠ[𝓝 w] (fun x => 4 * ℘[L] x ^ 3 - L.g₂ * ℘[L] x - L.g₃) := by
      filter_upwards [(isOpen_compl_lattice L).mem_nhds hw] with x hx
      exact L.derivWeierstrassP_sq x hx
    have := h1.unique (h2.congr_of_eventuallyEq hev)
    norm_num at this
    linear_combination this / 2
  set F : ℂ → ℂ := fun w => deriv ℘'[L] w - (6 * ℘[L] w ^ 2 - L.g₂ / 2) with hF
  have hFa : AnalyticAt ℂ F z := by
    have h1 := (L.analyticOnNhd_derivWeierstrassP z hz).deriv
    have h2 := L.analyticOnNhd_weierstrassP z hz
    exact h1.sub ((analyticAt_const.mul (h2.pow 2)).sub analyticAt_const)
  have hne : ∀ᶠ w in 𝓝[≠] z, ℘'[L] w ≠ 0 :=
    (L.analyticOnNhd_derivWeierstrassP z hz).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      ((derivWeierstrassP_not_eventually_zero L) hz)
  have hU : ∀ᶠ w in 𝓝[≠] z, w ∉ L.lattice :=
    nhdsWithin_le_nhds ((isOpen_compl_lattice L).mem_nhds hz)
  have hfreq : ∃ᶠ w in 𝓝[≠] z, F w = 0 := by
    refine (hne.and hU).mono ?_ |>.frequently
    rintro w ⟨h1, h2⟩
    exact (mul_eq_zero.mp (key w h2)).resolve_left h1
  have hFz : F z = 0 := (hFa.frequently_zero_iff_eventually_zero.mp hfreq).self_of_nhds
  have hd := ((differentiableAt_derivWeierstrassP L) hz).hasDerivAt
  rwa [sub_eq_zero.mp hFz] at hd
 
lemma derivWeierstrassP_half {ω : ℂ} (hω : ω ∈ L.lattice) : ℘'[L] (ω / 2) = 0 := by
  have h1 : ℘'[L] (ω / 2) = ℘'[L] (-(ω / 2)) := by
    rw [← L.derivWeierstrassP_sub_coe (ω / 2) ⟨ω, hω⟩]
    congr 1; ring
  rw [L.derivWeierstrassP_neg] at h1
  linear_combination h1 / 2
 
lemma weierstrassP_half_cubic {ω : ℂ} (hω : ω ∈ L.lattice) (h2 : ω / 2 ∉ L.lattice) :
    4 * ℘[L] (ω / 2) ^ 3 - L.g₂ * ℘[L] (ω / 2) - L.g₃ = 0 := by
  have := L.derivWeierstrassP_sq (ω / 2) h2
  rw [(derivWeierstrassP_half L) hω] at this
  linear_combination -this
section AlgIndep
variable {K : Type*} [Field K] [Algebra K ℂ]
end AlgIndep
end LSG.Weierstrass
end

/- LSG.Weierstrass.Legendre -/
section
open Module Filter Complex MeasureTheory intervalIntegral Set
open scoped Topology Real Interval
noncomputable section
namespace LSG.Weierstrass
open PeriodPair
variable (L : PeriodPair)
lemma differentiableOn_zetaExcept (l₀ : L.lattice) :
    DifferentiableOn ℂ (zetaExcept L l₀) (L.lattice \ {(l₀ : ℂ)} : Set ℂ)ᶜ := by
  refine (hasSumLocallyUniformly_zetaExcept L l₀).tendstoLocallyUniformlyOn.differentiableOn
    (.of_forall fun s ↦ .fun_sum fun l _ ↦ ?_) L.isOpen_compl_lattice_sdiff
  intro x hx
  split_ifs with hl
  · exact differentiableWithinAt_const _
  · have hxl : x - l ≠ 0 := by
      intro e
      have hxe : x = l := sub_eq_zero.mp e
      apply hx
      refine ⟨hxe ▸ l.2, ?_⟩
      rw [Set.mem_singleton_iff, hxe]
      exact fun h' ↦ hl (Subtype.ext h')
    exact (hasDerivAt_zetaSummand l x hxl).differentiableAt.differentiableWithinAt
lemma differentiableAt_zetaExcept_zero {w : ℂ} (hw : w ∉ L.lattice ∨ w = 0) :
    DifferentiableAt ℂ (zetaExcept L 0) w := by
  refine (differentiableOn_zetaExcept L 0 w ?_).differentiableAt
    (L.isOpen_compl_lattice_sdiff.mem_nhds ?_) <;>
  · rintro ⟨h1, h2⟩
    rcases hw with hw | hw
    · exact hw h1
    · exact h2 (by simp [hw])
 
lemma zeta_eq_zetaExcept_zero_add (w : ℂ) : zeta L w = zetaExcept L 0 w + w⁻¹ := by
  rw [zeta_eq_zetaExcept_add L 0 w]
  simp [zetaSummand]
 
theorem legendre_of_basis {α β : ℂ} (hα : α ∈ L.lattice) (hβ : β ∈ L.lattice)
    (hspan : ∀ l ∈ L.lattice, ∃ m n : ℤ, l = m * α + n * β) (him : 0 < (β / α).im) :
    eta L α * β - eta L β * α = 2 * π * I := by
  have hα0 : α ≠ 0 := by rintro rfl; simp at him
  set τ := β / α with hτ
  set b := τ.im / 2 with hb_def
  have hb : 0 < b := by positivity
  have hατ : α * τ = β := by rw [hτ]; field_simp
  set c := α * eta L β - eta L α * β with hc
  set f : ℂ → ℂ := fun z => α * zeta L (α * z) - α * eta L α * z with hf
  set G : ℂ → ℂ := fun z => α * zetaExcept L 0 (α * z) - α * eta L α * z with hG
  have hfG : f = fun z => G z + z⁻¹ := by
    funext z
    simp only [hf, hG]
    rw [zeta_eq_zetaExcept_zero_add, mul_inv, mul_add, mul_inv_cancel_left₀ hα0]
    ring
  have hf1 : ∀ z, f (z + 1) = f z := by
    intro z
    simp only [hf]
    rw [mul_add, mul_one, zeta_add L hα]
    ring
  have hfτ : ∀ z, f (z + τ) = f z + c := by
    intro z
    simp only [hf, hc]
    rw [mul_add, hατ, zeta_add L hβ, mul_add (α * eta L α), ← hατ]
    ring
  
  have hmem : ∀ z : ℂ, α * z ∈ L.lattice → ∃ m n : ℤ, z = m + n * τ := by
    intro z hz
    obtain ⟨m, n, hmn⟩ := hspan _ hz
    refine ⟨m, n, ?_⟩
    rw [hτ]
    field_simp
    linear_combination hmn
  have hpole : ∀ z : ℂ, z.re ∈ Icc (-1/2 : ℝ) (1/2) → z.im ∈ Icc (-b) b →
      α * z ∈ L.lattice → z = 0 := by
    intro z hre him' hz
    obtain ⟨m, n, rfl⟩ := hmem z hz
    have hi : ((m : ℂ) + n * τ).im = n * (2 * b) := by
      simp only [add_im, intCast_im, mul_im, intCast_re, zero_mul, add_zero, zero_add]
      rw [hb_def]; ring
    rw [hi] at him'
    have hn : n = 0 := by
      have h1 : (n : ℝ) * (2 * b) ≤ b := him'.2
      have h2 : -b ≤ (n : ℝ) * (2 * b) := him'.1
      have h3 : (n : ℝ) < 1 := by nlinarith
      have h4 : (-1 : ℝ) < n := by nlinarith
      have : n < 1 := by exact_mod_cast h3
      have : -1 < n := by exact_mod_cast h4
      omega
    subst hn
    have hr : ((m : ℂ) + ((0 : ℤ) : ℂ) * τ).re = m := by simp
    rw [hr] at hre
    have hm : m = 0 := by
      have h3 : (m : ℝ) < 1 := by linarith [hre.2]
      have h4 : (-1 : ℝ) < m := by linarith [hre.1]
      have : m < 1 := by exact_mod_cast h3
      have : -1 < m := by exact_mod_cast h4
      omega
    subst hm
    simp
  
  have hline : ∀ z : ℂ, (z.im = -b ∨ z.im = b) → α * z ∉ L.lattice := by
    intro z hz hzm
    obtain ⟨m, n, rfl⟩ := hmem z hzm
    have hi : ((m : ℂ) + n * τ).im = n * (2 * b) := by
      simp only [add_im, intCast_im, mul_im, intCast_re, zero_mul, add_zero, zero_add]
      rw [hb_def]; ring
    rw [hi] at hz
    rcases hz with hz | hz
    · have : (n : ℝ) * 2 = -1 := by nlinarith
      have : n * 2 = -1 := by exact_mod_cast this
      omega
    · have : (n : ℝ) * 2 = 1 := by nlinarith
      have : n * 2 = 1 := by exact_mod_cast this
      omega
  have hfcont : ∀ z : ℂ, α * z ∉ L.lattice → ContinuousAt f z := by
    intro z hz
    have h1 : DifferentiableAt ℂ (zeta L) (α * z) :=
      (differentiableOn_zeta L _ hz).differentiableAt ((isOpen_compl_coe_lattice L).mem_nhds hz)
    have : DifferentiableAt ℂ f z := by
      simp only [hf]
      fun_prop
    exact this.continuousAt
  
  set z₀ : ℂ := ⟨-1/2, -b⟩
  set w₀ : ℂ := ⟨1/2, b⟩
  have hrect : ∀ p ∈ [[z₀.re, w₀.re]] ×ℂ [[z₀.im, w₀.im]],
      p.re ∈ Icc (-1/2 : ℝ) (1/2) ∧ p.im ∈ Icc (-b) b := by
    intro p hp
    rw [mem_reProdIm] at hp
    simp only [z₀, w₀] at hp
    rw [uIcc_of_le (by norm_num), uIcc_of_le (by linarith)] at hp
    exact hp
  have hGd : ∀ p ∈ [[z₀.re, w₀.re]] ×ℂ [[z₀.im, w₀.im]], DifferentiableAt ℂ G p := by
    intro p hp
    obtain ⟨h1, h2⟩ := hrect p hp
    have hz : α * p ∉ L.lattice ∨ α * p = 0 := by
      by_cases h : α * p ∈ L.lattice
      · right; rw [hpole p h1 h2 h, mul_zero]
      · left; exact h
    have := differentiableAt_zetaExcept_zero L hz
    simp only [hG]
    fun_prop
  have hGzero : rectIntegral G z₀ w₀ = 0 :=
    rectIntegral_eq_zero fun p hp => (hGd p hp).differentiableWithinAt
  
  have hinv : rectIntegral (fun z => z⁻¹) z₀ w₀ = 2 * π * I := by
    have := rectIntegral_inv (a := 1/2) (b := b) (by norm_num) hb
    convert this using 2
    simp [z₀]
    norm_num
  have hbd_ne : ∀ p ∈ [[z₀.re, w₀.re]] ×ℂ [[z₀.im, w₀.im]],
      (p.re = z₀.re ∨ p.re = w₀.re ∨ p.im = z₀.im ∨ p.im = w₀.im) → p ≠ 0 := by
    rintro p - h rfl
    simp only [zero_re, zero_im, z₀, w₀] at h
    rcases h with h | h | h | h <;> linarith
  have hsplit : rectIntegral f z₀ w₀ = 2 * π * I := by
    rw [hfG, rectIntegral_add (fun p hp _ => (hGd p hp).continuousAt)
      (fun p hp hb' => continuousAt_inv₀ (hbd_ne p hp hb')), hGzero, hinv, zero_add]
  
  have hver : (∫ y : ℝ in z₀.im..w₀.im, f (w₀.re + y * I)) =
      ∫ y : ℝ in z₀.im..w₀.im, f (z₀.re + y * I) := by
    refine integral_congr fun y _ => ?_
    rw [← hf1 ((z₀.re : ℂ) + y * I)]
    congr 1
    simp only [z₀, w₀]
    push_cast
    ring
  set g : ℝ → ℂ := fun x => f (x + z₀.im * I) with hg
  have hgper : Function.Periodic g 1 := by
    intro x
    simp only [hg]
    rw [← hf1 ((x : ℂ) + z₀.im * I)]
    congr 1
    push_cast
    ring
  have hgcont : Continuous g := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    have : ContinuousAt f ((x : ℂ) + z₀.im * I) :=
      hfcont _ (hline _ (Or.inl (by simp [z₀])))
    exact this.comp (g := f) (f := fun x : ℝ => (x : ℂ) + z₀.im * I) (by fun_prop)
  have htop : (∫ x : ℝ in z₀.re..w₀.re, f (x + w₀.im * I)) =
      (∫ x : ℝ in z₀.re..w₀.re, f (x + z₀.im * I)) + c := by
    have e : ∀ x : ℝ, f (x + w₀.im * I) = g (x - τ.re) + c := by
      intro x
      simp only [hg]
      rw [← hfτ]
      congr 1
      apply Complex.ext
      · simp [z₀, w₀, hb_def]
      · simp [z₀, w₀, hb_def]
        ring
    simp_rw [e]
    have hint : IntervalIntegrable (fun x => g (x - τ.re)) volume z₀.re w₀.re :=
      (hgcont.comp (continuous_sub_right τ.re)).intervalIntegrable _ _
    rw [integral_add hint _root_.intervalIntegrable_const, integral_comp_sub_right, intervalIntegral.integral_const]
    have hw : w₀.re - τ.re = (z₀.re - τ.re) + 1 := by simp [z₀, w₀]; ring
    have hw' : w₀.re = z₀.re + 1 := by simp [z₀, w₀]; norm_num
    rw [hw, hgper.intervalIntegral_add_eq (z₀.re - τ.re) z₀.re, ← hw']
    have h1 : w₀.re - z₀.re = 1 := by simp [z₀, w₀]; norm_num
    rw [h1, one_smul]
  have hper : rectIntegral f z₀ w₀ = -c := by
    unfold rectIntegral
    rw [hver, htop]
    ring
  rw [hper] at hsplit
  rw [hc] at hsplit
  linear_combination hsplit
lemma im_div_ne_zero : (L.ω₂ / L.ω₁).im ≠ 0 := by
  intro h
  have h1 := ω₁_ne_zero L
  set t := (L.ω₂ / L.ω₁).re
  have ht : L.ω₂ / L.ω₁ = (t : ℂ) := Complex.ext (by simp [t]) (by simp [h])
  have hω : L.ω₂ = t * L.ω₁ := by rw [← ht]; field_simp
  have := LinearIndependent.pair_iff.mp L.indep t (-1) (by
    simp only [Complex.real_smul, hω]; push_cast; ring)
  norm_num at this
 
theorem legendre_of_im_pos (h : 0 < (L.ω₂ / L.ω₁).im) :
    eta L L.ω₁ * L.ω₂ - eta L L.ω₂ * L.ω₁ = 2 * π * I :=
  legendre_of_basis L L.ω₁_mem_lattice L.ω₂_mem_lattice
    (fun l hl => by obtain ⟨m, n, h⟩ := mem_lattice.mp hl; exact ⟨m, n, h.symm⟩) h
 
theorem legendre_of_im_neg (h : (L.ω₂ / L.ω₁).im < 0) :
    eta L L.ω₁ * L.ω₂ - eta L L.ω₂ * L.ω₁ = -(2 * π * I) := by
  have h' : 0 < (L.ω₁ / L.ω₂).im := by
    have : L.ω₁ / L.ω₂ = (L.ω₂ / L.ω₁)⁻¹ := by rw [inv_div]
    rw [this, inv_im, neg_div]
    apply neg_pos.mpr
    apply div_neg_of_neg_of_pos h
    rw [normSq_pos]
    intro h0
    rw [h0] at h
    simp at h
  have := legendre_of_basis L L.ω₂_mem_lattice L.ω₁_mem_lattice
    (fun l hl => by
      obtain ⟨m, n, h⟩ := mem_lattice.mp hl
      exact ⟨n, m, by rw [← h]; ring⟩) h'
  linear_combination -this
 
theorem legendre :
    eta L L.ω₁ * L.ω₂ - eta L L.ω₂ * L.ω₁ =
      2 * π * I * (if 0 < (L.ω₂ / L.ω₁).im then 1 else -1) := by
  split_ifs with h
  · rw [mul_one]; exact legendre_of_im_pos L h
  · rw [legendre_of_im_neg L (lt_of_le_of_ne (not_lt.mp h) (im_div_ne_zero L))]
    ring
lemma legendre_ne_zero : eta L L.ω₁ * L.ω₂ - eta L L.ω₂ * L.ω₁ ≠ 0 := by
  rw [legendre]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  split_ifs <;> simp [hπ, I_ne_zero]
end LSG.Weierstrass
end
end

/- LSG.Weierstrass.Residue -/
section
open Module Filter Complex Set
open scoped Topology
noncomputable section
namespace LSG.Weierstrass
open PeriodPair
 
def LocBdd (f : ℂ → ℂ) (s : ℂ) : Prop := ∃ M : ℝ, ∀ᶠ u in 𝓝[≠] s, ‖f u‖ ≤ M
 
def Discr (S : Set ℂ) : Prop := ∀ x, ∀ᶠ y in 𝓝[≠] x, y ∉ S
section LocBdd
variable {f g : ℂ → ℂ} {s : ℂ}
lemma LocBdd.of_continuousAt (h : ContinuousAt f s) : LocBdd f s := by
  refine ⟨‖f s‖ + 1, nhdsWithin_le_nhds ?_⟩
  exact (h.norm.eventually (Iio_mem_nhds (lt_add_one _))).mono fun u hu => le_of_lt hu
lemma LocBdd.congr (h : LocBdd f s) (hfg : ∀ᶠ u in 𝓝[≠] s, f u = g u) : LocBdd g s := by
  obtain ⟨M, hM⟩ := h
  exact ⟨M, (hM.and hfg).mono fun u hu => hu.2 ▸ hu.1⟩
lemma LocBdd.sub (hf : LocBdd f s) (hg : LocBdd g s) : LocBdd (fun u => f u - g u) s := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨N, hN⟩ := hg
  exact ⟨M + N, (hM.and hN).mono fun u hu => (norm_sub_le _ _).trans (add_le_add hu.1 hu.2)⟩
lemma LocBdd.mul (hf : LocBdd f s) (hg : LocBdd g s) : LocBdd (fun u => f u * g u) s := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨N, hN⟩ := hg
  refine ⟨max M 0 * max N 0, (hM.and hN).mono fun u hu => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hu.1.trans (le_max_left _ _)) (hu.2.trans (le_max_left _ _)) (norm_nonneg _)
    (le_max_right _ _)
lemma tendsto_sub_nhdsNE (s ω : ℂ) : Tendsto (fun u => u - ω) (𝓝[≠] (s + ω)) (𝓝[≠] s) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have := (continuous_sub_right ω).tendsto (s + ω)
    simp only [add_sub_cancel_right] at this
    exact this.mono_left nhdsWithin_le_nhds
  · refine eventually_nhdsWithin_of_forall fun u hu => ?_
    simp only [mem_compl_iff, mem_singleton_iff] at hu ⊢
    intro h
    exact hu (by rw [← h]; ring)
lemma tendsto_neg_nhdsNE (s : ℂ) : Tendsto (fun u => -u) (𝓝[≠] (-s)) (𝓝[≠] s) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have := continuous_neg.tendsto (-s)
    simp only [neg_neg] at this
    exact this.mono_left nhdsWithin_le_nhds
  · refine eventually_nhdsWithin_of_forall fun u hu => ?_
    simp only [mem_compl_iff, mem_singleton_iff] at hu ⊢
    intro h
    exact hu (by rw [← h]; ring)
lemma LocBdd.of_periodic {ω : ℂ} (hper : ∀ u, f (u + ω) = f u) (h : LocBdd f s) :
    LocBdd f (s + ω) := by
  obtain ⟨M, hM⟩ := h
  refine ⟨M, ((tendsto_sub_nhdsNE s ω).eventually hM).mono fun u hu => ?_⟩
  have := hper (u - ω)
  rw [sub_add_cancel] at this
  rw [this]; exact hu
lemma LocBdd.of_even (heven : ∀ u, f (-u) = f u) (h : LocBdd f s) : LocBdd f (-s) := by
  obtain ⟨M, hM⟩ := h
  refine ⟨M, ((tendsto_neg_nhdsNE s).eventually hM).mono fun u hu => ?_⟩
  have := heven u
  rwa [this] at hu
end LocBdd
 
lemma eq_of_eventuallyEq_nhdsNE {F₁ F₂ : ℂ → ℂ} {u : ℂ} (h₁ : ContinuousAt F₁ u)
    (h₂ : ContinuousAt F₂ u) (h : ∀ᶠ v in 𝓝[≠] u, F₁ v = F₂ v) : F₁ u = F₂ u :=
  tendsto_nhds_unique ((h₁.tendsto.mono_left nhdsWithin_le_nhds).congr' h)
    (h₂.tendsto.mono_left nhdsWithin_le_nhds)
section Discr
variable (L : PeriodPair)
lemma Discr.union {S T : Set ℂ} (hS : Discr S) (hT : Discr T) : Discr (S ∪ T) := fun x =>
  ((hS x).and (hT x)).mono fun _ hy h => h.elim hy.1 hy.2
lemma Discr.eventually_nhds {S : Set ℂ} (hS : Discr S) {x : ℂ} (hx : x ∉ S) :
    ∀ᶠ y in 𝓝 x, y ∉ S := by
  have := hS x
  rw [eventually_nhdsWithin_iff] at this
  filter_upwards [this] with y hy
  by_cases h : y = x
  · rw [h]; exact hx
  · exact hy h
lemma Discr.exists_notMem {S : Set ℂ} (hS : Discr S) : ∃ u, u ∉ S := (hS 0).exists
 
lemma discr_affine {c : ℂ} (hc : c ≠ 0) (d : ℂ) : Discr {u | c * u + d ∈ L.lattice} := by
  intro x
  have h1 := L.compl_lattice_sdiff_singleton_mem_nhds (c * x + d)
  have h2 : Tendsto (fun u => c * u + d) (𝓝 x) (𝓝 (c * x + d)) :=
    ((continuous_const.mul continuous_id).add continuous_const).tendsto x
  filter_upwards [nhdsWithin_le_nhds (h2.eventually h1), self_mem_nhdsWithin] with u hu hux
  intro hmem
  apply hu
  refine ⟨hmem, fun h => hux ?_⟩
  simp only [mem_singleton_iff, add_left_inj] at h ⊢
  exact mul_left_cancel₀ hc h
lemma discr_sub (a : ℂ) : Discr {u | u - a ∈ L.lattice} := by
  have := discr_affine L one_ne_zero (-a)
  simpa [sub_eq_add_neg] using this
lemma discr_add (a : ℂ) : Discr {u | u + a ∈ L.lattice} := by
  have := discr_affine L one_ne_zero a
  simpa using this
end Discr
 

theorem exists_differentiable_extension {f : ℂ → ℂ} {S : Set ℂ} (hS : Discr S)
    (hd : ∀ x ∉ S, DifferentiableAt ℂ f x) (hb : ∀ s ∈ S, LocBdd f s) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ x ∉ S, F x = f x := by
  classical
  set F : ℂ → ℂ := fun x => if x ∈ S then limUnder (𝓝[≠] x) f else f x with hF
  refine ⟨F, fun x => ?_, fun x hx => by simp [hF, hx]⟩
  by_cases hx : x ∈ S
  · obtain ⟨M, hM⟩ := hb x hx
    have h := (hS x).and hM
    rw [eventually_nhdsWithin_iff] at h
    set U := {y | y ≠ x → y ∉ S ∧ ‖f y‖ ≤ M}
    have hU : U ∈ 𝓝 x := h
    have hdU : DifferentiableOn ℂ f (U \ {x}) := fun y hy =>
      (hd y (hy.1 hy.2).1).differentiableWithinAt
    have hbU : BddAbove (norm ∘ f '' (U \ {x})) :=
      ⟨M, by rintro _ ⟨y, hy, rfl⟩; exact (hy.1 hy.2).2⟩
    have hD := (Complex.differentiableOn_update_limUnder_of_bddAbove hU hdU hbU).differentiableAt hU
    refine hD.congr_of_eventuallyEq ?_
    filter_upwards [hU] with y hy
    by_cases hyx : y = x
    · subst hyx; simp [hF, hx]
    · simp [hF, (hy hyx).1, Function.update_of_ne hyx]
  · refine (hd x hx).congr_of_eventuallyEq ?_
    filter_upwards [hS.eventually_nhds hx] with y hy
    simp [hF, hy]
variable (L : PeriodPair)
 
theorem eq_linear_of_add_sub_const {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (h : ∀ ω ∈ L.lattice, ∃ c, ∀ u, F (u + ω) = F u + c) :
    ∃ α β : ℂ, ∀ u, F u = α * u + β := by
  have hd : Differentiable ℂ (deriv F) := hF.deriv
  have hper : ∀ u ω, ω ∈ L.lattice → deriv F (u + ω) = deriv F u := by
    intro u ω hω
    obtain ⟨c, hc⟩ := h ω hω
    have e : (fun v => F (v + ω)) = fun v => F v + c := funext hc
    have h1 : deriv (fun v => F (v + ω)) u = deriv F (u + ω) := deriv_comp_add_const F ω u
    rw [← h1, e, deriv_add_const]
  have hc := IsZLattice.isCompact_range_of_periodic L.lattice _ hd.continuous
    (fun z w hw => hper z w hw)
  set α := deriv F 0
  have hconst : ∀ u, deriv F u = α := fun u => hd.apply_eq_apply_of_bounded hc.isBounded u 0
  refine ⟨α, F 0, fun u => ?_⟩
  have hG : Differentiable ℂ (fun v => F v - α * v) := hF.sub (differentiable_id.const_mul α)
  have hG' : ∀ v, deriv (fun v => F v - α * v) v = 0 := by
    intro v
    have : HasDerivAt (fun v => F v - α * v) (deriv F v - α * 1) v :=
      (hF v).hasDerivAt.sub ((hasDerivAt_id' v).const_mul α)
    rw [this.deriv, hconst v]
    ring
  have := is_const_of_deriv_eq_zero hG hG' u 0
  simp only [mul_zero, sub_zero] at this
  linear_combination this
 

theorem eq_const_of_simple_pole {f : ℂ → ℂ} {S : Set ℂ} (a : ℂ) (hS : Discr S)
    (hSinv : ∀ u ∈ S, ∀ ω ∈ L.lattice, u + ω ∈ S)
    (hper : ∀ u ∉ S, ∀ ω ∈ L.lattice, f (u + ω) = f u)
    (hd : ∀ x ∉ S, DifferentiableAt ℂ f x)
    (hb : ∀ s ∈ S, s - a ∉ L.lattice → LocBdd f s)
    (ha : LocBdd (fun u => (u - a) * f u) a) :
    ∃ C, ∀ u ∉ S, f u = C := by
  set A : Set ℂ := {u | u - a ∈ L.lattice} with hA_def
  set S' := S ∪ A with hS'_def
  have hS' : Discr S' := hS.union (discr_sub L a)
  have hS'inv : ∀ u ∉ S', ∀ ω ∈ L.lattice, u + ω ∉ S' := by
    intro u hu ω hω h
    apply hu
    rcases h with h | h
    · left
      have := hSinv _ h (-ω) (neg_mem hω)
      rwa [add_neg_cancel_right] at this
    · right
      change u + ω - a ∈ L.lattice at h
      change u - a ∈ L.lattice
      have := sub_mem h hω
      rwa [show u + ω - a - ω = u - a by ring] at this
  
  set h : ℂ → ℂ := fun u => (u - a) * f u with hh_def
  obtain ⟨M, hM⟩ := ha
  have hh := (hS a).and hM
  rw [eventually_nhdsWithin_iff] at hh
  set U := {y | y ≠ a → y ∉ S ∧ ‖h y‖ ≤ M}
  have hU : U ∈ 𝓝 a := hh
  have hdU : DifferentiableOn ℂ h (U \ {a}) := fun y hy =>
    ((differentiableAt_id.sub_const a).mul (hd y (hy.1 hy.2).1)).differentiableWithinAt
  have hbU : BddAbove (norm ∘ h '' (U \ {a})) :=
    ⟨M, by rintro _ ⟨y, hy, rfl⟩; exact (hy.1 hy.2).2⟩
  set r := limUnder (𝓝[≠] a) h
  set H := Function.update h a r with hH_def
  have hH : DifferentiableAt ℂ H a :=
    (Complex.differentiableOn_update_limUnder_of_bddAbove hU hdU hbU).differentiableAt hU
  have hdsl : ContinuousAt (dslope H a) a := continuousAt_dslope_same.mpr hH
  have hloc : ∀ u, u ≠ a → f u - r * (u - a)⁻¹ = dslope H a u := by
    intro u hu
    have hu' : u - a ≠ 0 := sub_ne_zero.mpr hu
    rw [dslope_of_ne _ hu, slope_def_field]
    simp only [hH_def, Function.update_of_ne hu, Function.update_self, hh_def]
    field_simp
  
  set g : ℂ → ℂ := fun u => f u - r * zeta L (u - a) with hg_def
  have hzc : ∀ x, x - a ∉ L.lattice → DifferentiableAt ℂ (fun u => zeta L (u - a)) x := by
    intro x hx
    have := (differentiableOn_zeta L _ hx).differentiableAt
      ((isOpen_compl_coe_lattice L).mem_nhds hx)
    exact this.comp x (differentiableAt_id.sub_const a)
  have hgd : ∀ x ∉ S', DifferentiableAt ℂ g x := by
    intro x hx
    have h1 : x ∉ S := fun h => hx (Or.inl h)
    have h2 : x - a ∉ L.lattice := fun h => hx (Or.inr h)
    exact (hd x h1).sub ((hzc x h2).const_mul r)
  have hgper : ∀ u ∉ S', ∀ ω ∈ L.lattice, g (u + ω) = g u + -(r * eta L ω) := by
    intro u hu ω hω
    have h1 : u ∉ S := fun h => hu (Or.inl h)
    simp only [hg_def]
    rw [hper u h1 ω hω, show u + ω - a = (u - a) + ω by ring, zeta_add L hω]
    ring
  have hga : LocBdd g a := by
    have hc : ContinuousAt (fun u => dslope H a u - r * zetaExcept L 0 (u - a)) a := by
      have h1 : ContinuousAt (fun u => zetaExcept L 0 (u - a)) a := by
        have := (differentiableAt_zetaExcept_zero L (w := a - a) (Or.inr (sub_self a))).continuousAt
        exact this.comp (f := fun u => u - a) (continuousAt_id.sub continuousAt_const)
      exact hdsl.sub (continuousAt_const.mul h1)
    refine (LocBdd.of_continuousAt hc).congr ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    rw [← hloc u hu]
    simp only [hg_def]
    rw [zeta_eq_zetaExcept_zero_add]
    ring
  have hgb : ∀ s ∈ S', LocBdd g s := by
    intro s hs
    by_cases hsa : s - a ∈ L.lattice
    · obtain ⟨M', hM'⟩ := hga
      refine ⟨M' + ‖r * eta L (s - a)‖, ?_⟩
      have h1 := (tendsto_sub_nhdsNE a (s - a)).eventually (hM'.and (hS' a))
      rw [show a + (s - a) = s by ring] at h1
      filter_upwards [h1] with u hu
      have := hgper (u - (s - a)) hu.2 (s - a) hsa
      rw [sub_add_cancel] at this
      rw [this]
      exact (norm_add_le _ _).trans (by rw [norm_neg]; linarith [hu.1])
    · have hsS : s ∈ S := hs.resolve_right hsa
      exact (hb s hsS hsa).sub
        (LocBdd.of_continuousAt (continuousAt_const.mul (hzc s hsa).continuousAt))
  obtain ⟨G, hGd, hGg⟩ := exists_differentiable_extension hS' hgd hgb
  have hGper : ∀ ω ∈ L.lattice, ∃ c, ∀ u, G (u + ω) = G u + c := by
    intro ω hω
    refine ⟨-(r * eta L ω), fun u => ?_⟩
    refine eq_of_eventuallyEq_nhdsNE (F₁ := fun u => G (u + ω)) (F₂ := fun u => G u + -(r * eta L ω))
      ((hGd _).continuousAt.comp (continuousAt_id.add continuousAt_const))
      ((hGd u).continuousAt.add continuousAt_const) ?_
    filter_upwards [hS' u] with v hv
    rw [hGg _ (hS'inv v hv ω hω), hGg v hv, hgper v hv ω hω]
  obtain ⟨α, β, hαβ⟩ := eq_linear_of_add_sub_const L hGd hGper
  obtain ⟨u₀, hu₀⟩ := hS'.exists_notMem
  have hαω : ∀ ω ∈ L.lattice, α * ω = -(r * eta L ω) := by
    intro ω hω
    have h1 := hgper u₀ hu₀ ω hω
    rw [← hGg _ (hS'inv u₀ hu₀ ω hω), ← hGg u₀ hu₀, hαβ, hαβ] at h1
    linear_combination h1
  have hr : r = 0 := by
    have h1 := hαω _ L.ω₁_mem_lattice
    have h2 := hαω _ L.ω₂_mem_lattice
    have hl := legendre_ne_zero L
    have : r * (eta L L.ω₁ * L.ω₂ - eta L L.ω₂ * L.ω₁) = 0 := by
      linear_combination L.ω₂ * h1 - L.ω₁ * h2
    exact (mul_eq_zero.mp this).resolve_right hl
  have hα : α = 0 := by
    have h1 := hαω _ L.ω₁_mem_lattice
    rw [hr, zero_mul, neg_zero] at h1
    exact (mul_eq_zero.mp h1).resolve_right (ω₁_ne_zero L)
  have hfG : ∀ v ∉ S', f v = β := by
    intro v hv
    have := hGg v hv
    rw [hαβ, hα, zero_mul, zero_add] at this
    simp only [hg_def, hr, zero_mul, sub_zero] at this
    exact this.symm
  refine ⟨β, fun u hu => ?_⟩
  by_cases hua : u - a ∈ L.lattice
  · refine eq_of_eventuallyEq_nhdsNE (F₂ := fun _ => β) (hd u hu).continuousAt continuousAt_const ?_
    filter_upwards [hS' u] with v hv
    exact hfG v hv
  · exact hfG u (fun h => h.elim hu hua)
end LSG.Weierstrass
end
end

/- LSG.Weierstrass.SigmaSign -/
section
open Module Filter Complex
open scoped Topology
noncomputable section
namespace LSG.Weierstrass
open PeriodPair
variable (L : PeriodPair)
open scoped Classical in
 
def sigmaSign (ω : ℂ) : ℂ := if ω / 2 ∈ L.lattice then 1 else -1
lemma sigmaSign_sq (ω : ℂ) : sigmaSign L ω ^ 2 = 1 := by
  unfold sigmaSign; split_ifs <;> norm_num
lemma sigmaSign_ne_zero (ω : ℂ) : sigmaSign L ω ≠ 0 := by
  unfold sigmaSign; split_ifs <;> norm_num
lemma sigmaSign_of_half_notMem {ω : ℂ} (h : ω / 2 ∉ L.lattice) : sigmaSign L ω = -1 := by
  simp [sigmaSign, h]
lemma sigmaSign_of_half_mem {ω : ℂ} (h : ω / 2 ∈ L.lattice) : sigmaSign L ω = 1 := by
  simp [sigmaSign, h]
 
lemma sigma_add_two_mul {ω' : ℂ} (hω' : ω' ∈ L.lattice)
    (ih : ∀ z, sigma L (z + ω') = sigmaSign L ω' * exp (eta L ω' * (z + ω' / 2)) * sigma L z)
    (z : ℂ) :
    sigma L (z + 2 * ω') = sigmaSign L (2 * ω') * exp (eta L (2 * ω') * (z + 2 * ω' / 2)) *
      sigma L z := by
  have h2 : (2 * ω') / 2 ∈ L.lattice := by simpa using hω'
  rw [sigmaSign_of_half_mem L h2, two_mul ω', eta_add L hω' hω',
    show z + (ω' + ω') = (z + ω') + ω' by ring, ih, ih]
  have hs := sigmaSign_sq L ω'
  have e : exp (eta L ω' * (z + ω' + ω' / 2)) * exp (eta L ω' * (z + ω' / 2)) =
      exp ((eta L ω' + eta L ω') * (z + (ω' + ω') / 2)) := by
    rw [← exp_add]; ring_nf
  linear_combination (exp (eta L ω' * (z + ω' + ω' / 2)) * exp (eta L ω' * (z + ω' / 2)) *
    sigma L z) * hs + sigma L z * e
 

theorem sigma_add {ω : ℂ} (hω : ω ∈ L.lattice) (z : ℂ) :
    sigma L (z + ω) = sigmaSign L ω * exp (eta L ω * (z + ω / 2)) * sigma L z := by
  obtain ⟨m, n, rfl⟩ := mem_lattice.mp hω
  revert z
  induction h : m.natAbs + n.natAbs using Nat.strong_induction_on generalizing m n with
  | _ N ih =>
  intro z
  by_cases h2 : ((m : ℂ) * L.ω₁ + n * L.ω₂) / 2 ∈ L.lattice
  · obtain ⟨m', n', hmn⟩ := mem_lattice.mp h2
    
    have hind := LinearIndependent.pair_iff.mp L.indep ((2 * m' - m : ℤ) : ℝ)
      ((2 * n' - n : ℤ) : ℝ) (by
        simp only [Complex.real_smul]
        push_cast
        linear_combination 2 * hmn)
    have hm : 2 * m' = m := by have := Int.cast_eq_zero.mp hind.1; omega
    have hn : 2 * n' = n := by have := Int.cast_eq_zero.mp hind.2; omega
    by_cases h0 : N = 0
    · have hm0 : m = 0 := by omega
      have hn0 : n = 0 := by omega
      subst hm0 hn0
      simp [sigmaSign]
    · have hlt : m'.natAbs + n'.natAbs < N := by omega
      have ih' := ih _ hlt m' n' (by rw [hmn]; exact h2) rfl
      have e : (m : ℂ) * L.ω₁ + n * L.ω₂ = 2 * ((m' : ℂ) * L.ω₁ + n' * L.ω₂) := by
        rw [← hm, ← hn]; push_cast; ring
      rw [e]
      exact sigma_add_two_mul L (by rw [hmn]; exact h2) ih' z
  · rw [sigmaSign_of_half_notMem L h2, sigma_add_of_half_notMem L hω h2 z]
    ring
end LSG.Weierstrass
end
end

/- LSG.Weierstrass.Degree -/
section
open Module Filter Complex Set
open scoped Topology
noncomputable section
namespace LSG.Weierstrass
open PeriodPair
variable (L : PeriodPair)
lemma sigma_eq_mul_sigmaProd (u : ℂ) : sigma L u = u * sigmaProd L u := rfl
lemma continuous_sigma : Continuous (sigma L) := (differentiable_sigma L).continuous
lemma continuous_sigmaProd : Continuous (sigmaProd L) := (differentiable_sigmaProd L).continuous
lemma differentiableAt_weierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    DifferentiableAt ℂ ℘[L] z :=
  L.differentiableOn_weierstrassP.differentiableAt ((isOpen_compl_lattice L).mem_nhds hz)
lemma continuousAt_weierstrassP {z : ℂ} (hz : z ∉ L.lattice) : ContinuousAt ℘[L] z :=
  (differentiableAt_weierstrassP L hz).continuousAt
lemma continuousAt_derivWeierstrassP {z : ℂ} (hz : z ∉ L.lattice) : ContinuousAt ℘'[L] z :=
  (differentiableAt_derivWeierstrassP L hz).continuousAt
lemma weierstrassP_add_mem (u : ℂ) {ω : ℂ} (hω : ω ∈ L.lattice) : ℘[L] (u + ω) = ℘[L] u :=
  L.weierstrassP_add_coe u ⟨ω, hω⟩
lemma derivWeierstrassP_add_mem (u : ℂ) {ω : ℂ} (hω : ω ∈ L.lattice) :
    ℘'[L] (u + ω) = ℘'[L] u :=
  L.derivWeierstrassP_add_coe u ⟨ω, hω⟩
 
lemma weierstrassP_eq_except_zero (u : ℂ) : ℘[L] u = L.weierstrassPExcept 0 u + 1 / u ^ 2 := by
  have := L.weierstrassPExcept_add ⟨0, L.lattice.zero_mem⟩ u
  simp only [sub_zero, div_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    sub_zero] at this
  rw [← this]
 
lemma derivWeierstrassP_eq_except_zero (u : ℂ) : ℘'[L] u = L.derivWeierstrassPExcept 0 u - 2 / u ^ 3 := by
  have := L.derivWeierstrassPExcept_def ⟨0, L.lattice.zero_mem⟩ u
  simp only [sub_zero] at this
  rw [this]
  ring
lemma continuousAt_weierstrassPExcept_zero : ContinuousAt (L.weierstrassPExcept 0) 0 :=
  (L.analyticAt_weierstrassPExcept 0).continuousAt
lemma continuousAt_derivWeierstrassPExcept_zero : ContinuousAt (L.derivWeierstrassPExcept 0) 0 :=
  (L.analyticAt_derivWeierstrassPExcept 0).continuousAt
 
lemma sigma_add' {ω : ℂ} (hω : ω ∈ L.lattice) (u : ℂ) :
    sigma L (u + ω) = (sigmaSign L ω * exp (eta L ω * (u + ω / 2))) * sigma L u :=
  sigma_add L hω u
lemma sigmaSign_mul_exp_ne_zero (ω v : ℂ) : sigmaSign L ω * exp v ≠ 0 :=
  mul_ne_zero (sigmaSign_ne_zero L ω) (exp_ne_zero v)
lemma exp_mul_exp_eq {e a b c : ℂ} (h : a + b = 2 * c) :
    exp (e * a) * exp (e * b) = exp (e * c) * exp (e * c) := by
  rw [← exp_add, ← exp_add]
  congr 1
  linear_combination e * h
 
lemma dslope_eq_div {f : ℂ → ℂ} {a u : ℂ} (hu : u ≠ a) :
    dslope f a u = (f u - f a) / (u - a) := by
  rw [dslope_of_ne _ hu, slope_def_field]
 
def degF (z u : ℂ) : ℂ :=
  (℘[L] u - ℘[L] z) * sigma L u ^ 2 / (sigma L (u - z) * sigma L (u + z))
lemma degF_add (z : ℂ) {ω : ℂ} (hω : ω ∈ L.lattice) (u : ℂ) :
    degF L z (u + ω) = degF L z u := by
  unfold degF
  rw [weierstrassP_add_mem L u hω, sigma_add' L hω u, show u + ω - z = (u - z) + ω by ring,
    sigma_add' L hω (u - z), show u + ω + z = (u + z) + ω by ring, sigma_add' L hω (u + z)]
  set s := sigmaSign L ω
  set e := eta L ω
  have hE := exp_mul_exp_eq (e := e) (a := u - z + ω / 2) (b := u + z + ω / 2) (c := u + ω / 2)
    (by ring)
  have hK : s * s * (exp (e * (u + ω / 2)) * exp (e * (u + ω / 2))) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (sigmaSign_ne_zero L ω) (sigmaSign_ne_zero L ω))
      (mul_ne_zero (exp_ne_zero _) (exp_ne_zero _))
  rw [show s * exp (e * (u - z + ω / 2)) * sigma L (u - z) *
      (s * exp (e * (u + z + ω / 2)) * sigma L (u + z)) =
      sigma L (u - z) * sigma L (u + z) *
        (s * s * (exp (e * (u - z + ω / 2)) * exp (e * (u + z + ω / 2)))) by ring, hE,
    show (℘[L] u - ℘[L] z) * (s * exp (e * (u + ω / 2)) * sigma L u) ^ 2 =
      (℘[L] u - ℘[L] z) * sigma L u ^ 2 *
        (s * s * (exp (e * (u + ω / 2)) * exp (e * (u + ω / 2)))) by ring,
    mul_div_mul_right _ _ hK]
lemma degF_neg (z u : ℂ) : degF L z (-u) = degF L z u := by
  unfold degF
  rw [weierstrassP_neg, sigma_neg, show -u - z = -(u + z) by ring, sigma_neg,
    show -u + z = -(u - z) by ring, sigma_neg]
  ring
 
def degS (z : ℂ) : Set ℂ := {u | u ∈ L.lattice ∨ u - z ∈ L.lattice ∨ u + z ∈ L.lattice}
lemma discr_degS (z : ℂ) : Discr (degS L z) := by
  have h := ((discr_add L 0).union (discr_sub L z)).union (discr_add L z)
  convert h using 1
  ext u
  simp [degS, or_assoc]
lemma degS_add {z u ω : ℂ} (hu : u ∈ degS L z) (hω : ω ∈ L.lattice) : u + ω ∈ degS L z := by
  rcases hu with h | h | h
  · exact Or.inl (add_mem h hω)
  · right; left
    rw [show u + ω - z = (u - z) + ω by ring]; exact add_mem h hω
  · right; right
    rw [show u + ω + z = (u + z) + ω by ring]; exact add_mem h hω
lemma differentiableAt_degF {z x : ℂ} (hx : x ∉ degS L z) : DifferentiableAt ℂ (degF L z) x := by
  have h0 : x ∉ L.lattice := fun h => hx (Or.inl h)
  have h1 : x - z ∉ L.lattice := fun h => hx (Or.inr (Or.inl h))
  have h2 : x + z ∉ L.lattice := fun h => hx (Or.inr (Or.inr h))
  have hP := differentiableAt_weierstrassP L h0
  have hs := differentiable_sigma L
  unfold degF
  refine DifferentiableAt.div ?_ ?_ (mul_ne_zero (sigma_ne_zero L h1) (sigma_ne_zero L h2))
  · exact (hP.sub_const _).mul ((hs x).pow 2)
  · exact ((hs _).comp x (differentiableAt_id.sub_const z)).mul
      ((hs _).comp x (differentiableAt_id.add_const z))
 
lemma locBdd_degF_zero {z : ℂ} (hz : z ∉ L.lattice) : LocBdd (degF L z) 0 := by
  have hz' : -z ∉ L.lattice := fun h => hz (by simpa using neg_mem h)
  set g : ℂ → ℂ := fun u => (1 + u ^ 2 * L.weierstrassPExcept 0 u - u ^ 2 * ℘[L] z) * sigmaProd L u ^ 2 /
    (sigma L (u - z) * sigma L (u + z))
  have hc : ContinuousAt g 0 := by
    refine ContinuousAt.div ?_ ?_ ?_
    · exact ((continuousAt_const.add ((continuousAt_id.pow 2).mul
        (continuousAt_weierstrassPExcept_zero L))).sub ((continuousAt_id.pow 2).mul
        continuousAt_const)).mul ((continuous_sigmaProd L).continuousAt.pow 2)
    · exact ((continuous_sigma L).continuousAt.comp (continuousAt_id.sub continuousAt_const)).mul
        ((continuous_sigma L).continuousAt.comp (continuousAt_id.add continuousAt_const))
    · simp only [zero_sub, zero_add]
      exact mul_ne_zero (sigma_ne_zero L hz') (sigma_ne_zero L hz)
  refine (LocBdd.of_continuousAt hc).congr ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu' : u ≠ 0 := hu
  simp only [g, degF, sigma_eq_mul_sigmaProd L u, weierstrassP_eq_except_zero L u]
  congr 1
  field_simp
  ring
 
lemma locBdd_degF_self {z : ℂ} (hz : z ∉ L.lattice) (h2 : 2 * z ∉ L.lattice) :
    LocBdd (degF L z) z := by
  set g : ℂ → ℂ := fun u => dslope ℘[L] z u * sigma L u ^ 2 /
    (sigmaProd L (u - z) * sigma L (u + z))
  have hc : ContinuousAt g z := by
    refine ContinuousAt.div ?_ ?_ ?_
    · exact (continuousAt_dslope_same.mpr (differentiableAt_weierstrassP L hz)).mul
        ((continuous_sigma L).continuousAt.pow 2)
    · exact ((continuous_sigmaProd L).continuousAt.comp (continuousAt_id.sub continuousAt_const)).mul
        ((continuous_sigma L).continuousAt.comp (continuousAt_id.add continuousAt_const))
    · simp only [sub_self, sigmaProd_zero, one_mul]
      exact sigma_ne_zero L (by rwa [← two_mul])
  refine (LocBdd.of_continuousAt hc).congr ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu' : u - z ≠ 0 := sub_ne_zero.mpr hu
  simp only [g, degF, dslope_eq_div hu, sigma_eq_mul_sigmaProd L (u - z)]
  field_simp
 
lemma locBdd_mul_degF_self_of_two_mul_mem {z : ℂ} (hz : z ∉ L.lattice) (h2 : 2 * z ∈ L.lattice) :
    LocBdd (fun u => (u - z) * degF L z u) z := by
  set s := sigmaSign L (2 * z)
  set e := eta L (2 * z)
  set g : ℂ → ℂ := fun u => dslope ℘[L] z u * sigma L u ^ 2 /
    (sigmaProd L (u - z) ^ 2 * (s * exp (e * u)))
  have hc : ContinuousAt g z := by
    refine ContinuousAt.div ?_ ?_ ?_
    · exact (continuousAt_dslope_same.mpr (differentiableAt_weierstrassP L hz)).mul
        ((continuous_sigma L).continuousAt.pow 2)
    · exact (((continuous_sigmaProd L).continuousAt.comp
        (continuousAt_id.sub continuousAt_const)).pow 2).mul (by fun_prop)
    · simp only [sub_self, sigmaProd_zero, one_pow, one_mul]
      exact sigmaSign_mul_exp_ne_zero L _ _
  refine (LocBdd.of_continuousAt hc).congr ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu' : u - z ≠ 0 := sub_ne_zero.mpr hu
  have hσ : sigma L (u + z) = s * exp (e * u) * sigma L (u - z) := by
    have := sigma_add L h2 (u - z)
    rw [show u - z + 2 * z = u + z by ring, show u - z + 2 * z / 2 = u by ring] at this
    exact this
  have hne := sigmaSign_mul_exp_ne_zero L (2 * z) (e * u)
  simp only [g, degF, dslope_eq_div hu, hσ, sigma_eq_mul_sigmaProd L (u - z)]
  field_simp
 

theorem sigma_identity {z : ℂ} (hz : z ∉ L.lattice) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ u ∉ L.lattice,
      (℘[L] u - ℘[L] z) * sigma L u ^ 2 = C * (sigma L (u - z) * sigma L (u + z)) := by
  have hb : ∀ s ∈ degS L z, s - z ∉ L.lattice → LocBdd (degF L z) s := by
    intro s hs hsz
    rcases hs with h | h | h
    · have := (locBdd_degF_zero L hz).of_periodic (ω := s) (fun u => degF_add L z h u)
      rwa [zero_add] at this
    · exact absurd h hsz
    · have h2 : 2 * z ∉ L.lattice := by
        intro h2
        apply hsz
        have := sub_mem h h2
        rwa [show s + z - 2 * z = s - z by ring] at this
      have h1 := ((locBdd_degF_self L hz h2).of_even (degF_neg L z)).of_periodic (ω := s + z)
        (fun u => degF_add L z h u)
      rwa [show -z + (s + z) = s by ring] at h1
  have ha : LocBdd (fun u => (u - z) * degF L z u) z := by
    by_cases h2 : 2 * z ∈ L.lattice
    · exact locBdd_mul_degF_self_of_two_mul_mem L hz h2
    · exact (LocBdd.of_continuousAt (f := fun u => u - z) (by fun_prop)).mul
        (locBdd_degF_self L hz h2)
  obtain ⟨C, hC⟩ := eq_const_of_simple_pole L z (discr_degS L z)
    (fun u hu ω hω => degS_add L hu hω) (fun u _ ω hω => degF_add L z hω u)
    (fun x hx => differentiableAt_degF L hx) hb ha
  have key : ∀ u ∉ L.lattice,
      (℘[L] u - ℘[L] z) * sigma L u ^ 2 = C * (sigma L (u - z) * sigma L (u + z)) := by
    intro u hu
    by_cases hS : u ∈ degS L z
    · rcases hS with h | h | h
      · exact absurd h hu
      · have hP : ℘[L] u = ℘[L] z := by
          have := weierstrassP_add_mem L z h
          rwa [show z + (u - z) = u by ring] at this
        rw [hP, (sigma_eq_zero_iff L).mpr h]
        ring
      · have hP : ℘[L] u = ℘[L] z := by
          have := weierstrassP_add_mem L (-z) h
          rwa [show -z + (u + z) = u by ring, weierstrassP_neg] at this
        rw [hP, (sigma_eq_zero_iff L).mpr h]
        ring
    · have h1 : u - z ∉ L.lattice := fun h => hS (Or.inr (Or.inl h))
      have h2 : u + z ∉ L.lattice := fun h => hS (Or.inr (Or.inr h))
      have := hC u hS
      unfold degF at this
      rw [div_eq_iff (mul_ne_zero (sigma_ne_zero L h1) (sigma_ne_zero L h2))] at this
      exact this
  refine ⟨C, fun hC0 => ?_, key⟩
  obtain ⟨u, hu, hM⟩ := exists_norm_weierstrassP_gt L ‖℘[L] z‖
  have := key u hu
  rw [hC0, zero_mul, mul_eq_zero] at this
  rcases this with h | h
  · rw [sub_eq_zero.mp h] at hM
    exact lt_irrefl _ hM
  · exact sigma_ne_zero L hu (pow_eq_zero_iff (by norm_num) |>.mp h)
 
theorem weierstrassP_eq_iff {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice) :
    ℘[L] w = ℘[L] z ↔ w - z ∈ L.lattice ∨ w + z ∈ L.lattice := by
  constructor
  · intro h
    obtain ⟨C, hC, key⟩ := sigma_identity L hz
    have := key w hw
    rw [h, sub_self, zero_mul, eq_comm, mul_eq_zero, mul_eq_zero] at this
    rcases this with h0 | h0 | h0
    · exact absurd h0 hC
    · exact Or.inl ((sigma_eq_zero_iff L).mp h0)
    · exact Or.inr ((sigma_eq_zero_iff L).mp h0)
  · rintro (h | h)
    · have := weierstrassP_add_mem L z h
      rwa [show z + (w - z) = w by ring] at this
    · have := weierstrassP_add_mem L (-z) h
      rwa [show -z + (w + z) = w by ring, weierstrassP_neg] at this
 
theorem derivWeierstrassP_eq_zero_iff {z : ℂ} (hz : z ∉ L.lattice) :
    ℘'[L] z = 0 ↔ 2 * z ∈ L.lattice := by
  constructor
  · intro h
    obtain ⟨C, hC, key⟩ := sigma_identity L hz
    have hs := differentiable_sigma L
    have hL : HasDerivAt (fun u => (℘[L] u - ℘[L] z) * sigma L u ^ 2)
        (℘'[L] z * sigma L z ^ 2 + (℘[L] z - ℘[L] z) * (2 * sigma L z ^ 1 * deriv (sigma L) z))
        z := by
      have := ((hasDerivAt_weierstrassP L hz).sub_const (℘[L] z)).mul ((hs z).hasDerivAt.pow 2)
      simpa only [Pi.pow_apply, Pi.mul_apply, sub_self, zero_mul, add_zero] using! this
    have hR : HasDerivAt (fun u => C * (sigma L (u - z) * sigma L (u + z)))
        (C * (deriv (sigma L) (z - z) * 1 * sigma L (z + z) +
          sigma L (z - z) * (deriv (sigma L) (z + z) * 1))) z := by
      have h1 : HasDerivAt (fun u => sigma L (u - z)) (deriv (sigma L) (z - z) * 1) z :=
        (hs (z - z)).hasDerivAt.comp (h := fun u => u - z) z ((hasDerivAt_id' z).sub_const z)
      have h2 : HasDerivAt (fun u => sigma L (u + z)) (deriv (sigma L) (z + z) * 1) z :=
        (hs (z + z)).hasDerivAt.comp (h := fun u => u + z) z ((hasDerivAt_id' z).add_const z)
      exact (h1.mul h2).const_mul C
    have heq : (fun u => (℘[L] u - ℘[L] z) * sigma L u ^ 2) =ᶠ[𝓝 z]
        fun u => C * (sigma L (u - z) * sigma L (u + z)) := by
      filter_upwards [(isOpen_compl_lattice L).mem_nhds hz] with u hu
      exact key u hu
    have := hL.unique (hR.congr_of_eventuallyEq heq)
    rw [h, sub_self, sub_self, deriv_sigma_zero, sigma_zero] at this
    simp only [zero_mul, add_zero, mul_one, one_mul] at this
    have h0 : sigma L (z + z) = 0 := by
      rcases mul_eq_zero.mp this.symm with h' | h'
      · exact absurd h' hC
      · exact h'
    rw [← two_mul] at h0
    exact (sigma_eq_zero_iff L).mp h0
  · intro h
    have := derivWeierstrassP_half L h
    rwa [mul_div_cancel_left₀ _ two_ne_zero] at this
end LSG.Weierstrass
end
end

/- LSG.Weierstrass.Addition -/
section
open Module Filter Complex Set
open scoped Topology
noncomputable section
namespace LSG.Weierstrass
open PeriodPair
variable (L : PeriodPair)
 
lemma vieta_three {a b c x₁ x₂ x₃ : ℂ} (h₁ : 4 * x₁ ^ 3 + a * x₁ ^ 2 + b * x₁ + c = 0)
    (h₂ : 4 * x₂ ^ 3 + a * x₂ ^ 2 + b * x₂ + c = 0) (h₃ : 4 * x₃ ^ 3 + a * x₃ ^ 2 + b * x₃ + c = 0)
    (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃) : x₁ + x₂ + x₃ = -a / 4 := by
  have q12 : 4 * (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2) + a * (x₁ + x₂) + b = 0 := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr h12)
    linear_combination h₁ - h₂
  have q13 : 4 * (x₁ ^ 2 + x₁ * x₃ + x₃ ^ 2) + a * (x₁ + x₃) + b = 0 := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr h13)
    linear_combination h₁ - h₃
  have : 4 * (x₁ + x₂ + x₃) + a = 0 := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr h23)
    linear_combination q12 - q13
  linear_combination this / 4
section Generic
variable {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice) (hzw : z + w ∉ L.lattice)
  (hd : z - w ∉ L.lattice) (h1 : 2 * z + w ∉ L.lattice) (h2 : z + 2 * w ∉ L.lattice)
 
def chordSlope (z w : ℂ) : ℂ := (℘'[L] z - ℘'[L] w) / (℘[L] z - ℘[L] w)
 
def chordFun (z w t : ℂ) : ℂ :=
  ℘'[L] t - chordSlope L z w * ℘[L] t - (℘'[L] z - chordSlope L z w * ℘[L] z)
 
def addF (z w t : ℂ) : ℂ :=
  chordFun L z w t * sigma L t ^ 3 /
    (sigma L (t - z) * sigma L (t - w) * sigma L (t + (z + w)))
 
def addS (z w : ℂ) : Set ℂ :=
  {t | t ∈ L.lattice ∨ t - z ∈ L.lattice ∨ t - w ∈ L.lattice ∨ t + (z + w) ∈ L.lattice}
lemma discr_addS (z w : ℂ) : Discr (addS L z w) := by
  have h := (((discr_add L 0).union (discr_sub L z)).union (discr_sub L w)).union
    (discr_add L (z + w))
  convert h using 1
  ext u
  simp [addS, or_assoc]
lemma addS_add {t ω : ℂ} (ht : t ∈ addS L z w) (hω : ω ∈ L.lattice) : t + ω ∈ addS L z w := by
  rcases ht with h | h | h | h
  · exact Or.inl (add_mem h hω)
  · right; left; rw [show t + ω - z = (t - z) + ω by ring]; exact add_mem h hω
  · right; right; left; rw [show t + ω - w = (t - w) + ω by ring]; exact add_mem h hω
  · right; right; right; rw [show t + ω + (z + w) = (t + (z + w)) + ω by ring]; exact add_mem h hω
lemma chordFun_add (z w t : ℂ) {ω : ℂ} (hω : ω ∈ L.lattice) :
    chordFun L z w (t + ω) = chordFun L z w t := by
  unfold chordFun
  rw [weierstrassP_add_mem L t hω, derivWeierstrassP_add_mem L t hω]
lemma addF_add (z w t : ℂ) {ω : ℂ} (hω : ω ∈ L.lattice) : addF L z w (t + ω) = addF L z w t := by
  unfold addF
  rw [chordFun_add L z w t hω, sigma_add' L hω t, show t + ω - z = (t - z) + ω by ring,
    sigma_add' L hω (t - z), show t + ω - w = (t - w) + ω by ring, sigma_add' L hω (t - w),
    show t + ω + (z + w) = (t + (z + w)) + ω by ring, sigma_add' L hω (t + (z + w))]
  set s := sigmaSign L ω
  set e := eta L ω
  have hE : exp (e * (t - z + ω / 2)) * exp (e * (t - w + ω / 2)) *
      exp (e * (t + (z + w) + ω / 2)) =
      exp (e * (t + ω / 2)) * exp (e * (t + ω / 2)) * exp (e * (t + ω / 2)) := by
    simp only [← exp_add]
    congr 1
    ring
  have hK : s * s * s * (exp (e * (t + ω / 2)) * exp (e * (t + ω / 2)) *
      exp (e * (t + ω / 2))) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (sigmaSign_ne_zero L ω) (sigmaSign_ne_zero L ω))
      (sigmaSign_ne_zero L ω)) (mul_ne_zero (mul_ne_zero (exp_ne_zero _) (exp_ne_zero _))
      (exp_ne_zero _))
  rw [show s * exp (e * (t - z + ω / 2)) * sigma L (t - z) *
      (s * exp (e * (t - w + ω / 2)) * sigma L (t - w)) *
      (s * exp (e * (t + (z + w) + ω / 2)) * sigma L (t + (z + w))) =
      sigma L (t - z) * sigma L (t - w) * sigma L (t + (z + w)) *
        (s * s * s * (exp (e * (t - z + ω / 2)) * exp (e * (t - w + ω / 2)) *
          exp (e * (t + (z + w) + ω / 2)))) by ring, hE,
    show chordFun L z w t * (s * exp (e * (t + ω / 2)) * sigma L t) ^ 3 =
      chordFun L z w t * sigma L t ^ 3 * (s * s * s * (exp (e * (t + ω / 2)) *
        exp (e * (t + ω / 2)) * exp (e * (t + ω / 2)))) by ring,
    mul_div_mul_right _ _ hK]
lemma differentiableAt_chordFun {t : ℂ} (ht : t ∉ L.lattice) :
    DifferentiableAt ℂ (chordFun L z w) t := by
  unfold chordFun
  exact ((differentiableAt_derivWeierstrassP L ht).sub
    ((differentiableAt_weierstrassP L ht).const_mul _)).sub_const _
lemma differentiableAt_addF {x : ℂ} (hx : x ∉ addS L z w) : DifferentiableAt ℂ (addF L z w) x := by
  have h0 : x ∉ L.lattice := fun h => hx (Or.inl h)
  have h1 : x - z ∉ L.lattice := fun h => hx (Or.inr (Or.inl h))
  have h2 : x - w ∉ L.lattice := fun h => hx (Or.inr (Or.inr (Or.inl h)))
  have h3 : x + (z + w) ∉ L.lattice := fun h => hx (Or.inr (Or.inr (Or.inr h)))
  have hs := differentiable_sigma L
  unfold addF
  refine DifferentiableAt.div ?_ ?_
    (mul_ne_zero (mul_ne_zero (sigma_ne_zero L h1) (sigma_ne_zero L h2)) (sigma_ne_zero L h3))
  · exact (differentiableAt_chordFun L h0).mul ((hs x).pow 3)
  · exact (((hs _).comp x (differentiableAt_id.sub_const z)).mul
      ((hs _).comp x (differentiableAt_id.sub_const w))).mul
      ((hs _).comp x (differentiableAt_id.add_const (z + w)))
include hz hw hzw hd in
lemma pdiff_ne : ℘[L] z - ℘[L] w ≠ 0 := by
  intro h
  rw [sub_eq_zero, eq_comm] at h
  rcases (weierstrassP_eq_iff L hz hw).mp h with h' | h'
  · exact hd (by simpa using neg_mem h')
  · exact hzw (by rwa [add_comm] at h')
lemma chordFun_self : chordFun L z w z = 0 := by unfold chordFun; ring
include hz hw hzw hd in
lemma chordFun_right : chordFun L z w w = 0 := by
  have := pdiff_ne L hz hw hzw hd
  unfold chordFun chordSlope
  field_simp
  ring
include hz hw hzw in
lemma locBdd_addF_zero : LocBdd (addF L z w) 0 := by
  set m := chordSlope L z w
  set ν := ℘'[L] z - m * ℘[L] z
  have hz' : -z ∉ L.lattice := fun h => hz (by simpa using neg_mem h)
  have hw' : -w ∉ L.lattice := fun h => hw (by simpa using neg_mem h)
  set g : ℂ → ℂ := fun t => (t ^ 3 * L.derivWeierstrassPExcept 0 t - 2 -
      m * (t ^ 3 * L.weierstrassPExcept 0 t + t) - ν * t ^ 3) * sigmaProd L t ^ 3 /
    (sigma L (t - z) * sigma L (t - w) * sigma L (t + (z + w)))
  have hc : ContinuousAt g 0 := by
    refine ContinuousAt.div ?_ ?_ ?_
    · refine ContinuousAt.mul ?_ ((continuous_sigmaProd L).continuousAt.pow 3)
      exact ((((continuousAt_id.pow 3).mul (continuousAt_derivWeierstrassPExcept_zero L)).sub
        continuousAt_const).sub (continuousAt_const.mul (((continuousAt_id.pow 3).mul
        (continuousAt_weierstrassPExcept_zero L)).add continuousAt_id))).sub
        (continuousAt_const.mul (continuousAt_id.pow 3))
    · exact (((continuous_sigma L).continuousAt.comp (continuousAt_id.sub continuousAt_const)).mul
        ((continuous_sigma L).continuousAt.comp (continuousAt_id.sub continuousAt_const))).mul
        ((continuous_sigma L).continuousAt.comp (continuousAt_id.add continuousAt_const))
    · simp only [zero_sub, zero_add]
      exact mul_ne_zero (mul_ne_zero (sigma_ne_zero L hz') (sigma_ne_zero L hw'))
        (sigma_ne_zero L hzw)
  refine (LocBdd.of_continuousAt hc).congr ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : t ≠ 0 := ht
  simp only [g, addF, chordFun, sigma_eq_mul_sigmaProd L t, weierstrassP_eq_except_zero L t,
    derivWeierstrassP_eq_except_zero L t]
  congr 1
  field_simp
  ring
include hz hd h1 in
lemma locBdd_addF_left : LocBdd (addF L z w) z := by
  set g : ℂ → ℂ := fun t => dslope (chordFun L z w) z t * sigma L t ^ 3 /
    (sigmaProd L (t - z) * sigma L (t - w) * sigma L (t + (z + w)))
  have hc : ContinuousAt g z := by
    refine ContinuousAt.div ?_ ?_ ?_
    · exact (continuousAt_dslope_same.mpr (differentiableAt_chordFun L hz)).mul
        ((continuous_sigma L).continuousAt.pow 3)
    · exact (((continuous_sigmaProd L).continuousAt.comp
        (continuousAt_id.sub continuousAt_const)).mul
        ((continuous_sigma L).continuousAt.comp (continuousAt_id.sub continuousAt_const))).mul
        ((continuous_sigma L).continuousAt.comp (continuousAt_id.add continuousAt_const))
    · simp only [sub_self, sigmaProd_zero, one_mul]
      refine mul_ne_zero (sigma_ne_zero L hd) (sigma_ne_zero L ?_)
      rwa [show z + (z + w) = 2 * z + w by ring]
  refine (LocBdd.of_continuousAt hc).congr ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : t - z ≠ 0 := sub_ne_zero.mpr ht
  simp only [g, addF, dslope_eq_div ht, chordFun_self, sub_zero, sigma_eq_mul_sigmaProd L (t - z)]
  field_simp
include hz hw hzw hd h2 in
lemma locBdd_addF_right : LocBdd (addF L z w) w := by
  set g : ℂ → ℂ := fun t => dslope (chordFun L z w) w t * sigma L t ^ 3 /
    (sigma L (t - z) * sigmaProd L (t - w) * sigma L (t + (z + w)))
  have hd' : w - z ∉ L.lattice := fun h => hd (by simpa using neg_mem h)
  have hc : ContinuousAt g w := by
    refine ContinuousAt.div ?_ ?_ ?_
    · exact (continuousAt_dslope_same.mpr (differentiableAt_chordFun L hw)).mul
        ((continuous_sigma L).continuousAt.pow 3)
    · exact (((continuous_sigma L).continuousAt.comp
        (continuousAt_id.sub continuousAt_const)).mul
        ((continuous_sigmaProd L).continuousAt.comp (continuousAt_id.sub continuousAt_const))).mul
        ((continuous_sigma L).continuousAt.comp (continuousAt_id.add continuousAt_const))
    · simp only [sub_self, sigmaProd_zero, mul_one]
      refine mul_ne_zero (sigma_ne_zero L hd') (sigma_ne_zero L ?_)
      rwa [show w + (z + w) = z + 2 * w by ring]
  refine (LocBdd.of_continuousAt hc).congr ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : t - w ≠ 0 := sub_ne_zero.mpr ht
  simp only [g, addF, dslope_eq_div ht, chordFun_right L hz hw hzw hd, sub_zero,
    sigma_eq_mul_sigmaProd L (t - w)]
  field_simp
include hzw h1 h2 in
lemma locBdd_mul_addF_pole : LocBdd (fun t => (t - -(z + w)) * addF L z w t) (-(z + w)) := by
  have ha : -(z + w) ∉ L.lattice := fun h => hzw (by simpa using neg_mem h)
  set g : ℂ → ℂ := fun t => chordFun L z w t * sigma L t ^ 3 /
    (sigma L (t - z) * sigma L (t - w) * sigmaProd L (t + (z + w)))
  have hc : ContinuousAt g (-(z + w)) := by
    refine ContinuousAt.div ?_ ?_ ?_
    · exact (differentiableAt_chordFun L ha).continuousAt.mul
        ((continuous_sigma L).continuousAt.pow 3)
    · exact (((continuous_sigma L).continuousAt.comp
        (continuousAt_id.sub continuousAt_const)).mul
        ((continuous_sigma L).continuousAt.comp (continuousAt_id.sub continuousAt_const))).mul
        ((continuous_sigmaProd L).continuousAt.comp (continuousAt_id.add continuousAt_const))
    · simp only [neg_add_cancel, sigmaProd_zero, mul_one]
      refine mul_ne_zero (sigma_ne_zero L ?_) (sigma_ne_zero L ?_)
      · intro h; apply h1; have := neg_mem h; rwa [show -(-(z + w) - z) = 2 * z + w by ring] at this
      · intro h; apply h2; have := neg_mem h; rwa [show -(-(z + w) - w) = z + 2 * w by ring] at this
  refine (LocBdd.of_continuousAt hc).congr ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : t + (z + w) ≠ 0 := by
    intro h; apply ht; simp only [mem_singleton_iff]; linear_combination h
  simp only [g, addF, sub_neg_eq_add, sigma_eq_mul_sigmaProd L (t + (z + w))]
  field_simp
include hz hw hzw hd h1 h2 in
 
lemma chordFun_neg_add : chordFun L z w (-(z + w)) = 0 := by
  have hb : ∀ s ∈ addS L z w, s - -(z + w) ∉ L.lattice → LocBdd (addF L z w) s := by
    intro s hs hsa
    rcases hs with h | h | h | h
    · have := (locBdd_addF_zero L hz hw hzw).of_periodic (ω := s) (fun t => addF_add L z w t h)
      rwa [zero_add] at this
    · have := (locBdd_addF_left L hz hd h1).of_periodic (ω := s - z)
        (fun t => addF_add L z w t h)
      rwa [show z + (s - z) = s by ring] at this
    · have := (locBdd_addF_right L hz hw hzw hd h2).of_periodic (ω := s - w)
        (fun t => addF_add L z w t h)
      rwa [show w + (s - w) = s by ring] at this
    · exact absurd (by rwa [sub_neg_eq_add]) hsa
  obtain ⟨C, hC⟩ := eq_const_of_simple_pole L (-(z + w)) (discr_addS L z w)
    (fun u hu ω hω => addS_add L hu hω) (fun u _ ω hω => addF_add L z w u hω)
    (fun x hx => differentiableAt_addF L hx) hb (locBdd_mul_addF_pole L hzw h1 h2)
  have ha : -(z + w) ∉ L.lattice := fun h => hzw (by simpa using neg_mem h)
  have hs := continuous_sigma L
  have key := eq_of_eventuallyEq_nhdsNE
    (F₁ := fun t => C * (sigma L (t - z) * sigma L (t - w) * sigma L (t + (z + w))))
    (F₂ := fun t => chordFun L z w t * sigma L t ^ 3) (u := -(z + w)) (by fun_prop)
    ((differentiableAt_chordFun L ha).continuousAt.mul (hs.continuousAt.pow 3)) (by
      filter_upwards [discr_addS L z w (-(z + w))] with t ht
      have h1 : t - z ∉ L.lattice := fun h => ht (Or.inr (Or.inl h))
      have h2 : t - w ∉ L.lattice := fun h => ht (Or.inr (Or.inr (Or.inl h)))
      have h3 : t + (z + w) ∉ L.lattice := fun h => ht (Or.inr (Or.inr (Or.inr h)))
      have := hC t ht
      unfold addF at this
      rw [div_eq_iff (mul_ne_zero (mul_ne_zero (sigma_ne_zero L h1) (sigma_ne_zero L h2))
        (sigma_ne_zero L h3))] at this
      exact this.symm)
  simp only [neg_add_cancel, sigma_zero, mul_zero] at key
  rcases mul_eq_zero.mp key.symm with h | h
  · exact h
  · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h) (sigma_ne_zero L ha)
include hz hw hzw hd h1 h2 in
 
lemma addition_generic :
    ℘[L] (z + w) = -℘[L] z - ℘[L] w + chordSlope L z w ^ 2 / 4 ∧
      ℘'[L] (z + w) = -chordSlope L z w * (℘[L] (z + w) - ℘[L] z) - ℘'[L] z := by
  have hφ := chordFun_neg_add L hz hw hzw hd h1 h2
  have hne := pdiff_ne L hz hw hzw hd
  set m := chordSlope L z w with hm
  set ν := ℘'[L] z - m * ℘[L] z with hν
  unfold chordFun at hφ
  rw [L.derivWeierstrassP_neg, L.weierstrassP_neg] at hφ
  rw [← hm] at hφ
  set x₁ := ℘[L] z
  set x₂ := ℘[L] w
  set x₃ := ℘[L] (z + w)
  have hy₃ : ℘'[L] (z + w) = -(m * x₃ + ν) := by linear_combination -hφ
  have hy₂ : ℘'[L] w = m * x₂ + ν := by
    have : m * (x₁ - x₂) = ℘'[L] z - ℘'[L] w := by
      rw [hm]
      show (℘'[L] z - ℘'[L] w) / (℘[L] z - ℘[L] w) * (℘[L] z - ℘[L] w) = _
      exact div_mul_cancel₀ _ hne
    linear_combination this
  have c₁ := L.derivWeierstrassP_sq z hz
  have c₂ := L.derivWeierstrassP_sq w hw
  have c₃ := L.derivWeierstrassP_sq (z + w) hzw
  have e₁ : 4 * x₁ ^ 3 + (-m ^ 2) * x₁ ^ 2 + (-(L.g₂ + 2 * m * ν)) * x₁ + (-(L.g₃ + ν ^ 2)) = 0 := by
    linear_combination -c₁
  have e₂ : 4 * x₂ ^ 3 + (-m ^ 2) * x₂ ^ 2 + (-(L.g₂ + 2 * m * ν)) * x₂ + (-(L.g₃ + ν ^ 2)) = 0 := by
    linear_combination -c₂ + (℘'[L] w + m * x₂ + ν) * hy₂
  have e₃ : 4 * x₃ ^ 3 + (-m ^ 2) * x₃ ^ 2 + (-(L.g₂ + 2 * m * ν)) * x₃ + (-(L.g₃ + ν ^ 2)) = 0 := by
    linear_combination -c₃ + (℘'[L] (z + w) - m * x₃ - ν) * hy₃
  have d₁₂ : x₁ ≠ x₂ := sub_ne_zero.mp hne
  have d₁₃ : x₁ ≠ x₃ := by
    intro h
    rcases (weierstrassP_eq_iff L hz hzw).mp h.symm with h' | h'
    · exact hw (by rwa [show z + w - z = w by ring] at h')
    · exact h1 (by rwa [show z + w + z = 2 * z + w by ring] at h')
  have d₂₃ : x₂ ≠ x₃ := by
    intro h
    rcases (weierstrassP_eq_iff L hw hzw).mp h.symm with h' | h'
    · exact hz (by rwa [show z + w - w = z by ring] at h')
    · exact h2 (by rwa [show z + w + w = z + 2 * w by ring] at h')
  have hsum := vieta_three e₁ e₂ e₃ d₁₂ d₁₃ d₂₃
  refine ⟨by linear_combination hsum, ?_⟩
  rw [hy₃, hν]
  ring
end Generic
 
lemma eventually_generic (z w₀ : ℂ) :
    ∀ᶠ w in 𝓝[≠] w₀, w ∉ L.lattice ∧ z + w ∉ L.lattice ∧ z - w ∉ L.lattice ∧
      2 * z + w ∉ L.lattice ∧ z + 2 * w ∉ L.lattice := by
  filter_upwards [discr_affine L one_ne_zero 0 w₀, discr_affine L one_ne_zero z w₀,
    discr_affine L (neg_ne_zero.mpr one_ne_zero) z w₀, discr_affine L one_ne_zero (2 * z) w₀,
    discr_affine L two_ne_zero z w₀] with w h₁ h₂ h₃ h₄ h₅
  simp only [one_mul, add_zero, neg_mul] at h₁ h₂ h₃ h₄ h₅
  refine ⟨h₁, by rwa [add_comm], by rwa [neg_add_eq_sub] at h₃, by rwa [add_comm],
    by rwa [add_comm]⟩
lemma continuousAt_chordSlope {z w : ℂ} (hw : w ∉ L.lattice) (hne : ℘[L] z - ℘[L] w ≠ 0) :
    ContinuousAt (fun v => chordSlope L z v) w := by
  unfold chordSlope
  exact (continuousAt_const.sub (continuousAt_derivWeierstrassP L hw)).div
    (continuousAt_const.sub (continuousAt_weierstrassP L hw)) hne
 
theorem weierstrassP_add {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hzw : z + w ∉ L.lattice) (hd : z - w ∉ L.lattice) :
    ℘[L] (z + w) = -℘[L] z - ℘[L] w + chordSlope L z w ^ 2 / 4 := by
  refine eq_of_eventuallyEq_nhdsNE (F₁ := fun v => ℘[L] (z + v))
    (F₂ := fun v => -℘[L] z - ℘[L] v + chordSlope L z v ^ 2 / 4)
    ((continuousAt_weierstrassP L hzw).comp (continuousAt_const.add continuousAt_id))
    ((continuousAt_const.sub (continuousAt_weierstrassP L hw)).add
      (((continuousAt_chordSlope L hw (pdiff_ne L hz hw hzw hd)).pow 2).div_const _)) ?_
  filter_upwards [eventually_generic L z w] with v ⟨h₁, h₂, h₃, h₄, h₅⟩
  exact (addition_generic L hz h₁ h₂ h₃ h₄ h₅).1
 
theorem derivWeierstrassP_add {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hzw : z + w ∉ L.lattice) (hd : z - w ∉ L.lattice) :
    ℘'[L] (z + w) = -chordSlope L z w * (℘[L] (z + w) - ℘[L] z) - ℘'[L] z := by
  refine eq_of_eventuallyEq_nhdsNE (F₁ := fun v => ℘'[L] (z + v))
    (F₂ := fun v => -chordSlope L z v * (℘[L] (z + v) - ℘[L] z) - ℘'[L] z)
    ((continuousAt_derivWeierstrassP L hzw).comp (continuousAt_const.add continuousAt_id))
    (((continuousAt_chordSlope L hw (pdiff_ne L hz hw hzw hd)).neg.mul
      (((continuousAt_weierstrassP L hzw).comp (continuousAt_const.add continuousAt_id)).sub
      continuousAt_const)).sub continuousAt_const) ?_
  filter_upwards [eventually_generic L z w] with v ⟨h₁, h₂, h₃, h₄, h₅⟩
  exact (addition_generic L hz h₁ h₂ h₃ h₄ h₅).2
 
def tangentSlope (z : ℂ) : ℂ := (6 * ℘[L] z ^ 2 - L.g₂ / 2) / ℘'[L] z
lemma notMem_of_two_mul_notMem {z : ℂ} (h2 : 2 * z ∉ L.lattice) : z ∉ L.lattice :=
  fun h => h2 (by simpa [two_mul] using add_mem h h)
lemma derivWeierstrassP_ne_zero {z : ℂ} (h2 : 2 * z ∉ L.lattice) : ℘'[L] z ≠ 0 := by
  rw [Ne, derivWeierstrassP_eq_zero_iff L (notMem_of_two_mul_notMem L h2)]
  exact h2
 
lemma chordSlope_eq_dslope {z v : ℂ} (hv : v ≠ z) (hne : ℘[L] z - ℘[L] v ≠ 0) :
    chordSlope L z v = dslope ℘'[L] z v / dslope ℘[L] z v := by
  rw [dslope_eq_div hv, dslope_eq_div hv]
  have hv' : v - z ≠ 0 := sub_ne_zero.mpr hv
  have hne' : ℘[L] v - ℘[L] z ≠ 0 := by
    intro h; apply hne; linear_combination -h
  unfold chordSlope
  field_simp
  ring
lemma continuousAt_slope_quot {z : ℂ} (h2 : 2 * z ∉ L.lattice) :
    ContinuousAt (fun v => dslope ℘'[L] z v / dslope ℘[L] z v) z := by
  have hz := notMem_of_two_mul_notMem L h2
  refine ContinuousAt.div (continuousAt_dslope_same.mpr (differentiableAt_derivWeierstrassP L hz))
    (continuousAt_dslope_same.mpr (differentiableAt_weierstrassP L hz)) ?_
  rw [dslope_same, L.deriv_weierstrassP]
  exact derivWeierstrassP_ne_zero L h2
lemma slope_quot_self {z : ℂ} (h2 : 2 * z ∉ L.lattice) :
    dslope ℘'[L] z z / dslope ℘[L] z z = tangentSlope L z := by
  have hz := notMem_of_two_mul_notMem L h2
  rw [dslope_same, dslope_same, L.deriv_weierstrassP, (hasDerivAt_derivWeierstrassP L hz).deriv]
  rfl
 
lemma eventually_near_self {z : ℂ} (h2 : 2 * z ∉ L.lattice) :
    ∀ᶠ v in 𝓝[≠] z, v ∉ L.lattice ∧ z + v ∉ L.lattice ∧ z - v ∉ L.lattice ∧ v ≠ z := by
  have hz := notMem_of_two_mul_notMem L h2
  have e1 : ∀ᶠ v in 𝓝 z, v ∉ L.lattice := (isOpen_compl_lattice L).mem_nhds hz
  have e2 : ∀ᶠ v in 𝓝 z, v ∉ {u | 1 * u + z ∈ L.lattice} :=
    (discr_affine L one_ne_zero z).eventually_nhds (by simpa [two_mul] using h2)
  filter_upwards [nhdsWithin_le_nhds e1, nhdsWithin_le_nhds e2,
    discr_affine L (neg_ne_zero.mpr one_ne_zero) z z, self_mem_nhdsWithin] with v h₁ h₂ h₃ h₄
  simp only [one_mul, neg_mul] at h₂ h₃
  exact ⟨h₁, by rwa [add_comm], by rwa [neg_add_eq_sub] at h₃, h₄⟩
 
theorem weierstrassP_two_mul {z : ℂ} (h2 : 2 * z ∉ L.lattice) :
    ℘[L] (2 * z) = -2 * ℘[L] z + tangentSlope L z ^ 2 / 4 := by
  have hz := notMem_of_two_mul_notMem L h2
  have h2' : z + z ∉ L.lattice := by rwa [← two_mul]
  have key := eq_of_eventuallyEq_nhdsNE (F₁ := fun v => ℘[L] (z + v))
    (F₂ := fun v => -℘[L] z - ℘[L] v + (dslope ℘'[L] z v / dslope ℘[L] z v) ^ 2 / 4) (u := z)
    ((continuousAt_weierstrassP L h2').comp (continuousAt_const.add continuousAt_id))
    ((continuousAt_const.sub (continuousAt_weierstrassP L hz)).add
      (((continuousAt_slope_quot L h2).pow 2).div_const _)) (by
      filter_upwards [eventually_near_self L h2] with v ⟨h₁, h₂, h₃, h₄⟩
      have hne := pdiff_ne L hz h₁ h₂ h₃
      rw [weierstrassP_add L hz h₁ h₂ h₃, chordSlope_eq_dslope L h₄ hne])
  simp only [slope_quot_self L h2] at key
  rw [two_mul, key]
  ring
 
theorem derivWeierstrassP_two_mul {z : ℂ} (h2 : 2 * z ∉ L.lattice) :
    ℘'[L] (2 * z) = -tangentSlope L z * (℘[L] (2 * z) - ℘[L] z) - ℘'[L] z := by
  have hz := notMem_of_two_mul_notMem L h2
  have h2' : z + z ∉ L.lattice := by rwa [← two_mul]
  have key := eq_of_eventuallyEq_nhdsNE (F₁ := fun v => ℘'[L] (z + v))
    (F₂ := fun v => -(dslope ℘'[L] z v / dslope ℘[L] z v) * (℘[L] (z + v) - ℘[L] z) - ℘'[L] z)
    (u := z)
    ((continuousAt_derivWeierstrassP L h2').comp (continuousAt_const.add continuousAt_id))
    ((((continuousAt_slope_quot L h2).neg.mul
      (((continuousAt_weierstrassP L h2').comp (continuousAt_const.add continuousAt_id)).sub
      continuousAt_const))).sub continuousAt_const) (by
      filter_upwards [eventually_near_self L h2] with v ⟨h₁, h₂, h₃, h₄⟩
      have hne := pdiff_ne L hz h₁ h₂ h₃
      rw [derivWeierstrassP_add L hz h₁ h₂ h₃, chordSlope_eq_dslope L h₄ hne])
  simp only [slope_quot_self L h2] at key
  rw [two_mul, key]
end LSG.Weierstrass
end
end

/- LSG.LemniscateIndep.Symm -/
section
noncomputable section
open Complex PeriodPair
namespace LSG.LemniscateIndep
variable {L : PeriodPair} {a : ℝ}
lemma mem_lattice_sq (h₁ : L.ω₁ = a) (h₂ : L.ω₂ = I * a) {z : ℂ} :
    z ∈ L.lattice ↔ ∃ m n : ℤ, (m : ℂ) * a + n * (I * a) = z := by
  rw [PeriodPair.mem_lattice, h₁, h₂]
lemma I_mul_mem (h₁ : L.ω₁ = a) (h₂ : L.ω₂ = I * a) {z : ℂ} (hz : z ∈ L.lattice) :
    I * z ∈ L.lattice := by
  obtain ⟨m, n, rfl⟩ := (mem_lattice_sq h₁ h₂).1 hz
  refine (mem_lattice_sq h₁ h₂).2 ⟨-n, m, ?_⟩
  push_cast
  linear_combination (-(n : ℂ) * a) * I_sq
lemma conj_mem (h₁ : L.ω₁ = a) (h₂ : L.ω₂ = I * a) {z : ℂ} (hz : z ∈ L.lattice) :
    (starRingEnd ℂ) z ∈ L.lattice := by
  obtain ⟨m, n, rfl⟩ := (mem_lattice_sq h₁ h₂).1 hz
  refine (mem_lattice_sq h₁ h₂).2 ⟨m, -n, ?_⟩
  simp only [map_add, map_mul, map_intCast, conj_ofReal, conj_I]
  push_cast
  ring
 
def mulIEquiv (h₁ : L.ω₁ = a) (h₂ : L.ω₂ = I * a) : L.lattice ≃ L.lattice where
  toFun l := ⟨I * l, I_mul_mem h₁ h₂ l.2⟩
  invFun l := ⟨I * (I * (I * l)), I_mul_mem h₁ h₂ (I_mul_mem h₁ h₂ (I_mul_mem h₁ h₂ l.2))⟩
  left_inv l := by
    ext; simp only
    linear_combination (I ^ 2 - 1) * (l : ℂ) * I_sq
  right_inv l := by
    ext; simp only
    linear_combination (I ^ 2 - 1) * (l : ℂ) * I_sq
 
def conjEquiv (h₁ : L.ω₁ = a) (h₂ : L.ω₂ = I * a) : L.lattice ≃ L.lattice where
  toFun l := ⟨(starRingEnd ℂ) l, conj_mem h₁ h₂ l.2⟩
  invFun l := ⟨(starRingEnd ℂ) l, conj_mem h₁ h₂ l.2⟩
  left_inv l := by ext; simp
  right_inv l := by ext; simp
lemma tsum_mulI (h₁ : L.ω₁ = a) (h₂ : L.ω₂ = I * a) (f : ℂ → ℂ) :
    ∑' l : L.lattice, f (I * l) = ∑' l : L.lattice, f l :=
  (mulIEquiv h₁ h₂).tsum_eq (fun l => f l)
lemma tsum_conj (h₁ : L.ω₁ = a) (h₂ : L.ω₂ = I * a) (f : ℂ → ℂ) :
    ∑' l : L.lattice, f ((starRingEnd ℂ) l) = ∑' l : L.lattice, f l :=
  (conjEquiv h₁ h₂).tsum_eq (fun l => f l)
 
lemma G_six_eq_zero (h₁ : L.ω₁ = a) (h₂ : L.ω₂ = I * a) : L.G 6 = 0 := by
  have h := tsum_mulI h₁ h₂ (fun z => (z ^ 6)⁻¹)
  have hI6 : I ^ 6 = -1 := by
    rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul, I_sq]; norm_num
  simp only [mul_pow, hI6, neg_one_mul, inv_neg, tsum_neg] at h
  have : L.G 6 = -L.G 6 := by rw [PeriodPair.G]; exact h.symm
  linear_combination this / 2
theorem g₃_eq_zero_of_square (h₁ : L.ω₁ = a) (h₂ : L.ω₂ = I * a) : L.g₃ = 0 := by
  rw [PeriodPair.g₃, G_six_eq_zero h₁ h₂, mul_zero]
 
lemma weierstrassP_I_mul (h₁ : L.ω₁ = a) (h₂ : L.ω₂ = I * a) (z : ℂ) :
    ℘[L] (I * z) = -℘[L] z := by
  have h := tsum_mulI h₁ h₂ (fun w => 1 / (I * z - w) ^ 2 - 1 / w ^ 2)
  have hpt : ∀ w : ℂ, 1 / (I * z - I * w) ^ 2 - 1 / (I * w) ^ 2 =
      -(1 / (z - w) ^ 2 - 1 / w ^ 2) := by
    intro w
    rw [← mul_sub, mul_pow, mul_pow, I_sq]
    simp only [neg_one_mul, one_div, inv_neg]
    ring
  simp only [hpt, tsum_neg] at h
  change ℘[L] (I * z) = -(∑' l : L.lattice, (1 / (z - l) ^ 2 - 1 / (l : ℂ) ^ 2))
  rw [h]
  rfl
 
lemma weierstrassP_conj (h₁ : L.ω₁ = a) (h₂ : L.ω₂ = I * a) (z : ℂ) :
    ℘[L] ((starRingEnd ℂ) z) = (starRingEnd ℂ) (℘[L] z) := by
  have h := tsum_conj h₁ h₂ (fun w => 1 / ((starRingEnd ℂ) z - w) ^ 2 - 1 / w ^ 2)
  change _ = (starRingEnd ℂ) (∑' l : L.lattice, (1 / (z - l) ^ 2 - 1 / (l : ℂ) ^ 2))
  rw [Complex.conj_tsum]
  simp only [map_sub, map_div₀, map_one, map_pow] at h ⊢
  rw [h]
  rfl
 
lemma derivWeierstrassP_conj (h₁ : L.ω₁ = a) (h₂ : L.ω₂ = I * a) (z : ℂ) :
    ℘'[L] ((starRingEnd ℂ) z) = (starRingEnd ℂ) (℘'[L] z) := by
  have h := tsum_conj h₁ h₂ (fun w => 2 / ((starRingEnd ℂ) z - w) ^ 3)
  change _ = (starRingEnd ℂ) (-∑' l : L.lattice, 2 / (z - l) ^ 3)
  rw [map_neg, Complex.conj_tsum]
  simp only [map_sub, map_div₀, map_ofNat, map_pow] at h ⊢
  rw [h]
  rfl
 
lemma weierstrassP_ofReal (h₁ : L.ω₁ = a) (h₂ : L.ω₂ = I * a) (t : ℝ) :
    ℘[L] (t : ℂ) = ((℘[L] (t : ℂ)).re : ℂ) := by
  have h := weierstrassP_conj h₁ h₂ (t : ℂ)
  rw [conj_ofReal] at h
  exact (Complex.conj_eq_iff_re.1 h.symm).symm
 
lemma derivWeierstrassP_ofReal (h₁ : L.ω₁ = a) (h₂ : L.ω₂ = I * a) (t : ℝ) :
    ℘'[L] (t : ℂ) = ((℘'[L] (t : ℂ)).re : ℂ) := by
  have h := derivWeierstrassP_conj h₁ h₂ (t : ℂ)
  rw [conj_ofReal] at h
  exact (Complex.conj_eq_iff_re.1 h.symm).symm
 
lemma ofReal_notMem (ha : 0 < a) (h₁ : L.ω₁ = a) (h₂ : L.ω₂ = I * a) {t : ℝ} (ht0 : 0 < t)
    (hta : t < a) : (t : ℂ) ∉ L.lattice := by
  intro hm
  obtain ⟨m, n, h⟩ := (mem_lattice_sq h₁ h₂).1 hm
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [add_re, mul_re, intCast_re, ofReal_re, intCast_im, ofReal_im, mul_zero, sub_zero,
    I_re, zero_mul, I_im, sub_self, mul_im, one_mul, zero_add, add_zero, add_im, mul_eq_zero,
    Int.cast_eq_zero] at hre him
  rcases him with hn | hn
  · subst hn
    have h1 : (0 : ℝ) < m := by
      by_contra hc; rw [not_lt] at hc; nlinarith
    have h2 : (m : ℝ) < 1 := by
      by_contra hc; rw [not_lt] at hc; nlinarith
    have h1' : (0 : ℤ) < m := by exact_mod_cast h1
    have h2' : m < (1 : ℤ) := by exact_mod_cast h2
    omega
  · exact absurd hn ha.ne'
end LSG.LemniscateIndep
end
end

/- LSG.LemniscateIndep.RealLine -/
section
noncomputable section
open Complex PeriodPair Filter Topology Set LSG.Weierstrass
namespace LSG.LemniscateIndep
 
structure Sq (L : PeriodPair) (a : ℝ) : Prop where
  pos : 0 < a
  h₁ : L.ω₁ = a
  h₂ : L.ω₂ = I * a
 
def rP (L : PeriodPair) (t : ℝ) : ℝ := (℘[L] (t : ℂ)).re
 
def rQ (L : PeriodPair) (t : ℝ) : ℝ := (℘'[L] (t : ℂ)).re
 
def rPhi (L : PeriodPair) (t : ℝ) : ℝ := t ^ 2 * (L.weierstrassPExcept 0 (t : ℂ)).re + 1
 
def tau (L : PeriodPair) (a t : ℝ) : ℝ := Real.sqrt (rP L (a / 2)) * t / Real.sqrt (rPhi L t)
variable {L : PeriodPair} {a : ℝ}
namespace Sq
variable (S : Sq L a)
include S
lemma notMem {t : ℝ} (ht0 : 0 < t) (hta : t < a) : (t : ℂ) ∉ L.lattice :=
  ofReal_notMem S.pos S.h₁ S.h₂ ht0 hta
lemma P_ofReal (t : ℝ) : ℘[L] (t : ℂ) = (rP L t : ℂ) := weierstrassP_ofReal S.h₁ S.h₂ t
lemma Q_ofReal (t : ℝ) : ℘'[L] (t : ℂ) = (rQ L t : ℂ) := derivWeierstrassP_ofReal S.h₁ S.h₂ t
lemma hasDerivAt_rP {t : ℝ} (ht0 : 0 < t) (hta : t < a) : HasDerivAt (rP L) (rQ L t) t :=
  (hasDerivAt_weierstrassP L (S.notMem ht0 hta)).real_of_complex
lemma half_eq : L.ω₁ / 2 = ((a / 2 : ℝ) : ℂ) := by rw [S.h₁]; push_cast; ring
lemma rP_half_ne_zero : rP L (a / 2) ≠ 0 := by
  intro he
  have hP : ℘[L] (L.ω₁ / 2) = 0 := by rw [S.half_eq, S.P_ofReal, he, ofReal_zero]
  have hI : ℘[L] (L.ω₂ / 2) = 0 := by
    rw [show L.ω₂ / 2 = I * (L.ω₁ / 2) by rw [S.h₁, S.h₂]; ring, weierstrassP_I_mul S.h₁ S.h₂,
      hP, neg_zero]
  rcases (weierstrassP_eq_iff L L.ω₁_div_two_notMem_lattice L.ω₂_div_two_notMem_lattice).1
    (hI.trans hP.symm) with h | h
  · have := (L.mul_ω₁_add_mul_ω₂_mem_lattice (α := -1 / 2) (β := 1 / 2)).1
      (by convert h using 1; push_cast; ring)
    exact absurd this.1 (by norm_num)
  · have := (L.mul_ω₁_add_mul_ω₂_mem_lattice (α := 1 / 2) (β := 1 / 2)).1
      (by convert h using 1; push_cast; ring)
    exact absurd this.1 (by norm_num)
 
lemma g₂_eq : L.g₂ = 4 * (rP L (a / 2) : ℂ) ^ 2 := by
  have hc := weierstrassP_half_cubic L L.ω₁_mem_lattice L.ω₁_div_two_notMem_lattice
  rw [g₃_eq_zero_of_square S.h₁ S.h₂, S.half_eq, S.P_ofReal] at hc
  have h0 : (rP L (a / 2) : ℂ) ≠ 0 := ofReal_ne_zero.2 S.rP_half_ne_zero
  have : (rP L (a / 2) : ℂ) * (4 * (rP L (a / 2) : ℂ) ^ 2 - L.g₂) = 0 := by
    linear_combination hc
  exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h0)).symm
lemma relation {t : ℝ} (ht0 : 0 < t) (hta : t < a) :
    rQ L t ^ 2 = 4 * rP L t ^ 3 - 4 * rP L (a / 2) ^ 2 * rP L t := by
  have h := L.derivWeierstrassP_sq (t : ℂ) (S.notMem ht0 hta)
  rw [S.P_ofReal, S.Q_ofReal, S.g₂_eq, g₃_eq_zero_of_square S.h₁ S.h₂, sub_zero] at h
  exact_mod_cast h
lemma rQ_ne_zero {t : ℝ} (ht0 : 0 < t) (hta : t < a / 2) : rQ L t ≠ 0 := by
  have h := derivWeierstrassP_ne_zero L (z := (t : ℂ)) (by
    rw [show (2 : ℂ) * t = ((2 * t : ℝ) : ℂ) by push_cast; ring]
    exact S.notMem (by linarith) (by linarith))
  rw [S.Q_ofReal] at h
  exact_mod_cast h
end Sq
lemma rPhi_eq {t : ℝ} (ht : t ≠ 0) : rPhi L t = t ^ 2 * rP L t := by
  have h := congrArg Complex.re (weierstrassP_eq_except_zero L (t : ℂ))
  rw [show (1 : ℂ) / (t : ℂ) ^ 2 = ((1 / t ^ 2 : ℝ) : ℂ) by push_cast; ring, add_re,
    ofReal_re] at h
  rw [rPhi, rP, h]
  field_simp
lemma continuousAt_rPhi {t : ℝ} (h : (t : ℂ) ∉ (L.lattice : Set ℂ) \ {0}) :
    ContinuousAt (rPhi L) t := by
  have hw : ContinuousAt (fun s : ℝ => L.weierstrassPExcept 0 (s : ℂ)) t :=
    (L.analyticOnNhd_weierstrassPExcept 0 _ h).continuousAt.comp continuous_ofReal.continuousAt
  exact ((continuousAt_id.pow 2).mul (continuous_re.continuousAt.comp hw)).add continuousAt_const
namespace Sq
variable (S : Sq L a)
include S
lemma exists_large : ∃ t₀ ∈ Ioo 0 (a / 2), |rP L (a / 2)| < rP L t₀ := by
  have h0 : rPhi L 0 = 1 := by simp [rPhi]
  have hφ : Tendsto (rPhi L) (𝓝[>] 0) (𝓝 1) := by
    have := (continuousAt_rPhi (L := L) (t := 0) (by simp)).tendsto
    rw [h0] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hinv : Tendsto (fun t : ℝ => (t⁻¹) ^ 2) (𝓝[>] 0) atTop :=
    (tendsto_pow_atTop two_ne_zero).comp tendsto_inv_nhdsGT_zero
  have hprod := hφ.pos_mul_atTop one_pos hinv
  have hev1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 (a / 2) := Ioo_mem_nhdsGT (half_pos S.pos)
  obtain ⟨t, ht, hgt⟩ := (hev1.and (hprod.eventually_gt_atTop |rP L (a / 2)|)).exists
  refine ⟨t, ht, ?_⟩
  rw [rPhi_eq ht.1.ne'] at hgt
  have : t ^ 2 * rP L t * (t⁻¹) ^ 2 = rP L t := by
    have := ht.1.ne'; field_simp
  linarith
lemma abs_lt_rP {t : ℝ} (ht : t ∈ Ioo 0 (a / 2)) : |rP L (a / 2)| < rP L t := by
  obtain ⟨t₀, ht₀, hgt⟩ := S.exists_large
  by_contra hle
  rw [not_lt] at hle
  have hsub : uIcc t t₀ ⊆ Ioo 0 (a / 2) := ordConnected_Ioo.uIcc_subset ht ht₀
  have hcont : ContinuousOn (rP L) (uIcc t t₀) := fun x hx =>
    (S.hasDerivAt_rP (hsub hx).1 (by linarith [(hsub hx).2, S.pos])).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hPc⟩ := intermediate_value_uIcc hcont (mem_uIcc.2 (Or.inl ⟨hle, hgt.le⟩))
  have hrel := S.relation (hsub hc).1 (by linarith [(hsub hc).2, S.pos])
  rw [hPc] at hrel
  have h3 : |rP L (a / 2)| ^ 3 = |rP L (a / 2)| ^ 2 * |rP L (a / 2)| := pow_succ _ 2
  have : rQ L c ^ 2 = 0 := by rw [hrel, h3, sq_abs]; ring
  exact S.rQ_ne_zero (hsub hc).1 (hsub hc).2 (pow_eq_zero_iff two_ne_zero |>.1 this)
lemma rP_half_pos : 0 < rP L (a / 2) := by
  have hcont : ContinuousAt (rP L) (a / 2) :=
    (S.hasDerivAt_rP (half_pos S.pos) (half_lt_self S.pos)).continuousAt
  have hle : |rP L (a / 2)| ≤ rP L (a / 2) := by
    refine ge_of_tendsto (hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio (a / 2)))) ?_
    filter_upwards [Ioo_mem_nhdsLT (half_pos S.pos)] with t ht using (S.abs_lt_rP ht).le
  exact lt_of_le_of_ne ((abs_nonneg _).trans hle) (Ne.symm S.rP_half_ne_zero)
lemma lt_rP {t : ℝ} (ht : t ∈ Ioo 0 (a / 2)) : rP L (a / 2) < rP L t :=
  (le_abs_self _).trans_lt (S.abs_lt_rP ht)
lemma le_rP {t : ℝ} (ht : t ∈ Ioc 0 (a / 2)) : rP L (a / 2) ≤ rP L t := by
  rcases eq_or_lt_of_le ht.2 with h | h
  · rw [h]
  · exact (S.lt_rP ⟨ht.1, h⟩).le
lemma rPhi_pos {t : ℝ} (ht : t ∈ Icc 0 (a / 2)) : 0 < rPhi L t := by
  rcases eq_or_lt_of_le ht.1 with h | h
  · subst h; simp [rPhi]
  · rw [rPhi_eq h.ne']
    exact mul_pos (pow_pos h 2) (S.rP_half_pos.trans_le (S.le_rP ⟨h, ht.2⟩))
lemma tau_eq {t : ℝ} (ht : t ∈ Ioc 0 (a / 2)) :
    tau L a t = Real.sqrt (rP L (a / 2)) / Real.sqrt (rP L t) := by
  have hP : 0 < rP L t := S.rP_half_pos.trans_le (S.le_rP ht)
  rw [tau, rPhi_eq ht.1.ne', Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.1.le]
  have := Real.sqrt_pos.2 hP
  have := ht.1.ne'
  field_simp
omit S in
lemma tau_zero : tau L a 0 = 0 := by simp [tau]
lemma tau_half : tau L a (a / 2) = 1 := by
  rw [S.tau_eq ⟨half_pos S.pos, le_rfl⟩]
  exact div_self (Real.sqrt_pos.2 S.rP_half_pos).ne'
lemma tau_mem_Icc {t : ℝ} (ht : t ∈ Icc 0 (a / 2)) : tau L a t ∈ Icc 0 1 := by
  rcases eq_or_lt_of_le ht.1 with h | h
  · subst h; rw [tau_zero]; exact ⟨le_rfl, zero_le_one⟩
  · rw [S.tau_eq ⟨h, ht.2⟩]
    have hP : 0 < rP L t := S.rP_half_pos.trans_le (S.le_rP ⟨h, ht.2⟩)
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (Real.sqrt_pos.2 hP)]
    exact Real.sqrt_le_sqrt (S.le_rP ⟨h, ht.2⟩)
lemma tau_mem_Ioo {t : ℝ} (ht : t ∈ Ioo 0 (a / 2)) : tau L a t ∈ Ioo 0 1 := by
  rw [S.tau_eq ⟨ht.1, ht.2.le⟩]
  have hP : 0 < rP L t := S.rP_half_pos.trans (S.lt_rP ht)
  refine ⟨div_pos (Real.sqrt_pos.2 S.rP_half_pos) (Real.sqrt_pos.2 hP), ?_⟩
  rw [div_lt_one (Real.sqrt_pos.2 hP)]
  exact Real.sqrt_lt_sqrt S.rP_half_pos.le (S.lt_rP ht)
lemma continuousOn_tau : ContinuousOn (tau L a) (Icc 0 (a / 2)) := by
  have hφ : ContinuousOn (rPhi L) (Icc 0 (a / 2)) := by
    intro t ht
    refine (continuousAt_rPhi ?_).continuousWithinAt
    rintro ⟨hm, hne⟩
    rcases eq_or_lt_of_le ht.1 with h | h
    · subst h; exact hne (by simp)
    · exact S.notMem h (by linarith [ht.2, S.pos]) hm
  exact (continuousOn_const.mul continuousOn_id).div hφ.sqrt
    (fun t ht => (Real.sqrt_pos.2 (S.rPhi_pos ht)).ne')
 
def dtau (L : PeriodPair) (a t : ℝ) : ℝ :=
  (0 * Real.sqrt (rP L t) - Real.sqrt (rP L (a / 2)) * (rQ L t / (2 * Real.sqrt (rP L t)))) /
    Real.sqrt (rP L t) ^ 2
lemma hasDerivAt_tau {t : ℝ} (ht : t ∈ Ioo 0 (a / 2)) : HasDerivAt (tau L a) (dtau L a t) t := by
  have hP : 0 < rP L t := S.rP_half_pos.trans (S.lt_rP ht)
  have hs := (S.hasDerivAt_rP ht.1 (by linarith [ht.2, S.pos])).sqrt hP.ne'
  have hd := (hasDerivAt_const t (Real.sqrt (rP L (a / 2)))).div hs (Real.sqrt_pos.2 hP).ne'
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs using S.tau_eq ⟨hs.1, hs.2.le⟩
lemma deriv_sq {t : ℝ} (ht : t ∈ Ioo 0 (a / 2)) :
    (lemInt (tau L a t) * dtau L a t) ^ 2 = rP L (a / 2) := by
  have hP : 0 < rP L t := S.rP_half_pos.trans (S.lt_rP ht)
  have hτ := S.tau_mem_Ioo ht
  have hrel := S.relation ht.1 (by linarith [ht.2, S.pos])
  rw [S.tau_eq ⟨ht.1, ht.2.le⟩] at hτ ⊢
  set r := Real.sqrt (rP L (a / 2)) with hr
  set s := Real.sqrt (rP L t) with hs
  have hr0 : 0 < r := Real.sqrt_pos.2 S.rP_half_pos
  have hs0 : 0 < s := Real.sqrt_pos.2 hP
  have hr2 : r ^ 2 = rP L (a / 2) := Real.sq_sqrt S.rP_half_pos.le
  have hs2 : s ^ 2 = rP L t := Real.sq_sqrt hP.le
  have h4 : (r / s) ^ 4 < 1 := pow_lt_one₀ hτ.1.le hτ.2 (by norm_num)
  set u := Real.sqrt (1 - (r / s) ^ 4) with hu
  have hu0 : 0 < u := Real.sqrt_pos.2 (by linarith)
  have hu2 : u ^ 2 = 1 - (r / s) ^ 4 := Real.sq_sqrt (by linarith)
  have hQ : rQ L t ^ 2 = 4 * s ^ 6 - 4 * r ^ 4 * s ^ 2 := by
    rw [hrel, ← hs2, ← hr2]; ring
  have hX : (dtau L a t) ^ 2 = r ^ 2 * u ^ 2 := by
    rw [dtau, ← hr, ← hs, hu2, div_pow]
    field_simp
    linear_combination r ^ 2 * hQ
  rw [lemInt, ← hu, mul_pow, hX, ← hr2]
  field_simp
 
theorem rP_half_eq : rP L (a / 2) = (varpi / a) ^ 2 := by
  have ha := S.pos
  have hGc : ContinuousOn (fun t => lemF (tau L a t)) (Icc 0 (a / 2)) :=
    continuousOn_lemF.comp S.continuousOn_tau (fun t ht => S.tau_mem_Icc ht)
  have hGd : ∀ x ∈ Ioo 0 (a / 2),
      HasDerivAt (fun t => lemF (tau L a t)) (lemInt (tau L a x) * dtau L a x) x :=
    fun x hx => (hasDerivAt_lemF (S.tau_mem_Ioo hx)).comp x (S.hasDerivAt_tau hx)
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope _ _ (half_pos ha) hGc hGd
  rw [S.tau_half, tau_zero, lemF_one, lemF_zero] at hcd
  have hsl : (varpi / 2 - 0) / (a / 2 - 0) = varpi / a := by
    rw [sub_zero, sub_zero]; field_simp
  rw [← S.deriv_sq hc, hcd, hsl]
 
theorem g₂_eq_of_square : L.g₂ = 4 * ((varpi / a : ℝ) : ℂ) ^ 4 := by
  rw [S.g₂_eq, S.rP_half_eq]; push_cast; ring
end Sq
end LSG.LemniscateIndep
end
end

/- LSG.Weierstrass.Dictionary -/
section
open Module Filter Complex Set WeierstrassCurve WeierstrassCurve.Affine
open scoped Topology
noncomputable section
namespace LSG.Weierstrass
open PeriodPair
variable (L : PeriodPair)
 
def curve : WeierstrassCurve ℂ :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := -L.g₂ / 4, a₆ := -L.g₃ / 4 }
 
abbrev curveA : WeierstrassCurve.Affine ℂ := (curve L).toAffine
lemma curve_Δ : (curve L).Δ = L.g₂ ^ 3 - 27 * L.g₃ ^ 2 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, curve]
  ring
lemma half_comb_notMem {a b : ℤ} (h : ¬ ((2 : ℤ) ∣ a ∧ (2 : ℤ) ∣ b)) :
    ((a : ℂ) * L.ω₁ + b * L.ω₂) / 2 ∉ L.lattice := by
  intro hm
  obtain ⟨m, n, hmn⟩ := mem_lattice.mp hm
  have := int_coords_eq L (a := 2 * m) (b := 2 * n) (c := a) (d := b)
    (by push_cast; linear_combination 2 * hmn)
  exact h ⟨⟨m, by omega⟩, ⟨n, by omega⟩⟩
 
theorem discr_ne_zero : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0 := by
  have hn : ∀ a b : ℤ, ¬ ((2 : ℤ) ∣ a ∧ (2 : ℤ) ∣ b) →
      ((a : ℂ) * L.ω₁ + b * L.ω₂) / 2 ∉ L.lattice := fun a b h => half_comb_notMem L h
  have h1 : L.ω₁ / 2 ∉ L.lattice := L.ω₁_div_two_notMem_lattice
  have h2 : L.ω₂ / 2 ∉ L.lattice := L.ω₂_div_two_notMem_lattice
  have h3 : (L.ω₁ + L.ω₂) / 2 ∉ L.lattice := by
    have := hn 1 1 (by omega); push_cast at this; simpa using this
  set e₁ := ℘[L] (L.ω₁ / 2)
  set e₂ := ℘[L] (L.ω₂ / 2)
  set e₃ := ℘[L] ((L.ω₁ + L.ω₂) / 2)
  have c₁ := weierstrassP_half_cubic L L.ω₁_mem_lattice h1
  have c₂ := weierstrassP_half_cubic L L.ω₂_mem_lattice h2
  have c₃ := weierstrassP_half_cubic L (add_mem L.ω₁_mem_lattice L.ω₂_mem_lattice) h3
  have d₁₂ : e₁ ≠ e₂ := by
    intro h
    rcases (weierstrassP_eq_iff L h2 h1).mp h with h' | h'
    · exact hn 1 (-1) (by omega) (by push_cast; rw [show (1 * L.ω₁ + -1 * L.ω₂) / 2 =
        L.ω₁ / 2 - L.ω₂ / 2 by ring]; exact h')
    · exact hn 1 1 (by omega) (by push_cast; rw [show (1 * L.ω₁ + 1 * L.ω₂) / 2 =
        L.ω₁ / 2 + L.ω₂ / 2 by ring]; exact h')
  have d₁₃ : e₁ ≠ e₃ := by
    intro h
    rcases (weierstrassP_eq_iff L h3 h1).mp h with h' | h'
    · exact hn 0 (-1) (by omega) (by push_cast; rw [show (0 * L.ω₁ + -1 * L.ω₂) / 2 =
        L.ω₁ / 2 - (L.ω₁ + L.ω₂) / 2 by ring]; exact h')
    · exact hn 2 1 (by omega) (by push_cast; rw [show (2 * L.ω₁ + 1 * L.ω₂) / 2 =
        L.ω₁ / 2 + (L.ω₁ + L.ω₂) / 2 by ring]; exact h')
  have d₂₃ : e₂ ≠ e₃ := by
    intro h
    rcases (weierstrassP_eq_iff L h3 h2).mp h with h' | h'
    · exact hn (-1) 0 (by omega) (by push_cast; rw [show (-1 * L.ω₁ + 0 * L.ω₂) / 2 =
        L.ω₂ / 2 - (L.ω₁ + L.ω₂) / 2 by ring]; exact h')
    · exact hn 1 2 (by omega) (by push_cast; rw [show (1 * L.ω₁ + 2 * L.ω₂) / 2 =
        L.ω₂ / 2 + (L.ω₁ + L.ω₂) / 2 by ring]; exact h')
  have hs := vieta_three (a := 0) (b := -L.g₂) (c := -L.g₃) (by linear_combination c₁)
    (by linear_combination c₂) (by linear_combination c₃) d₁₂ d₁₃ d₂₃
  have hg₂ : L.g₂ = 4 * (e₁ ^ 2 + e₁ * e₂ + e₂ ^ 2) := by
    have : (e₁ - e₂) * (4 * (e₁ ^ 2 + e₁ * e₂ + e₂ ^ 2) - L.g₂) = 0 := by
      linear_combination c₁ - c₂
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) d₁₂
    · linear_combination -h
  have hg₃ : L.g₃ = 4 * e₁ ^ 3 - L.g₂ * e₁ := by linear_combination -c₁
  have he₃ : e₃ = -e₁ - e₂ := by linear_combination hs
  have key : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 =
      16 * ((e₁ - e₂) * (e₁ - e₃) * (e₂ - e₃)) ^ 2 := by
    rw [hg₃, hg₂, he₃]
    ring
  rw [key]
  have : (e₁ - e₂) * (e₁ - e₃) * (e₂ - e₃) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr d₁₂) (sub_ne_zero.mpr d₁₃)) (sub_ne_zero.mpr d₂₃)
  exact mul_ne_zero (by norm_num) (pow_ne_zero 2 this)
lemma curve_Δ_ne_zero : (curveA L).Δ ≠ 0 := by
  rw [show (curveA L).Δ = (curve L).Δ from rfl, curve_Δ]
  exact discr_ne_zero L
lemma equation_weierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    (curveA L).Equation (℘[L] z) (℘'[L] z / 2) := by
  rw [equation_iff]
  have := L.derivWeierstrassP_sq z hz
  simp only [curveA, curve]
  linear_combination this / 4
lemma nonsingular_weierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    (curveA L).Nonsingular (℘[L] z) (℘'[L] z / 2) :=
  (equation_iff_nonsingular_of_Δ_ne_zero (curve_Δ_ne_zero L)).mp (equation_weierstrassP L hz)
open Classical in
 
def expE (z : ℂ) : (curveA L).Point :=
  if h : z ∈ L.lattice then 0 else .some _ _ (nonsingular_weierstrassP L h)
lemma expE_of_mem {z : ℂ} (h : z ∈ L.lattice) : expE L z = 0 := by
  simp [expE, h]
lemma expE_of_notMem {z : ℂ} (h : z ∉ L.lattice) :
    expE L z = .some _ _ (nonsingular_weierstrassP L h) := by
  simp [expE, h]
lemma some_eq_some {x y x' y' : ℂ} {h : (curveA L).Nonsingular x y}
    {h' : (curveA L).Nonsingular x' y'} (hx : x = x') (hy : y = y') :
    Point.some x y h = Point.some x' y' h' := by
  subst hx hy; rfl
lemma expE_zero : expE L 0 = 0 := expE_of_mem L L.lattice.zero_mem
 
lemma expE_add_mem (z : ℂ) {ω : ℂ} (hω : ω ∈ L.lattice) : expE L (z + ω) = expE L z := by
  by_cases hz : z ∈ L.lattice
  · rw [expE_of_mem L hz, expE_of_mem L (add_mem hz hω)]
  · have hz' : z + ω ∉ L.lattice := add_notMem_lattice L hz hω
    rw [expE_of_notMem L hz, expE_of_notMem L hz']
    exact some_eq_some L (weierstrassP_add_mem L z hω) (by rw [derivWeierstrassP_add_mem L z hω])
 
theorem expE_add (z w : ℂ) : expE L (z + w) = expE L z + expE L w := by
  by_cases hz : z ∈ L.lattice
  · rw [expE_of_mem L hz, zero_add, add_comm, expE_add_mem L w hz]
  by_cases hw : w ∈ L.lattice
  · rw [expE_of_mem L hw, add_zero, expE_add_mem L z hw]
  rw [expE_of_notMem L hz, expE_of_notMem L hw]
  by_cases hzw : z + w ∈ L.lattice
  · 
    rw [expE_of_mem L hzw]
    have hP : ℘[L] z = ℘[L] w := (weierstrassP_eq_iff L hw hz).mpr (Or.inr hzw)
    have hP' : ℘'[L] z = -℘'[L] w := by
      have := derivWeierstrassP_add_mem L (-w) hzw
      rw [show -w + (z + w) = z by ring, L.derivWeierstrassP_neg] at this
      exact this
    refine (Point.add_of_Y_eq hP ?_).symm
    rw [negY, hP']
    simp [curveA, curve]
    ring
  rw [expE_of_notMem L hzw]
  by_cases hd : z - w ∈ L.lattice
  · 
    have hP : ℘[L] z = ℘[L] w := (weierstrassP_eq_iff L hw hz).mpr (Or.inl hd)
    have hP' : ℘'[L] z = ℘'[L] w := by
      have := derivWeierstrassP_add_mem L w hd
      rwa [show w + (z - w) = z by ring] at this
    have h2 : 2 * z ∉ L.lattice := by
      intro h
      apply hzw
      have := sub_mem h hd
      rwa [show 2 * z - (z - w) = z + w by ring] at this
    have hne := derivWeierstrassP_ne_zero L h2
    have hy : ℘'[L] z / 2 ≠ (curveA L).negY (℘[L] w) (℘'[L] w / 2) := by
      rw [negY, ← hP']
      simp only [curveA, curve, zero_mul, sub_zero]
      intro h
      apply hne
      linear_combination h
    rw [Point.add_of_Y_ne hy]
    have hzw' : z + w = 2 * z + (w - z) := by ring
    have hwz : w - z ∈ L.lattice := by simpa using neg_mem hd
    have hsl : (curveA L).slope (℘[L] z) (℘[L] w) (℘'[L] z / 2) (℘'[L] w / 2) =
        tangentSlope L z / 2 := by
      rw [slope_of_Y_ne hP hy, negY]
      simp only [curveA, curve, zero_mul, sub_zero, mul_zero, add_zero]
      unfold tangentSlope
      field_simp
      ring
    have hx : ℘[L] (z + w) = ℘[L] (2 * z) := by rw [hzw', weierstrassP_add_mem L _ hwz]
    have hy' : ℘'[L] (z + w) = ℘'[L] (2 * z) := by rw [hzw', derivWeierstrassP_add_mem L _ hwz]
    have hdx := weierstrassP_two_mul L h2
    have hdy := derivWeierstrassP_two_mul L h2
    refine some_eq_some L ?_ ?_
    · rw [addX, hsl, hx, hdx, ← hP]
      simp only [curveA, curve]
      ring
    · rw [addY, negAddY, addX, negY, hsl, hy', hdy, hdx, ← hP]
      simp only [curveA, curve]
      ring
  · 
    have hdw : z - w ∉ L.lattice := hd
    have hne := pdiff_ne L hz hw hzw hdw
    have hx : ℘[L] z ≠ ℘[L] w := sub_ne_zero.mp hne
    rw [Point.add_of_X_ne hx]
    have hsl : (curveA L).slope (℘[L] z) (℘[L] w) (℘'[L] z / 2) (℘'[L] w / 2) =
        chordSlope L z w / 2 := by
      rw [slope_of_X_ne hx]
      unfold chordSlope
      field_simp
    have hax := weierstrassP_add L hz hw hzw hdw
    have hay := derivWeierstrassP_add L hz hw hzw hdw
    refine some_eq_some L ?_ ?_
    · rw [addX, hsl, hax]
      simp only [curveA, curve]
      ring
    · rw [addY, negAddY, addX, negY, hsl, hay, hax]
      simp only [curveA, curve]
      ring
 
def expHom : ℂ →+ (curveA L).Point where
  toFun := expE L
  map_zero' := expE_zero L
  map_add' := expE_add L
@[simp] lemma expHom_apply (z : ℂ) : expHom L z = expE L z := rfl
lemma expE_intCast_mul (n : ℤ) (z : ℂ) : expE L (n * z) = n • expE L z := by
  rw [← expHom_apply, ← zsmul_eq_mul, map_zsmul, expHom_apply]
section Rational
variable (K : Subfield ℂ) (h₂ : L.g₂ ∈ K)
end Rational
end LSG.Weierstrass
end
end

/- TunnellCMModelUnit -/
section
namespace TunnellCMModelUnit
open WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open IsLocalRing NumberField TunnellCMLocalUnit TunnellCMUnitCriterion
open scoped NumberField
variable {F : Type*} [Field F] {W : WeierstrassCurve F}
def X : W.toAffine.Point → F
  | .zero => 0
  | .some x _ _ => x
def Y : W.toAffine.Point → F
  | .zero => 0
  | .some _ y _ => y
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [CharZero K]
  [Algebra R K] [IsFractionRing R K] {v : HeightOneSpectrum R}
end TunnellCMModelUnit
end

/- TunnellCMGlobalModelUnit -/
section
namespace TunnellCMGlobalModelUnit
open WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open IsLocalRing NumberField TunnellCMModelUnit TunnellCMUnitCriterion
open scoped NumberField
variable {F : Type*} [Field F] (W : WeierstrassCurve F) (L : Type*) [Field L] [Algebra F L]
  [DecidableEq F] [DecidableEq L]
theorem base_self : W.baseChange F = W := by
  change W.map (algebraMap F F) = W
  rw [Algebra.algebraMap_self,W.map_id]
noncomputable def pointMap : W.toAffine.Point →+ (W.baseChange L).toAffine.Point :=
  (Point.map (W' := W.toAffine) (Algebra.ofId F L)).comp
    (Point.equivOfEq (base_self W).symm).toAddMonoidHom
theorem pointMap_inj : Function.Injective (pointMap W L) :=
  (Point.map_injective _).comp (Point.equivOfEq _).injective
theorem x_map (P : W.toAffine.Point) :
    X (pointMap W L P) = algebraMap F L (X P) := by
  cases P with
  | zero => change X (pointMap W L 0) = algebraMap F L 0; rw [map_zero,map_zero]; rfl
  | some x y h =>
    simp only [pointMap,AddMonoidHom.comp_apply,AddEquiv.coe_toAddMonoidHom,Point.equivOfEq_some,Point.map_some]
    rfl
variable {K : Type*} [Field K] [NumberField K]
end TunnellCMGlobalModelUnit
end

/- TunnellCoates -/
section
namespace TunnellCoates
open WeierstrassCurve WeierstrassCurve.Affine
def E {K : Type*} [CommRing K] (n : K) : WeierstrassCurve K := ⟨0,0,0,-n^2,0⟩
end TunnellCoates
end

/- TunnellCMAbsoluteUnit -/
section
namespace TunnellCMAbsoluteUnit
open WeierstrassCurve WeierstrassCurve.Affine NumberField TunnellCoates
open TunnellCMModelUnit TunnellCMGlobalModelUnit TunnellCMGoodDescent
open scoped NumberField
noncomputable section
variable (F B : Type*) [Field F] [Field B] [Algebra F B] [DecidableEq F] [DecidableEq B]
lemma eq_E (n : ℕ) : (E (n:F)).baseChange B = E (n:B) := by
  ext <;> simp [WeierstrassCurve.baseChange,E]
def mapPoint (n : ℕ) : (E (n:F)).toAffine.Point →+ (E (n:B)).toAffine.Point :=
  (Point.equivOfEq (eq_E F B n)).toAddMonoidHom.comp (pointMap (E (n:F)) B)
lemma mapPoint_injective (n : ℕ) : Function.Injective (mapPoint F B n) :=
  (Point.equivOfEq _).injective.comp (pointMap_inj _ B)
lemma x_equality {W W' : WeierstrassCurve B} (h : W=W') (P : W.toAffine.Point) :
    X (Point.equivOfEq h P) = X P := by subst W'; rfl
lemma x_point (n : ℕ) (P : (E (n:F)).toAffine.Point) :
    X (mapPoint F B n P) = algebraMap F B (X P) := by
  exact (x_equality B _ _).trans (x_map _ B P)
variable {B} [CharZero B] (K : IntermediateField ℚ B) [DecidableEq K]
lemma lift_point (n : ℕ) (P : (E (n:B)).toAffine.Point) (hx : X P ∈ K) (hy : Y P ∈ K) :
    ∃ P' : (E (n:K)).toAffine.Point, mapPoint K B n P'=P := by
  cases P with
  | zero => exact ⟨0,map_zero _⟩
  | some x y hh =>
    let u : K := ⟨x,hx⟩
    let v : K := ⟨y,hy⟩
    have he := eq_E K B n
    have h : (E (n:K)).toAffine.Nonsingular u v := by
      apply ((E (n:K)).toAffine.map_nonsingular (f := algebraMap K B) (algebraMap K B).injective u v).mp
      change ((E (n:K)).baseChange B).toAffine.Nonsingular x y
      rw [he]; exact hh
    refine ⟨.some u v h,?_⟩
    simp only [mapPoint,pointMap,AddMonoidHom.comp_apply,AddEquiv.coe_toAddMonoidHom,
      Point.equivOfEq_some,Point.map_some]
    rfl
end
end TunnellCMAbsoluteUnit
end

/- TunnellGaussian -/
section
namespace TunnellGaussian
open GaussianInt
def Primary (z : GaussianInt) : Prop := (⟨2,2⟩ : GaussianInt) ∣ z-1
lemma primary_iff (z : GaussianInt) :
    Primary z ↔ z.im % 2 = 0 ∧ (z.re + z.im) % 4 = 1 := by
  constructor
  · rintro ⟨⟨u,v⟩,h⟩
    have ha := congrArg Zsqrtd.re h
    have hb := congrArg Zsqrtd.im h
    change z.re - 1 = 2*u + -1*2*v at ha
    change z.im - 0 = 2*v + 2*u at hb
    omega
  · rintro ⟨h₁,h₂⟩
    refine ⟨⟨(z.re + z.im - 1)/4, (z.im - z.re + 1)/4⟩, ?_⟩
    ext
    · change z.re - 1 = 2*((z.re + z.im - 1)/4) + -1*2*((z.im - z.re + 1)/4)
      omega
    · change z.im - 0 = 2*((z.im - z.re + 1)/4) + 2*((z.re + z.im - 1)/4)
      omega
lemma primary_mul_iff {z w : GaussianInt} (hz : Primary z) : Primary (z*w) ↔ Primary w := by
  have h : (⟨2,2⟩ : GaussianInt) ∣ (z-1)*w := dvd_mul_of_dvd_left hz _
  unfold Primary
  rw [show z*w - 1 = (z-1)*w + (w-1) by ring, dvd_add_right h]
lemma norm_sq (z : GaussianInt) : z.norm = z.re^2 + z.im^2 := by rw [Zsqrtd.norm_def]; ring
end TunnellGaussian
end

/- TunnellCMLComplete -/
section
namespace TunnellSplit
open Finset
open scoped ComplexConjugate
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end TunnellSplit
namespace TunnellInert
open Finset Polynomial
end TunnellInert
namespace TunnellSplitMass
open Finset TunnellGaussian
end TunnellSplitMass
namespace TunnellJacobiFiniteBridge
open Polynomial Finset
end TunnellJacobiFiniteBridge
namespace TunnellEtaLattice
open Finset TunnellGaussian
end TunnellEtaLattice
namespace TunnellQBin
open Polynomial Finset
variable {R : Type*} [CommRing R]
end TunnellQBin
namespace TunnellBalanced
open Finset
variable {K : Type*} [Field K]
end TunnellBalanced
namespace TunnellCubicFinite
open Finset Polynomial TunnellQBin
open LaurentPolynomial hiding C
end TunnellCubicFinite
namespace TunnellCubicFinite
open Polynomial Finset TunnellQBin
end TunnellCubicFinite
namespace TunnellTruncated
open TunnellQBin Polynomial Finset
variable {R : Type*} [CommRing R]
end TunnellTruncated
namespace TunnellArithmetic
open Polynomial Finset TunnellGaussian TunnellEtaLattice
end TunnellArithmetic
namespace TunnellCMLSeries
open Finset TunnellGaussian
noncomputable def twistSign (n m : ℕ) : ℤ := if Odd m then jacobiSym n m else 0
end TunnellCMLSeries
namespace TunnellCMLSeries
open TunnellGaussian OMA.R_CongruentNumber_Tunnell_even_R1 Finset
lemma twistSign_mul (n a b : ℕ) : twistSign n (a*b) = twistSign n a * twistSign n b := by
  by_cases ha : Odd a <;> by_cases hb : Odd b <;> simp [twistSign, Nat.odd_mul, ha, hb]
  exact jacobiSym.mul_right' _ (fun e => by simp [e] at ha) (fun e => by simp [e] at hb)
end TunnellCMLSeries
end

/- TunnellCMResidues -/
section
namespace TunnellCMLSeries
open TunnellGaussian Finset
abbrev Residues (n : ℕ) := ZMod (4*n) × ZMod (4*n)
def residue (n : ℕ) (z : GaussianInt) : Residues n := (z.re, z.im)
def liftResidue {n : ℕ} (r : Residues n) : GaussianInt := ⟨r.1.val,r.2.val⟩
lemma residue_lift {n : ℕ} (hn : 0<n) (r : Residues n) : residue n (liftResidue r) = r := by
  letI : NeZero (4*n) := ⟨by omega⟩
  simp [liftResidue,residue]
noncomputable def charWeight (n : ℕ) (z : GaussianInt) : ℤ := by
  classical exact if Primary z then twistSign n z.norm.natAbs else 0
lemma twistSign_mod (n m : ℕ) : twistSign n (m % (4*n)) = twistSign n m := by
  have he : Even (4*n) := Even.mul_right (by decide) _
  have h : Odd (m % (4*n)) ↔ Odd m := by
    simp only [Nat.odd_iff, Nat.mod_mod_of_dvd _ he.two_dvd]
  by_cases hm : Odd m
  · simpa [twistSign, h, hm] using (jacobiSym.mod_right' n hm).symm
  · simp [twistSign, h, hm]
theorem charWeight_residue (n : ℕ) {z w : GaussianInt} (h : residue n z = residue n w) :
    charWeight n z = charWeight n w := by
  have ha := (ZMod.intCast_eq_intCast_iff _ _ _).mp (congrArg Prod.fst h)
  have hb := (ZMod.intCast_eq_intCast_iff _ _ _).mp (congrArg Prod.snd h)
  change z.re ≡ w.re [ZMOD ↑(4*n)] at ha
  change z.im ≡ w.im [ZMOD ↑(4*n)] at hb
  have h2 : (2:ℤ) ∣ (↑(4*n) : ℤ) := by exact_mod_cast (dvd_mul_of_dvd_left (by decide : 2∣4) n)
  have h4 : (4:ℤ) ∣ (↑(4*n) : ℤ) := by exact_mod_cast dvd_mul_right 4 n
  have hpr : Primary z ↔ Primary w := by
    rw [primary_iff,primary_iff,(hb.of_dvd h2).eq,((ha.add hb).of_dvd h4).eq]
  have hnorm : (z.norm.natAbs : ℕ) ≡ w.norm.natAbs [MOD 4*n] := by
    apply Int.natCast_modEq_iff.mp
    rw [GaussianInt.natCast_natAbs_norm,GaussianInt.natCast_natAbs_norm,norm_sq,norm_sq]
    exact (ha.pow 2).add (hb.pow 2)
  classical
  simp only [charWeight,hpr]
  have he := (twistSign_mod n z.norm.natAbs).symm.trans ((congrArg (twistSign n) hnorm).trans (twistSign_mod n w.norm.natAbs))
  rw [he]
end TunnellCMLSeries
end

/- TunnellCMCritical -/
section
namespace TunnellCMCritical
open Complex Filter Set TunnellCMRegularized TunnellCMLSeries
open scoped Topology ComplexConjugate
noncomputable def aux (n : ℕ) := 1+3*(4*n)
end TunnellCMCritical
end

/- TunnellCMDistribution -/
section
namespace TunnellCMDistribution
open Complex Filter Set
open scoped Topology PeriodPair
abbrev Grid (a : ℕ) := Fin a × Fin a
noncomputable def liftGrid (L : PeriodPair) {a : ℕ} (j : Grid a) : ℂ :=
  ((j.1.val:ℂ)*L.ω₁+(j.2.val:ℂ)*L.ω₂)/(a:ℂ)
def regular (L : PeriodPair) (a : ℕ) := {z : ℂ | (a:ℂ)*z ∉ L.lattice}
lemma mul_lift (L : PeriodPair) {a : ℕ} [NeZero a] (j : Grid a) :
    (a:ℂ)*liftGrid L j ∈ L.lattice := by
  have ha : (a:ℂ)≠0 := by exact_mod_cast NeZero.ne a
  rw [liftGrid,← mul_div_assoc,mul_div_cancel_left₀ _ ha]
  exact PeriodPair.mem_lattice.mpr ⟨(j.1.val:ℤ),(j.2.val:ℤ),by simp⟩
lemma mul_mem (L : PeriodPair) (a : ℕ) {z : ℂ} (hz : z ∈ L.lattice) :
    (a:ℂ)*z ∈ L.lattice := by
  rw [← nsmul_eq_mul]
  exact L.lattice.nsmul_mem hz _
lemma sub_regular (L : PeriodPair) {a : ℕ} [NeZero a] {z : ℂ} (hz : z∈regular L a) (j : Grid a) :
    z-liftGrid L j ∉ L.lattice := fun h => hz (by simpa [mul_sub] using add_mem (mul_mem L a h) (mul_lift L j))
lemma add_regular (L : PeriodPair) {a : ℕ} [NeZero a] {z : ℂ} (hz : z∈regular L a) (j : Grid a) :
    z+liftGrid L j ∉ L.lattice := fun h => hz (by simpa [mul_add] using sub_mem (mul_mem L a h) (mul_lift L j))
open TunnellEllipticZeta
end TunnellCMDistribution
end

/- TunnellCMEllipticUnit -/
section
namespace TunnellCMEllipticUnit
open Complex Set Filter TunnellEllipticZeta TunnellCMDistribution
open scoped Topology PeriodPair
open LSG.Weierstrass (sigma sigma_identity logDeriv_sigma weierstrassP_eq_iff)
noncomputable def divisionGrid (L : PeriodPair) (a : ℕ) : Finset (Grid a) := by
  classical exact Finset.univ.filter (fun j => liftGrid L j ∉ L.lattice)
noncomputable def divisionProduct (L : PeriodPair) (a : ℕ) (z : ℂ) :=
  ∏ j ∈ divisionGrid L a, (L.weierstrassP z - L.weierstrassP (liftGrid L j))
end TunnellCMEllipticUnit
end

/- TunnellPeriod -/
section
namespace TunnellCoates
open MeasureTheory Set Filter
open scoped Topology
noncomputable def realPeriod (n : ℝ) : ℝ :=
  ∫ x in Ioi n, (Real.sqrt (x^3-n^2*x))⁻¹
end TunnellCoates
end

/- TunnellCMLemniscate -/
section
namespace TunnellCMLemniscate
open MeasureTheory Set Complex LSG.LemniscateIndep
open TunnellCoates
theorem period_one : realPeriod 1 = varpi := by
  let f (t : ℝ) := t⁻¹^2
  let D (t : ℝ) := -2/t^3
  have hd {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) : HasDerivAt f (D t) t := by
    apply (((hasDerivAt_id' t).inv ht.1.ne').pow 2).congr_deriv
    dsimp [D]
    field_simp
    <;> ring
  have hi : StrictAntiOn f (Ioo 0 1) := by
    intro t ht v hv he
    exact pow_lt_pow_left₀ (inv_lt_inv₀ hv.1 ht.1 |>.mpr he) (inv_nonneg.mpr hv.1.le) (by decide)
  have him : f '' Ioo (0:ℝ) 1=Ioi 1 := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      have hp : 1<t⁻¹ := (one_lt_inv₀ ht.1).mpr ht.2
      change 1<t⁻¹^2
      nlinarith
    · intro hx
      change 1<x at hx
      have hp : 1<Real.sqrt x := by simpa using Real.sqrt_lt_sqrt (by norm_num : (0:ℝ)≤1) hx
      refine ⟨(Real.sqrt x)⁻¹,⟨inv_pos.mpr (by linarith),(inv_lt_one₀ (by linarith)).mpr hp⟩,?_⟩
      simp [f,Real.sq_sqrt (by linarith : 0≤x)]
  let g (x : ℝ) := (Real.sqrt (x^3-x))⁻¹
  have e := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun t ht => (hd ht).hasDerivWithinAt) hi.injOn g
  rw [varpi_eq_integral,intervalIntegral.integral_of_le zero_le_one,integral_Ioc_eq_integral_Ioo,
    ← integral_const_mul]
  change (∫ x in Ioi 1, (Real.sqrt (x^3-(1:ℝ)^2*x))⁻¹)=_
  simp only [one_pow,one_mul]
  change (∫ x in Ioi 1, g x)=_
  rw [← him,e]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have ht0 := ht.1
  have he : (t⁻¹^2)^3-t⁻¹^2=(1-t^4)/(t^3)^2 := by field_simp <;> ring
  have hv : 0≤1-t^4 := by nlinarith [pow_le_pow_left₀ ht.1.le ht.2.le 4]
  change |(-2/t^3)| * (Real.sqrt ((t⁻¹^2)^3-t⁻¹^2))⁻¹=2*(1 / Real.sqrt (1-t^4))
  rw [he,Real.sqrt_div hv,Real.sqrt_sq (by positivity),abs_of_neg (div_neg_of_neg_of_pos (by norm_num : (-2:ℝ)<0) (pow_pos ht0 3))]
  field_simp
noncomputable def twistPeriods (n : ℕ) (hn : 0<n) : PeriodPair where
  ω₁ := (realPeriod n:ℂ)
  ω₂ := I * (realPeriod n:ℂ)
  indep := by
    have h : realPeriod n ≠ 0 := (realPeriod_pos (show (0:ℝ)<n by exact_mod_cast hn)).ne'
    apply LinearIndependent.pair_iff.mpr
    intro x y he
    have hr := congrArg re he
    have hi := congrArg im he
    simp [Complex.mul_re,Complex.mul_im,h] at hr hi
    exact ⟨hr,hi⟩
theorem g₂_twist (n : ℕ) (hn : 0<n) : (twistPeriods n hn).g₂ = 4*(n:ℂ)^2 := by
  have hpos : (0:ℝ)<n := by exact_mod_cast hn
  rw [Sq.g₂_eq_of_square (L := twistPeriods n hn) (a := realPeriod n)
      ⟨realPeriod_pos hpos,rfl,rfl⟩,(show realPeriod n=realPeriod 1/Real.sqrt n from realPeriod_eq hpos),period_one]
  have he : varpi/(varpi/Real.sqrt n)=Real.sqrt n := by field_simp [varpi_pos.ne']
  rw [he]
  have e := congrArg ((↑):ℝ→ℂ) (Real.sq_sqrt hpos.le)
  push_cast at e
  linear_combination 4*((Real.sqrt n:ℂ)^2+(n:ℂ))*e
theorem curve_eq (n : ℕ) (hn : 0<n) :
    LSG.Weierstrass.curve (twistPeriods n hn) = (⟨0,0,0,-(n:ℂ)^2,0⟩ : WeierstrassCurve ℂ) := by
  have hg := g₃_eq_zero_of_square (L := twistPeriods n hn) (a := realPeriod n) rfl rfl
  unfold LSG.Weierstrass.curve
  rw [g₂_twist,hg]
  congr 1 <;> ring
end TunnellCMLemniscate
end

/- TunnellCMWeights -/
section
namespace TunnellCMWeights
open TunnellCMLSeries TunnellGaussian
def mover (n : ℕ) : GaussianInt := ⟨1+n,n⟩
lemma mover_primary (n : ℕ) (hn : n%8=2) : Primary (mover n) := by
  rw [primary_iff]
  dsimp [mover]
  omega
lemma mover_norm (n : ℕ) : (mover n).norm.natAbs = 1 + 2*n + 2*n^2 := by
  rw [← Int.natCast_inj,GaussianInt.natCast_natAbs_norm,norm_sq]
  simp [mover]
  ring
lemma mover_sign (n : ℕ) (hn : n%8=2) : twistSign n (mover n).norm.natAbs = -1 := by
  let d := n/2
  have hd : d%4=1 := by dsimp [d]; omega
  have h₀ : n=2*d := by dsimp [d]; omega
  let m := 1 + 2*n + 2*n^2
  have hm8 : m%8=5 := by
    have e : n = 2+8*(n/8) := by omega
    dsimp [m]
    conv_lhs => rw [e]
    rw [show 1+2*(2+8*(n/8))+2*(2+8*(n/8))^2 =
        5+8*(1+10*(n/8)+16*(n/8)^2) by ring]
    simp
  have hm : Odd m := Nat.odd_iff.mpr (by omega)
  rw [mover_norm]
  change twistSign n m = -1
  rw [twistSign,if_pos hm,show (n:ℤ)=2*(d:ℤ) by exact_mod_cast h₀,
    jacobiSym.mul_left,jacobiSym.at_two hm,ZMod.χ₈_nat_mod_eight,hm8,
    jacobiSym.quadratic_reciprocity_one_mod_four hd hm]
  have he : (m:ℤ) % (d:ℤ) = 1 % (d:ℤ) := by
    dsimp [m]; rw [h₀]; push_cast
    rw [show (1+(2:ℤ)*(2*d)+2*(2*d)^2)=1+(4+8*d)*d by ring,Int.add_mul_emod_self_right]
  rw [jacobiSym.mod_left' he,jacobiSym.one_left]
  decide
lemma weight_move (n : ℕ) (hn : n%8=2) (x : GaussianInt) :
    charWeight n (mover n*x) = -charWeight n x := by
  classical
  simp only [charWeight,primary_mul_iff (mover_primary n hn),Zsqrtd.norm_mul,Int.natAbs_mul,
    twistSign_mul,mover_sign _ hn]
  split_ifs <;> ring
def forward (n : ℕ) (r : Residues n) : Residues n :=
  (r.1+n*(r.1-r.2), r.2+n*(r.1+r.2))
lemma forward_residue (n : ℕ) (x : GaussianInt) :
    residue n (mover n*x) = forward n (residue n x) := by
  ext <;> simp [residue,forward,mover] <;> ring
noncomputable def permutation (n : ℕ) (hn : n%8=2) : Equiv.Perm (Residues n) where
  toFun := forward n
  invFun := fun r => (r.1-n*(r.1-r.2), r.2-n*(r.1+r.2))
  left_inv := by
    have h : (2:ZMod (4*n))*n^2=0 := by
      have he : 2*n^2=(4*n)*(n/2) := by
        have e : n=2*(n/2) := by omega
        calc
          2*n^2 = 2*n*n := by ring
          _ = (4*n)*(n/2) := by nth_rw 2 [e]; ring
      exact_mod_cast (show ((2*n^2:ℕ):ZMod (4*n))=0 by rw [he,Nat.cast_mul,ZMod.natCast_self,zero_mul])
    intro r
    apply Prod.ext <;> dsimp [forward] <;>
      first | linear_combination r.2*h | linear_combination -r.1*h
  right_inv := by
    have h : (2:ZMod (4*n))*n^2=0 := by
      have he : 2*n^2=(4*n)*(n/2) := by
        have e : n=2*(n/2) := by omega
        calc
          2*n^2 = 2*n*n := by ring
          _ = (4*n)*(n/2) := by nth_rw 2 [e]; ring
      exact_mod_cast (show ((2*n^2:ℕ):ZMod (4*n))=0 by rw [he,Nat.cast_mul,ZMod.natCast_self,zero_mul])
    intro r
    apply Prod.ext <;> dsimp [forward] <;>
      first | linear_combination r.2*h | linear_combination -r.1*h
theorem weight_sum_zero (n : ℕ) (hn : n%8=2) :
    letI : NeZero (4*n) := ⟨by omega⟩
    ∑ r : Residues n, charWeight n (liftResidue r) = 0 := by
  letI : NeZero (4*n) := ⟨by omega⟩
  have hp : 0<n := by omega
  have e (r : Residues n) : charWeight n (liftResidue (permutation n hn r)) = -charWeight n (liftResidue r) := by
    rw [← weight_move n hn]
    apply charWeight_residue
    rw [residue_lift hp,forward_residue,residue_lift hp]
    rfl
  have h := Equiv.sum_comp (permutation n hn) (fun r => charWeight n (liftResidue r))
  simp only [e,Finset.sum_neg_distrib] at h
  omega
end TunnellCMWeights
end

/- TunnellCMUnitTrace -/
section
namespace TunnellCMUnitTrace
open Complex Finset TunnellCMLSeries TunnellCMCritical TunnellCMLemniscate
open TunnellCMEllipticUnit TunnellCMDistribution TunnellEllipticZeta TunnellCoates
open scoped ComplexConjugate
noncomputable def dilation (n : ℕ) : ℝ := realPeriod n / (4*n)
noncomputable def point (n : ℕ) (r : Residues n) : ℂ := (dilation n:ℂ)*(liftResidue r:ℂ)
noncomputable def weight (n : ℕ) (r : Residues n) := charWeight n (liftResidue r)
noncomputable def traceUnit (n : ℕ) (hn : 0<n) (Z : ℂ) : ℂ := by
  classical
  letI : NeZero (4*n) := ⟨by omega⟩
  exact ∏ r ∈ univ.filter (fun r => weight n r ≠ 0),
    divisionProduct (twistPeriods n hn) (aux n) (Z+point n r) ^ weight n r
lemma division_nonzero (M : PeriodPair) (a : ℕ) [NeZero a] {z : ℂ} (hz : z∈regular M a) :
    divisionProduct M a z ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hs : z∉M.lattice := fun h => hz (mul_mem M a h)
  have ht : liftGrid M j∉M.lattice := (Finset.mem_filter.mp hj).2
  exact sub_ne_zero.mpr (fun h => ((LSG.Weierstrass.weierstrassP_eq_iff M ht hs).mp h).elim
    (sub_regular M hz j) (add_regular M hz j))
end TunnellCMUnitTrace
end

/- TunnellCMTranscendental -/
section
namespace TunnellCMTranscendental
open Polynomial Set Complex LSG.Weierstrass
abbrev F := RatFunc ℚ
abbrev K := AlgebraicClosure F
noncomputable section
local instance : DecidableEq K := Classical.decEq _
noncomputable def Xgeneric : K := algebraMap F K RatFunc.X
lemma specialize {x : ℂ} (hx : Transcendental ℚ x) : ∃ φ : K →ₐ[ℚ] ℂ, φ Xgeneric=x := by
  let h : F →ₐ[ℚ] ℂ := IsFractionRing.liftAlgHom (transcendental_iff_injective.mp hx)
  obtain ⟨φ,hφ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := ℚ) (L := F)
    (E := K) (M := ℂ) h
  refine ⟨φ,?_⟩
  change φ.domRestrict F RatFunc.X = x
  change φ.domRestrict F = h at hφ
  rw [hφ,← RatFunc.algebraMap_X]
  simp only [h,IsFractionRing.liftAlgHom_apply,IsFractionRing.lift_algebraMap]
  exact aeval_X x
lemma values_fiber_countable (M : PeriodPair) (x : ℂ) :
    {z : ℂ | z∉M.lattice ∧ M.weierstrassP z=x}.Countable := by
  by_cases h : ∃ b : ℂ, b∉M.lattice ∧ M.weierstrassP b=x
  · obtain ⟨b,hb,rfl⟩ := h
    have hc := lattice_countable M
    refine ((hc.image (fun l : ℂ => l+b)).union (hc.image (fun l : ℂ => l-b))).mono ?_
    rintro z ⟨hz,he⟩
    rcases (weierstrassP_eq_iff M hb hz).mp he with h|h
    · exact Or.inl ⟨z-b,h,sub_add_cancel _ _⟩
    · exact Or.inr ⟨z+b,h,add_sub_cancel_right _ _⟩
  · apply countable_empty.mono
    exact fun z hz => (h ⟨z,hz⟩).elim
lemma generic_analytic_point (M : PeriodPair) (a : ℕ) (ha : 0<a) :
    ∃ z : ℂ, z∉M.lattice ∧ (a:ℂ)*z∉M.lattice ∧ Transcendental ℚ (M.weierstrassP z) := by
  let bad := ⋃ x ∈ {x : ℂ | IsAlgebraic ℚ x}, {z : ℂ | z∉M.lattice ∧ M.weierstrassP z=x}
  have hc : bad.Countable := (Algebraic.countable ℚ ℂ).biUnion (fun x _ => values_fiber_countable M x)
  have hn : (a:ℂ)≠0 := by exact_mod_cast ha.ne'
  have hD := (lattice_countable M).preimage (mul_right_injective₀ hn)
  let B := (bad ∪ (M.lattice : Set ℂ)) ∪ (fun x : ℂ => (a:ℂ)*x) ⁻¹' (M.lattice : Set ℂ)
  let : Uncountable ℂ := Complex.ofReal_injective.uncountable
  have hb : B.Countable := (hc.union (lattice_countable M)).union hD
  obtain ⟨z,hz⟩ : ∃ z, z∉B := by
    by_contra! h
    exact not_countable_univ (α := ℂ) (hb.mono (fun z _ => h z))
  have h1 : z ∉ M.lattice := fun h => hz (Or.inl (Or.inr h))
  refine ⟨z,h1,fun h => hz (Or.inr h),fun he => hz (Or.inl (Or.inl ?_))⟩
  exact mem_iUnion₂.mpr ⟨_,he,h1,rfl⟩
noncomputable def E (n : ℕ) : WeierstrassCurve ℚ := ⟨0,0,0,-(n:ℚ)^2,0⟩
lemma model (n : ℕ) (k : Type*) [Field k] [CharZero k] :
    (E n).baseChange k = (⟨0,0,0,-(n:k)^2,0⟩ : WeierstrassCurve k) := by
  ext <;> simp [E,WeierstrassCurve.baseChange]
instance elliptic (n : ℕ) [NeZero n] : (E n).IsElliptic := by
  constructor
  have hn : (n:ℚ)≠0 := by exact_mod_cast NeZero.ne n
  have h : (E n).Δ=64*(n:ℚ)^6 := by
    simp [E,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,
      WeierstrassCurve.b₆,WeierstrassCurve.b₈]
    ring
  rw [h]
  exact isUnit_iff_ne_zero.mpr (mul_ne_zero (by norm_num) (pow_ne_zero _ hn))
noncomputable def Ygeneric (n : ℕ) : K :=
  (IsAlgClosed.exists_pow_nat_eq (Xgeneric^3-(n:K)^2*Xgeneric) zero_lt_two).choose
lemma generic_nonsingular (n : ℕ) [NeZero n] :
    ((E n).baseChange K).toAffine.Nonsingular Xgeneric (Ygeneric n) := by
  letI : ((E n).baseChange K).IsElliptic :=
    inferInstanceAs (((E n).map (algebraMap ℚ K)).IsElliptic)
  apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff,model]
  have hY : Ygeneric n^2 = Xgeneric^3-(n:K)^2*Xgeneric :=
    (IsAlgClosed.exists_pow_nat_eq (Xgeneric^3-(n:K)^2*Xgeneric) zero_lt_two).choose_spec
  simpa only [zero_mul,zero_add,mul_zero,add_zero,neg_mul,sub_eq_add_neg] using hY
noncomputable def genericPoint (n : ℕ) [NeZero n] : ((E n).baseChange K).toAffine.Point :=
  .some _ _ (generic_nonsingular n)
open WeierstrassCurve.Affine (Point)
lemma generic_killed_iff (n a : ℕ) [NeZero n] {x y : ℂ} (hx : Transcendental ℚ x)
    (h : ((E n).baseChange ℂ).toAffine.Nonsingular x y) :
    a • genericPoint n = 0 ↔ a • (Point.some x y h) = 0 := by
  classical
  obtain ⟨φ,hφ⟩ := specialize hx
  let m := Point.map (W' := (E n).toAffine) φ
  have he : a • genericPoint n=0 ↔ a • m (genericPoint n)=0 := by
    rw [← map_nsmul,← map_zero m]
    exact (Point.map_injective (W' := (E n).toAffine) φ).eq_iff.symm
  rw [he]
  have e := (Point.X_eq_iff (h₁ := (((E n).toAffine.baseChange_nonsingular φ.injective ..).mpr
    (generic_nonsingular n))) (h₂ := h)).mp hφ
  change m (genericPoint n)=Point.some x y h ∨ m (genericPoint n)= -Point.some x y h at e
  rcases e with e|e
  · rw [e]
  · rw [e,smul_neg,neg_eq_zero]
noncomputable def killedAt (W : WeierstrassCurve ℂ) (a : ℕ) (x : ℂ) : Prop :=
  ∃ y, ∃ h : W.toAffine.Nonsingular x y, a • Point.some x y h=0
lemma uniform_killed (n a : ℕ) [NeZero n] {x : ℂ} (hx : Transcendental ℚ x)
    (h : killedAt ((E n).baseChange ℂ) a x) :
    ∀ {x' y' : ℂ}, Transcendental ℚ x' →
      ∀ h' : ((E n).baseChange ℂ).toAffine.Nonsingular x' y', a • Point.some x' y' h'=0 := by
  obtain ⟨y,h,he⟩ := h
  intro x' y' hx' h'
  exact (generic_killed_iff n a hx' h').mp ((generic_killed_iff n a hx h).mpr he)
lemma analytic_killed (M : PeriodPair) (a : ℕ) (z : ℂ) :
    a • expE M z = 0 ↔ (a:ℂ)*z ∈ M.lattice := by
  have e : expE M ((a:ℂ)*z) = a • expE M z := by
    simpa only [Int.cast_natCast,natCast_zsmul] using expE_intCast_mul M (a:ℤ) z
  rw [← e]
  by_cases h : (a:ℂ)*z∈M.lattice
  · simp [h,expE_of_mem M h]
  · rw [expE_of_notMem M h]
    simp [h]
theorem torsion_x_algebraic (n a : ℕ) (hn : 0<n) (ha : 0<a) {x : ℂ}
    (h : killedAt ((E n).baseChange ℂ) a x) : IsAlgebraic ℚ x := by
  classical
  by_contra hx
  letI : NeZero n := ⟨hn.ne'⟩
  let M := TunnellCMLemniscate.twistPeriods n hn
  have eqM : (E n).baseChange ℂ = curve M :=
    (model n ℂ).trans (TunnellCMLemniscate.curve_eq n hn).symm
  obtain ⟨v,hv,hav,hxv⟩ := generic_analytic_point M a ha
  have all := @uniform_killed n a _ x hx h
  rw [eqM] at all
  have hp := all hxv (nonsingular_weierstrassP M hv)
  rw [← expE_of_notMem M hv,analytic_killed] at hp
  exact hav hp
theorem division_x_algebraic (n a : ℕ) (hn : 0<n) (ha : 0<a) {z : ℂ}
    (hz : z∉(TunnellCMLemniscate.twistPeriods n hn).lattice)
    (haz : (a:ℂ)*z∈(TunnellCMLemniscate.twistPeriods n hn).lattice) :
    IsAlgebraic ℚ ((TunnellCMLemniscate.twistPeriods n hn).weierstrassP z) := by
  let M := TunnellCMLemniscate.twistPeriods n hn
  apply torsion_x_algebraic n a hn ha
  rw [(model n ℂ).trans (TunnellCMLemniscate.curve_eq n hn).symm]
  refine ⟨_,nonsingular_weierstrassP M hz,?_⟩
  rw [← expE_of_notMem M hz,analytic_killed]
  exact haz
end
end TunnellCMTranscendental
end

/- TunnellCMAlgebraicUnits -/
section
namespace TunnellCMAlgebraicUnits
open Complex LSG.Weierstrass TunnellCMLemniscate TunnellCMDistribution TunnellCMUnitTrace
open TunnellCMEllipticUnit TunnellCoates TunnellCMLSeries TunnellCMCritical
variable (n : ℕ) (hn : 0<n)
lemma wp_mem {z : ℂ} {m : ℕ} (hm : 0 < m) (h : (m:ℂ)*z∈((twistPeriods n hn)).lattice) :
    ((twistPeriods n hn)).weierstrassP z ∈ (algebraicClosure ℚ ℂ) := by
  by_cases hz : z∈((twistPeriods n hn)).lattice
  · rw [show ((twistPeriods n hn)).weierstrassP z=0 from ((twistPeriods n hn)).weierstrassP_coe ⟨z,hz⟩]
    exact ((algebraicClosure ℚ ℂ)).zero_mem
  exact mem_algebraicClosure_iff.mpr (TunnellCMTranscendental.division_x_algebraic n m hn hm hz h)
lemma y_mem {z : ℂ} {m : ℕ} (hm : 0 < m) (h : (m:ℂ)*z∈((twistPeriods n hn)).lattice) (hz : z∉((twistPeriods n hn)).lattice) :
    ((twistPeriods n hn)).derivWeierstrassP z/2 ∈ (algebraicClosure ℚ ℂ) := by
  have hX := wp_mem n hn hm h
  apply mem_algebraicClosure_iff.mpr
  apply IsAlgebraic.of_pow (n := 2) (by decide)
  have e := equation_weierstrassP (twistPeriods n hn) hz
  change (curve (twistPeriods n hn)).toAffine.Equation _ _ at e
  rw [curve_eq] at e
  rw [(TunnellCoates.E_equation (n:ℂ) _ _).mp e]
  exact mem_algebraicClosure_iff.mp (((algebraicClosure ℚ ℂ)).sub_mem (((algebraicClosure ℚ ℂ)).pow_mem hX (3:ℕ)) (((algebraicClosure ℚ ℂ)).mul_mem (((algebraicClosure ℚ ℂ)).pow_mem (((algebraicClosure ℚ ℂ)).natCast_mem n) 2) hX))
lemma conductor_point (r : Residues n) : ((4*n:ℕ):ℂ)*point n r∈((twistPeriods n hn)).lattice := by
  apply PeriodPair.mem_lattice.mpr
  let g := liftResidue r
  refine ⟨g.re,g.im,?_⟩
  change (g.re:ℂ)*(realPeriod n:ℂ)+g.im*(I*(realPeriod n:ℂ))= ((4*n:ℕ):ℂ)*((dilation n:ℂ)*(g:ℂ))
  rw [GaussianInt.toComplex_def]
  dsimp [dilation]
  push_cast
  have hN : (n:ℂ)≠0 := by exact_mod_cast hn.ne'
  field_simp [hN]
  <;> ring
end TunnellCMAlgebraicUnits
end

/- TunnellCMConductorOrder -/
section
namespace TunnellCMConductorOrder
open Complex LSG.Weierstrass LSG.LemniscateIndep TunnellCMLemniscate TunnellCMDistribution
open TunnellCMUnitTrace TunnellCMLSeries TunnellCMCritical TunnellCoates TunnellGaussian
lemma weight_coprime {n : ℕ} (r : Residues n) (hr : weight n r≠0) :
    (liftResidue r).norm.natAbs.Coprime (4*n) := by
  classical
  let g := liftResidue r
  change charWeight n g≠0 at hr
  have hp : Primary g := by by_contra h; exact hr (by simp [charWeight,h])
  have ho : Odd g.norm.natAbs := by by_contra h; exact hr (by simp [charWeight,hp,twistSign,h])
  have hn : jacobiSym n g.norm.natAbs≠0 := by simpa [charWeight,hp,twistSign,ho] using hr
  have hg : g.norm.natAbs≠0 := by intro h; rw [h] at ho; simpa using ho
  letI : NeZero g.norm.natAbs := ⟨hg⟩
  have e : (n:ℤ).gcd g.norm.natAbs=1 := by by_contra hh; exact hn (jacobiSym.eq_zero_iff_not_coprime.mpr hh)
  have ec : n.Coprime g.norm.natAbs := by simpa [Int.gcd_eq_natAbs] using e
  exact Nat.coprime_mul_iff_right.mpr ⟨by simpa using ho.coprime_two_right.pow_right 2,ec.symm⟩
variable (n : ℕ) (hn : 0<n)
theorem conductor_order (r : Residues n) (hr : weight n r≠0) :
    addOrderOf (expE (twistPeriods n hn) (point n r))=4*n := by
  let g := liftResidue r
  let f := 4*n
  have hf : (f:ℂ)≠0 := by exact_mod_cast (show f≠0 by dsimp [f]; omega)
  have hω : (realPeriod n:ℂ)≠0 := ofReal_ne_zero.mpr (realPeriod_pos (by exact_mod_cast hn)).ne'
  have hpt : point n r=(realPeriod n:ℂ)*(g:ℂ)/(f:ℂ) := by
    dsimp [f,point,dilation,g]
    push_cast
    ring
  have hg : IsCoprime g (f:GaussianInt) := by
    have h := (weight_coprime r hr).isCoprime.map (Int.castRingHom GaussianInt)
    have hg0 : g∣(g.norm.natAbs:GaussianInt) := by
      rw [GaussianInt.natCast_natAbs_norm,Zsqrtd.norm_eq_mul_conj]
      exact dvd_mul_right _ _
    apply IsCoprime.of_isCoprime_of_dvd_left _ hg0
    simpa [g,f] using h
  apply Nat.dvd_antisymm
  · apply addOrderOf_dvd_of_nsmul_eq_zero
    apply (TunnellCMTranscendental.analytic_killed (twistPeriods n hn) _ _).mpr
    exact TunnellCMAlgebraicUnits.conductor_point n hn r
  · let k := addOrderOf (expE (twistPeriods n hn) (point n r))
    have e := (TunnellCMTranscendental.analytic_killed (twistPeriods n hn) k _).mp (addOrderOf_nsmul_eq_zero _)
    rw [hpt,mem_lattice_sq (a := realPeriod n) rfl rfl] at e
    obtain ⟨u,v,he⟩ := e
    let b : GaussianInt := ⟨u,v⟩
    have hd : (f:GaussianInt)∣(k:GaussianInt)*g := by
      refine ⟨b,GaussianInt.toComplex_inj.mp ?_⟩
      change GaussianInt.toComplex _=GaussianInt.toComplex _
      rw [map_mul,map_mul,map_natCast,map_natCast]
      change (k:ℂ)*(g:ℂ)=(f:ℂ)*(b:ℂ)
      rw [GaussianInt.toComplex_def' u v]
      field_simp [hf] at he
      simpa only [mul_comm] using he.symm
    have e' := hg.symm.dvd_of_dvd_mul_right hd
    obtain ⟨b,hb⟩ := e'
    have hh : (k:ℤ)=(f:ℤ)*b.re := by simpa using congrArg Zsqrtd.re hb
    exact_mod_cast (show (f:ℤ)∣(k:ℤ) from ⟨_,hh⟩)
end TunnellCMConductorOrder
end

/- TunnellCMTorsionOrder -/
section
namespace TunnellCMTorsionOrder
open Complex LSG.Weierstrass LSG.LemniscateIndep TunnellCMToricDivision TunnellCMLemniscate TunnellCoates
variable (n : ℕ) (hn : 0<n)
lemma zero_iff (z : ℂ) : expE (twistPeriods n hn) z=0 ↔ z∈((twistPeriods n hn)).lattice := by
  by_cases h : z∈((twistPeriods n hn)).lattice
  · simp [expE_of_mem (twistPeriods n hn) h,h]
  · simp [expE_of_notMem (twistPeriods n hn) h,h]
end TunnellCMTorsionOrder
end

/- TunnellCMCriticalIntegers -/
section
namespace TunnellCMCriticalIntegers
open WeierstrassCurve WeierstrassCurve.Affine NumberField Complex LSG.Weierstrass
open TunnellCoates TunnellCMLemniscate TunnellCMDistribution TunnellCMEllipticUnit
open TunnellCMCritical TunnellCMUnitTrace TunnellCMLSeries TunnellCMModelUnit TunnellCMAbsoluteUnit
open TunnellCMNormDistribution TunnellCMAlgebraicUnits
open scoped NumberField
noncomputable section
variable (n : ℕ) (hn : 0<n)
lemma model_eq : curve (twistPeriods n hn) = E (n:ℂ) := curve_eq n hn
def uniformize : ℂ →+ (E (n:ℂ)).toAffine.Point :=
  (Point.equivOfEq (model_eq n hn)).toAddMonoidHom.comp (expHom (twistPeriods n hn))
lemma uniformize_apply (z : ℂ) : uniformize n hn z = Point.equivOfEq (model_eq n hn) (expE (twistPeriods n hn) z) := rfl
lemma x_uniformize (z : ℂ) : X (uniformize n hn z) = ((twistPeriods n hn)).weierstrassP z := by
  rw [uniformize_apply,x_equality]
  by_cases h : z ∈ ((twistPeriods n hn)).lattice
  · rw [expE_of_mem (twistPeriods n hn) h,((twistPeriods n hn)).weierstrassP_coe ⟨z,h⟩]; rfl
  · rw [expE_of_notMem (twistPeriods n hn) h]; rfl
lemma torsion_lift {z : ℂ} {m : ℕ} (hm : 0 < m) (h : (m:ℂ)*z ∈ ((twistPeriods n hn)).lattice) :
    ∃ P : (E (n:(algebraicClosure ℚ ℂ))).toAffine.Point, mapPoint (algebraicClosure ℚ ℂ) ℂ n P=uniformize n hn z := by
  apply lift_point
  · rw [x_uniformize]; exact wp_mem n hn hm h
  · by_cases h' : z ∈ ((twistPeriods n hn)).lattice
    · rw [uniformize_apply,expE_of_mem (twistPeriods n hn) h',map_zero]
      exact ((algebraicClosure ℚ ℂ)).zero_mem
    · rw [uniformize_apply,expE_of_notMem (twistPeriods n hn) h',Point.equivOfEq_some]
      exact y_mem n hn hm h h'
lemma killed {m : ℕ} {z : ℂ} (h : (m:ℂ)*z ∈ ((twistPeriods n hn)).lattice) : m • uniformize n hn z=0 := by
  rw [← map_nsmul,nsmul_eq_mul,uniformize_apply,expE_of_mem (twistPeriods n hn) h,map_zero]
end
end TunnellCMCriticalIntegers
end

/- TunnellCMPrimeToConductor -/
section
namespace TunnellCMPrimeToConductor
open Complex LSG.Weierstrass TunnellCMLemniscate TunnellCMDistribution TunnellCMEllipticUnit
open TunnellCMCritical TunnellCMLSeries TunnellCMUnitTrace TunnellCMNormDistribution
open TunnellCMTraceDistribution TunnellCMCriticalIntegers TunnellCMToricDivision
open scoped NumberField
noncomputable section
variable (n : ℕ) (hn : 0<n)
theorem translated_regular {m : ℕ} (hc : (4*n).Coprime (aux n*m))
    {z : ℂ} (hz : (m:ℂ)*z∈((twistPeriods n hn)).lattice) (i : Residues n) (hi : weight n i≠0) :
    z+point n i∈regular (twistPeriods n hn) (aux n) := by
  intro hbad
  have h := (TunnellCMTranscendental.analytic_killed (twistPeriods n hn) _ _).mpr hbad
  have h' := congrArg (m • ·) h
  have hZ := (TunnellCMTranscendental.analytic_killed (twistPeriods n hn) _ _).mpr hz
  have hz' : (aux n*m) • expE (twistPeriods n hn) z=0 := by rw [← smul_smul,hZ,nsmul_zero]
  have H : (aux n*m) • expE (twistPeriods n hn) (point n i)=0 := by
    simpa only [expE_add,← mul_nsmul,mul_comm m (aux n),nsmul_add,hz',zero_add,nsmul_zero] using h'
  have hd := addOrderOf_dvd_of_nsmul_eq_zero H
  rw [TunnellCMConductorOrder.conductor_order n hn i hi] at hd
  have he := hc.gcd_eq_one
  rw [Nat.gcd_eq_left hd] at he
  omega
end
end TunnellCMPrimeToConductor
end

/- TunnellPublicUnitRepresentation -/
section
namespace TunnellPublicUnitRepresentation
open WeierstrassCurve WeierstrassCurve.Affine NumberField Complex LSG.Weierstrass
open TunnellCoates TunnellCMLemniscate TunnellCMDistribution TunnellCMEllipticUnit
open TunnellCMCritical TunnellCMUnitTrace TunnellCMLSeries TunnellCMModelUnit TunnellCMAbsoluteUnit
open TunnellCMNormDistribution TunnellCMAlgebraicUnits TunnellCMCriticalIntegers
open scoped NumberField
noncomputable section
open Complex NumberField IsDedekindDomain IntermediateField IsLocalRing Set MeasureTheory
open scoped Classical NumberField
def Representation : Prop :=
  ∀ (n : ℕ) (hn : 0<n),
  letI : NeZero (4*n) := ⟨Nat.ne_of_gt (Nat.mul_pos (by decide) hn)⟩
  let a := 1+3*(4*n)
  let ω : ℝ := (∫ x in Ioi (n:ℝ), (Real.sqrt (x^3-(n:ℝ)^2*x))⁻¹)
  let b (v : ZMod (4*n) × ZMod (4*n)) : GaussianInt := ⟨v.1.val,v.2.val⟩
  let χ (v : ZMod (4*n) × ZMod (4*n)) : ℤ :=
    let m := (b v).norm.natAbs
    if (⟨2,2⟩:GaussianInt) ∣ b v-1 then (if Odd m then jacobiSym n m else 0) else 0
  ∀ M : PeriodPair, M.ω₁=(ω:ℂ) → M.ω₂=Complex.I*(ω:ℂ) →
  let t (j : Fin a × Fin a) : ℂ := ((j.1.val:ℂ)*M.ω₁+(j.2.val:ℂ)*M.ω₂)/(a:ℂ)
  let D (z : ℂ) := ∏ j ∈ Finset.univ.filter (fun j => t j ∉ M.lattice),
    (M.weierstrassP z-M.weierstrassP (t j))
  let G (z : ℂ) := ∏ v ∈ Finset.univ.filter (fun v => χ v≠0),
    D (z+((ω/(4*n):ℝ):ℂ)*(b v:ℂ))^χ v
  n%8=2 → 2<n → ∀ m:ℕ, 0 < m → (4*n).Coprime (a*m) → ∀ z:ℂ, (m:ℂ)*z∈M.lattice →
  let A:=algebraicClosure ℚ ℂ
  let W:WeierstrassCurve A:=⟨0,0,0,-(n:A)^2,0⟩
  ∃ X:W.toAffine.Point→A, (X 0=0 ∧ ∀ x y (h:W.toAffine.Nonsingular x y), X (.some x y h)=x) ∧ ∃ (ι κ:Type) (hi:Fintype ι) (hk:Fintype κ), letI:=hi; letI:=hk;
    ∃ (w:ι→ℤ) (U:ι→W.toAffine.Point) (V:W.toAffine.Point) (Q:κ→W.toAffine.Point),
    let H:=∏ i,(∏ j,(X (U i+V)-X (Q j)))^w i
    (∑ i,w i=0) ∧ (∀ i,addOrderOf (U i)=4*n) ∧ (m • V=0) ∧ (∀ j,a • Q j=0) ∧ (∀ j,Q j≠0) ∧ (H≠0) ∧ (H:ℂ)=G z
set_option maxHeartbeats 1200000 in
theorem result : Representation := by
  refine fun n hn M hx hy hn8 h2 m hm hc z hz => ?_
  have eM : M=twistPeriods n hn := by
    rcases M with ⟨x,y,h⟩
    change x=_ at hx
    change y=_ at hy
    subst x
    subst y
    rfl
  subst M
  classical
  letI : NeZero (aux n) := ⟨by unfold aux; omega⟩
  letI : NeZero (4*n) := ⟨by omega⟩
  have hu : traceUnit n hn z ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i hi =>
    zpow_ne_zero _ (division_nonzero _ _ (TunnellCMPrimeToConductor.translated_regular n hn hc hz i (Finset.mem_filter.mp hi).2))
  classical
  letI : IsAlgClosure ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgClosure ℚ ℂ
  letI : IsAlgClosed (algebraicClosure ℚ ℂ) := IsAlgClosure.isAlgClosed ℚ
  letI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  letI : NeZero (4*n) := ⟨by omega⟩
  letI : NeZero (aux n) := ⟨by unfold aux; omega⟩
  let s := Finset.univ.filter (fun i : Residues n => weight n i≠0)
  let t := divisionGrid (twistPeriods n hn) (aux n)
  let M := mapPoint (algebraicClosure ℚ ℂ) ℂ n
  have hM := mapPoint_injective (algebraicClosure ℚ ℂ) ℂ n
  choose U eu using fun i : s => torsion_lift n hn (by omega : 0<4*n) (conductor_point n hn i.val)
  choose Q eq using fun j : t => torsion_lift n hn (Nat.pos_of_ne_zero (NeZero.ne (aux n))) (mul_lift (twistPeriods n hn) j.val)
  obtain ⟨V,ev⟩ := torsion_lift n hn hm hz
  have hU (i : s) : addOrderOf (U i)=4*n := by
    rw [← addOrderOf_injective M hM,show M (U i)=_ from eu i]
    exact (addOrderOf_injective (Point.equivOfEq (model_eq n hn)).toAddMonoidHom (Point.equivOfEq _).injective _).trans
      (TunnellCMConductorOrder.conductor_order n hn i.val ((Finset.mem_filter.mp i.property).2))
  have hV : m • V=0 := hM (by rw [map_nsmul,show M V=_ from ev,killed n hn hz,map_zero])
  have hQ (j : t) : aux n • Q j=0 := hM (by rw [map_nsmul,show M (Q j)=_ from eq j,killed n hn (mul_lift (twistPeriods n hn) j.val),map_zero])
  have hQ0 (j : t) : Q j≠0 := by
    intro hh
    have e := (eq j).symm
    rw [hh,map_zero] at e
    have h := (Point.equivOfEq (model_eq n hn)).injective (e.trans (map_zero _).symm)
    exact (Finset.mem_filter.mp j.property).2 ((TunnellCMTorsionOrder.zero_iff n hn _).mp h)
  have term (i : s) (j : t) : algebraMap (algebraicClosure ℚ ℂ) ℂ (X (U i+V)-X (Q j)) =
      (twistPeriods n hn).weierstrassP (z+point n i.val) - (twistPeriods n hn).weierstrassP (liftGrid (twistPeriods n hn) j.val) := by
    change algebraMap (algebraicClosure ℚ ℂ) ℂ (X (U i+V)-X (Q j))=_
    rw [map_sub,← x_point,← x_point,map_add,eu,ev,eq,← map_add,add_comm (point n i.val) z,x_uniformize,x_uniformize]
  have he : algebraMap (algebraicClosure ℚ ℂ) ℂ (∏ i : s, (∏ j : t, (X (U i+V)-X (Q j)))^weight n i.val) =
      traceUnit n hn z := by
    simp only [map_prod,map_zpow₀,term]
    change (∏ i : s, (∏ j : t, ((twistPeriods n hn).weierstrassP (z+point n i.val) - (twistPeriods n hn).weierstrassP (liftGrid (twistPeriods n hn) j.val)))^weight n i.val) = _
    have pj (i : Residues n) : (∏ j : t, ((twistPeriods n hn).weierstrassP (z+point n i) - (twistPeriods n hn).weierstrassP (liftGrid (twistPeriods n hn) j.val))) =
        divisionProduct (twistPeriods n hn) (aux n) (z+point n i) :=
      Finset.prod_coe_sort t (fun j => (twistPeriods n hn).weierstrassP (z+point n i) - (twistPeriods n hn).weierstrassP (liftGrid (twistPeriods n hn) j))
    simp only [pj]
    exact Finset.prod_coe_sort s (fun i => divisionProduct (twistPeriods n hn) (aux n) (z+point n i)^weight n i)
  have hw : ∑ i : s, weight n i.val=0 := by
    rw [Finset.sum_coe_sort,Finset.sum_filter_ne_zero]
    exact TunnellCMWeights.weight_sum_zero n hn8
  refine ⟨X,⟨rfl,fun _ _ _ => rfl⟩,s,t,inferInstance,inferInstance,fun i:s => weight n i.val,U,V,Q,hw,hU,hV,hQ,hQ0,?_⟩
  have nonzero (v : algebraicClosure ℚ ℂ) (g:ℂ) (h:(v:ℂ)=g) (hg:g≠0) : v≠0 ∧ (v:ℂ)=g := by
    refine ⟨?_,h⟩
    intro hv
    subst v
    exact hg h.symm
  exact nonzero _ _ he hu
end
end TunnellPublicUnitRepresentation
end

theorem OMA.solution : OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1.H2 := TunnellPublicUnitRepresentation.result
