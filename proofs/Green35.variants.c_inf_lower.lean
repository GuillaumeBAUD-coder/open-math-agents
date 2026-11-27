import FormalConjectures.GreensOpenProblems.«35»
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Polynomial.Roots

/-! # A finite Fourier certificate for the peak of an autoconvolution

For a nonnegative mass-one density on [0,1], we prove its autoconvolution
has essential supremum at least 0.643, which implies the 0.64 bound of
Cloninger and Steinerberger. The finite certificate uses 32 frequencies:
combine Bessel's inequality on [0,2] with a nonnegative cosine test on the
output and a cosine minorant on the input. All sign and coefficient checks
are exact integer polynomial calculations.

The dual witness and certificate are by @JaviSoto. The Fourier Bessel
formalization adapts @Dugongue's Green 35 proof (PR #1718), as used in
@JaviSoto's White B₃ proof (PR #3364). -/

/-
# A finite Fourier moment bound for unit-interval densities

The underlying period-two Bessel inequality and convolution identity follow
Dugongue's Green 35 formalization (PR 1718), as used in the White B₃ bound
from PR 3364. Centering a moment changes its phase but preserves its norm.
-/

namespace OMA.Moment35

open MeasureTheory Filter Topology
open scoped Convolution ENNReal Real

private instance : Fact ((0 : ℝ) < 2) := ⟨by norm_num⟩

/- ## Elementary helpers for `fourier` on `AddCircle (2 : ℝ)` -/

private lemma fourier2_coe (n : ℤ) (x : ℝ) :
    @fourier 2 n (x : AddCircle (2 : ℝ)) = Complex.exp (Real.pi * Complex.I * n * x) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast; ring

private lemma fourier2_norm (n : ℤ) (x : ℝ) :
    ‖@fourier 2 n (x : AddCircle (2 : ℝ))‖ = 1 := by
  rw [fourier_apply, Circle.norm_coe]

private lemma fourier2_zero (x : ℝ) :
    @fourier 2 0 (x : AddCircle (2 : ℝ)) = 1 := by
  simp

private lemma fourier2_add (n : ℤ) (x y : ℝ) :
    @fourier 2 n ((x + y : ℝ) : AddCircle (2 : ℝ)) =
      @fourier 2 n (x : AddCircle (2 : ℝ)) * @fourier 2 n (y : AddCircle (2 : ℝ)) := by
  rw [fourier2_coe, fourier2_coe, fourier2_coe, ← Complex.exp_add]
  congr 1; push_cast; ring

private lemma fourier2_mul_conj (n m : ℤ) (x : ℝ) :
    @fourier 2 (-n) (x : AddCircle (2 : ℝ)) * starRingEnd ℂ (@fourier 2 (-m) (x : AddCircle (2 : ℝ))) =
      @fourier 2 (m - n) (x : AddCircle (2 : ℝ)) := by
  rw [← fourier_neg, neg_neg, fourier2_coe, fourier2_coe, fourier2_coe, ← Complex.exp_add]
  congr 1; push_cast; ring

private lemma intervalIntegral_fourier2 (k : ℤ) :
    ∫ x in (0 : ℝ)..2, @fourier 2 k (x : AddCircle (2 : ℝ)) = if k = 0 then (2 : ℂ) else 0 := by
  split_ifs with hk
  · subst hk
    simp_rw [fourier2_zero]
    simp
  · simp_rw [fourier2_coe]
    let c : ℂ := Real.pi * Complex.I * (k : ℂ)
    have hc : c ≠ 0 := by
      simp only [c, ne_eq, mul_eq_zero, Complex.ofReal_eq_zero, Real.pi_ne_zero,
        Complex.I_ne_zero, Int.cast_eq_zero, hk, or_self, not_false_eq_true]
    have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 2,
        HasDerivAt (fun t : ℝ => Complex.exp (c * t) / c) (Complex.exp (c * x)) x := by
      intro x _
      have h1 : HasDerivAt (fun t : ℝ => c * (t : ℂ)) (c * 1) x :=
        (Complex.ofRealCLM.hasDerivAt).const_mul c
      rw [mul_one] at h1
      have h2 : HasDerivAt (fun t : ℝ => Complex.exp (c * (t : ℂ)))
          (Complex.exp (c * (x : ℂ)) * c) x := h1.cexp
      have h3 := h2.div_const c
      rwa [mul_div_cancel_right₀ _ hc] at h3
    have hint : IntervalIntegrable (fun x : ℝ => Complex.exp (c * (x : ℂ))) volume 0 2 :=
      (Continuous.intervalIntegrable (by fun_prop) 0 2)
    have hval := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    have hrew : (fun x : ℝ => Complex.exp (Real.pi * Complex.I * (k : ℂ) * (x : ℂ))) =
        (fun x : ℝ => Complex.exp (c * (x : ℂ))) := rfl
    rw [hrew, hval]
    have hexp2 : Complex.exp (c * (2 : ℂ)) = 1 := by
      have : c * (2 : ℂ) = (k : ℂ) * (2 * Real.pi * Complex.I) := by simp only [c]; ring
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    simp [hexp2]


/- ## Main Fourier-analytic lower bound for unit-interval densities -/

private lemma convolution_support_subset {f : ℝ → ℝ}
    (hsupp : Function.support f ⊆ Set.Icc (0 : ℝ) 1) :
    Function.support (f ⋆ f) ⊆ Set.Icc (0 : ℝ) 2 := by
  intro z hz
  by_contra hnot
  apply hz
  rw [convolution_lsmul]
  have hzero : ∀ t : ℝ, f t * f (z - t) = 0 := by
    intro t
    by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
    · have hzt : z - t ∉ Set.Icc (0 : ℝ) 1 := by
        intro hzt
        exact hnot ⟨by linarith [ht.1, hzt.1], by linarith [ht.2, hzt.2]⟩
      have hfz : f (z - t) = 0 := by
        by_contra hne
        exact hzt (hsupp hne)
      rw [hfz, mul_zero]
    · have hft : f t = 0 := by
        by_contra hne
        exact ht (hsupp hne)
      rw [hft, zero_mul]
  simp [hzero]

private lemma fourier_coeff_conv {f : ℝ → ℝ} (hfi : Integrable f)
    (hsupp : Function.support f ⊆ Set.Icc (0 : ℝ) 1) (n : ℤ) :
    ∫ z in Set.Ioc (0 : ℝ) 2, ((f ⋆ f) z : ℂ) * @fourier 2 n (z : AddCircle (2 : ℝ)) =
      (∫ x, (f x : ℂ) * @fourier 2 n (x : AddCircle (2 : ℝ))) ^ 2 := by
  have hgsupp := convolution_support_subset hsupp
  have hIoc : ∫ z in Set.Ioc (0 : ℝ) 2, ((f ⋆ f) z : ℂ) * @fourier 2 n (z : AddCircle (2 : ℝ)) =
      ∫ z, ((f ⋆ f) z : ℂ) * @fourier 2 n (z : AddCircle (2 : ℝ)) := by
    rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
    refine integral_congr_ae ?_
    have hne0 : ∀ᵐ z : ℝ ∂volume, z ≠ 0 := by
      rw [ae_iff]; simp
    filter_upwards [hne0] with z hz0
    by_cases hz : z ∈ Set.Ioc (0 : ℝ) 2
    · simp [Set.indicator_of_mem hz]
    · simp only [Set.indicator_of_notMem hz]
      have hnotIcc : z ∉ Set.Icc (0 : ℝ) 2 := by
        intro h; exact hz ⟨lt_of_le_of_ne h.1 hz0.symm, h.2⟩
      have hg0 : (f ⋆ f) z = 0 := by
        by_contra hne
        exact hnotIcc (hgsupp hne)
      simp [hg0]
  rw [hIoc]
  let φ : ℝ → ℂ := fun x => (f x : ℂ) * @fourier 2 n (x : AddCircle (2 : ℝ))
  have hφ_int : Integrable φ := by
    refine Integrable.mono' hfi.norm ?_ ?_
    · have hcont : Continuous (fun x : ℝ => @fourier 2 n (x : AddCircle (2 : ℝ))) := by
        simp_rw [fourier2_coe]; fun_prop
      exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hfi.aestronglyMeasurable).mul
        hcont.aestronglyMeasurable
    · filter_upwards with x
      simp only [φ, norm_mul, Complex.norm_real, fourier2_norm, mul_one, le_refl]
  have hconv_eq : ∀ z : ℝ,
      ((f ⋆ f) z : ℂ) * @fourier 2 n (z : AddCircle (2 : ℝ)) =
        (φ ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] φ) z := by
    intro z
    rw [convolution_lsmul, convolution_def]
    simp only [ContinuousLinearMap.mul_apply', φ]
    have hofReal : ((∫ t : ℝ, f t * f (z - t) : ℝ) : ℂ) = ∫ t : ℝ, ((f t * f (z - t) : ℝ) : ℂ) := by
      simp_rw [← Complex.coe_algebraMap]
      exact (integral_ofReal (𝕜 := ℂ)).symm
    simp only [smul_eq_mul]
    rw [hofReal, ← integral_mul_const]
    congr 1; funext t
    have hsplit : @fourier 2 n (z : AddCircle (2 : ℝ)) =
        @fourier 2 n (t : AddCircle (2 : ℝ)) * @fourier 2 n ((z - t : ℝ) : AddCircle (2 : ℝ)) := by
      have : z = t + (z - t) := by ring
      conv_lhs => rw [this]
      exact fourier2_add n t (z - t)
    rw [hsplit]
    push_cast; ring
  simp_rw [hconv_eq]
  rw [integral_convolution (ContinuousLinearMap.mul ℝ ℂ) hφ_int hφ_int]
  simp only [ContinuousLinearMap.mul_apply', sq, φ]

private lemma bessel_Ioc_two {g : ℝ → ℝ} (hgi : Integrable g)
    (hg_sq : Integrable (fun z => (g z) ^ 2))
    (c : ℤ → ℂ)
    (hc : ∀ n : ℤ, ∫ z in Set.Ioc (0 : ℝ) 2, (g z : ℂ) * @fourier 2 n (z : AddCircle (2 : ℝ)) = c n)
    (F : Finset ℤ) :
    (1 / 2 : ℝ) * ∑ n ∈ F, ‖c n‖ ^ 2 ≤ ∫ z in Set.Ioc (0 : ℝ) 2, (g z) ^ 2 := by
  let S : ℝ → ℂ := fun z => (1 / 2 : ℂ) * ∑ n ∈ F, c n * @fourier 2 (-n) (z : AddCircle (2 : ℝ))
  have hS_cont : Continuous S := by
    simp only [S]
    refine continuous_const.mul (continuous_finsetSum F fun n _ => ?_)
    simp_rw [fourier2_coe]; fun_prop
  have hS2_int : IntegrableOn (fun z => ‖S z‖ ^ 2) (Set.Ioc (0 : ℝ) 2) volume :=
    (hS_cont.norm.pow 2).continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hg2_int : IntegrableOn (fun z => (g z) ^ 2) (Set.Ioc (0 : ℝ) 2) volume :=
    hg_sq.integrableOn
  have hcross_int : IntegrableOn (fun z => (g z : ℂ) * starRingEnd ℂ (S z))
      (Set.Ioc (0 : ℝ) 2) volume := by
    refine Integrable.mono' (hg2_int.add hS2_int) ?_ ?_
    · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable
        hgi.aestronglyMeasurable.restrict).mul
        (Complex.continuous_conj.comp hS_cont).aestronglyMeasurable
    · filter_upwards with z
      simp only [Pi.add_apply]
      rw [norm_mul, Complex.norm_real, Complex.norm_conj, Real.norm_eq_abs]
      nlinarith [sq_nonneg (|g z| - ‖S z‖), sq_abs (g z)]
  have hcross_re_int : IntegrableOn (fun z => ((g z : ℂ) * starRingEnd ℂ (S z)).re)
      (Set.Ioc (0 : ℝ) 2) volume :=
    Complex.reCLM.integrable_comp hcross_int
  have hexpand : ∀ z : ℝ,
      ‖(g z : ℂ) - S z‖ ^ 2 =
        (g z) ^ 2 - 2 * ((g z : ℂ) * starRingEnd ℂ (S z)).re + ‖S z‖ ^ 2 := by
    intro z
    rw [Complex.sq_norm, Complex.sq_norm]
    simp [Complex.normSq_apply]
    ring
  have hnonneg : 0 ≤ ∫ z in Set.Ioc (0 : ℝ) 2, ‖(g z : ℂ) - S z‖ ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  simp_rw [hexpand] at hnonneg
  have hsplit_int :
      ∫ z in Set.Ioc (0 : ℝ) 2,
          ((g z) ^ 2 - 2 * ((g z : ℂ) * starRingEnd ℂ (S z)).re + ‖S z‖ ^ 2) =
        (∫ z in Set.Ioc (0 : ℝ) 2, (g z) ^ 2) -
        2 * (∫ z in Set.Ioc (0 : ℝ) 2, ((g z : ℂ) * starRingEnd ℂ (S z)).re) +
        (∫ z in Set.Ioc (0 : ℝ) 2, ‖S z‖ ^ 2) := by
    have hadd := integral_add (hg2_int.sub (hcross_re_int.const_mul 2)) hS2_int
    have hsub := integral_sub hg2_int (hcross_re_int.const_mul 2)
    have hmul := integral_const_mul (μ := volume.restrict (Set.Ioc (0 : ℝ) 2))
      (2 : ℝ) (fun z => ((g z : ℂ) * starRingEnd ℂ (S z)).re)
    dsimp only [Pi.add_apply, Pi.sub_apply] at hadd hsub
    rw [hadd, hsub, hmul]
  rw [hsplit_int] at hnonneg
  have hcross_val :
      ∫ z in Set.Ioc (0 : ℝ) 2, ((g z : ℂ) * starRingEnd ℂ (S z)).re =
        (1 / 2 : ℝ) * ∑ n ∈ F, ‖c n‖ ^ 2 := by
    have hre : ∫ z in Set.Ioc (0 : ℝ) 2, ((g z : ℂ) * starRingEnd ℂ (S z)).re =
        (∫ z in Set.Ioc (0 : ℝ) 2, (g z : ℂ) * starRingEnd ℂ (S z)).re :=
      Complex.reCLM.integral_comp_comm hcross_int
    rw [hre]
    have hpt : (fun z : ℝ => (g z : ℂ) * starRingEnd ℂ (S z)) =
        fun z : ℝ => (1 / 2 : ℂ) * ∑ n ∈ F,
          starRingEnd ℂ (c n) * ((g z : ℂ) * @fourier 2 n (z : AddCircle (2 : ℝ))) := by
      funext z
      simp only [S, map_mul, map_div₀, map_one, map_ofNat, map_sum, ← fourier_neg, neg_neg,
        Finset.mul_sum]
      ring_nf
    rw [hpt, integral_const_mul, integral_finsetSum]
    · have hterm : ∀ n ∈ F,
          ∫ z in Set.Ioc (0 : ℝ) 2,
            starRingEnd ℂ (c n) * ((g z : ℂ) * @fourier 2 n (z : AddCircle (2 : ℝ))) =
          starRingEnd ℂ (c n) * c n := by
        intro n _
        rw [integral_const_mul, hc n]
      rw [Finset.sum_congr rfl hterm]
      have hdiv : ((1 / 2 : ℂ) * ∑ n ∈ F, starRingEnd ℂ (c n) * c n).re =
          (1 / 2 : ℝ) * (∑ n ∈ F, starRingEnd ℂ (c n) * c n).re := by
        simp [Complex.mul_re]
      rw [hdiv, Complex.re_sum]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply]
    · intro n _
      have hcont : Continuous (fun z : ℝ => @fourier 2 n (z : AddCircle (2 : ℝ))) := by
        simp_rw [fourier2_coe]; fun_prop
      have hgn : IntegrableOn (fun z : ℝ => (g z : ℂ) * @fourier 2 n (z : AddCircle (2 : ℝ)))
          (Set.Ioc (0 : ℝ) 2) volume := by
        refine Integrable.mono' hgi.norm.integrableOn ?_ ?_
        · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable
            hgi.aestronglyMeasurable.restrict).mul hcont.aestronglyMeasurable
        · filter_upwards with z
          simp only [norm_mul, Complex.norm_real, fourier2_norm, mul_one, le_refl]
      exact hgn.const_mul _
  have hS2_val :
      ∫ z in Set.Ioc (0 : ℝ) 2, ‖S z‖ ^ 2 = (1 / 2 : ℝ) * ∑ n ∈ F, ‖c n‖ ^ 2 := by
    have hpt : (fun z : ℝ => ‖S z‖ ^ 2) = fun z : ℝ => (S z * starRingEnd ℂ (S z)).re := by
      funext z; rw [Complex.sq_norm]; simp [Complex.normSq_apply]
    rw [hpt]
    have hSS_int : IntegrableOn (fun z : ℝ => S z * starRingEnd ℂ (S z))
        (Set.Ioc (0 : ℝ) 2) volume :=
      (hS_cont.mul (Complex.continuous_conj.comp hS_cont)).continuousOn.integrableOn_Icc.mono_set
        Set.Ioc_subset_Icc_self
    have hre2 : ∫ z in Set.Ioc (0 : ℝ) 2, (S z * starRingEnd ℂ (S z)).re =
        (∫ z in Set.Ioc (0 : ℝ) 2, S z * starRingEnd ℂ (S z)).re :=
      Complex.reCLM.integral_comp_comm hSS_int
    rw [hre2]
    have hexp : (fun z : ℝ => S z * starRingEnd ℂ (S z)) =
        fun z : ℝ => (1 / 4 : ℂ) * ∑ n ∈ F, ∑ m ∈ F,
          (c n * starRingEnd ℂ (c m)) * @fourier 2 (m - n) (z : AddCircle (2 : ℝ)) := by
      funext z
      simp only [S, map_mul, map_div₀, map_one, map_ofNat, map_sum]
      calc (1 / 2 : ℂ) * (∑ n ∈ F, c n * @fourier 2 (-n) (z : AddCircle (2 : ℝ))) *
            ((1 / 2 : ℂ) * ∑ m ∈ F, starRingEnd ℂ (c m) *
              starRingEnd ℂ (@fourier 2 (-m) (z : AddCircle (2 : ℝ))))
          = (1 / 4 : ℂ) * ((∑ n ∈ F, c n * @fourier 2 (-n) (z : AddCircle (2 : ℝ))) *
              (∑ m ∈ F, starRingEnd ℂ (c m) *
                starRingEnd ℂ (@fourier 2 (-m) (z : AddCircle (2 : ℝ))))) := by ring
        _ = (1 / 4 : ℂ) * ∑ n ∈ F, ∑ m ∈ F,
              (c n * starRingEnd ℂ (c m)) * @fourier 2 (m - n) (z : AddCircle (2 : ℝ)) := by
            congr 1
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun n _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [← fourier2_mul_conj n m z]; ring
    rw [hexp, integral_const_mul, integral_finsetSum]
    · have hinner : ∀ n ∈ F,
          ∫ z in Set.Ioc (0 : ℝ) 2, ∑ m ∈ F,
            (c n * starRingEnd ℂ (c m)) * @fourier 2 (m - n) (z : AddCircle (2 : ℝ)) =
          (c n * starRingEnd ℂ (c n)) * (2 : ℂ) := by
        intro n hn
        rw [integral_finsetSum]
        · have hterm : ∀ m ∈ F,
              ∫ z in Set.Ioc (0 : ℝ) 2,
                (c n * starRingEnd ℂ (c m)) * @fourier 2 (m - n) (z : AddCircle (2 : ℝ)) =
              if m = n then (c n * starRingEnd ℂ (c m)) * (2 : ℂ) else 0 := by
            intro m _
            rw [integral_const_mul, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2),
              intervalIntegral_fourier2 (m - n)]
            by_cases hmn : m = n
            · subst hmn; simp
            · have : m - n ≠ 0 := sub_ne_zero.mpr hmn
              simp [hmn, this]
          rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' F n, if_pos hn]
        · intro m _
          have hcont : Continuous (fun z : ℝ =>
              (c n * starRingEnd ℂ (c m)) * @fourier 2 (m - n) (z : AddCircle (2 : ℝ))) := by
            simp_rw [fourier2_coe]; fun_prop
          exact hcont.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
      rw [Finset.sum_congr rfl hinner]
      have hdiv : ((1 / 4 : ℂ) * ∑ n ∈ F, c n * starRingEnd ℂ (c n) * 2).re =
          (1 / 2 : ℝ) * (∑ n ∈ F, c n * starRingEnd ℂ (c n)).re := by
        rw [← Finset.sum_mul, show (1 / 4 : ℂ) * ((∑ n ∈ F, c n * starRingEnd ℂ (c n)) * 2) =
            (1 / 2 : ℂ) * ∑ n ∈ F, c n * starRingEnd ℂ (c n) by ring]
        simp [Complex.mul_re]
      rw [hdiv, Complex.re_sum]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply]
    · intro n _
      have hcont : Continuous (fun z : ℝ => ∑ m ∈ F,
          (c n * starRingEnd ℂ (c m)) * @fourier 2 (m - n) (z : AddCircle (2 : ℝ))) := by
        refine continuous_finsetSum F fun m _ => ?_
        simp_rw [fourier2_coe]; fun_prop
      exact hcont.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  linarith

private theorem partial_bound {f : ℝ → ℝ} (hf : Green35.IsUnitIntervalDensity f)
    (hgi : Integrable (f ⋆ f)) (hgsq : Integrable (fun x => ((f ⋆ f) x)^2)) (L : ℕ) :
    ∑ k ∈ Finset.range L, ‖∫ x : ℝ, (f x : ℂ) * @fourier 2 ((k+1:ℕ):ℤ) (x : AddCircle (2:ℝ))‖^4
      ≤ (∫ x, ((f ⋆ f) x)^2) - 1/2 := by
  obtain ⟨hfi, hf0, hfsupp, hf1⟩ := hf
  let c : ℤ → ℂ := fun n => ∫ x, (f x : ℂ) * @fourier 2 n (x : AddCircle (2 : ℝ))
  have hc0 : c 0 = 1 := by
    simp only [c, fourier2_zero, mul_one]
    have h1 : ∫ x : ℝ, (f x : ℂ) = ((∫ x : ℝ, f x : ℝ) : ℂ) :=
      Complex.ofRealCLM.integral_comp_comm hfi
    rw [h1, hf1, Complex.ofReal_one]
  have hc_neg : ∀ n : ℤ, ‖c (-n)‖ = ‖c n‖ := by
    intro n
    have hconj : c (-n) = starRingEnd ℂ (c n) := by
      simp only [c]
      rw [← integral_conj]
      congr 1; funext x
      rw [map_mul, Complex.conj_ofReal, fourier_neg]
    rw [hconj, Complex.norm_conj]
  -- Step 1: Bessel inequality for c n ^ 2 via f ⋆ f
  have hg_Ioc : ∫ z in Set.Ioc (0 : ℝ) 2, ((f ⋆ f) z) ^ 2 = ∫ z, ((f ⋆ f) z) ^ 2 := by
    have hgsupp := convolution_support_subset hfsupp
    rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
    refine integral_congr_ae ?_
    have hne0 : ∀ᵐ z : ℝ ∂volume, z ≠ 0 := by rw [ae_iff]; simp
    filter_upwards [hne0] with z hz0
    by_cases hz : z ∈ Set.Ioc (0 : ℝ) 2
    · simp [Set.indicator_of_mem hz]
    · simp only [Set.indicator_of_notMem hz]
      have hnotIcc : z ∉ Set.Icc (0 : ℝ) 2 := fun h => hz ⟨lt_of_le_of_ne h.1 hz0.symm, h.2⟩
      have hg0 : (f ⋆ f) z = 0 := by by_contra hne; exact hnotIcc (hgsupp hne)
      simp [hg0]
  have hbessel_partial : ∀ N : ℕ,
      ∑ r ∈ Finset.range N, ‖c ((r + 1 : ℕ) : ℤ)‖ ^ 4 ≤ (∫ z, ((f ⋆ f) z) ^ 2) - 1 / 2 := by
    intro N
    let F : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
    have hb := bessel_Ioc_two hgi hgsq (fun n => c n ^ 2) (fourier_coeff_conv hfi hfsupp) F
    rw [hg_Ioc] at hb
    have hsum_F : ∑ n ∈ F, ‖c n ^ 2‖ ^ 2 = 1 + 2 * ∑ r ∈ Finset.range N, ‖c ((r + 1 : ℕ) : ℤ)‖ ^ 4 := by
      have hF_eq : F = insert (0 : ℤ)
          ((Finset.range N).image (fun r : ℕ => ((r + 1 : ℕ) : ℤ)) ∪
           (Finset.range N).image (fun r : ℕ => -((r + 1 : ℕ) : ℤ))) := by
        ext n
        simp only [F, Finset.mem_Icc, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
          Finset.mem_range]
        constructor
        · intro ⟨h1, h2⟩
          by_cases hn0 : n = 0
          · exact Or.inl hn0
          · right
            by_cases hpos : 0 < n
            · left; exact ⟨(n - 1).toNat, by omega, by omega⟩
            · right; exact ⟨(-n - 1).toNat, by omega, by omega⟩
        · rintro (rfl | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩) <;> omega
      rw [hF_eq, Finset.sum_insert (by
        simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range]
        rintro (⟨r, _, hr⟩ | ⟨r, _, hr⟩) <;> omega)]
      have hdisj : Disjoint ((Finset.range N).image (fun r : ℕ => ((r + 1 : ℕ) : ℤ)))
          ((Finset.range N).image (fun r : ℕ => -((r + 1 : ℕ) : ℤ))) := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        rw [Finset.mem_image] at hx1 hx2
        obtain ⟨a, _, rfl⟩ := hx1
        obtain ⟨b, _, hb⟩ := hx2
        omega
      rw [Finset.sum_union hdisj,
        Finset.sum_image (by intro a _ b _ h; dsimp at h; omega),
        Finset.sum_image (by intro a _ b _ h; dsimp at h; omega)]
      simp only [hc0, one_pow, norm_one, norm_pow]
      have hpow4 : ∀ z : ℂ, (‖z‖ ^ 2) ^ 2 = ‖z‖ ^ 4 := fun z => by ring
      simp_rw [hpow4, hc_neg]
      ring
    rw [hsum_F] at hb
    have hsimp : (1 / 2 : ℝ) * (1 + 2 * ∑ r ∈ Finset.range N, ‖c ((r + 1 : ℕ) : ℤ)‖ ^ 4) =
        1 / 2 + ∑ r ∈ Finset.range N, ‖c ((r + 1 : ℕ) : ℤ)‖ ^ 4 := by ring
    linarith
  exact hbessel_partial L

private lemma centered_norm {f : ℝ → ℝ} (hf : Integrable f) (k : ℕ) :
    (∫ x, f x * Real.cos (((k:ℝ)+1)*Real.pi*(x-1/2)))^2 +
    (∫ x, f x * Real.sin (((k:ℝ)+1)*Real.pi*(x-1/2)))^2 =
    ‖∫ x : ℝ, (f x : ℂ) * @fourier 2 ((k+1:ℕ):ℤ) (x : AddCircle (2:ℝ))‖^2 := by
  let t := ((k:ℝ)+1)*Real.pi
  let phase (v : ℝ) := Complex.exp ((t*v:ℝ) * Complex.I)
  let F (x : ℝ) := (f x:ℂ) * phase (x-1/2)
  have un (v : ℝ) : ‖phase v‖=1 := Complex.norm_exp_ofReal_mul_I _
  have hi : Integrable F := by
    apply hf.norm.mono' ((Complex.continuous_ofReal.comp_aestronglyMeasurable hf.1).mul (show Continuous (fun x : ℝ => phase (x-1/2)) by unfold phase; fun_prop).aestronglyMeasurable)
    filter_upwards with x
    simp [un]
  have hRe : (∫ x, F x).re = ∫ x, f x * Real.cos (t*(x-1/2)) := by
    change RCLike.re (∫ x, F x) = _
    rw [←integral_re hi]
    change (∫ x, (F x).re) = _
    simp only [F, phase, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, zero_mul, sub_zero]
  have hIm : (∫ x, F x).im = ∫ x, f x * Real.sin (t*(x-1/2)) := by
    change RCLike.im (∫ x, F x) = _
    rw [←integral_im hi]
    change (∫ x, (F x).im) = _
    simp only [F, phase, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_im, zero_mul, add_zero]
  change (∫ x, f x * Real.cos (t*(x-1/2)))^2 + (∫ x, f x * Real.sin (t*(x-1/2)))^2 = _
  rw [←hRe, ←hIm]
  have hp (x : ℝ) : F x = phase (-(1/2)) * ((f x : ℂ) * @fourier 2 ((k+1:ℕ):ℤ) (x : AddCircle (2:ℝ))) := by
    rw [fourier2_coe]
    dsimp [F, phase, t]
    rw [mul_left_comm,←Complex.exp_add]
    congr 2
    push_cast
    ring
  calc (∫ x, F x).re ^ 2 + (∫ x, F x).im ^ 2 = ‖∫ x, F x‖ ^ 2 := by
         rw [Complex.sq_norm, Complex.normSq_apply]; ring
       _ = _ := by simp_rw [hp]; rw [integral_const_mul, norm_mul, un, one_mul]

theorem bessel {f : ℝ → ℝ} (hf : Green35.IsUnitIntervalDensity f) {M : ℝ}
    (cap : ∀ᵐ x : ℝ, (f ⋆ f) x ≤ M) (N : ℕ) :
    1 + 2 * ∑ i : Fin N, ((∫ x, f x * Real.cos (((i.val:ℝ)+1)*Real.pi*(x-1/2)))^2 +
      (∫ x, f x * Real.sin (((i.val:ℝ)+1)*Real.pi*(x-1/2)))^2)^2 ≤ 2*M := by
  let g := f ⋆ f
  have nn (x : ℝ) : 0 ≤ g x := by
    rw [show g x = (f ⋆ f) x from rfl, convolution_lsmul]
    exact integral_nonneg (fun t => mul_nonneg (hf.2.1 t) (hf.2.1 (x-t)))
  have gi : Integrable g := hf.1.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hf.1
  have mass : ∫ x, g x = 1 := by
    simpa [g, hf.2.2.2] using integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hf.1 hf.1
  have major : ∀ᵐ x : ℝ, g x ^ 2 ≤ M*g x := by
    filter_upwards [cap] with x hx
    nlinarith [mul_nonneg (nn x) (sub_nonneg.mpr (show g x ≤ M from hx))]
  have gs : Integrable (fun x => (g x)^2) := (gi.const_mul M).mono' (gi.1.pow 2) (by
    filter_upwards [major] with x hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (g x))] using hx)
  have ub := integral_mono_ae gs (gi.const_mul M) major
  rw [integral_const_mul, mass, mul_one] at ub
  simp_rw [centered_norm hf.1, ←pow_mul]
  have h := partial_bound hf gi gs N
  rw [← Fin.sum_univ_eq_sum_range] at h
  change 1 + 2 * ∑ i : Fin N, ‖∫ x : ℝ, (f x : ℂ) * @fourier 2 ((i.val + 1 : ℕ) : ℤ) (x : AddCircle (2 : ℝ))‖^4 ≤ 2*M
  change (∫ x, ((f ⋆ f) x)^2) ≤ M at ub
  linarith

end OMA.Moment35

/- Centered trigonometric moments of an interval density and its self-convolution. -/
namespace OMA.CSDual35
open MeasureTheory Filter Finset Set Real
open scoped ENNReal Convolution Pointwise

noncomputable def C (t x : ℝ) := Real.cos (t*(x-1/2))
noncomputable def S (t x : ℝ) := Real.sin (t*(x-1/2))
noncomputable def A (f : ℝ → ℝ) (t : ℝ) := ∫ x, f x * C t x
noncomputable def B (f : ℝ → ℝ) (t : ℝ) := ∫ x, f x * S t x

private theorem iC {f : ℝ → ℝ} (hf : Integrable f) (t z : ℝ) :
    Integrable (fun x => f x * Real.cos (t*(x-z))) :=
  hf.mul_bdd (by fun_prop) (Eventually.of_forall (fun x => by
    simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (t*(x-z))))

private theorem iS {f : ℝ → ℝ} (hf : Integrable f) (t z : ℝ) :
    Integrable (fun x => f x * Real.sin (t*(x-z))) :=
  hf.mul_bdd (by fun_prop) (Eventually.of_forall (fun x => by
    simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (t*(x-z))))

theorem cos_moment {f : ℝ → ℝ} (hf : Integrable f) (t : ℝ) :
    (∫ x, (f ⋆ f) x * Real.cos (t*(x-1))) = (A f t)^2-(B f t)^2 := by
  let c x := f x*C t x
  let s x := f x*S t x
  have hc : Integrable c := iC hf t (1/2)
  have hs : Integrable s := iS hf t (1/2)
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  calc
    _ = ∫ x, (c ⋆ c) x - (s ⋆ s) x := by
      apply integral_congr_ae
      filter_upwards [hc.ae_convolution_exists L hc,hs.ae_convolution_exists L hs] with x hcc hss
      change (∫ y, f y*f (x-y))*_ = (∫ y, c y*c (x-y)) - ∫ y, s y*s (x-y)
      rw [←integral_mul_const,←integral_sub
        (show Integrable (fun y => c y*c (x-y)) volume by simpa [L] using hcc.integrable)
        (show Integrable (fun y => s y*s (x-y)) volume by simpa [L] using hss.integrable)]
      apply integral_congr_ae
      filter_upwards with y
      rw [show t*(x-1) = t*(y-1/2) + t*((x-y)-1/2) by ring,Real.cos_add]
      dsimp only [c,s,C,S]; ring
    _ = _ := by
      rw [integral_sub (hc.integrable_convolution L hc) (hs.integrable_convolution L hs),
        integral_convolution L hc hc,integral_convolution L hs hs]
      change (A f t)*(A f t)-(B f t)*(B f t)=_
      ring

theorem sin_moment {f : ℝ → ℝ} (hf : Integrable f) (t : ℝ) :
    (∫ x, (f ⋆ f) x * Real.sin (t*(x-1))) = 2*(A f t)*(B f t) := by
  let c x := f x*C t x
  let s x := f x*S t x
  have hc : Integrable c := iC hf t (1/2)
  have hs : Integrable s := iS hf t (1/2)
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  calc
    _ = ∫ x, (s ⋆ c) x + (c ⋆ s) x := by
      apply integral_congr_ae
      filter_upwards [hs.ae_convolution_exists L hc,hc.ae_convolution_exists L hs] with x hsc hcs
      change (∫ y, f y*f (x-y))*_ = (∫ y, s y*c (x-y)) + ∫ y, c y*s (x-y)
      rw [←integral_mul_const,←integral_add
        (show Integrable (fun y => s y*c (x-y)) volume by simpa [L] using hsc.integrable)
        (show Integrable (fun y => c y*s (x-y)) volume by simpa [L] using hcs.integrable)]
      apply integral_congr_ae
      filter_upwards with y
      rw [show t*(x-1) = t*(y-1/2) + t*((x-y)-1/2) by ring,Real.sin_add]
      dsimp only [c,s,C,S]; ring
    _ = _ := by
      rw [integral_add (hs.integrable_convolution L hc) (hc.integrable_convolution L hs),
        integral_convolution L hs hc,integral_convolution L hc hs]
      change (B f t)*(A f t)+(A f t)*(B f t)=_
      ring

private noncomputable def P {N : ℕ} (c : Fin N → ℝ) (x : ℝ) :=
  ∑ i, c i * Real.cos (((i.val:ℝ)+1)*x)

private theorem factor {N : ℕ} {f : ℝ → ℝ} (hf : Integrable f) (z : ℝ) (c : Fin N → ℝ) :
    Integrable (fun x => f x * P c (π*(x-z))) ∧
    (∫ x, f x * P c (π*(x-z))) =
      ∑ i, c i * ∫ x, f x * Real.cos ((((i.val:ℝ)+1)*π)*(x-z)) := by
  let term (i : Fin N) (x : ℝ) := c i * (f x * Real.cos ((((i.val:ℝ)+1)*π)*(x-z)))
  have eq : (fun x => f x*P c (π*(x-z))) = fun x => ∑ i, term i x := by
    funext x
    rw [P,mul_sum]
    apply sum_congr rfl
    intro i _
    dsimp [term]; rw [mul_assoc (((i.val:ℝ)+1)) π]; ring
  have hterm (i : Fin N) : Integrable (term i) := (iC hf _ _).const_mul _
  rw [eq]
  refine ⟨integrable_finsetSum _ (fun i _ => hterm i),?_⟩
  rw [integral_finsetSum _ (fun i _ => hterm i)]
  exact sum_congr rfl (fun i _ => integral_const_mul _ _)

/-- A lower bound for a cosine polynomial on the right semicircle gives
a linear constraint on the input moments. -/
theorem input_bound {f : ℝ → ℝ} (hf : Green35.IsUnitIntervalDensity f) {N : ℕ}
    (c : Fin N → ℝ) (u : ℝ)
    (test : ∀ x : ℝ, 0 ≤ Real.cos x → u ≤ ∑ i, c i * Real.cos (((i.val:ℝ)+1)*x)) :
    u ≤ ∑ i, c i*A f (((i.val:ℝ)+1)*π) := by
  obtain ⟨hi,eq⟩ := factor hf.1 (1/2) c
  change u ≤ ∑ i, c i * ∫ x, f x*Real.cos ((((i.val:ℝ)+1)*π)*(x-1/2))
  rw [←eq]
  calc
    u = ∫ x, f x*u := by rw [integral_mul_const,hf.2.2.2,one_mul]
    _ ≤ _ := integral_mono (hf.1.mul_const _) hi (fun x => by
      by_cases hx : f x = 0
      · simp [hx]
      · have bound := hf.2.2.1 (show x∈Function.support f from hx)
        have angle : π*(x-1/2) ∈ Icc (-(π/2)) (π/2) := by
          constructor <;> nlinarith only [mul_nonneg pi_pos.le bound.1,
            mul_nonneg pi_pos.le (sub_nonneg.mpr bound.2)]
        exact mul_le_mul_of_nonneg_left (test _ (Real.cos_nonneg_of_mem_Icc angle)) (hf.2.1 x))

private theorem zero_mode (n : ℕ) :
    (∫ x in Icc (0:ℝ) 2, Real.cos ((((n:ℝ)+1)*π)*(x-1))) = 0 := by
  let w := ((n:ℝ)+1)*π
  have hw : w≠0 := by dsimp [w]; positivity
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤2)]
  have eq := intervalIntegral.mul_integral_comp_mul_sub (f:=Real.cos) (a:=0) (b:=2) w w
  rw [integral_cos,show w*2-w=w by ring,show w*0-w= -w by ring,Real.sin_neg] at eq
  have hz : Real.sin w = 0 := by simpa [w] using Real.sin_nat_mul_pi (n+1)
  rw [hz] at eq
  change (∫ x in 0..2, Real.cos (w*(x-1))) = 0
  simp_rw [mul_sub,mul_one]
  exact (mul_eq_zero.mp (eq.trans (by ring))).resolve_left hw

/-- Nonnegativity of a test polynomial on the circle bounds the cosine
moments of the convolution by its height times the mean of the polynomial. -/
theorem output_bound {f : ℝ → ℝ} (hf : Green35.IsUnitIntervalDensity f) {M : ℝ}
    (cap : ∀ᵐ x, (f ⋆ f) x ≤ M) {N : ℕ} (c : Fin N → ℝ) (m : ℝ)
    (test : ∀ x, 0 ≤ m+2*∑ i, c i*Real.cos (((i.val:ℝ)+1)*x)) :
    m + 2*∑ i, c i*((A f (((i.val:ℝ)+1)*π))^2-(B f (((i.val:ℝ)+1)*π))^2) ≤ m*(2*M) := by
  let g := f ⋆ f
  let W (x : ℝ) := m+2*P c (π*(x-1))
  let J := Icc (0:ℝ) 2
  have hgi : Integrable g := hf.1.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hf.1
  have hg : (∫ x,g x) = 1 := by
    rw [show (∫ x,g x)=(∫ x,f x)*(∫ x,f x) from
      integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hf.1 hf.1,hf.2.2.2,one_mul]
  have support : Function.support g ⊆ J := by
    intro z hz
    obtain ⟨x,hx,y,hy,rfl⟩ := support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ) hz
    have hx' := hf.2.2.1 hx
    have hy' := hf.2.2.1 hy
    exact ⟨add_nonneg hx'.1 hy'.1,by linarith only [hx'.2,hy'.2]⟩
  have wcont : Continuous W := by dsimp [W,P]; fun_prop
  have wi : IntegrableOn W J := wcont.continuousOn.integrableOn_compact isCompact_Icc
  obtain ⟨hi,eq⟩ := factor hgi 1 c
  have alg (x : ℝ) : g x*W x = g x*m + 2*(g x*P c (π*(x-1))) := by dsimp [W]; ring
  have hprod : Integrable (fun x => g x*W x) := by
    simp_rw [alg]; exact (hgi.mul_const _).add (hi.const_mul _)
  have moment : (∫ x, g x*W x) =
      m+2*∑ i, c i*((A f (((i.val:ℝ)+1)*π))^2-(B f (((i.val:ℝ)+1)*π))^2) := by
    simp_rw [alg]
    rw [integral_add (hgi.mul_const _) (hi.const_mul _),integral_mul_const,integral_const_mul,
      hg,one_mul,eq]
    simp only [g,cos_moment hf.1]
  have cosine : (∫ x in J, P c (π*(x-1)))=0 := by
    dsimp only [P]
    rw [integral_finsetSum]
    · apply sum_eq_zero
      intro i _
      rw [integral_const_mul]
      simp_rw [←mul_assoc]
      rw [zero_mode]
      ring
    · intro i _
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      apply Continuous.continuousOn
      fun_prop
  have mean : (∫ x in J, W x)=2*m := by
    have cw : IntegrableOn (fun _ : ℝ => m) J := integrableOn_const measure_Icc_lt_top.ne
    have pw : IntegrableOn (fun x => 2*P c (π*(x-1))) J := by
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      apply Continuous.continuousOn
      dsimp [P]; fun_prop
    dsimp only [W]
    rw [integral_add cw pw,integral_const_mul,cosine]
    simp [J,mul_comm]
  rw [←moment]
  calc
    _ = ∫ x in J, g x*W x := (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by rw [Function.notMem_support.mp (fun h => hx (support h)),zero_mul])).symm
    _ ≤ ∫ x in J, M*W x := by
      apply integral_mono_ae hprod.integrableOn (wi.const_mul _)
      apply ae_restrict_of_ae
      filter_upwards [cap] with x hx
      exact mul_le_mul_of_nonneg_right hx (test _)
    _ = _ := by rw [integral_const_mul,mean]; ring

end OMA.CSDual35

/- A finite cosine series with integer coefficients. -/

namespace OMA.Poly35

noncomputable def cosSum : List ℤ → ℕ → ℝ → ℝ
  | [],_,_ => 0
  | c::cs,k,t => c*Real.cos (k*t) + cosSum cs (k+1) t

end OMA.Poly35

/- Exact certificates of nonnegativity from squared trigonometric polynomials. -/

namespace OMA.Square35
open Finset

private def gap {n : ℕ} (i j : Fin (n+1)) : Fin (n+1) :=
  ⟨if i.val≤j.val then j.val-i.val else i.val-j.val, by split <;> omega⟩

def coeff {n : ℕ} (h : Fin (n+1) → ℤ) (k : Fin (n+1)) : ℤ :=
  ∑ i, ∑ j, if gap i j = k then h i*h j else 0

private theorem cos_gap {n : ℕ} (i j : Fin (n+1)) (t : ℝ) :
    Real.cos ((gap i j).val*t) =
      Real.cos (i.val*t)*Real.cos (j.val*t) + Real.sin (i.val*t)*Real.sin (j.val*t) := by
  unfold gap
  split <;> rename_i hij
  · simp only [Nat.cast_sub hij,sub_mul,Real.cos_sub]
    ring
  · rw [Nat.cast_sub (by omega),sub_mul,Real.cos_sub]

private theorem square_nonneg {n : ℕ} (h : Fin (n+1) → ℤ) (t : ℝ) :
    0 ≤ ∑ k, (coeff h k:ℝ)*Real.cos (k.val*t) := by
  have he : ∑ k, (coeff h k:ℝ)*Real.cos (k.val*t) =
      (∑ i, (h i:ℝ)*Real.cos (i.val*t))^2 + (∑ i, (h i:ℝ)*Real.sin (i.val*t))^2 := by
    simp only [coeff,Int.cast_sum,Int.cast_ite,Int.cast_mul,Int.cast_zero,sum_mul,ite_mul,zero_mul]
    rw [sum_comm]
    simp_rw [sum_comm (γ:=Fin (n+1)) (s:=univ) (t:=univ)
      (f:=fun k j => if gap _ j = k then _ else (0:ℝ))]
    simp only [sum_ite_eq,mem_univ,if_true,cos_gap]
    rw [sq,sq,sum_mul,sum_mul,←sum_add_distrib]
    apply sum_congr rfl
    intro i _
    simp only [mul_sum,←sum_add_distrib]
    apply sum_congr rfl
    intro j _
    ring
  rw [he]
  positivity

def valid {n : ℕ} (c h : Fin (n+1) → ℤ) : Bool :=
  decide ((∑ j : Fin n, |c j.succ-coeff h j.succ|) ≤ c 0-coeff h 0)

theorem sound {n : ℕ} (c h : Fin (n+1) → ℤ) (hcheck : valid c h = true) (t : ℝ) :
    0≤∑ i, (c i:ℝ)*Real.cos (i.val*t) := by
  have hscore : (∑ j : Fin n, |(c j.succ:ℝ)-coeff h j.succ|) ≤ c 0-coeff h 0 := by
    exact_mod_cast (of_decide_eq_true hcheck :
      (∑ j : Fin n, |c j.succ-coeff h j.succ|) ≤ c 0-coeff h 0)
  have htail (j : Fin n) :
      -|(c j.succ:ℝ)-coeff h j.succ| ≤ ((c j.succ:ℝ)-coeff h j.succ)*Real.cos (j.succ.val*t) := by
    apply (abs_le.mp ?_).1
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_le.mpr ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩)
  have hs := Finset.sum_le_sum (s:=univ) (fun j _ => htail j)
  have hn := square_nonneg h t
  rw [Fin.sum_univ_succ] at hn ⊢
  simp only [Fin.val_zero,Nat.cast_zero,zero_mul,Real.cos_zero,mul_one] at hn ⊢
  simp only [sum_neg_distrib,sub_mul,sum_sub_distrib] at hs
  linarith

end OMA.Square35

/- Exact interpolation of two finite Chebyshev expansions by integer samples. -/
namespace OMA.ChebInterp35
open Polynomial Real

/-- Accumulated Chebyshev sum; the two auxiliary values are consecutive
Chebyshev polynomials, so evaluation costs one recurrence step per coefficient. -/
def run {R : Type*} [Ring R] (x : R) : List ℤ → R → R → R → R
  | [], _, _, total => total
  | c::cs, p, q, total => run x cs q (2*x*q-p) (total+(c:R)*p)

def vI (cs : List ℤ) (x : ℤ) := run x cs 1 x 0

private theorem run_map {R D : Type*} [Ring R] [Ring D] (h : R →+* D)
    (cs : List ℤ) (x p q total : R) :
    h (run x cs p q total) = run (h x) cs (h p) (h q) (h total) := by
  induction cs generalizing p q total with
  | nil => rfl
  | cons c cs ih => simp only [run,ih,map_sub,map_mul,map_ofNat,map_add,map_intCast]

private theorem bound_deg (cs : List ℤ) (x p q total : ℝ[X]) (k : ℕ)
    (hx : x.natDegree ≤ 1) (hp : p.natDegree ≤ k) (hq : q.natDegree ≤ k+1)
    (hs : total.natDegree ≤ 32) (len : k+cs.length ≤ 33) :
    (run x cs p q total).natDegree ≤ 32 := by
  induction cs generalizing p q total k with
  | nil => exact hs
  | cons c cs ih =>
    simp only [List.length_cons] at len
    apply ih _ _ _ (k+1) hq
    · apply (natDegree_sub_le ..).trans (max_le _ _)
      · have two : (2*x).natDegree ≤ 1 := by
          apply (natDegree_mul_le ..).trans
          simpa using hx
        have h := natDegree_mul_le (p:=2*x) (q:=q)
        omega
      · omega
    · apply (natDegree_add_le ..).trans (max_le hs _)
      have h := natDegree_mul_le (p:=(c:ℝ[X])) (q:=p)
      have hc : (c:ℝ[X]).natDegree=0 := by simp
      omega
    · omega

private theorem polynomial_int (cs : List ℤ) (x : ℤ) (p : ℝ[X]) (y : ℝ)
    (hp : p.eval y = x) : (run p cs 1 p 0).eval y = (vI cs x:ℝ) := by
  have h := run_map (Polynomial.evalRingHom y) cs p 1 p 0
  have hi := run_map (Int.castRingHom ℝ) cs x 1 x 0
  simpa only [Polynomial.coe_evalRingHom,map_one,map_zero,hp,Int.coe_castRingHom,vI] using h.trans
    (by simpa only [Polynomial.coe_evalRingHom,map_one,map_zero,hp,Int.coe_castRingHom] using hi.symm)

private theorem cos_run (cs : List ℤ) (t : ℝ) (k : ℕ) (total : ℝ) :
    run (Real.cos t) cs (Real.cos (k*t)) (Real.cos ((k+1:ℕ)*t)) total =
      total + OMA.Poly35.cosSum cs k t := by
  induction cs generalizing k total with
  | nil => simp [run,OMA.Poly35.cosSum]
  | cons c cs ih =>
    have trig := Real.two_mul_cos_mul_cos ((k+1)*t) t
    rw [show ((k:ℝ)+1)*t-t = k*t by ring,
      show ((k:ℝ)+1)*t+t = (k+1+1)*t by ring] at trig
    simp only [run,OMA.Poly35.cosSum,Nat.cast_add,Nat.cast_one]
    rw [show 2*cos t*cos (((k:ℝ)+1)*t)-cos (k*t)=cos ((k+1+1)*t) by linarith only [trig]]
    simpa [add_assoc,one_add_one_eq_two] using ih (k+1) (total+c*cos (k*t))

private theorem polynomial_cos (cs : List ℤ) (p : ℝ[X]) (x t : ℝ)
    (hp : p.eval x = cos t) :
    (run p cs 1 p 0).eval x = OMA.Poly35.cosSum cs 0 t := by
  have h := run_map (Polynomial.evalRingHom x) cs p 1 p 0
  simp only [Polynomial.coe_evalRingHom,eval_one,eval_zero,hp] at h
  exact h.trans (by simpa using cos_run cs t 0 0)

theorem cos_eq {cs ds : List ℤ} (hc : cs.length ≤ 33) (hd : ds.length ≤ 33)
    (points : ∀ i : Fin 33, vI cs i.val = vI ds (2*(i.val:ℤ)-1)) {t s : ℝ}
    (ts : 2*Real.cos t-1=Real.cos s) :
    OMA.Poly35.cosSum cs 0 t = OMA.Poly35.cosSum ds 0 s := by
  let q : ℝ[X] := 2*X-1
  have dq : q.natDegree ≤ 1 := by
    apply (natDegree_sub_le ..).trans (max_le _ _)
    · apply (natDegree_mul_le ..).trans; simp
    · simp
  have eq : run (X : ℝ[X]) cs 1 X 0 = run q ds 1 q 0 := by
    apply eq_of_natDegree_lt_card_of_eval_eq _ _ (f:=fun i : Fin 33 => (i.val:ℝ))
      (fun i j h => Fin.ext (Nat.cast_injective (R:=ℝ) h))
    · intro i
      rw [polynomial_int cs (i.val:ℤ) _ _ (by simp),
        polynomial_int ds (2*(i.val:ℤ)-1) _ _ (by simp [q]),points i]
    · change max _ _ < 33
      exact Nat.lt_succ_of_le (max_le
        (bound_deg _ _ _ _ _ 0 (by simp) (by simp) (by simp) (by simp) (by simpa using hc))
        (bound_deg _ _ _ _ _ 0 dq (by simp) dq (by simp) (by simpa using hd)))
  rw [←polynomial_cos cs X (cos t) t (by simp),
    ←polynomial_cos ds q (cos t) s (by simpa [q] using ts),eq]

end OMA.ChebInterp35

/- A 32-frequency dual certificate for the supremum of autoconvolution. -/

namespace OMA.Spectral35

open Finset OMA.Poly35

private def data : Array (ℤ × ℤ × ℤ × ℤ) := #[
  (340113, 680299, 282018, 218052), (218270, -199360, 180987, 42514),
  (117477, -91965, 97411, 14721), (77204, 67521, 64017, 9853),
  (71876, 45885, 59599, 5804), (65158, -44969, 54029, 5640),
  (51335, -22365, 42567, 2311), (42566, 28918, 35296, 3207),
  (40902, 15610, 33916, 1439), (38731, -23347, 32116, 2382),
  (33611, -9369, 27870, 795), (29884, 17881, 24780, 1708),
  (28859, 6952, 23930, 555), (27721, -15375, 22986, 1385),
  (25269, -4334, 20953, 358), (23359, 12774, 19369, 1100),
  (22542, 3015, 18692, 262), (21666, -11256, 17966, 926),
  (20345, -1625, 16870, 188), (19376, 9794, 16067, 775),
  (18608, 598, 15430, 146), (17621, -8601, 14742, 654),
  (16808, 296, 13937, 118), (16578, 7603, 13747, 550),
  (15919, -1327, 13200, 119), (14488, -6324, 12014, 433),
  (13723, 1989, 11379, 115), (14521, 5461, 12041, 345),
  (14636, -3615, 12136, 201), (11501, -2906, 9537, 147),
  (5994, 4231, 11428, 306), (1598, -1451, 6267, 82)]

private def row (i : Fin 32) := data[i.val]'i.isLt
private def B (i : Fin 32) := (row i).1
private def L (i : Fin 32) := (row i).2.1
private def T (i : Fin 32) := (row i).2.2.1
private def P (i : Fin 32) := (row i).2.2.2

private theorem cosSum_ofFn {n : ℕ} (c : Fin n → ℤ) (k : ℕ) (t : ℝ) :
    cosSum (List.ofFn c) k t = ∑ i, c i * Real.cos (((i.val+k:ℕ):ℝ)*t) := by
  induction n generalizing k with
  | zero => simp [cosSum]
  | succ n ih =>
    rw [List.ofFn_succ,cosSum,Fin.sum_univ_succ,ih]
    simp only [Fin.val_zero,zero_add,Fin.val_succ]
    congr 1
    apply sum_congr rfl
    intro i _
    rw [show i.val+1+k=i.val+(k+1) by omega]

private def level := (-460300:ℤ)::List.ofFn L

private def unit : ℤ := 4294967296000000

private def windowFactorArray : Array ℤ := #[
  9469872369, 21089549866, 26070597886, 19051585755, 7364113316,
  1404511872, 2791594630, 4723688639, 3356994370, 1170354873,
  1327686727, 2330095745, 2056309837, 958439466, 942107156,
  1509850253, 1434219017, 790337938, 795984748, 1146746499,
  1086834356, 654423922, 739638506, 968906658, 860498146,
  545097249, 711729771, 909780974, 715686837, 444058712,
  761224418, 1104474426, 724757153]
private def windowFactor (i : Fin 33) := windowFactorArray[i.val]'i.isLt

private def levelCoeffsArray : Array ℤ := #[
  19693008770815000000, -30907252270614000000, 19006210963028000000, -6897634596194000000, -3298921249112000000,
  10861114135314000000, -15567075526916000000, 17300385328134000000, -16037953719976000000, 12092412572426000000,
  -6462385359484000000, 751247718366000000, 3184895909560000000, -4094146407502000000, 2240806869228000000,
  467435047238000000, -1763207273748000000, 885710183426000000, 603169856228000000, -701911486426000000,
  -238901011928000000, 329525163658000000, 192335594092000000, -42942232338000000, -84709434776000000,
  -43430288766000000, -13060169708000000, -2625181178000000, -365559688000000, -35084790000000,
  -2226468000000, -84402000000, -1451000000]
private def levelCoeffs (i : Fin 33) := levelCoeffsArray[i.val]'i.isLt

private def levelFactorArray : Array ℤ := #[
  2129223602, -1996242611, 1480020684, -861642228, 274117432,
  244559697, -691632274, 1057301864, -1305378858, 1354482974,
  -1151168740, 688726193, -82883630, -418608192, 548131580,
  -254115577, -185351776, 316251026, -26817272, -206439247,
  24886950, 118962102, 32683446, -30408402, -29975826,
  -13181328, -3660046, -698424, -93662, -8733,
  -541, -20, 0]
private def levelFactor (i : Fin 33) := levelFactorArray[i.val]'i.isLt

private def wc : Fin 33 → ℤ := Fin.cons (unit*397000) (fun i => unit*(2*B i))

private theorem window_check : OMA.Square35.valid wc windowFactor = true := by decide +kernel
private theorem level_check : OMA.Square35.valid levelCoeffs levelFactor = true := by decide +kernel

private theorem level_id : ∀ i : Fin 33, OMA.ChebInterp35.vI (level.map (unit*·)) i.val =
    OMA.ChebInterp35.vI (List.ofFn levelCoeffs) (2*(i.val:ℤ)-1) := by decide +kernel

private theorem cosSum_scale (v : ℤ) (cs : List ℤ) (k : ℕ) (t : ℝ) :
    cosSum (cs.map (v*·)) k t = v*cosSum cs k t := by
  induction cs generalizing k with
  | nil => simp [cosSum]
  | cons c cs ih => simp only [List.map_cons,cosSum,ih,Int.cast_mul]; ring

private theorem window_pos (t : ℝ) : 0 ≤ 397000 + 2*∑ i, (B i:ℝ)*Real.cos (((i.val+1:ℕ):ℝ)*t) := by
  have h := OMA.Square35.sound wc windowFactor window_check t
  rw [Fin.sum_univ_succ] at h
  simp only [wc,Fin.cons_zero,Fin.cons_succ,Fin.val_succ,Fin.val_zero,Nat.cast_zero,
    zero_mul,Real.cos_zero,mul_one,Int.cast_mul,Int.cast_ofNat,mul_assoc,←mul_sum] at h
  norm_num [unit] at h
  push_cast
  linarith

private theorem level_pos (t : ℝ) (ht : 0≤Real.cos t) :
    460300 ≤ ∑ i, (L i:ℝ)*Real.cos (((i.val+1:ℕ):ℝ)*t) := by
  let s := Real.arccos (2*Real.cos t-1)
  have hs : 2*Real.cos t-1=Real.cos s := (Real.cos_arccos (by linarith)
    (by linarith [Real.cos_le_one t])).symm
  have h := OMA.Square35.sound levelCoeffs levelFactor level_check s
  have hid := OMA.ChebInterp35.cos_eq (cs:=level.map (unit*·)) (ds:=List.ofFn levelCoeffs)
    (by decide +kernel) (by simp) level_id hs
  rw [cosSum_scale,cosSum_ofFn] at hid
  simp only [level,cosSum,Nat.cast_zero,zero_mul,Real.cos_zero,mul_one,zero_add,add_zero,cosSum_ofFn,
    Int.cast_neg,Int.cast_ofNat] at hid
  norm_num [unit] at hid
  push_cast
  linarith

private def valid (b l t p : ℤ) : Bool :=
  let c := 1206000*t+b*1000000
  decide (0<c ∧ b*1000000≤1206000*t ∧
    l^2 * 1000000^3 ≤ 4*c*(p*1000000^2-603000*t^2))

private theorem rows_valid : ∀ i : Fin 32, valid (B i) (L i) (T i) (P i) = true := by decide +kernel
private theorem score : (∑ i, P i) = 317191 := by decide +kernel

private theorem mode (b l t p : ℤ) (h : valid b l t p = true) (x y : ℝ) :
    (l:ℝ)*x ≤ 603000*(x^2+y^2)^2 + b*(x^2-y^2) + p := by
  unfold valid at h
  obtain ⟨h1,h2,h3⟩ := of_decide_eq_true h
  let z : ℝ := t/1000000
  let c : ℝ := 1206000*z+b
  have r1 : (0:ℝ)<1206000*t+b*1000000 := by exact_mod_cast h1
  have r2 : (b:ℝ)*1000000≤1206000*t := by exact_mod_cast h2
  have r3 : (l:ℝ)^2*1000000^3 ≤ 4*(1206000*t+b*1000000)*(p*1000000^2-603000*(t:ℝ)^2) := by
    exact_mod_cast h3
  have hc : 0<c := by dsimp [c,z]; linarith
  have hb : 0≤1206000*z-b := by dsimp [z]; linarith
  have hq : (l:ℝ)^2 ≤ 4*c*(p-603000*z^2) := by dsimp [c,z]; nlinarith only [r3]
  have hlin : 0≤4*c*(c*x^2+p-603000*z^2-l*x) := by nlinarith only [sq_nonneg (2*c*x-l), hq]
  have hc' : 0≤c*x^2+p-603000*z^2-l*x := nonneg_of_mul_nonneg_right hlin (by positivity)
  have hr := sq_nonneg (x^2+y^2-z)
  have hi := mul_nonneg hb (sq_nonneg y)
  dsimp [c] at hc'
  nlinarith only [hc',hr,hi]

/-- A finite dual lower bound in the normalization where the sum of two
independent samples is supported on an interval of length one. -/
theorem bound (a b : Fin 32 → ℝ) (M : ℝ)
    (bessel : 1 + 2*∑ i, (a i^2+b i^2)^2 ≤ M)
    (win : ∀ (c : Fin 32 → ℝ) (m : ℝ),
      (∀ t : ℝ, 0 ≤ m + 2*∑ i, c i*Real.cos (((i.val+1:ℕ):ℝ)*t)) →
      m + 2*∑ i, c i*(a i^2-b i^2) ≤ m*M)
    (lev : ∀ (c : Fin 32 → ℝ) (u : ℝ),
      (∀ t : ℝ, 0 ≤ Real.cos t → u ≤ ∑ i, c i*Real.cos (((i.val+1:ℕ):ℝ)*t)) →
      u ≤ ∑ i, c i*a i) : 1.286 ≤ M := by
  have hw := win (fun i => (B i:ℝ)) 397000 window_pos
  have hl := lev (fun i => (L i:ℝ)) 460300 level_pos
  have hs := Finset.sum_le_sum (s:=Finset.univ)
    (fun i _ => mode (B i) (L i) (T i) (P i) (rows_valid i) (a i) (b i))
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,← Int.cast_sum,score,Int.cast_ofNat] at hs
  linarith

end OMA.Spectral35

/- Transfer a trigonometric certificate to the essential supremum and then
take the infimum over all nonnegative mass-one functions on the interval. -/
namespace OMA.Green35Sharp
open MeasureTheory Filter Finset Real
open scoped ENNReal Convolution

theorem lower (certificate : ∀ (a b : Fin 32 → ℝ) (M : ℝ),
    1+2*∑ i, (a i^2+b i^2)^2 ≤ M →
    (∀ (c : Fin 32 → ℝ) (m : ℝ), (∀ t : ℝ, 0 ≤ m+2*∑ i, c i*Real.cos (((i.val+1:ℕ):ℝ)*t)) →
      m+2*∑ i, c i*(a i^2-b i^2) ≤ m*M) →
    (∀ (c : Fin 32 → ℝ) (u : ℝ), (∀ t : ℝ, 0≤Real.cos t → u≤∑ i, c i*Real.cos (((i.val+1:ℕ):ℝ)*t)) →
      u≤∑ i, c i*a i) → 1.286 ≤ M) : 0.643 ≤ Green35.c ⊤ := by
  apply le_sInf
  rintro _ ⟨f,hf,rfl⟩
  by_cases ht : eLpNorm (f ⋆ f) ⊤ = ⊤
  · rw [ht]; exact le_top
  let M := (eLpNorm (f ⋆ f) ⊤).toReal
  have cap : ∀ᵐ x, (f ⋆ f) x ≤ M := by
    filter_upwards [ae_le_eLpNormEssSup (f:= f ⋆ f) (μ:=volume)] with x hx
    exact (le_abs_self _).trans (by
      simpa [M,eLpNorm_exponent_top,Real.norm_eq_abs] using ENNReal.toReal_mono ht hx)
  let t (i : Fin 32) := ((i.val:ℝ)+1)*π
  let a (i : Fin 32) := OMA.CSDual35.A f (t i)
  let b (i : Fin 32) := OMA.CSDual35.B f (t i)
  have e : 1.286 ≤ 2*M := certificate a b (2*M) (OMA.Moment35.bessel hf cap 32)
    (fun c m test => OMA.CSDual35.output_bound hf cap c m (by simpa using test))
    (fun c u test => OMA.CSDual35.input_bound hf c u (by simpa using test))
  change ((0.643:NNReal):ℝ≥0∞) ≤ _
  apply (ENNReal.toReal_le_toReal ENNReal.coe_ne_top ht).mp
  rw [ENNReal.coe_toReal,NNReal.coe_ofScientific]
  change 0.643 ≤ M
  linarith

theorem relax : (0.64:ℝ≥0∞) ≤ 0.643 := by
  change ((0.64:NNReal):ℝ≥0∞) ≤ ((0.643:NNReal):ℝ≥0∞)
  rw [ENNReal.coe_le_coe,←NNReal.coe_le_coe,NNReal.coe_ofScientific,NNReal.coe_ofScientific]
  norm_num

end OMA.Green35Sharp

open scoped ENNReal in
theorem OMA.Green35Sharp.c_inf_lower_643 : (0.643:ℝ≥0∞) ≤ Green35.c ⊤ :=
  OMA.Green35Sharp.lower OMA.Spectral35.bound

theorem OMA.solution : type_of% @Green35.variants.c_inf_lower :=
  OMA.Green35Sharp.relax.trans OMA.Green35Sharp.c_inf_lower_643
