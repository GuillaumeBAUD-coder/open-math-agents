import OMAReductions.R_Erdos516_erdos_516_variants_limsup_ratio_eq_one_R1
import Mathlib.Analysis.Fourier.AddCircle

-- Credit: @marcusbuffett
open Finset Filter MeasureTheory AddCircle
open scoped Topology

theorem OMA.solution : OMA.R_Erdos516_erdos_516_variants_limsup_ratio_eq_one_R1.H2 := by
  classical
  intro n a f hn ha hs
  have ha' : 0 < ‖a 1‖ := norm_pos_iff.mpr ha
  filter_upwards [eventually_ge_atTop (1:ℝ), eventually_gt_atTop (2/‖a 1‖)] with r hr hr'
  by_contra! h
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  obtain ⟨K, hu, hK⟩ := ((Metric.tendstoUniformlyOn_iff.mp
    (OMA.SectionApprox516.uniform hs r hr0) 1 (by norm_num)).and (eventually_ge_atTop 2)).exists
  let c (j : ℕ) := a j*(r:ℂ)^(n j)
  let g (j : ℕ) (x : AddCircle (1:ℝ)) := c j * fourier (n j) x
  let S := ∑ j ∈ range K, g j
  have powF (x : AddCircle (1:ℝ)) (m : ℕ) : (fourier 1 x)^m = fourier (m:ℤ) x := by
    induction m with
    | zero => simp only [pow_zero, Nat.cast_zero, fourier_zero]
    | succ m ih => rw [pow_succ, ih, Nat.cast_succ, fourier_add]
  have B (x : AddCircle (1:ℝ)) : ‖S x‖ ≤ 2 := by
    let z : ℂ := (r:ℂ)*fourier 1 x
    have hz : ‖z‖ = r := by simp only [z, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0, fourier_apply, Circle.norm_coe, mul_one]
    have val : S x = ∑ j ∈ range K, a j*z^(n j) := by
      simp only [S, Finset.sum_apply, g, c, z, mul_pow, powF, mul_assoc]
    have err := (abs_norm_sub_norm_le (f z) _).trans_lt
      (show ‖f z - (∑ j ∈ range K, a j*z^(n j))‖ < 1 by simpa [dist_eq_norm] using hu z hz.le)
    rw [val]
    linarith [(abs_lt.mp err).1,h z hz]
  have hb : ‖fourierCoeff S (n 1)‖ ≤ 2 := by
    unfold fourierCoeff
    have hbound := norm_integral_le_of_norm_le_const (μ := (haarAddCircle : Measure (AddCircle (1:ℝ))))
      (f := fun x => fourier (-(n 1:ℤ)) x • S x) (C := 2) (ae_of_all _ fun x => by
        simpa only [smul_eq_mul, norm_mul, fourier_apply, Circle.norm_coe, one_mul] using B x)
    simpa using hbound
  have hg (j : ℕ) : Integrable (g j) haarAddCircle :=
    (continuous_const.mul (fourier (n j)).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have coeff : fourierCoeff S (n 1) = c 1 := by
    change fourierCoeff (∑ j ∈ range K, g j) (n 1) = c 1
    rw [fourierCoeff.sum _ _ (fun j _ => hg j), Finset.sum_apply]
    simp only [g, fourierCoeff.const_mul, fourierCoeff_fourier]
    rw [Finset.sum_eq_single 1]
    · simp
    · intro j _ hne
      have hnj : (n 1:ℤ) ≠ n j := by exact_mod_cast (hn.injective.ne hne.symm)
      simp [Pi.single_eq_of_ne hnj]
    · simp [Finset.mem_range,show 1<K by omega]
  rw [coeff] at hb
  simp only [c, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0] at hb
  have hn1 : 1 ≤ n 1 := by have := hn (show 0<1 by decide); omega
  have hp := pow_le_pow_right₀ hr hn1
  rw [pow_one] at hp
  linarith [(div_lt_iff₀ ha').mp hr', mul_le_mul_of_nonneg_left hp ha'.le]
