import FormalConjectures.Paper.RiemannZetaMoments

/-!
# The cubic divisor-polynomial reduction of the sixth zeta moment

Write D for the divisor Dirichlet polynomial of length t/(2π) on the critical
line, and W for D multiplied by the quotient of the real gamma factor and
its conjugate. Conrey and Ghosh (https://arxiv.org/pdf/math/9807187, pp. 4–5) predict
cancellation in Re(W³) and a main term in |W|² Re(W). H2 and H3 isolate
these two integrals with the moving cutoff retained.

H1 is the complex approximate functional equation for ζ². The exact
functional equation identifies the error after rotation. The transfer
lemma absorbs its logarithmic error after cubing without using a sixth- or
fourth-moment bound. The identity (2 Re W)³ = 2 Re(W³) + 6 |W|² Re W
then gives the coefficient 42 from the coefficient 7 in H3.
-/

open Complex Filter Real MeasureTheory Set Asymptotics Topology RiemannZetaMoments
open scoped ComplexConjugate Nat

namespace OMA.R_RiemannZetaMoments_moment_isEquiv_109_R1

private theorem cube_error {x y d L : ℝ} (hx : 0 ≤ x) (hd : 0 ≤ d) (hL : 1 ≤ L)
    (h : |x - y| ≤ d) :
    |x ^ 3 - y ^ 3| ≤ (7 / L) * x ^ 3 + 9 * (d * L) ^ 3 := by
  have hL0 : 0 < L := by linarith
  have hdL : d ≤ d * L := le_mul_of_one_le_right hd hL
  have hy : |y| ≤ x + d := calc
    |y| = |x - (x - y)| := by ring_nf
    _ ≤ |x| + |x - y| := abs_sub _ _
    _ ≤ x + d := by rw [abs_of_nonneg hx]; gcongr
  rcases le_total x (d * L) with hs | hs
  · have hy' : |y| ≤ 2 * (d * L) := by linarith
    calc
      |x ^ 3 - y ^ 3| ≤ |x ^ 3| + |y ^ 3| := abs_sub _ _
      _ ≤ (d * L) ^ 3 + (2 * (d * L)) ^ 3 := by
        rw [abs_pow, abs_pow, abs_of_nonneg hx]
        gcongr
      _ ≤ _ := by linarith only [show 0 ≤ (7 / L) * x ^ 3 by positivity]
  · have hy' : |y| ≤ 2 * x := by linarith
    have hquad : |x ^ 2 + x * y + y ^ 2| ≤ 7 * x ^ 2 := calc
      _ ≤ (|x ^ 2| + |x * y|) + |y ^ 2| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ x ^ 2 + x * (2 * x) + (2 * x) ^ 2 := by
        rw [abs_mul, abs_pow, abs_pow, abs_of_nonneg hx]
        gcongr
      _ = _ := by ring
    calc
      |x ^ 3 - y ^ 3| = |x - y| * |x ^ 2 + x * y + y ^ 2| := by rw [← abs_mul]; congr 1; ring
      _ ≤ d * (7 * x ^ 2) := mul_le_mul h hquad (abs_nonneg _) hd
      _ ≤ (x / L) * (7 * x ^ 2) := by gcongr; exact (le_div_iff₀ hL0).2 hs
      _ ≤ _ := by
        have h₀ : 0 ≤ 9 * (d * L) ^ 3 := by positivity
        linarith only [h₀, show x / L * (7 * x ^ 2) = 7 / L * x ^ 3 by ring]

private theorem projected_cube (z : ℂ) :
    (2 * z.re) ^ 3 = 2 * (z ^ 3).re + 6 * ‖z‖ ^ 2 * z.re := by
  rw [Complex.sq_norm]
  simp only [pow_succ, pow_zero, one_mul, Complex.mul_re, Complex.mul_im,
    Complex.normSq_apply]
  ring

private theorem truncation_integrable {F : ℕ → ℝ → ℝ} (hF : ∀ k, Continuous (F k))
    {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun t => F ⌊t / (2 * π)⌋₊ t) volume 0 T := by
  let n := fun t : ℝ => ⌊t / (2 * π)⌋₊
  have hn : Measurable n := by dsimp [n]; fun_prop
  let B := Finset.range (n T + 1)
  let part := fun k : ℕ => {t : ℝ | n t = k}.indicator (F k)
  have hpart (k : ℕ) : IntervalIntegrable (part k) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    have hk := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1
      ((hF k).intervalIntegrable (μ := volume) 0 T)
    exact hk.indicator (measurableSet_eq_fun hn measurable_const)
  apply (IntervalIntegrable.sum B (fun k _ => hpart k)).congr
  intro t ht
  rw [uIoc_of_le hT] at ht
  have ht' : n t ∈ B := Finset.mem_range.mpr (Nat.lt_succ_of_le
    (Nat.floor_mono (div_le_div_of_nonneg_right ht.2 (by positivity))))
  rw [Finset.sum_apply, Finset.sum_eq_single (n t)]
  · simp [part, n]
  · intro k _ hk
    simp [part, Ne.symm hk]
  · exact fun h => (h ht').elim

private theorem transfer_cube {x y : ℝ → ℝ} {C c : ℝ}
    (hx : ∀ t, 0 ≤ x t) (hC : 0 ≤ C)
    (herr : ∀ t ≥ 0, |x t - y t| ≤ C * Real.log (max 3 t))
    (hix : ∀ T ≥ 0, IntervalIntegrable (fun t => x t ^ 3) volume 0 T)
    (hiy : ∀ T ≥ 0, IntervalIntegrable (fun t => y t ^ 3) volume 0 T)
    (hy : Tendsto (fun T => (∫ t in (0 : ℝ)..T, y t ^ 3) / (T * Real.log T ^ 9))
      atTop (𝓝 c)) :
    Tendsto (fun T => (∫ t in (0 : ℝ)..T, x t ^ 3) / (T * Real.log T ^ 9)) atTop (𝓝 c) := by
  let X := fun T => (∫ t in (0 : ℝ)..T, x t ^ 3) / (T * Real.log T ^ 9)
  let Y := fun T => (∫ t in (0 : ℝ)..T, y t ^ 3) / (T * Real.log T ^ 9)
  let a := fun T => 7 / Real.log T
  let b := fun T => 9 * C ^ 3 * (Real.log T)⁻¹ ^ 3
  have hi := tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have ha : Tendsto a atTop (𝓝 0) := by
    simpa [a, div_eq_mul_inv, Function.comp_def] using hi.const_mul 7
  have hb : Tendsto b atTop (𝓝 0) := by
    simpa [b, Function.comp_def] using (hi.pow 3).const_mul (9 * C ^ 3)
  have he : ∀ᶠ T : ℝ in atTop, |X T - Y T| ≤ a T * X T + b T := by
    filter_upwards [eventually_ge_atTop (3 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1]
      with T hT hL
    have hT0 : 0 < T := by linarith
    have hL0 : 0 < Real.log T := by linarith
    have hden : 0 < T * Real.log T ^ 9 := by positivity
    let d := C * Real.log T
    let k := 9 * (d * Real.log T) ^ 3
    have hp (t : ℝ) (ht : t ∈ Icc 0 T) :
        |x t ^ 3 - y t ^ 3| ≤ a T * x t ^ 3 + k := by
      apply cube_error (hx t) (mul_nonneg hC hL0.le) hL
      exact (herr t ht.1).trans (mul_le_mul_of_nonneg_left
        (Real.log_le_log (by positivity) (max_le hT ht.2)) hC)
    have hbound := intervalIntegral.integral_mono_on hT0.le
      (((hix T hT0.le).sub (hiy T hT0.le)).abs)
      (((hix T hT0.le).const_mul (a T)).add (intervalIntegrable_const (b := T) (c := k))) hp
    have hab := (intervalIntegral.abs_integral_le_integral_abs hT0.le).trans hbound
    rw [intervalIntegral.integral_sub (hix T hT0.le) (hiy T hT0.le),
      intervalIntegral.integral_add ((hix T hT0.le).const_mul (a T)) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hab
    dsimp only [X, Y]
    rw [← sub_div, abs_div, abs_of_pos hden]
    apply (div_le_div_of_nonneg_right hab hden.le).trans_eq
    dsimp only [b, k, d]
    simp only [sub_zero, smul_eq_mul]
    field_simp
  have hbounds : ∀ᶠ T : ℝ in atTop,
      (Y T - b T) / (1 + a T) ≤ X T ∧ X T ≤ (Y T + b T) / (1 - a T) := by
    filter_upwards [he, ha.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
      ha.eventually (Ioi_mem_nhds (show (-1 : ℝ) < 0 by norm_num))] with T h ha₁ ha₂
    obtain ⟨hl, hu⟩ := abs_le.mp h
    change a T < 1 at ha₁
    change -1 < a T at ha₂
    constructor
    · apply (div_le_iff₀ (by linarith : 0 < 1 + a T)).2
      linarith only [hl]
    · apply (le_div_iff₀ (by linarith : 0 < 1 - a T)).2
      linarith only [hu]
  have h₁ : Tendsto (fun T => (Y T - b T) / (1 + a T)) atTop (𝓝 c) := by
    simpa [Y, Pi.div_def] using (hy.sub hb).div
      (tendsto_const_nhds.add ha) (by norm_num : (1 : ℝ) + 0 ≠ 0)
  have h₂ : Tendsto (fun T => (Y T + b T) / (1 - a T)) atTop (𝓝 c) := by
    simpa [Y, Pi.div_def] using (hy.add hb).div
      (tendsto_const_nhds.sub ha) (by norm_num : (1 : ℝ) - 0 ≠ 0)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h₁ h₂
    (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)

/-- Rotation by the gamma phase turns the error in the complex approximate
functional equation into exactly the error in its real projection. -/
private theorem phase_error {s : ℂ} (hs : s.re = 1 / 2) (D : ℂ) :
    |‖riemannZeta s‖ ^ 2 - 2 * (Gammaℝ s / conj (Gammaℝ s) * D).re| =
    ‖riemannZeta s ^ 2 - (D + (conj (Gammaℝ s) / Gammaℝ s) ^ 2 * conj D)‖ := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  have hsc : conj s = 1 - s := by
    apply Complex.ext <;> simp [hs]
    ring
  have hΓ : Gammaℝ (conj s) = conj (Gammaℝ s) := by
    have harg : (π : ℂ).arg ≠ π := by
      simp [Complex.arg_ofReal_of_nonneg Real.pi_pos.le, Real.pi_pos.ne]
    have hg := Complex.Gamma_conj (s / 2)
    have hp := Complex.cpow_conj (π : ℂ) (-s / 2) harg
    simp only [map_div₀, map_neg, map_ofNat, conj_ofReal] at hg hp
    simp only [Gammaℝ_def, map_mul, hg, hp]
  let G := Gammaℝ s
  let z := riemannZeta s
  have hg0 : G ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [hs]; norm_num)
  have hgc0 : conj G ≠ 0 := by simpa using hg0
  have hF : z * G = conj z * conj G := calc
    z * G = completedRiemannZeta s :=
      (eq_div_iff hg0).mp (riemannZeta_def_of_ne_zero hs0)
    _ = completedRiemannZeta (conj s) := hsc ▸ (completedRiemannZeta_one_sub s).symm
    _ = conj z * conj G := by
      rw [← hΓ, ← riemannZeta_conj]
      exact ((eq_div_iff (Gammaℝ_ne_zero_of_re_pos (by simp [hs]))).mp
        (riemannZeta_def_of_ne_zero (by simpa using hs0))).symm
  have hrot : G / conj G * z = conj z := by
    apply (div_mul_eq_mul_div ..).trans
    exact (div_eq_iff hgc0).2 (by simpa [mul_comm] using hF)
  have hz : G / conj G * z ^ 2 = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [sq, ← mul_assoc, hrot, Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
  have hc : conj (G / conj G * D) = (conj G / G) * conj D := by simp
  have hrotD : G / conj G * ((conj G / G) ^ 2 * conj D) = conj (G / conj G * D) := by
    rw [hc]
    field_simp
  have hid : G / conj G * (z ^ 2 - (D + (conj G / G) ^ 2 * conj D)) =
      ((‖z‖ ^ 2 - 2 * (G / conj G * D).re : ℝ) : ℂ) := by
    rw [mul_sub, hz, mul_add, hrotD, Complex.add_conj, Complex.ofReal_sub]
  have hn : ‖G / conj G‖ = 1 := by simp [hg0]
  have hh := congrArg norm hid
  simpa only [norm_mul, hn, one_mul, Complex.norm_real, Real.norm_eq_abs] using hh.symm

/-- The symmetric approximate functional equation for ζ² at its natural cutoff. -/
def H1 : Prop :=
  let s := fun t : ℝ => (1 / 2 : ℂ) + I * t
  let D := fun t : ℝ =>
    ∑ n ∈ Finset.range ⌊t / (2 * π)⌋₊,
      ((n + 1).divisors.card : ℂ) * ((n + 1 : ℕ) : ℂ) ^ (-s t)
  ∃ C : ℝ, 0 ≤ C ∧ ∀ t ≥ 0,
    ‖riemannZeta (s t) ^ 2 - (D t +
      (conj (Gammaℝ (s t)) / Gammaℝ (s t)) ^ 2 * conj (D t))‖ ≤ C * Real.log (max 3 t)

/-- Cancellation in the cubic term with three copies of the same phase. -/
def H2 : Prop :=
  let s := fun t : ℝ => (1 / 2 : ℂ) + I * t
  let W := fun t : ℝ =>
    Gammaℝ (s t) / conj (Gammaℝ (s t)) *
      ∑ n ∈ Finset.range ⌊t / (2 * π)⌋₊,
        ((n + 1).divisors.card : ℂ) * ((n + 1 : ℕ) : ℂ) ^ (-s t)
  Tendsto (fun T => (∫ t in (0 : ℝ)..T, ((W t) ^ 3).re) / (T * Real.log T ^ 9))
    atTop (𝓝 0)

/-- The mixed cubic has two copies of the polynomial and one conjugate copy. -/
def H3 : Prop :=
  let s := fun t : ℝ => (1 / 2 : ℂ) + I * t
  let W := fun t : ℝ =>
    Gammaℝ (s t) / conj (Gammaℝ (s t)) *
      ∑ n ∈ Finset.range ⌊t / (2 * π)⌋₊,
        ((n + 1).divisors.card : ℂ) * ((n + 1 : ℕ) : ℂ) ^ (-s t)
  Tendsto (fun T => (∫ t in (0 : ℝ)..T, ‖W t‖ ^ 2 * (W t).re) /
    ((T * Real.log T ^ 9) * (arithmeticFactor 3 / 9 !))) atTop (𝓝 7)

theorem main : H1 → H2 → H3 → type_of% @RiemannZetaMoments.moment_isEquiv₃ := by
  intro hApprox hSpin hMix
  let s := fun t : ℝ => (1 / 2 : ℂ) + I * t
  let Wn := fun (N : ℕ) (t : ℝ) =>
    Gammaℝ (s t) / conj (Gammaℝ (s t)) *
      ∑ n ∈ Finset.range N, ((n + 1).divisors.card : ℂ) * ((n + 1 : ℕ) : ℂ) ^ (-s t)
  let W := fun t : ℝ => Wn ⌊t / (2 * π)⌋₊ t
  let x := fun t : ℝ => ‖riemannZeta (s t)‖ ^ 2
  let A := arithmeticFactor 3 / (9 ! : ℝ)
  let scale := fun T : ℝ => T * Real.log T ^ 9
  let U := fun T : ℝ => ∫ t in (0 : ℝ)..T, ((W t) ^ 3).re
  let V := fun T : ℝ => ∫ t in (0 : ℝ)..T, ‖W t‖ ^ 2 * (W t).re
  change Tendsto (fun T => U T / scale T) atTop (𝓝 0) at hSpin
  change Tendsto (fun T => V T / (scale T * A)) atTop (𝓝 7) at hMix
  obtain ⟨C, hC, hAFE⟩ := hApprox
  have he (t : ℝ) (ht : 0 ≤ t) : |x t - 2 * (W t).re| ≤ C * Real.log (max 3 t) :=
    (phase_error (s := s t) (by norm_num [s]) _).trans_le (hAFE t ht)
  have hA : A ≠ 0 := by
    intro hz
    simp only [hz, mul_zero, div_zero] at hMix
    have := tendsto_nhds_unique (tendsto_const_nhds (x := (0 : ℝ)) (f := atTop (α := ℝ))) hMix
    norm_num at this
  have hs : Continuous s := by dsimp [s]; fun_prop
  have hG0 (t : ℝ) : Gammaℝ (s t) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by norm_num [s])
  have hG : Continuous (fun t => Gammaℝ (s t)) := by
    have hi := differentiable_Gammaℝ_inv.continuous.comp hs
    have h := hi.inv₀ (fun t => inv_ne_zero (hG0 t))
    change Continuous (fun t => ((Gammaℝ (s t))⁻¹)⁻¹) at h
    simpa only [inv_inv] using h
  have hw (N : ℕ) : Continuous (Wn N) := by
    apply (hG.div (continuous_conj.comp hG) (fun t => by simpa using hG0 t)).mul
    apply continuous_finsetSum
    intro n hn
    apply continuous_const.mul
    exact hs.neg.const_cpow (Or.inl (by exact_mod_cast Nat.succ_ne_zero n))
  have hwI {f : ℂ → ℝ} (hf : Continuous f) (T : ℝ) (hT : 0 ≤ T) :
      IntervalIntegrable (fun t => f (W t)) volume 0 T :=
    truncation_integrable (F := fun N t => f (Wn N t)) (fun N => hf.comp (hw N)) hT
  have hxcont : Continuous x := by
    have hne (t : ℝ) : s t ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      norm_num [s] at this
    have hz : Continuous (fun t => riemannZeta (s t)) := continuous_iff_continuousAt.2 fun t =>
      (differentiableAt_riemannZeta (hne t)).continuousAt.comp hs.continuousAt
    exact hz.norm.pow 2
  have hV : Tendsto (fun T => V T / scale T) atTop (𝓝 (7 * A)) := by
    apply (hMix.mul_const A).congr'
    filter_upwards with T
    rw [← div_div, div_mul_cancel₀ _ hA]
  have hY : Tendsto (fun T => (∫ t in (0 : ℝ)..T, (2 * (W t).re) ^ 3) / scale T)
      atTop (𝓝 (42 * A)) := by
    have h := (hSpin.const_mul 2).add (hV.const_mul 6)
    rw [show (2 : ℝ) * 0 + 6 * (7 * A) = 42 * A by ring] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    have hu := hwI (f := fun z => (z ^ 3).re) (by fun_prop) T hT
    have hv := hwI (f := fun z => ‖z‖ ^ 2 * z.re) (by fun_prop) T hT
    have hid : (∫ t in (0 : ℝ)..T, (2 * (W t).re) ^ 3) = 2 * U T + 6 * V T := by
      simp_rw [projected_cube, mul_assoc (6 : ℝ)]
      rw [intervalIntegral.integral_add (hu.const_mul 2) (hv.const_mul 6)]
      simp only [intervalIntegral.integral_const_mul, U, V]
    change 2 * (U T / scale T) + 6 * (V T / scale T) =
      (∫ t in (0 : ℝ)..T, (2 * (W t).re) ^ 3) / scale T
    rw [hid]
    ring
  have hX := transfer_cube (x := x) (y := fun t => 2 * (W t).re)
    (fun t => sq_nonneg _) hC he (fun T _ => (hxcont.pow 3).intervalIntegrable 0 T)
    (hwI (f := fun z => (2 * z.re) ^ 3) (by fun_prop)) hY
  have h42 : 42 * A ≠ 0 := mul_ne_zero (by norm_num) hA
  apply Asymptotics.isEquivalent_of_tendsto_one
  have h := hX.div_const (42 * A)
  rw [div_self h42] at h
  apply h.congr'
  filter_upwards with T
  simp only [Pi.div_apply, moment, x, s, A, ← pow_mul]
  norm_num only
  ring

end OMA.R_RiemannZetaMoments_moment_isEquiv_109_R1
