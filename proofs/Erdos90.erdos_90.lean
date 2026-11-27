import FormalConjectures.ErdosProblems.«90»

/-!
# Erdos Problem 90 (disproof of the n^(1+O(1/log log n)) unit distance bound)

Credits:
* Construction and mathematical argument: Levent Alpoge, and the classical
  number-theoretic lattice construction underlying the unit distance lower bound.
* Lean formalization of the unit distance construction: Kim Morrison and the
  Tau Ceti contributors (Apache License 2.0).
* Prime number theorem / Wiener-Ikehara material: the PrimeNumberTheoremAnd project
  contributors (Apache License 2.0).
* This file assembles and ports the above to the Formal Conjectures statement and adds
  a short bridge lemma.
-/

section
open Filter Real
end
section
open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun
theorem CS.ext' {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : CS n E}
    (h : ∀ x, f.toFun x = g.toFun x) : f = g := by
  cases f; cases g; congr; funext x; exact h x
structure trunc extends (CS 2 ℝ) where
  h3 : (Set.Icc (-1) (1)).indicator 1 ≤ toFun
  h4 : toFun ≤ Set.indicator (Set.Ioo (-2) (2)) 1
structure W1 (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  smooth : ContDiff ℝ n toFun
  integrable : ∀ ⦃k⦄, k ≤ n → Integrable (iteratedDeriv k toFun)
abbrev W21 := W1 2 ℂ
section lemmas
noncomputable def funscale {E : Type*} (g : ℝ → E) (R x : ℝ) : E := g (R⁻¹ • x)
lemma contDiff_ofReal : ContDiff ℝ ∞ ofReal := by
  have key x : HasDerivAt ofReal 1 x := hasDerivAt_id x |>.ofReal_comp
  have key' : deriv ofReal = fun _ => 1 := by ext x ; exact (key x).deriv
  refine contDiff_infty_iff_deriv.mpr ⟨fun x => (key x).differentiableAt, ?_⟩
  simpa [key'] using contDiff_const
omit [NormedSpace ℝ E] in
lemma tendsto_funscale {f : ℝ → E} (hf : ContinuousAt f 0) (x : ℝ) :
    Tendsto (fun R => funscale f R x) atTop (𝓝 (f 0)) :=
  hf.tendsto.comp (by simpa using tendsto_inv_atTop_zero.mul_const x)
end lemmas
namespace CS
variable {f : CS n E} {R x v : ℝ}
instance : CoeFun (CS n E) (fun _ => ℝ → E) where coe := CS.toFun
instance : Coe (CS n ℝ) (CS n ℂ) where coe f := ⟨fun x => f x,
  contDiff_ofReal.of_le (mod_cast le_top) |>.comp f.h1, f.h2.comp_left (g := ofReal) rfl⟩
def neg (f : CS n E) : CS n E where
  toFun := -f
  h1 := f.h1.neg
  h2 := by simpa [HasCompactSupport, tsupport] using f.h2
instance : Neg (CS n E) where neg := neg
@[simp] lemma neg_apply {x : ℝ} : (-f) x = - (f x) := rfl
def smul (R : ℝ) (f : CS n E) : CS n E := ⟨R • f, f.h1.const_smul R, f.h2.smul_left⟩
instance : HSMul ℝ (CS n E) (CS n E) where hSMul := smul
@[simp] lemma smul_apply : (R • f) x = R • f x := rfl
lemma continuous (f : CS n E) : Continuous f := f.h1.continuous
noncomputable def deriv (f : CS (n + 1) E) : CS n E where
  toFun := _root_.deriv f
  h1 := (contDiff_succ_iff_deriv.mp f.h1).2.2
  h2 := f.h2.deriv
lemma hasDerivAt (f : CS (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x :=
  (f.h1.differentiable (by simp)).differentiableAt.hasDerivAt
lemma deriv_smul {f : CS (n + 1) E} : (R • f).deriv = R • f.deriv := by
  apply CS.ext'; intro x ; exact (f.hasDerivAt x |>.const_smul R).deriv
noncomputable def scale (g : CS n E) (R : ℝ) : CS n E := by
  by_cases h : R = 0
  · exact ⟨0, contDiff_const, by simp [HasCompactSupport, tsupport]⟩
  · refine ⟨fun x => funscale g R x, ?_, ?_⟩
    · exact g.h1.comp (contDiff_const_smul R⁻¹)
    · exact g.h2.comp_smul (inv_ne_zero h)
lemma deriv_scale {f : CS (n + 1) E} : (f.scale R).deriv = R⁻¹ • f.deriv.scale R := by
  apply CS.ext'; intro v ; by_cases hR : R = 0
  · simp [hR, scale, deriv]
  · simp only [scale, hR, ↓reduceDIte, smul_apply]
    exact ((f.hasDerivAt (R⁻¹ • v)).scomp v
      (by simpa using! (hasDerivAt_id v).const_smul R⁻¹)).deriv
lemma deriv_scale' {f : CS (n + 1) E} :
    (f.scale R).deriv v = R⁻¹ • f.deriv (R⁻¹ • v) := by
  rw [deriv_scale, smul_apply]
  by_cases hR : R = 0 <;> simp [hR, scale, funscale]
lemma hasDerivAt_scale (f : CS (n + 1) E) (R x : ℝ) :
    HasDerivAt (f.scale R) (R⁻¹ • f.deriv (R⁻¹ • x)) x := by
  simpa [deriv_scale'] using hasDerivAt (f.scale R) x
lemma tendsto_scale (f : CS n E) (x : ℝ) : Tendsto (fun R => f.scale R x) atTop (𝓝 (f 0)) := by
  apply (tendsto_funscale f.continuous.continuousAt x).congr'
  filter_upwards [eventually_ne_atTop 0] with R hR ; simp [scale, hR]
lemma bounded : ∃ C, ∀ v, ‖f v‖ ≤ C := by
  obtain ⟨x, hx⟩ :=
    (continuous_norm.comp f.continuous).exists_forall_ge_of_hasCompactSupport f.h2.norm
  exact ⟨_, hx⟩
end CS
namespace trunc
instance : CoeFun trunc (fun _ => ℝ → ℝ) where coe f := f.toFun
instance : Coe trunc (CS 2 ℝ) where coe := trunc.toCS
lemma nonneg (g : trunc) (x : ℝ) : 0 ≤ g x := (Set.indicator_nonneg (by simp) x).trans (g.h3 x)
lemma le_one (g : trunc) (x : ℝ) : g x ≤ 1 :=
  (g.h4 x).trans <| Set.indicator_le_self' (by simp) x
lemma zero (g : trunc) : g =ᶠ[𝓝 0] 1 := by
  have : Set.Icc (-1) 1 ∈ 𝓝 (0 : ℝ) := by apply Icc_mem_nhds <;> linarith
  exact eventually_of_mem this (fun x hx => le_antisymm (g.le_one x) (by simpa [hx] using g.h3 x))
@[simp] lemma zero_at {g : trunc} : g 0 = 1 := g.zero.eq_of_nhds
end trunc
namespace W1
instance : CoeFun (W1 n E) (fun _ => ℝ → E) where coe := W1.toFun
lemma continuous (f : W1 n E) : Continuous f := f.smooth.continuous
lemma differentiable (f : W1 (n + 1) E) : Differentiable ℝ f :=
  f.smooth.differentiable (by simp)
lemma iteratedDeriv_sub {f g : ℝ → E} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    iteratedDeriv n (f - g) = iteratedDeriv n f - iteratedDeriv n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    have hf' : ContDiff ℝ n (deriv f) := hf.iterate_deriv' n 1
    have hg' : ContDiff ℝ n (deriv g) := hg.iterate_deriv' n 1
    have hfg : deriv (f - g) = deriv f - deriv g := by
      ext x ; apply deriv_sub
      · exact (hf.differentiable (by simp)).differentiableAt
      · exact (hg.differentiable (by simp)).differentiableAt
    simp_rw [iteratedDeriv_succ', ← ih hf' hg', hfg]
noncomputable def deriv (f : W1 (n + 1) E) : W1 n E where
  toFun := _root_.deriv f
  smooth := contDiff_succ_iff_deriv.mp f.smooth |>.2.2
  integrable k hk := by
    simpa [iteratedDeriv_succ'] using f.integrable (Nat.succ_le_succ hk)
lemma hasDerivAt (f : W1 (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x :=
  f.differentiable.differentiableAt.hasDerivAt
def sub (f g : W1 n E) : W1 n E where
  toFun := f - g
  smooth := f.smooth.sub g.smooth
  integrable k hk := by
    have hf : ContDiff ℝ k f := f.smooth.of_le (by simp [hk])
    have hg : ContDiff ℝ k g := g.smooth.of_le (by simp [hk])
    simpa [iteratedDeriv_sub hf hg] using (f.integrable hk).sub (g.integrable hk)
instance : Sub (W1 n E) where sub := sub
lemma integrable_iteratedDeriv_Schwarz {f : 𝓢(ℝ, ℂ)} : Integrable (iteratedDeriv n f) := by
  induction n generalizing f with
  | zero => exact f.integrable
  | succ n ih =>
      have hderiv : ⇑(SchwartzMap.derivCLM ℝ ℂ f) = _root_.deriv (f : ℝ → ℂ) := by
        funext x
        exact SchwartzMap.derivCLM_apply (𝕜 := ℝ) (F := ℂ) f x
      simpa [iteratedDeriv_succ', hderiv] using
        ih (f := SchwartzMap.derivCLM ℝ ℂ f)
noncomputable def of_Schwartz (f : 𝓢(ℝ, ℂ)) : W1 n ℂ where
  toFun := f
  smooth := f.smooth n
  integrable _ _ := integrable_iteratedDeriv_Schwarz
end W1
namespace W21
variable {f : W21}
noncomputable def norm (f : ℝ → ℂ) : ℝ :=
    (∫ v, ‖f v‖) + (4 * π ^ 2)⁻¹ * (∫ v, ‖deriv (deriv f) v‖)
lemma norm_nonneg {f : ℝ → ℂ} : 0 ≤ norm f :=
  add_nonneg (integral_nonneg (fun t => by simp))
    (mul_nonneg (by positivity) (integral_nonneg (fun t => by simp)))
noncomputable instance : Norm W21 where norm := norm ∘ W1.toFun
noncomputable instance : Coe 𝓢(ℝ, ℂ) W21 where coe := W1.of_Schwartz
def ofCS2 (f : CS 2 ℂ) : W21 := by
  refine ⟨f, f.h1, fun k hk => ?_⟩ ; match k with
  | 0 => exact f.h1.continuous.integrable_of_hasCompactSupport f.h2
  | 1 => simpa using (f.h1.continuous_deriv one_le_two).integrable_of_hasCompactSupport f.h2.deriv
  | 2 => simpa [iteratedDeriv_succ] using
    (f.h1.iterate_deriv' 0 2).continuous.integrable_of_hasCompactSupport f.h2.deriv.deriv
instance : Coe (CS 2 ℂ) W21 where coe := ofCS2
instance : HMul (CS 2 ℂ) W21 (CS 2 ℂ) where
  hMul g f := ⟨g * f, g.h1.mul f.smooth, g.h2.mul_right⟩
instance : HMul (CS 2 ℝ) W21 (CS 2 ℂ) where hMul g f := (g : CS 2 ℂ) * f
lemma hf (f : W21) : Integrable f := f.integrable zero_le_two
lemma hf' (f : W21) : Integrable (deriv f) := by
  simpa [iteratedDeriv_succ] using f.integrable one_le_two
lemma hf'' (f : W21) : Integrable (deriv (deriv f))  := by
  simpa [iteratedDeriv_succ] using f.integrable le_rfl
end W21
set_option maxHeartbeats 800000 in
theorem W21_approximation (f : W21) (g : trunc) :
    Tendsto (fun R => ‖f - (g.scale R * f : W21)‖) atTop (𝓝 0) := by
  let f' := f.deriv
  let f'' := f'.deriv
  let g' := (g : CS 2 ℝ).deriv
  let g'' := g'.deriv
  let h R v := 1 - g.scale R v
  let h' R := - (g.scale R).deriv
  let h'' R := - (g.scale R).deriv.deriv
  have ch {R} : Continuous (fun v => (h R v : ℂ)) :=
    continuous_ofReal.comp <| continuous_const.sub (CS.continuous _)
  have ch' {R} : Continuous (fun v => (h' R v : ℂ)) := continuous_ofReal.comp (CS.continuous _)
  have ch'' {R} : Continuous (fun v => (h'' R v : ℂ)) := continuous_ofReal.comp (CS.continuous _)
  have dh R v : HasDerivAt (h R) (h' R v) v := by
    simpa [h, h', CS.deriv_scale'] using
      (CS.hasDerivAt_scale (g : CS 2 ℝ) R v).const_sub 1
  have dh' R v : HasDerivAt (h' R) (h'' R v) v := ((g.scale R).deriv.hasDerivAt v).neg
  have hh1 R v : |h R v| ≤ 1 := by
    by_cases hR : R = 0 <;>
      simp only [CS.scale, funscale, smul_eq_mul, hR, ↓reduceDIte, Pi.zero_apply, sub_zero,
        abs_one, le_refl, h]
    rw [abs_le] ; constructor <;>
    linarith [g.le_one (R⁻¹ * v), g.nonneg (R⁻¹ * v)]
  have vR v : Tendsto (fun R : ℝ => v * R⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul v
  convert_to Tendsto (fun R => W21.norm (fun v => h R v * f v)) atTop (𝓝 0)
  · ext R ; change W21.norm _ = _ ; congr ; ext v ; simp [h, sub_mul] ; rfl
  rw [show (0 : ℝ) = 0 + ((4 * π ^ 2)⁻¹ : ℝ) * 0 by simp]
  refine Tendsto.add ?_ (Tendsto.const_mul _ ?_)
  · let F R v := ‖h R v * f v‖
    have eh v : ∀ᶠ R in atTop, h R v = 0 := by
      filter_upwards [(vR v).eventually g.zero, eventually_ne_atTop 0] with R hR hR'
      simp [h, hR, CS.scale, hR', funscale, mul_comm R⁻¹]
    have e1 : ∀ᶠ (n : ℝ) in atTop, AEStronglyMeasurable (F n) volume := by
      apply Eventually.of_forall ; intro R
      exact (ch.mul f.continuous).norm.aestronglyMeasurable
    have e2 : ∀ᶠ (n : ℝ) in atTop, ∀ᵐ (a : ℝ), ‖F n a‖ ≤ ‖f a‖ := by
      apply Eventually.of_forall ; intro R
      apply Eventually.of_forall ; intro v
      simpa [F] using mul_le_mul (hh1 R v) le_rfl (by simp) zero_le_one
    have e4 : ∀ᵐ (a : ℝ), Tendsto (fun n ↦ F n a) atTop (𝓝 0) := by
      apply Eventually.of_forall ; intro v
      apply tendsto_nhds_of_eventually_eq ; filter_upwards [eh v] with R hR ; simp [F, hR]
    simpa [F] using tendsto_integral_filter_of_dominated_convergence _ e1 e2 f.hf.norm e4
  · let F R v := ‖h'' R v * f v + 2 * h' R v * f' v + h R v * f'' v‖
    convert_to Tendsto (fun R ↦ ∫ (v : ℝ), F R v) atTop (𝓝 0)
    · have this R v :
        deriv (deriv (fun v => h R v * f v)) v =
          h'' R v * f v + 2 * h' R v * f' v + h R v * f'' v := by
        have df v : HasDerivAt f (f' v) v := f.hasDerivAt v
        have df' v : HasDerivAt f' (f'' v) v := f'.hasDerivAt v
        have l3 v : HasDerivAt (fun v => h R v * f v) (h' R v * f v + h R v * f' v) v :=
          (dh R v).ofReal_comp.mul (df v)
        have l5 : HasDerivAt (fun v => h' R v * f v) (h'' R v * f v + h' R v * f' v) v :=
          (dh' R v).ofReal_comp.mul (df v)
        have l7 : HasDerivAt (fun v => h R v * f' v) (h' R v * f' v + h R v * f'' v) v :=
          (dh R v).ofReal_comp.mul (df' v)
        have d1 : deriv (fun v => h R v * f v) = fun v => h' R v * f v + h R v * f' v :=
          funext (fun v => (l3 v).deriv)
        rw [d1]
        convert (l5.add l7).deriv using 1
        · congr 1
        · ring
      simp_rw [this, F]
    obtain ⟨c1, mg'⟩ := g'.bounded
    obtain ⟨c2, mg''⟩ := g''.bounded
    let bound v := c2 * ‖f v‖ + 2 * c1 * ‖f' v‖ + ‖f'' v‖
    have e1 : ∀ᶠ (n : ℝ) in atTop, AEStronglyMeasurable (F n) volume := by
      apply Eventually.of_forall ; intro R ; apply (Continuous.norm ?_).aestronglyMeasurable
      exact ((ch''.mul f.continuous).add ((continuous_const.mul ch').mul f.deriv.continuous)).add
        (ch.mul f.deriv.deriv.continuous)
    have e2 : ∀ᶠ R in atTop, ∀ᵐ (a : ℝ), ‖F R a‖ ≤ bound a := by
      have hc1 : ∀ᶠ R in atTop, ∀ v, |h' R v| ≤ c1 := by
        filter_upwards [eventually_ge_atTop 1] with R hR v
        have hR' : R ≠ 0 := by linarith
        have : 0 ≤ R := by linarith
        simp only [CS.deriv_scale, CS.neg_apply, CS.smul_apply, smul_eq_mul, abs_neg, abs_mul,
          abs_inv, abs_eq_self.mpr this, ge_iff_le, h']
        simp only [CS.scale, hR', ↓reduceDIte, funscale, smul_eq_mul]
        convert_to _ ≤ c1 * 1
        · simp
        · rw [mul_comm]
          apply mul_le_mul (mg' _)
            (inv_le_of_inv_le₀ (by linarith) (by simpa using hR)) (by positivity)
          exact (abs_nonneg _).trans (mg' 0)
      have hc2 : ∀ᶠ R in atTop, ∀ v, |h'' R v| ≤ c2 := by
        filter_upwards [eventually_ge_atTop 1] with R hR v
        have e1 : 0 ≤ R := by linarith
        have e2 : R⁻¹ ≤ 1 := inv_le_of_inv_le₀ (by linarith) (by simpa using hR)
        have e3 : R ≠ 0 := by linarith
        simp only [CS.deriv_scale, CS.deriv_smul, CS.neg_apply, CS.smul_apply, smul_eq_mul, abs_neg,
          abs_mul, abs_inv, abs_eq_self.mpr e1, ge_iff_le, h'']
        convert_to _ ≤ 1 * (1 * c2)
        · simp
        apply mul_le_mul e2 ?_ (by positivity) zero_le_one
        apply mul_le_mul e2 ?_ (by positivity) zero_le_one
        simp only [CS.scale, e3, ↓reduceDIte, funscale, smul_eq_mul] ; apply mg''
      filter_upwards [hc1, hc2] with R hc1 hc2
      apply Eventually.of_forall ; intro v ; specialize hc1 v ; specialize hc2 v
      simp only [F, bound, norm_norm]
      refine (norm_add_le _ _).trans ?_ ; apply add_le_add
      · refine (norm_add_le _ _).trans ?_ ; apply add_le_add <;> simp only [Complex.norm_mul,
        Complex.norm_ofNat, norm_real, norm_eq_abs] <;> gcongr
      · simpa using mul_le_mul (hh1 R v) le_rfl (by simp) zero_le_one
    have e3 : Integrable bound volume :=
      (((f.hf.norm).const_mul _).add ((f.hf'.norm).const_mul _)).add f.hf''.norm
    have e4 : ∀ᵐ (a : ℝ), Tendsto (fun n ↦ F n a) atTop (𝓝 0) := by
      apply Eventually.of_forall ; intro v
      have evg' : g' =ᶠ[𝓝 0] 0 := by
        change _root_.deriv g.toFun =ᶠ[𝓝 0] 0
        refine g.zero.deriv.trans ?_
        simp
      have evg'' : g'' =ᶠ[𝓝 0] 0 := by
        change _root_.deriv g'.toFun =ᶠ[𝓝 0] 0
        refine evg'.deriv.trans ?_
        simp
      refine tendsto_norm_zero.comp <| (ZeroAtFilter.add ?_ ?_).add ?_
      · have eh'' v : ∀ᶠ R in atTop, h'' R v = 0 := by
          filter_upwards [(vR v).eventually evg'', eventually_ne_atTop 0] with R hR hR'
          simp only [CS.deriv_scale, CS.deriv_smul, CS.neg_apply, CS.smul_apply, smul_eq_mul,
            neg_eq_zero, mul_eq_zero, inv_eq_zero, hR', false_or, h'']
          simp only [CS.scale, hR', ↓reduceDIte, funscale, smul_eq_mul, mul_comm R⁻¹]
          exact hR
        apply tendsto_nhds_of_eventually_eq
        filter_upwards [eh'' v] with R hR ; simp [hR]
      · have eh' v : ∀ᶠ R in atTop, h' R v = 0 := by
          filter_upwards [(vR v).eventually evg'] with R hR
          simp [g'] at hR
          simp [h', CS.deriv_scale', mul_comm R⁻¹, hR]
        apply tendsto_nhds_of_eventually_eq
        filter_upwards [eh' v] with R hR ; simp [hR]
      · rw [Filter.ZeroAtFilter]
        simpa [h] using ((g.tendsto_scale v).const_sub 1).ofReal.mul tendsto_const_nhds
    simpa [F] using tendsto_integral_filter_of_dominated_convergence bound e1 e2 e3 e4
end
section
open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators
local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩
section lemmas
@[simp]
theorem nnnorm_eq_of_mem_circle (z : Circle) : ‖z.val‖₊ = 1 :=
  NNReal.coe_eq_one.mp z.norm_coe
@[simp]
theorem nnnorm_circle_smul (z : Circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]
noncomputable def e (u : ℝ) : ℝ →ᵇ ℂ where
  toFun v := 𝐞 (-v * u)
  map_bounded' :=
    ⟨2, fun x y => (dist_le_norm_add_norm _ _).trans (by
      simp only [Circle.norm_coe, one_add_one_eq_two]
      exact le_rfl)⟩
@[simp] lemma e_apply (u : ℝ) (v : ℝ) : e u v = 𝐞 (-v * u) := rfl
@[simp] lemma F_neg {f : ℝ → ℂ} {u : ℝ} : 𝓕 (fun x => -f x) u = - 𝓕 f u := by
  simp [fourier_eq, integral_neg]
@[simp] lemma F_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := by
  have : Continuous fun p : ℝ × ℝ ↦ ((innerₗ ℝ) p.1) p.2 := continuous_inner
  have := fourierIntegral_add continuous_fourierChar this hf hg
  exact congr_fun this x
@[simp] lemma F_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simpa [sub_eq_add_neg, Pi.neg_def] using F_add hf hg.neg x
@[simp] lemma F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  simp [fourier_real_eq, ← integral_const_mul, Real.fourierChar, Circle.exp,
    ← smul_mul_assoc, mul_smul_comm]
end lemmas
theorem fourierIntegral_self_add_deriv_deriv (f : W21) (u : ℝ) :
    (1 + u ^ 2) * 𝓕 (f : ℝ → ℂ) u =
      𝓕 (fun u : ℝ => (f u - (1 / (4 * π ^ 2)) * deriv^[2] f u : ℂ)) u := by
  have l1 : Integrable (fun x => (((π : ℂ) ^ 2)⁻¹ * 4⁻¹) * deriv (deriv f) x) := by
    apply Integrable.const_mul ; simpa [iteratedDeriv_succ] using f.integrable le_rfl
  have l4 : Differentiable ℝ f := f.differentiable
  have l5 : Differentiable ℝ (deriv f) := f.deriv.differentiable
  simp [f.hf, l1, add_mul, Real.fourier_deriv f.hf' l5 f.hf'', Real.fourier_deriv f.hf l4 f.hf']
  field_simp [pi_ne_zero] ; ring_nf ; simp
@[simp] lemma deriv_ofReal : deriv ofReal = fun _ => 1 := by
  ext x ; exact ((hasDerivAt_id x).ofReal_comp).deriv
end
section
open ArithmeticFunction hiding log
open Nat hiding log
open Finset Topology
open BigOperators Filter Real Asymptotics
open MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.Omega Chebyshev
noncomputable abbrev Psi (x : ℝ) : ℝ := ψ x
noncomputable def M (x : ℝ) : ℝ :=
  ∑ n ∈ Iic ⌊x⌋₊, (μ n : ℝ)
noncomputable def pi (x : ℝ) : ℝ :=
  Nat.primeCounting ⌊x⌋₊
noncomputable def pi_star (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 1 ⌊x⌋₊, (Λ n : ℝ) / n
noncomputable def Li (x : ℝ) : ℝ := ∫ t in 2..x, 1 / log t
noncomputable def Eψ (x : ℝ) : ℝ := |ψ x - x| / x
noncomputable def admissible_bound (A B C R : ℝ) (x : ℝ) :=
  A * (log x / R) ^ B * exp (-C * (log x / R) ^ ((1 : ℝ) / (2 : ℝ)))
def Eψ.bound (ε x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eψ x ≤ ε
noncomputable def Eπ (x : ℝ) : ℝ :=
  |pi x - Li x| / (x / log x)
noncomputable def Eπ_star (x : ℝ) : ℝ :=
  |pi_star x - Li x| / (x / log x)
def Eπ.bound (ε x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eπ x ≤ ε
def Eπ_star.bound (ε x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eπ_star x ≤ ε
lemma admissible_bound.mono
    (A B C R : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hC : 0 < C) (hR : 0 < R) :
    AntitoneOn (admissible_bound A B C R)
      (Set.Ici (exp (R * (2 * B / C) ^ 2))) := by
  intro a ha b _ hab
  simp only [admissible_bound, mul_assoc]
  have hua : (2 * B / C) ^ 2 ≤ log a / R := by
    rw [le_div_iff₀ hR, mul_comm ((2 * B / C) ^ 2), ← log_exp (R * (2 * B / C) ^ 2)]
    exact log_le_log (exp_pos _) (Set.mem_Ici.mp ha)
  have huab : log a / R ≤ log b / R :=
    div_le_div_of_nonneg_right
      (log_le_log ((exp_pos _).trans_le (Set.mem_Ici.mp ha)) hab) hR.le
  have hua₀ : 0 < log a / R :=
    lt_of_lt_of_le (by positivity) hua
  apply mul_le_mul_of_nonneg_left _ hA.le
  rw [rpow_def_of_pos (hua₀.trans_le huab), rpow_def_of_pos hua₀,
    ← exp_add, ← exp_add, exp_le_exp]
  let sa := (log a / R) ^ ((1 : ℝ) / 2)
  let sb := (log b / R) ^ ((1 : ℝ) / 2)
  rw [show log (log b / R) = 2 * log sb from by
      grind [log_rpow (hua₀.trans_le huab) ((1 : ℝ) / 2)],
    show log (log a / R) = 2 * log sa from by
      grind [log_rpow hua₀ ((1 : ℝ) / 2)]]
  have hsab : sa ≤ sb :=
    rpow_le_rpow (le_trans (by positivity) hua) huab (by positivity)
  have : 2 * B / C ≤ sa := by
    rw [show (2 * B / C : ℝ) = ((2 * B / C) ^ 2) ^ ((1 : ℝ) / 2) from by
      rw [← rpow_natCast _ 2, ← rpow_mul (by positivity)]
      norm_num [rpow_one]]
    exact rpow_le_rpow (by positivity) hua (by positivity)
  suffices h : AntitoneOn (fun t ↦ 2 * B * log t - C * t) (Set.Ici (2 * B / C)) by
    grind [h (Set.mem_Ici.mpr this) (Set.mem_Ici.mpr (this.trans hsab)) hsab]
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · exact ((continuousOn_const.mul (continuousOn_log.mono fun t ht ↦
        ne_of_gt ((div_pos (by positivity) hC).trans_le ht))).sub
      (continuousOn_const.mul continuousOn_id))
  · intro t ht
    rw [interior_Ici] at ht
    exact (((hasDerivAt_log ((div_pos (by positivity) hC).trans ht).ne').const_mul _).sub
      ((hasDerivAt_id t).const_mul C)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    have hdt : HasDerivAt (fun t ↦ 2 * B * log t - C * t) (2 * B * t⁻¹ - C * 1) t :=
      ((hasDerivAt_log ((div_pos (by positivity) hC).trans ht).ne').const_mul _).sub
        ((hasDerivAt_id t).const_mul C)
    rw [hdt.deriv, mul_one, sub_nonpos, ← div_eq_mul_inv,
      div_le_iff₀ ((div_pos (by positivity) hC).trans ht)]
    linarith [(div_lt_iff₀ hC).mp ht, mul_comm C t]
end
section
open Filter Topology
namespace Asymptotics
variable {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*} {E' : Type*}
  {F' : Type*} {G' : Type*} {E'' : Type*} {F'' : Type*} {G'' : Type*} {R : Type*}
  {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}
variable [Norm E] [Norm F] [Norm G]
variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedRing R']
theorem _root_.Filter.Eventually.natCast {f : ℝ → Prop} (hf : ∀ᶠ x in atTop, f x) :
    ∀ᶠ n : ℕ in atTop, f n :=
  tendsto_natCast_atTop_atTop.eventually hf
theorem IsBigO.natCast {f g : ℝ → E} (h : f =O[atTop] g) :
    (fun n : ℕ => f n) =O[atTop] fun n : ℕ => g n :=
  h.comp_tendsto tendsto_natCast_atTop_atTop
end Asymptotics
end
section
namespace Function
variable {α : Type*} [Zero α]
end Function
end
section
open MeasureTheory Set Real
open scoped ContDiff
lemma smooth_urysohn_support_Ioo {a b c d : ℝ} (h1 : a < b) (h3 : c < d) :
    ∃ Ψ : ℝ → ℝ, (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
    Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 ∧
    (Function.support Ψ = Set.Ioo a d) := by
  have := exists_contMDiff_zero_iff_one_iff_of_isClosed (n := ⊤)
    (modelWithCornersSelf ℝ ℝ) (s := Set.Iic a ∪ Set.Ici d) (t := Set.Icc b c)
    (IsClosed.union isClosed_Iic isClosed_Ici) isClosed_Icc
    (by
      simp_rw [Set.disjoint_union_left, Set.disjoint_iff, Set.subset_def,
        Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_empty_iff_false,
        and_imp, imp_false, not_le, Set.mem_Ici]
      constructor <;> intros <;> linarith)
  obtain ⟨Ψ, hΨSmooth, hΨrange, hΨ0, hΨ1⟩ := this
  simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_Icc] at *
  use Ψ
  simp only [range_subset_iff, mem_Icc] at hΨrange
  refine ⟨ContMDiff.contDiff hΨSmooth, ?_, ?_, ?_, ?_⟩
  · apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc a d) isCompact_Icc
    simp only [Function.support_subset_iff, ne_eq, mem_Icc, ← hΨ0, not_or]
    bound
  · apply Set.indicator_le'
    · intro x hx
      rw [hΨ1 x |>.mp, Pi.one_apply]
      simpa using hx
    · exact fun x _ ↦ (hΨrange x).1
  · intro x
    apply Set.le_indicator_apply
    · exact fun _ ↦ (hΨrange x).2
    · intro hx
      rw [← hΨ0 x |>.mp]
      simpa [-not_and, mem_Ioo, not_and_or, not_lt] using hx
  · ext x
    simp only [Function.mem_support, ne_eq, mem_Ioo, ← hΨ0, not_or, not_le]
end
section
open Real BigOperators ArithmeticFunction MeasureTheory Filter Set FourierTransform LSeries
  Asymptotics SchwartzMap
open Complex hiding log
open scoped Topology
open scoped ContDiff
open scoped ComplexConjugate
variable {n : ℕ} {A a b c d u x y t σ' : ℝ} {ψ Ψ : ℝ → ℂ} {F G : ℂ → ℂ} {f : ℕ → ℂ} {𝕜 : Type}
  [RCLike 𝕜]
@[simp] lemma W21.ofCS2_toFun (ψ : CS 2 ℂ) : (W21.ofCS2 ψ).toFun = ψ.toFun := rfl
@[simp] lemma W21.ofCS2_apply (ψ : CS 2 ℂ) (x : ℝ) : (W21.ofCS2 ψ : W21) x = ψ x := rfl
@[simp] lemma W21.sub_toFun (f g : W21) : (f - g).toFun = f.toFun - g.toFun := rfl
noncomputable
def nterm (f : ℕ → ℂ) (σ' : ℝ) (n : ℕ) : ℝ := if n = 0 then 0 else ‖f n‖ / n ^ σ'
lemma nterm_eq_norm_term {f : ℕ → ℂ} : nterm f σ' n = ‖term f σ' n‖ := by
  by_cases h : n = 0 <;> simp [nterm, term, h]
theorem norm_term_eq_nterm_re (s : ℂ) :
    ‖term f s n‖ = nterm f (s.re) n := by
  simp only [nterm, term, apply_ite (‖·‖), norm_zero, norm_div]
  apply ite_congr rfl (fun _ ↦ rfl)
  intro h
  congr
  refine norm_natCast_cpow_of_pos (by omega) s
lemma hf_coe1 (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hσ : 1 < σ') :
    ∑' i, (‖term f σ' i‖₊ : ENNReal) ≠ ⊤ := by
  simp_rw [ENNReal.tsum_coe_ne_top_iff_summable_coe, ← norm_toNNReal]
  norm_cast
  apply Summable.toNNReal
  convert hf σ' hσ with i
  simp [nterm_eq_norm_term]
instance instMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype _
instance instBorelSpace : BorelSpace Circle :=
  inferInstanceAs <| BorelSpace <| Subtype (· ∈ Metric.sphere (0 : ℂ) 1)

lemma first_fourier_aux1 (hψ : AEMeasurable ψ) {x : ℝ} (n : ℕ) : AEMeasurable fun (u : ℝ) ↦
    (‖fourierChar (-(u * ((1 : ℝ) / ((2 : ℝ) * π) * (n / x).log))) • ψ u‖ₑ : ENNReal) := by
  fun_prop
lemma first_fourier_aux2a :
    (2 : ℂ) * π * -(y * (1 / (2 * π) * Real.log ((n) / x))) = -(y * ((n) / x).log) := by
  calc
    _ = -(y * (((2 : ℂ) * π) / (2 * π) * Real.log ((n) / x))) := by ring
    _ = _ := by rw [div_self (by norm_num), one_mul]
lemma first_fourier_aux2 (hx : 0 < x) (n : ℕ) :
    term f σ' n * 𝐞 (-(y * (1 / (2 * π) * Real.log (n / x)))) • ψ y =
    term f (σ' + y * I) n • (ψ y * x ^ (y * I)) := by
  by_cases hn : n = 0
  · simp [term, hn]
  simp only [term, hn, ↓reduceIte]
  calc
    _ = (f n * (cexp ((2 * π * -(y * (1 / (2 * π) * Real.log (n / x)))) * I) /
        ↑((n : ℝ) ^ σ'))) • ψ y := by
      rw [Circle.smul_def, fourierChar_apply, ofReal_cpow (by norm_num)]
      simp only [one_div, mul_inv_rev, mul_neg, ofReal_neg, ofReal_mul, ofReal_ofNat, ofReal_inv,
        neg_mul, smul_eq_mul, ofReal_natCast]
      ring
    _ = (f n * (x ^ (y * I) / n ^ (σ' + y * I))) • ψ y := by
      congr 2
      have l1 : 0 < (n : ℝ) := by simpa using Nat.pos_iff_ne_zero.mpr hn
      have l2 : (x : ℂ) ≠ 0 := by simp [hx.ne.symm]
      have l3 : (n : ℂ) ≠ 0 := by simp [hn]
      rw [Real.rpow_def_of_pos l1, Complex.cpow_def_of_ne_zero l2, Complex.cpow_def_of_ne_zero l3]
      push_cast
      simp_rw [← Complex.exp_sub]
      congr 1
      rw [first_fourier_aux2a, Real.log_div l1.ne.symm hx.ne.symm]
      push_cast
      rw [Complex.ofReal_log hx.le]
      ring
    _ = _ := by simp ; group
lemma first_fourier (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hsupp : Integrable ψ) (hx : 0 < x) (hσ : 1 < σ') :
    ∑' n : ℕ, term f σ' n * (𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))) =
    ∫ t : ℝ, LSeries f (σ' + t * I) * ψ t * x ^ (t * I) := by
  calc
    _ = ∑' n, term f σ' n * ∫ (v : ℝ), 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      simp only [Real.fourier_eq]
      simp only [one_div, mul_inv_rev, RCLike.inner_apply', conj_trivial]
    _ = ∑' n, ∫ (v : ℝ), term f σ' n * 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      simp [integral_const_mul]
    _ = ∫ (v : ℝ), ∑' n, term f σ' n * 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      refine (integral_tsum ?_ ?_).symm
      · refine fun _ ↦ AEMeasurable.aestronglyMeasurable ?_
        have := hsupp.aemeasurable
        fun_prop
      · simp only [enorm_mul]
        simp_rw [lintegral_const_mul'' _ (first_fourier_aux1 hsupp.aemeasurable _)]
        calc
          _ = (∑' (i : ℕ), ‖term f σ' i‖ₑ) * ∫⁻ (a : ℝ), ‖ψ a‖ₑ ∂volume := by
            simp [ENNReal.tsum_mul_right, enorm_eq_nnnorm]
          _ ≠ ⊤ := ENNReal.mul_ne_top (hf_coe1 hf hσ)
            (ne_top_of_lt hsupp.2)
    _ = _ := by
      congr 1; ext y
      simp_rw [mul_assoc (LSeries _ _), ← smul_eq_mul (a := (LSeries _ _)), LSeries]
      rw [← Summable.tsum_smul_const]
      · simp_rw [first_fourier_aux2 hx]
      · apply Summable.of_norm
        convert hf σ' hσ with n
        rw [norm_term_eq_nterm_re]
        simp

lemma second_fourier_integrable_aux1a (hσ : 1 < σ') :
    IntegrableOn (fun (x : ℝ) ↦ cexp (-((x : ℂ) * ((σ' : ℂ) - 1)))) (Ici (-Real.log x)) := by
  norm_cast
  suffices IntegrableOn (fun (x : ℝ) ↦ (rexp (-(x * (σ' - 1))))) (Ici (-x.log)) _ from this.ofReal
  simp_rw [fun (a x : ℝ) ↦ (by ring : -(x * a) = -a * x)]
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  apply exp_neg_integrableOn_Ioi
  linarith
lemma second_fourier_integrable_aux1 (hcont : Measurable ψ) (hsupp : Integrable ψ) (hσ : 1 < σ') :
    let ν : Measure (ℝ × ℝ) := (volume.restrict (Ici (-Real.log x))).prod volume
    Integrable (Function.uncurry fun (u : ℝ) (a : ℝ) ↦ ((rexp (-u * (σ' - 1))) : ℂ) •
    (𝐞 (Multiplicative.ofAdd (-(a * (u / (2 * π))))) : ℂ) • ψ a) ν := by
  intro ν
  constructor
  · apply Measurable.aestronglyMeasurable
    have hc : Continuous (fun p : ℝ × ℝ => ((rexp (-p.1 * (σ' - 1)) : ℝ) : ℂ) *
        ((𝐞 (Multiplicative.ofAdd (-(p.2 * (p.1 / (2 * π))))) : Circle) : ℂ)) := by
      apply Continuous.mul
      · fun_prop
      · exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp
          (by fun_prop : Continuous fun p : ℝ × ℝ => -(p.2 * (p.1 / (2 * π)))))
    have := hc.measurable.mul (hcont.comp measurable_snd)
    convert this using 1
    funext p
    simp only [Function.uncurry, smul_eq_mul, Pi.mul_apply, Function.comp_apply]
    ring_nf
  · let f1 : ℝ → ENNReal := fun a1 ↦ ‖cexp (-(↑a1 * (↑σ' - 1)))‖ₑ
    let f2 : ℝ → ENNReal := fun a2 ↦ ‖ψ a2‖ₑ
    suffices ∫⁻ (a : ℝ × ℝ), f1 a.1 * f2 a.2 ∂ν < ⊤ by
      simpa [hasFiniteIntegral_iff_enorm, enorm_eq_nnnorm, Function.uncurry]
    refine (lintegral_prod_mul ?_ ?_).trans_lt ?_ <;> try fun_prop
    exact ENNReal.mul_lt_top (second_fourier_integrable_aux1a hσ).2 hsupp.2
lemma second_fourier_integrable_aux2 (hσ : 1 < σ') :
    IntegrableOn (fun (u : ℝ) ↦ cexp ((1 - ↑σ' - ↑t * I) * ↑u)) (Ioi (-Real.log x)) := by
  refine (integrable_norm_iff (Measurable.aestronglyMeasurable <| by fun_prop)).mp ?_
  suffices IntegrableOn (fun a ↦ rexp (-(σ' - 1) * a)) (Ioi (-x.log)) _ by simpa [Complex.norm_exp]
  apply exp_neg_integrableOn_Ioi
  linarith
lemma second_fourier_aux (hx : 0 < x) :
    -(cexp (-((1 - ↑σ' - ↑t * I) * ↑(Real.log x))) / (1 - ↑σ' - ↑t * I)) =
    ↑(x ^ (σ' - 1)) * (↑σ' + ↑t * I - 1)⁻¹ * ↑x ^ (↑t * I) := by
  calc
    _ = cexp (↑(Real.log x) * ((↑σ' - 1) + ↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [← div_neg]; ring_nf
    _ = (x ^ ((↑σ' - 1) + ↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt hx)), Complex.ofReal_log hx.le]
    _ = (x ^ ((σ' : ℂ) - 1)) * (x ^ (↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [Complex.cpow_add _ _ (ofReal_ne_zero.mpr (ne_of_gt hx))]
    _ = _ := by rw [ofReal_cpow hx.le]; push_cast; ring
lemma second_fourier (hcont : Measurable ψ) (hsupp : Integrable ψ)
    {x σ' : ℝ} (hx : 0 < x) (hσ : 1 < σ') :
    ∫ u in Ici (-log x), Real.exp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)) =
    (x^(σ' - 1) : ℝ) * ∫ t, (1 / (σ' + t * I - 1)) * ψ t * x^(t * I) ∂ volume := by
  conv in ↑(rexp _) * _ => { rw [Real.fourier_real_eq, ← smul_eq_mul, ← integral_smul] }
  rw [MeasureTheory.integral_integral_swap]
  swap
  · exact second_fourier_integrable_aux1 hcont hsupp hσ
  rw [← integral_const_mul]
  congr 1; ext t
  have e1 : ∀ u : ℝ, (↑(rexp (-u * (σ' - 1))) : ℂ) • 𝐞 (-(t * (u / (2 * π)))) • ψ t
      = cexp ((1 - σ' - t * I) * u) * ψ t := by
    intro u
    rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, smul_eq_mul, ofReal_exp,
      ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  simp_rw [e1, integral_mul_const]
  rw [fun (a b d : ℂ) ↦ show a * (b * (ψ t) * d) = (a * b * d) * ψ t by ring]
  congr 1
  let c : ℂ := (1 - ↑σ' - ↑t * I)
  have : c ≠ 0 := by simp [Complex.ext_iff, c, sub_ne_zero.mpr hσ.ne]
  let f' (u : ℝ) := cexp (c * u)
  let f := fun (u : ℝ) ↦ (f' u) / c
  have hderiv : ∀ u ∈ Ici (-Real.log x), HasDerivAt f (f' u) u := by
    intro u _
    rw [show f' u = cexp (c * u) * (c * 1) / c by simp only [f']; field_simp]
    exact (hasDerivAt_id' u).ofReal_comp.const_mul c |>.cexp.div_const c
  have hf : Tendsto f atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    suffices Tendsto (fun (x : ℝ) ↦ ‖cexp (c * ↑x)‖ / ‖c‖) atTop (𝓝 (0 / ‖c‖)) by
      simpa [f, f'] using this
    apply Filter.Tendsto.div_const
    suffices Tendsto (· * (1 - σ')) atTop atBot by simpa [Complex.norm_exp, mul_comm (1 - σ'), c]
    exact Tendsto.atTop_mul_const_of_neg (by linarith) fun ⦃s⦄ h ↦ h
  rw [integral_Ici_eq_integral_Ioi,
    integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (second_fourier_integrable_aux2 hσ) hf]
  simpa [f, f'] using second_fourier_aux hx
lemma one_add_sq_pos (u : ℝ) : 0 < 1 + u ^ 2 := zero_lt_one.trans_le (by simpa using sq_nonneg u)
lemma decay_bounds_key (f : W21) (u : ℝ) : ‖𝓕 (f : ℝ → ℂ) u‖ ≤ ‖f‖ * (1 + u ^ 2)⁻¹ := by
  have l1 : 0 < 1 + u ^ 2 := one_add_sq_pos _
  have l2 : 1 + u ^ 2 = ‖(1 : ℂ) + u ^ 2‖ := by
    norm_cast ; simp only [Real.norm_eq_abs, abs_eq_self.2 l1.le]
  have l3 : ‖1 / ((4 : ℂ) * ↑π ^ 2)‖ ≤ (4 * π ^ 2)⁻¹ := by simp
  have key := fourierIntegral_self_add_deriv_deriv f u
  simp only [Function.iterate_succ _ 1, Function.iterate_one, Function.comp_apply] at key
  rw [F_sub f.hf (f.hf''.const_mul (1 / (4 * ↑π ^ 2)))] at key
  rw [← div_eq_mul_inv, le_div_iff₀ l1, mul_comm, l2, ← norm_mul, key, sub_eq_add_neg]
  apply norm_add_le _ _ |>.trans
  change _ ≤ W21.norm _
  rw [norm_neg, F_mul, norm_mul, W21.norm]
  gcongr <;> apply VectorFourier.norm_fourierIntegral_le_integral_norm
lemma decay_bounds_cor (ψ : W21) :
    ∃ C : ℝ, ∀ u, ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ C / (1 + u ^ 2) := by
  simpa only [div_eq_mul_inv] using ⟨_, decay_bounds_key ψ⟩
lemma continuous_FourierIntegral (ψ : W21) : Continuous (𝓕 (ψ : ℝ → ℂ)) :=
  VectorFourier.fourierIntegral_continuous continuous_fourierChar
    (by simp only [innerₗ_apply_apply, RCLike.inner_apply', conj_trivial, continuous_mul])
    ψ.hf
lemma W21.integrable_fourier (ψ : W21) (hc : c ≠ 0) :
    Integrable fun u ↦ 𝓕 (ψ : ℝ → ℂ) (u / c) := by
  have l1 (C) : Integrable (fun u ↦ C / (1 + (u / c) ^ 2)) volume := by
    simpa [div_eq_mul_inv] using (integrable_inv_one_add_sq.comp_div hc).const_mul C
  have l2 : AEStronglyMeasurable (fun u ↦ 𝓕 (ψ : ℝ → ℂ) (u / c)) volume := by
    exact ((continuous_FourierIntegral ψ).comp (continuous_id.div_const c)).aestronglyMeasurable
  obtain ⟨C, h⟩ := decay_bounds_cor ψ
  apply @Integrable.mono' ℝ ℂ _ volume _ _ (fun u => C / (1 + (u / c) ^ 2)) (l1 C) l2 ?_
  apply Eventually.of_forall (fun x => h _)
lemma continuous_LSeries_aux (hf : Summable (nterm f σ')) :
    Continuous fun x : ℝ => LSeries f (σ' + x * I) := by
  have l1 i : Continuous fun x : ℝ ↦ term f (σ' + x * I) i := by
    by_cases h : i = 0
    · simpa [h] using continuous_const
    · simp only [LSeries.term, h, ↓reduceIte]
      exact continuous_const.div₀
        (continuous_const.cpow (by fun_prop) (fun x => by simp [h]))
        (fun x => by simp [h])
  have l2 n (x : ℝ) : ‖term f (σ' + x * I) n‖ = nterm f σ' n := by
    by_cases h : n = 0
    · simp [h, nterm]
    · simp [h, nterm, cpow_add _ _ (Nat.cast_ne_zero.mpr h),
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero h)]
  exact continuous_tsum l1 hf (fun n x => le_of_eq (l2 n x))
lemma limiting_fourier_aux (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (ψ : CS 2 ℂ) (hx : 1 ≤ x) (σ' : ℝ)
    (hσ' : 1 < σ') :
    ∑' n, term f σ' n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
    A * (x ^ (1 - σ') : ℝ) * ∫ u in Ici (- log x), rexp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ)
      (u / (2 * π)) = ∫ t : ℝ, G (σ' + t * I) * ψ t * x ^ (t * I) := by
  have hint : Integrable ψ := ψ.h1.continuous.integrable_of_hasCompactSupport ψ.h2
  have l3 : 0 < x := zero_lt_one.trans_le hx
  have l1 (σ') (hσ' : 1 < σ') := first_fourier hf hint l3 hσ'
  have l2 (σ') (hσ' : 1 < σ') := second_fourier ψ.h1.continuous.measurable hint l3 hσ'
  have l8 : Continuous fun t : ℝ ↦ (x : ℂ) ^ (t * I) :=
    continuous_const.cpow (continuous_ofReal.mul continuous_const) (by simp [l3])
  have l6 : Continuous fun t : ℝ ↦ LSeries f (↑σ' + ↑t * I) * ψ t * ↑x ^ (↑t * I) := by
    apply ((continuous_LSeries_aux (hf _ hσ')).mul ψ.h1.continuous).mul l8
  have l4 : Integrable fun t : ℝ ↦ LSeries f (↑σ' + ↑t * I) * ψ t * ↑x ^ (↑t * I) := by
    exact l6.integrable_of_hasCompactSupport ψ.h2.mul_left.mul_right
  have e2 (u : ℝ) : σ' + u * I - 1 ≠ 0 := by
    intro h ; have := congr_arg Complex.re h ; simp at this ; linarith
  have l7 : Continuous fun a ↦ A * ↑(x ^ (1 - σ')) * (↑(x ^ (σ' - 1)) *
      (1 / (σ' + a * I - 1) * ψ a * x ^ (a * I))) := by
    simp only [one_div, ← mul_assoc]
    refine ((continuous_const.mul <| Continuous.inv₀ ?_ e2).mul ψ.h1.continuous).mul l8
    fun_prop
  have l5 : Integrable fun a ↦ A * ↑(x ^ (1 - σ')) * (↑(x ^ (σ' - 1)) *
      (1 / (σ' + a * I - 1) * ψ a * x ^ (a * I))) := by
    apply l7.integrable_of_hasCompactSupport
    exact ψ.h2.mul_left.mul_right.mul_left.mul_left
  simp_rw [l1 σ' hσ', l2 σ' hσ', ← integral_const_mul, ← integral_sub l4 l5]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro u
  have e1 : 1 < ((σ' : ℂ) + (u : ℂ) * I).re := by simp [hσ']
  simp_rw [hG' e1, sub_mul, ← mul_assoc]
  simp only [one_div, sub_right_inj, mul_eq_mul_right_iff, cpow_eq_zero_iff, ofReal_eq_zero, ne_eq,
    mul_eq_zero, I_ne_zero, or_false]
  left ; left
  field_simp [e2]
  norm_cast
  simp [mul_assoc, ← rpow_add l3]
section nabla
variable {α E : Type*} [OfNat α 1] [Add α] [Sub α] {u : α → ℂ}
def cumsum [AddCommMonoid E] (u : ℕ → E) (n : ℕ) : E := ∑ i ∈ Finset.range n, u i
def nabla [Sub E] (u : α → E) (n : α) : E := u (n + 1) - u n
def nnabla [Sub E] (u : α → E) (n : α) : E := u n - u (n + 1)
def shift (u : α → E) (n : α) : E := u (n + 1)
@[simp] lemma cumsum_zero [AddCommMonoid E] {u : ℕ → E} : cumsum u 0 = 0 := by simp [cumsum]
lemma cumsum_succ [AddCommMonoid E] {u : ℕ → E} (n : ℕ) :
    cumsum u (n + 1) = cumsum u n + u n := by
  simp [cumsum, Finset.sum_range_succ]
@[simp] lemma nabla_cumsum [AddCommGroup E] {u : ℕ → E} : nabla (cumsum u) = u := by
  ext n ; simp [nabla, cumsum, Finset.range_add_one]
lemma neg_cumsum [AddCommGroup E] {u : ℕ → E} : -(cumsum u) = cumsum (-u) :=
  funext (fun n => by simp [cumsum])
lemma cumsum_nonneg {u : ℕ → ℝ} (hu : 0 ≤ u) : 0 ≤ cumsum u :=
  fun _ => Finset.sum_nonneg (fun i _ => hu i)
omit [Sub α] in
lemma neg_nabla [Ring E] {u : α → E} : -(nabla u) = nnabla u := by ext n ; simp [nabla, nnabla]
omit [Sub α] in
@[simp] lemma nnabla_mul [Ring E] {u : α → E} {c : E} :
    nnabla (fun n => c * u n) = c • nnabla u := by
  ext n ; simp [nnabla, mul_sub]
end nabla
lemma Finset.sum_shift_front {E : Type*} [Ring E] {u : ℕ → E} {n : ℕ} :
    cumsum u (n + 1) = u 0 + cumsum (shift u) n := by
  simp_rw [add_comm n, cumsum, sum_range_add, sum_range_one, add_comm 1] ; rfl
lemma Finset.sum_shift_back {E : Type*} [Ring E] {u : ℕ → E} {n : ℕ} :
    cumsum u (n + 1) = cumsum u n + u n := by
  simp [cumsum, Finset.range_add_one, add_comm]
lemma summation_by_parts {E : Type*} [Ring E] {a A b : ℕ → E} (ha : a = nabla A) {n : ℕ} :
    cumsum (a * b) (n + 1) = A (n + 1) * b n - A 0 * b 0 -
    cumsum (shift A * fun i => (b (i + 1) - b i)) n := by
  have l1 : ∑ x ∈ Finset.range (n + 1), A (x + 1) * b x = ∑ x ∈ Finset.range n,
      A (x + 1) * b x + A (n + 1) * b n :=
    Finset.sum_shift_back
  have l2 : ∑ x ∈ Finset.range (n + 1), A x * b x = A 0 * b 0 + ∑ x ∈ Finset.range n,
      A (x + 1) * b (x + 1) :=
    Finset.sum_shift_front
  simp only [cumsum, ha, Pi.mul_apply, nabla, sub_mul, Finset.sum_sub_distrib, l1, l2, shift,
    mul_sub]
  abel
lemma summation_by_parts' {E : Type*} [Ring E] {a b : ℕ → E} {n : ℕ} :
    cumsum (a * b) (n + 1) = cumsum a (n + 1) * b n - cumsum (shift (cumsum a) * nabla b) n := by
  change cumsum (a * b) (n + 1) =
    cumsum a (n + 1) * b n - cumsum (shift (cumsum a) * (fun i => b (i + 1) - b i)) n
  simpa using summation_by_parts (a := a) (b := b) (A := cumsum a) (by simp)
lemma summation_by_parts'' {E : Type*} [Ring E] {a b : ℕ → E} :
    shift (cumsum (a * b)) = shift (cumsum a) * b - cumsum (shift (cumsum a) * nabla b) := by
  ext n ; apply summation_by_parts'
lemma summable_iff_bounded {u : ℕ → ℝ} (hu : 0 ≤ u) :
    Summable u ↔ BoundedAtFilter atTop (cumsum u) := by
  have l1 : (cumsum u =O[atTop] 1) ↔ _ := isBigO_one_nat_atTop_iff
  have l2 n : ‖cumsum u n‖ = cumsum u n := by simpa using cumsum_nonneg hu n
  simp only [BoundedAtFilter, l1, l2]
  constructor <;> intro ⟨C, h1⟩
  · exact ⟨C, fun n => sum_le_hasSum _ (fun i _ => hu i) h1⟩
  · exact summable_of_sum_range_le hu h1
lemma Filter.EventuallyEq.summable {u v : ℕ → ℝ} (h : u =ᶠ[atTop] v) (hu : Summable v) :
    Summable u :=
  summable_of_isBigO_nat hu h.isBigO
lemma summable_congr_ae {u v : ℕ → ℝ} (huv : u =ᶠ[atTop] v) : Summable u ↔ Summable v := by
  constructor <;> intro h <;> simp [huv.summable, huv.symm.summable, h]
lemma BoundedAtFilter.add_const {u : ℕ → ℝ} {c : ℝ} :
    BoundedAtFilter atTop (fun n => u n + c) ↔ BoundedAtFilter atTop u := by
  have : u = fun n => (u n + c) + (-c) := by ext n ; ring
  simp only [BoundedAtFilter]
  constructor <;> intro h
  on_goal 1 => rw [this]
  all_goals { exact h.add (const_boundedAtFilter _ _) }
lemma BoundedAtFilter.comp_add {u : ℕ → ℝ} {N : ℕ} :
    BoundedAtFilter atTop (fun n => u (n + N)) ↔ BoundedAtFilter atTop u := by
  simp only [BoundedAtFilter, isBigO_iff, norm_eq_abs, Pi.one_apply, one_mem,
    CStarRing.norm_of_mem_unitary, mul_one, eventually_atTop]
  constructor <;> intro ⟨C, n₀, h⟩ <;> use C
  · refine ⟨n₀ + N, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (m := N) (n := n) (by grind)
    exact h _ <| Nat.add_le_add_iff_right.mp hn
  · exact ⟨n₀, fun n hn => h _ (by grind)⟩
lemma summable_iff_bounded' {u : ℕ → ℝ} (hu : ∀ᶠ n in atTop, 0 ≤ u n) :
    Summable u ↔ BoundedAtFilter atTop (cumsum u) := by
  obtain ⟨N, hu⟩ := eventually_atTop.mp hu
  have e2 : cumsum (fun i ↦ u (i + N)) = fun n => cumsum u (n + N) - cumsum u N := by
    ext n ; simp_rw [cumsum, add_comm _ N, Finset.sum_range_add] ; ring
  rw [← summable_nat_add_iff N, summable_iff_bounded (fun n => hu _ <| Nat.le_add_left N n), e2]
  simp_rw [sub_eq_add_neg, BoundedAtFilter.add_const, BoundedAtFilter.comp_add]
lemma bounded_of_shift {u : ℕ → ℝ} (h : BoundedAtFilter atTop (shift u)) :
    BoundedAtFilter atTop u := by
  simp only [BoundedAtFilter, isBigO_iff, eventually_atTop] at h ⊢
  obtain ⟨C, N, hC⟩ := h
  refine ⟨C, N + 1, fun n hn => ?_⟩
  simp only [shift] at hC
  have r1 : n - 1 ≥ N := Nat.le_sub_one_of_lt hn
  have r2 : n - 1 + 1 = n := by omega
  simpa [r2] using hC (n - 1) r1
lemma dirichlet_test' {a b : ℕ → ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hAb : BoundedAtFilter atTop (shift (cumsum a) * b)) (hbb : ∀ᶠ n in atTop, b (n + 1) ≤ b n)
    (h : Summable (shift (cumsum a) * nnabla b)) : Summable (a * b) := by
  have l1 : ∀ᶠ n in atTop, 0 ≤ (shift (cumsum a) * nnabla b) n := by
    filter_upwards [hbb] with n hb
    exact mul_nonneg (by simpa [shift, cumsum] using Finset.sum_nonneg' ha) (sub_nonneg.mpr hb)
  rw [summable_iff_bounded (mul_nonneg ha hb)]
  rw [summable_iff_bounded' l1] at h
  apply bounded_of_shift
  simpa only [summation_by_parts'', sub_eq_add_neg, neg_cumsum, ← mul_neg, neg_nabla]
    using hAb.add h
lemma exists_antitone_of_eventually {u : ℕ → ℝ} (hu : ∀ᶠ n in atTop, u (n + 1) ≤ u n) :
    ∃ v : ℕ → ℝ, range v ⊆ range u ∧ Antitone v ∧ v =ᶠ[atTop] u := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hu
  let v (n : ℕ) := u (if n < N then N else n)
  refine ⟨v, ?_, ?_, ?_⟩
  · exact fun x ⟨n, hn⟩ => ⟨if n < N then N else n, hn⟩
  · refine antitone_nat_of_succ_le (fun n => ?_)
    by_cases h : n < N
    · by_cases h' : n + 1 < N <;> simp [v, h, h']
      have : n + 1 = N := by linarith
      simp [this]
    · have : ¬(n + 1 < N) := by linarith
      simp only [this, ↓reduceIte, h, ge_iff_le, v] ; apply hN ; linarith
  · have : ∀ᶠ n in atTop, ¬(n < N) := by simpa using ⟨N, fun b hb => by linarith⟩
    filter_upwards [this] with n hn ; simp [v, hn]
lemma summable_inv_mul_log_sq : Summable (fun n : ℕ => (n * (Real.log n) ^ 2)⁻¹) := by
  let u (n : ℕ) := (n * (Real.log n) ^ 2)⁻¹
  have l7 : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n :=
    tendsto_atTop.mp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop) 1
  have l8 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  have l9 : ∀ᶠ n in atTop, u (n + 1) ≤ u n := by
    filter_upwards [l7, l8] with n l2 l8; dsimp [u]; gcongr <;> simp
  obtain ⟨v, l1, l2, l3⟩ := exists_antitone_of_eventually l9
  rw [summable_congr_ae l3.symm]
  have l4 (n : ℕ) : 0 ≤ v n := by obtain ⟨k, hk⟩ := l1 ⟨n, rfl⟩ ; rw [← hk] ; positivity
  apply (summable_condensed_iff_of_nonneg l4 (fun _ _ _ a ↦ l2 a)).mp
  suffices this : ∀ᶠ k : ℕ in atTop, 2 ^ k * v (2 ^ k) = ((k : ℝ) ^ 2)⁻¹ * ((Real.log 2) ^ 2)⁻¹ by
    exact (summable_congr_ae this).mpr <| (Real.summable_nat_pow_inv.mpr one_lt_two).mul_right _
  have l5 : ∀ᶠ k in atTop, v (2 ^ k) = u (2 ^ k) :=
    l3.comp_tendsto <| tendsto_pow_atTop_atTop_of_one_lt Nat.le.refl
  filter_upwards [l5, l8] with k l5 l8
  simp only [l5, mul_inv_rev, Nat.cast_pow, Nat.cast_ofNat, log_pow, u]
  field_simp
lemma tendsto_mul_add_atTop {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun x => a * x + b) atTop atTop :=
  tendsto_atTop_add_const_right _ b (tendsto_id.const_mul_atTop ha)
lemma isLittleO_const_of_tendsto_atTop {α : Type*} [Preorder α] (a : ℝ) {f : α → ℝ}
    (hf : Tendsto f atTop atTop) : (fun _ => a) =o[atTop] f := by
  simp [tendsto_norm_atTop_atTop.comp hf]
lemma isLittleO_mul_add_sq (a b : ℝ) : (fun x => a * x + b) =o[atTop] (fun x => x ^ 2) := by
  apply IsLittleO.add
  · apply IsLittleO.const_mul_left ; simpa using isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) one_lt_two
  · apply isLittleO_const_of_tendsto_atTop _ <| tendsto_pow_atTop (by linarith)
lemma log_mul_add_isBigO_log {a : ℝ} (ha : 0 < a) (b : ℝ) :
    (fun x => Real.log (a * x + b)) =O[atTop] Real.log := by
  apply IsBigO.of_bound (2 : ℕ)
  have l2 : ∀ᶠ x : ℝ in atTop, 0 ≤ log x := tendsto_atTop.mp tendsto_log_atTop 0
  have l3 : ∀ᶠ x : ℝ in atTop, 0 ≤ log (a * x + b) :=
    tendsto_atTop.mp (tendsto_log_atTop.comp (tendsto_mul_add_atTop ha b)) 0
  have l5 : ∀ᶠ x : ℝ in atTop, 1 ≤ a * x + b := tendsto_atTop.mp (tendsto_mul_add_atTop ha b) 1
  have l1 : ∀ᶠ x : ℝ in atTop, a * x + b ≤ x ^ 2 := by
    filter_upwards [(isLittleO_mul_add_sq a b).eventuallyLE, l5] with x r2 l5
    simpa [abs_eq_self.mpr (zero_le_one.trans l5)] using r2
  filter_upwards [l1, l2, l3, l5] with x l1 l2 l3 l5
  simpa [abs_eq_self.mpr l2, abs_eq_self.mpr l3, Real.log_pow] using
    Real.log_le_log (by linarith) l1
lemma isBigO_log_mul_add {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Real.log =O[atTop] (fun x => Real.log (a * x + b)) := by
  convert (log_mul_add_isBigO_log (b := -b / a) (inv_pos.mpr ha)).comp_tendsto
    (tendsto_mul_add_atTop (b := b) ha) using 1
  · ext x
    simp only [Function.comp_apply]
    congr
    field_simp
    simp
  · rfl
lemma log_isbigo_log_div {d : ℝ} (hb : 0 < d) :
    (fun n ↦ Real.log n) =O[atTop] (fun n ↦ Real.log (n / d)) := by
  convert isBigO_log_mul_add (inv_pos.mpr hb) 0 using 1; simp only [add_zero]; field_simp
lemma Asymptotics.IsBigO.add_isLittleO_right {f g : ℝ → ℝ} (h : g =o[atTop] f) :
    f =O[atTop] (f + g) := by
  rw [isLittleO_iff] at h ; specialize h (c := 2⁻¹) (by norm_num)
  rw [isBigO_iff'']
  refine ⟨2⁻¹, by norm_num, ?_⟩
  filter_upwards [h] with x h
  simp only [norm_eq_abs, Pi.add_apply] at h ⊢
  calc _ = |f x| - 2⁻¹ * |f x| := by ring
       _ ≤ |f x| - |g x| := by linarith
       _ ≤ |(|f x| - |g x|)| := le_abs_self _
       _ ≤ _ := by rw [← sub_neg_eq_add, ← abs_neg (g x)] ; exact abs_abs_sub_abs_le (f x) (-g x)
lemma Asymptotics.IsBigO.sq {α : Type*} [Preorder α] {f g : α → ℝ} (h : f =O[atTop] g) :
    (fun n ↦ f n ^ 2) =O[atTop] (fun n => g n ^ 2) := by
  simpa [pow_two] using h.mul h
lemma log_sq_isbigo_mul {a b : ℝ} (hb : 0 < b) :
    (fun x ↦ Real.log x ^ 2) =O[atTop] (fun x ↦ a + Real.log (x / b) ^ 2) := by
  apply (log_isbigo_log_div hb).sq.trans ; simp_rw [add_comm a]
  refine IsBigO.add_isLittleO_right <| isLittleO_const_of_tendsto_atTop _ ?_
  exact (tendsto_pow_atTop two_ne_zero).comp <|
    tendsto_log_atTop.comp <| tendsto_id.atTop_div_const hb
theorem log_add_div_isBigO_log (a : ℝ) {b : ℝ} (hb : 0 < b) :
    (fun x ↦ Real.log ((x + a) / b)) =O[atTop] fun x ↦ Real.log x := by
  convert log_mul_add_isBigO_log (inv_pos.mpr hb) (a / b) using 3 ; ring
lemma log_add_one_sub_log_le {x : ℝ} (hx : 0 < x) : nabla Real.log x ≤ x⁻¹ := by
  have l1 : ContinuousOn Real.log (Icc x (x + 1)) := by
    apply continuousOn_log.mono ; intro t ⟨h1, _⟩ ; simp ; linarith
  have l2 t (ht : t ∈ Ioo x (x + 1)) : HasDerivAt Real.log t⁻¹ t :=
    Real.hasDerivAt_log (by linarith [ht.1])
  obtain ⟨t, ⟨ht1, _⟩, htx⟩ := exists_hasDerivAt_eq_slope Real.log (·⁻¹) (by linarith) l1 l2
  simp only [add_sub_cancel_left, div_one] at htx
  rw [nabla, ← htx, inv_le_inv₀ (by linarith) hx]
  exact ht1.le
lemma nabla_log_main : nabla Real.log =O[atTop] fun x ↦ 1 / x := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_gt_atTop 0] with x l1
  have l2 : log x ≤ log (x + 1) := log_le_log l1 (by linarith)
  simpa [nabla, abs_eq_self.mpr l1.le, abs_eq_self.mpr (sub_nonneg.mpr l2)] using
    log_add_one_sub_log_le l1
lemma nabla_log {b : ℝ} (hb : 0 < b) :
    nabla (fun x => Real.log (x / b)) =O[atTop] (fun x => 1 / x) := by
  refine EventuallyEq.trans_isBigO ?_ nabla_log_main
  filter_upwards [eventually_gt_atTop 0] with x l2
  rw [nabla, log_div (by linarith) (by linarith), log_div l2.ne.symm (by linarith), nabla] ; ring
lemma nnabla_mul_log_sq (a : ℝ) {b : ℝ} (hb : 0 < b) :
    nabla (fun x => x * (a + Real.log (x / b) ^ 2)) =O[atTop] (fun x => Real.log x ^ 2) := by
  have l1 : nabla (fun n => n * (a + Real.log (n / b) ^ 2)) = fun n =>
      a + Real.log ((n + 1) / b) ^ 2 +
        (n * (Real.log ((n + 1) / b) ^ 2 - Real.log (n / b) ^ 2)) := by
    ext n ; simp [nabla] ; ring
  have l2 := (isLittleO_const_of_tendsto_atTop a
    ((tendsto_pow_atTop two_ne_zero).comp tendsto_log_atTop)).isBigO
  have l3 := (log_add_div_isBigO_log 1 hb).sq
  have l4 : (fun x => Real.log ((x + 1) / b) + Real.log (x / b)) =O[atTop] Real.log := by
    simpa using (log_add_div_isBigO_log _ hb).add (log_add_div_isBigO_log 0 hb)
  have e2 : (fun x : ℝ => x * (Real.log x * (1 / x))) =ᶠ[atTop] Real.log := by
    filter_upwards [eventually_ge_atTop 1] with x hx using by field_simp
  have l5 : (fun n ↦ n * (Real.log n * (1 / n))) =O[atTop] (fun n ↦ (Real.log n) ^ 2) :=
    e2.trans_isBigO
      (by
        simpa [Function.comp_def] using
          (isLittleO_mul_add_sq 1 0).isBigO.comp_tendsto Real.tendsto_log_atTop)
  simp_rw [l1, _root_.sq_sub_sq]
  exact ((l2.add l3).add (isBigO_refl (·) atTop |>.mul (l4.mul (nabla_log hb)) |>.trans l5))
lemma nnabla_bound_aux1 (a : ℝ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun x => x * (a + Real.log (x / b) ^ 2)) atTop atTop :=
  tendsto_id.atTop_mul_atTop₀ <| tendsto_atTop_add_const_left _ _ <|
    (tendsto_pow_atTop two_ne_zero).comp <| tendsto_log_atTop.comp <| tendsto_id.atTop_div_const hb
lemma nnabla_bound_aux2 (a : ℝ) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ x in atTop, 0 < x * (a + Real.log (x / b) ^ 2) :=
  (nnabla_bound_aux1 a hb).eventually (eventually_gt_atTop 0)
lemma Real.log_eventually_gt_atTop (a : ℝ) :
    ∀ᶠ x in atTop, a < Real.log x :=
  Real.tendsto_log_atTop.eventually (eventually_gt_atTop a)
lemma nnabla_bound_aux {x : ℝ} (hx : 0 < x) :
    nnabla (fun n ↦ 1 / (n * ((2 * π) ^ 2 + Real.log (n / x) ^ 2))) =O[atTop]
    (fun n ↦ 1 / (Real.log n ^ 2 * n ^ 2)) := by
  let d n : ℝ := n * ((2 * π) ^ 2 + Real.log (n / x) ^ 2)
  change (fun x_1 ↦ nnabla (fun n ↦ 1 / d n) x_1) =O[atTop] _
  have l2 : ∀ᶠ n in atTop, 0 < d n := (nnabla_bound_aux2 ((2 * π) ^ 2) hx)
  have l3 : ∀ᶠ n in atTop, 0 < d (n + 1) :=
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id).eventually l2
  have l1 : ∀ᶠ n : ℝ in atTop,
      nnabla (fun n ↦ 1 / d n) n = (d (n + 1) - d n) * (d n)⁻¹ * (d (n + 1))⁻¹ := by
    filter_upwards [l2, l3] with n l2 l3
    rw [nnabla, one_div, one_div, inv_sub_inv l2.ne.symm l3.ne.symm, div_eq_mul_inv, mul_inv,
      mul_assoc]
  have l4 : (fun n => (d n)⁻¹) =O[atTop] (fun n => (n * (Real.log n) ^ 2)⁻¹) := by
    apply IsBigO.inv_rev
    · refine (isBigO_refl _ _).mul <| (log_sq_isbigo_mul hx)
    · filter_upwards [Real.log_eventually_gt_atTop 0, eventually_gt_atTop 0] with x hx hx'
      rw [← not_imp_not]
      intro _
      positivity
  have l5 : (fun n => (d (n + 1))⁻¹) =O[atTop] (fun n => (n * (Real.log n) ^ 2)⁻¹) := by
    refine IsBigO.trans ?_ l4
    rw [isBigO_iff]; use 1
    have e3 : ∀ᶠ n in atTop, d n ≤ d (n + 1) := by
      filter_upwards [eventually_ge_atTop x] with n hn
      have e2 : 1 ≤ n / x := (one_le_div hx).mpr hn
      have : 0 ≤ n := hx.le.trans hn
      simp only [d]
      gcongr <;> simp [Real.log_nonneg, *]
    filter_upwards [l2, l3, e3] with n e1 e2 e3
    simp_rw [one_mul]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr e2), abs_of_pos (inv_pos.mpr e1)]
    exact inv_anti₀ e1 e3
  have l6 : (fun n => d (n + 1) - d n) =O[atTop] (fun n => (Real.log n) ^ 2) := by
    change nabla d =O[atTop] (fun n => (Real.log n) ^ 2)
    simpa [d] using (nnabla_mul_log_sq ((2 * π) ^ 2) hx)
  apply EventuallyEq.trans_isBigO l1
  apply ((l6.mul l4).mul l5).trans_eventuallyEq
  filter_upwards [eventually_ge_atTop 2, Real.log_eventually_gt_atTop 0] with n hn hn'
  field_simp
lemma nnabla_bound (C : ℝ) {x : ℝ} (hx : 0 < x) :
    nnabla (fun n => C / (1 + (Real.log (n / x) / (2 * π)) ^ 2) / n) =O[atTop]
    (fun n => (n ^ 2 * (Real.log n) ^ 2)⁻¹) := by
  field_simp
  simp only [div_eq_mul_inv, mul_inv, nnabla_mul, one_mul]
  apply IsBigO.const_mul_left
  simpa [div_eq_mul_inv, mul_pow, mul_comm] using nnabla_bound_aux hx
def chebyWith (C : ℝ) (f : ℕ → ℂ) : Prop := ∀ n, cumsum (‖f ·‖) n ≤ C * n
def cheby (f : ℕ → ℂ) : Prop := ∃ C, chebyWith C f
lemma cheby.bigO (h : cheby f) : cumsum (‖f ·‖) =O[atTop] ((↑) : ℕ → ℝ) := by
  have l1 : 0 ≤ cumsum (‖f ·‖) := cumsum_nonneg (fun _ => norm_nonneg _)
  obtain ⟨C, hC⟩ := h
  apply isBigO_of_le' (c := C) atTop
  intro n
  rw [Real.norm_eq_abs, abs_eq_self.mpr (l1 n)]
  simpa using hC n
lemma limiting_fourier_lim1_aux (hcheby : cheby f) (hx : 0 < x) (C : ℝ) (hC : 0 ≤ C) :
    Summable fun n ↦ ‖f n‖ / ↑n * (C / (1 + (1 / (2 * π) * Real.log (↑n / x)) ^ 2)) := by
  let a (n : ℕ) := (C / (1 + (Real.log (↑n / x) / (2 * π)) ^ 2) / ↑n)
  replace hcheby := hcheby.bigO
  have l1 : shift (cumsum (‖f ·‖)) =O[atTop] (fun n : ℕ => (↑(n + 1) : ℝ)) :=
    hcheby.comp_tendsto <| tendsto_add_atTop_nat 1
  have l2 : shift (cumsum (‖f ·‖)) =O[atTop] (fun n => (n : ℝ)) :=
    l1.trans
      (by simpa using (isBigO_refl _ _).add <| isBigO_iff.mpr ⟨1, by simpa using ⟨1, by tauto⟩⟩)
  have l5 : BoundedAtFilter atTop (fun n : ℕ => C / (1 + (Real.log (↑n / x) / (2 * π)) ^ 2)) := by
    simp only [BoundedAtFilter]
    field_simp
    apply isBigO_of_le' (c := C) ; intro n
    have : 0 ≤ 2 ^ 2 * π ^ 2 + Real.log (n / x) ^ 2 := by positivity
    simp only [norm_div, norm_mul, norm_eq_abs, abs_eq_self.mpr hC, norm_pow,
      abs_eq_self.mpr pi_nonneg, abs_eq_self.mpr this, Pi.one_apply, one_mem,
      CStarRing.norm_of_mem_unitary, mul_one, ge_iff_le, Nat.abs_ofNat]
    apply div_le_of_le_mul₀ this hC
    rw [mul_add, ← mul_assoc]
    apply le_add_of_le_of_nonneg le_rfl
    positivity
  have l3 : a =O[atTop] (fun n => 1 / (n : ℝ)) := by
    simpa [a, div_eq_mul_inv] using IsBigO.mul l5 (isBigO_refl (fun n : ℕ => 1 / (n : ℝ)) _)
  have l4 : nnabla a =O[atTop] (fun n : ℕ => (n ^ 2 * (Real.log n) ^ 2)⁻¹) := by
    convert (nnabla_bound C hx).natCast ; simp [nnabla, a]
  simp_rw [div_mul_eq_mul_div, mul_div_assoc, one_mul]
  apply dirichlet_test'
  · intro n ; exact norm_nonneg _
  · intro n ; positivity
  · apply (l2.mul l3).trans_eventuallyEq
    apply eventually_of_mem (Ici_mem_atTop 1)
    intro x (hx : 1 ≤ x)
    have : x ≠ 0 := Nat.one_le_iff_ne_zero.mp hx
    simp [this]
  · have : ∀ᶠ n : ℕ in atTop, x ≤ n := by simpa using eventually_ge_atTop ⌈x⌉₊
    filter_upwards [this] with n hn
    have e1 : 0 < (n : ℝ) := by linarith
    have e2 : 1 ≤ n / x := (one_le_div hx).mpr hn
    have e3 := Nat.le_succ n
    gcongr
    refine div_nonneg (Real.log_nonneg e2) (by norm_num [pi_nonneg])
  · apply summable_of_isBigO_nat summable_inv_mul_log_sq
    apply (l2.mul l4).trans_eventuallyEq
    apply eventually_of_mem (Ici_mem_atTop 2)
    intro x (hx : 2 ≤ x)
    have : (x : ℝ) ≠ 0 := by simp ; linarith
    have : Real.log x ≠ 0 := by
      have ll : 2 ≤ (x : ℝ) := by simp [hx]
      simp
      grind
    field_simp
theorem limiting_fourier_lim1 (hcheby : cheby f) (ψ : W21) (hx : 0 < x) :
    Tendsto (fun σ' : ℝ ↦
        ∑' n, term f σ' n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (n / x))) (𝓝[>] 1)
      (𝓝 (∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (n / x)))) := by
  obtain ⟨C, hC⟩ := decay_bounds_cor ψ
  have : 0 ≤ C := by simpa using (norm_nonneg _).trans (hC 0)
  refine tendsto_tsum_of_dominated_convergence
    (limiting_fourier_lim1_aux hcheby hx C this) (fun n => ?_) ?_
  · apply Tendsto.mul_const
    by_cases h : n = 0 <;> simp only [term, h, ↓reduceIte, CharP.cast_eq_zero, div_zero,
      tendsto_const_nhds_iff]
    refine tendsto_const_nhds.div ?_ (by simp [h])
    simpa using ((continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds).const_cpow
  · rw [eventually_nhdsWithin_iff]
    apply Eventually.of_forall
    intro σ' (hσ' : 1 < σ') n
    rw [norm_mul, ← nterm_eq_norm_term]
    refine mul_le_mul ?_ (hC _) (norm_nonneg _) (div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
    by_cases h : n = 0 <;> simp only [nterm, h, ↓reduceIte, CharP.cast_eq_zero, div_zero, le_refl]
    have : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.pos_iff_ne_zero.mpr h
    refine div_le_div₀ (norm_nonneg _) le_rfl (by simpa [Nat.pos_iff_ne_zero]) ?_
    simpa using Real.rpow_le_rpow_of_exponent_le this hσ'.le
theorem limiting_fourier_lim2_aux (x : ℝ) (C : ℝ) :
    Integrable (fun t ↦ max |x| 1 * (C / (1 + (t / (2 * π)) ^ 2)))
      (Measure.restrict volume (Ici (-Real.log x))) := by
  simp_rw [div_eq_mul_inv C]
  exact (((integrable_inv_one_add_sq.comp_div
    (by simp [pi_ne_zero])).const_mul _).const_mul _).restrict
theorem limiting_fourier_lim2 (A : ℝ) (ψ : W21) (hx : 1 ≤ x) :
    Tendsto (fun σ' ↦ A * ↑(x ^ (1 - σ')) *
        ∫ u in Ici (-Real.log x), rexp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)))
      (𝓝[>] 1) (𝓝 (A * ∫ u in Ici (-Real.log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)))) := by
  obtain ⟨C, hC⟩ := decay_bounds_cor ψ
  apply Tendsto.mul
  · suffices h : Tendsto (fun σ' : ℝ ↦ ofReal (x ^ (1 - σ'))) (𝓝[>] 1) (𝓝 1) by
      simpa using h.const_mul ↑A
    suffices h : Tendsto (fun σ' : ℝ ↦ x ^ (1 - σ')) (𝓝[>] 1) (𝓝 1) from
      (continuous_ofReal.tendsto 1).comp h
    have : Tendsto (fun σ' : ℝ ↦ σ') (𝓝 1) (𝓝 1) := fun _ a ↦ a
    have : Tendsto (fun σ' : ℝ ↦ 1 - σ') (𝓝[>] 1) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds (by simpa using this.const_sub 1)
    simpa using tendsto_const_nhds.rpow this (Or.inl (zero_lt_one.trans_le hx).ne.symm)
  · refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_
      (limiting_fourier_lim2_aux x C) ?_
    · apply Eventually.of_forall ; intro σ'
      apply Continuous.aestronglyMeasurable
      have := continuous_FourierIntegral ψ
      continuity
    · apply eventually_of_mem (U := Ioo 1 2)
      · apply Ioo_mem_nhdsGT_of_mem ; simp
      · intro σ' ⟨h1, h2⟩
        rw [ae_restrict_iff' measurableSet_Ici]
        apply Eventually.of_forall
        intro t (ht : - Real.log x ≤ t)
        rw [norm_mul]
        have hdom_nonneg : 0 ≤ max |x| 1 := by
          exact (abs_nonneg x).trans (le_max_left _ _)
        refine mul_le_mul ?_ (hC _) (norm_nonneg _) hdom_nonneg
        simp only [neg_mul, ofReal_exp, ofReal_neg, ofReal_mul, ofReal_sub, ofReal_one, norm_exp,
          neg_re, mul_re, ofReal_re, sub_re, one_re, ofReal_im, sub_im, one_im, sub_self, mul_zero,
          sub_zero]
        have : -Real.log x * (σ' - 1) ≤ t * (σ' - 1) := mul_le_mul_of_nonneg_right ht (by linarith)
        have : -(t * (σ' - 1)) ≤ Real.log x * (σ' - 1) := by simpa using neg_le_neg this
        have := Real.exp_monotone this
        apply this.trans
        have l1 : σ' - 1 ≤ 1 := by linarith
        have : 0 ≤ Real.log x := Real.log_nonneg hx
        have := mul_le_mul_of_nonneg_left l1 this
        refine (Real.exp_monotone this).trans ?_
        have hxabs : |x| = x := abs_of_nonneg (zero_le_one.trans hx)
        calc
          Real.exp (Real.log x * 1) = |x| := by
            simpa [mul_one, hxabs] using (Real.exp_log (zero_lt_one.trans_le hx))
          _ ≤ max |x| 1 := le_max_left _ _
    · apply Eventually.of_forall
      intro x
      suffices h : Tendsto (fun n ↦ ((rexp (-x * (n - 1))) : ℂ)) (𝓝[>] 1) (𝓝 1) by
        simpa using h.mul_const _
      apply Tendsto.mono_left ?_ nhdsWithin_le_nhds
      suffices h : Continuous (fun n ↦ ((rexp (-x * (n - 1))) : ℂ)) by simpa using h.tendsto 1
      continuity
theorem limiting_fourier_lim3 (hG : ContinuousOn G {s | 1 ≤ s.re}) (ψ : CS 2 ℂ) (hx : 1 ≤ x) :
    Tendsto (fun σ' : ℝ ↦ ∫ t : ℝ, G (σ' + t * I) * ψ t * x ^ (t * I)) (𝓝[>] 1)
      (𝓝 (∫ t : ℝ, G (1 + t * I) * ψ t * x ^ (t * I))) := by
  by_cases hh : tsupport ψ = ∅
  · simp [tsupport_eq_empty_iff.mp hh]
  obtain ⟨a₀, ha₀⟩ := Set.nonempty_iff_ne_empty.mpr hh
  let S : Set ℂ := reProdIm (Icc 1 2) (tsupport ψ)
  have l1 : IsCompact S := by
    refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨?_, ?_⟩
    · exact isClosed_Icc.reProdIm (isClosed_tsupport ψ)
    · exact (Metric.isBounded_Icc 1 2).reProdIm ψ.h2.isBounded
  have l2 : S ⊆ {s : ℂ | 1 ≤ s.re} := fun z hz => (mem_reProdIm.mp hz).1.1
  have l3 : ContinuousOn (‖G ·‖) S := (hG.mono l2).norm
  have l4 : S.Nonempty := ⟨1 + a₀ * I, by simp [S, mem_reProdIm, ha₀]⟩
  obtain ⟨z, -, hmax⟩ := l1.exists_isMaxOn l4 l3
  let MG := ‖G z‖
  let bound (a : ℝ) : ℝ := MG * ‖ψ a‖
  apply tendsto_integral_filter_of_dominated_convergence (bound := bound)
  · apply eventually_of_mem (U := Icc 1 2) (Icc_mem_nhdsGT_of_mem (by simp)) ; intro u hu
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · exact (hG.comp_continuous (by fun_prop) (by simp [hu.1])).mul ψ.h1.continuous
    · apply Continuous.const_cpow (by fun_prop) ; simp ; linarith
  · apply eventually_of_mem (U := Icc 1 2) (Icc_mem_nhdsGT_of_mem (by simp))
    intro u hu
    apply Eventually.of_forall ; intro v
    by_cases h : v ∈ tsupport ψ
    · have r1 : u + v * I ∈ S := by simp [S, mem_reProdIm, hu.1, hu.2, h]
      have r2 := isMaxOn_iff.mp hmax _ r1
      have r4 : (x : ℂ) ≠ 0 := by simp ; linarith
      have r5 : arg x = 0 := by simp [arg_eq_zero_iff] ; linarith
      have r3 : ‖(x : ℂ) ^ (v * I)‖ = 1 := by simp [norm_cpow_of_ne_zero r4, r5]
      simp_rw [norm_mul, r3, mul_one]
      exact mul_le_mul_of_nonneg_right r2 (norm_nonneg _)
    · have : v ∉ Function.support ψ := fun a ↦ h (subset_tsupport ψ a)
      simp at this ; simp [this, bound]
  · suffices h : Continuous bound by exact h.integrable_of_hasCompactSupport ψ.h2.norm.mul_left
    have := ψ.h1.continuous ; fun_prop
  · apply Eventually.of_forall ; intro t
    apply Tendsto.mul_const
    apply Tendsto.mul_const
    refine (hG (1 + t * I) (by simp)).tendsto.comp <| tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact ((continuous_ofReal.tendsto _).add tendsto_const_nhds).mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall (fun x (hx : 1 < x) => by simp [hx.le])
lemma limiting_fourier (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (ψ : CS 2 ℂ) (hx : 1 ≤ x) :
    ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)) =
      ∫ (t : ℝ), (G (1 + t * I)) * (ψ t) * x ^ (t * I) := by
  have l1 := limiting_fourier_lim1 hcheby ψ (by linarith)
  have l2 := limiting_fourier_lim2 A ψ hx
  have l3 := limiting_fourier_lim3 hG ψ hx
  apply tendsto_nhds_unique_of_eventuallyEq (l1.sub l2) l3
  simpa [eventuallyEq_nhdsWithin_iff] using Eventually.of_forall (limiting_fourier_aux hG' hf ψ hx)
lemma limiting_cor_aux {f : ℝ → ℂ} : Tendsto (fun x : ℝ ↦ ∫ t, f t * x ^ (t * I)) atTop (𝓝 0) := by
  have l1 : ∀ᶠ x : ℝ in atTop, ∀ t : ℝ, x ^ (t * I) = exp (log x * t * I) := by
    filter_upwards [eventually_ne_atTop 0, eventually_ge_atTop 0] with x hx hx' t
    rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx), ofReal_log hx'] ; ring_nf
  have l2 : ∀ᶠ x : ℝ in atTop, ∫ t, f t * x ^ (t * I) = ∫ t, f t * exp (log x * t * I) := by
    filter_upwards [l1] with x hx
    refine integral_congr_ae (Eventually.of_forall (fun x => by simp [hx]))
  simp_rw [tendsto_congr' l2]
  convert_to Tendsto (fun x => 𝓕 f (-Real.log x / (2 * π))) atTop (𝓝 0)
  · ext x
    rw [Real.fourier_real_eq]
    congr 1; ext t
    rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, mul_comm]
    congr 2
    push_cast
    field_simp
    try ring
  refine (Real.zero_at_infty_fourier f).comp <| Tendsto.mono_right ?_ _root_.atBot_le_cocompact
  exact (tendsto_neg_atBot_iff.mpr tendsto_log_atTop).atBot_mul_const (inv_pos.mpr two_pi_pos)
lemma limiting_cor (ψ : CS 2 ℂ) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) := by
  apply limiting_cor_aux.congr'
  filter_upwards [eventually_ge_atTop 1] with x hx using
    limiting_fourier hcheby hG hG' hf ψ hx |>.symm
lemma smooth_urysohn (a b c d : ℝ) (h1 : a < b) (h3 : c < d) : ∃ Ψ : ℝ → ℝ,
    (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
      Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 := by
  obtain ⟨ψ, l1, l2, l3, l4, -⟩ := smooth_urysohn_support_Ioo h1 h3
  refine ⟨ψ, l1, l2, l3, l4⟩
noncomputable def exists_trunc : trunc := by
  choose ψ h1 h2 h3 h4 using smooth_urysohn (-2) (-1) (1) (2) (by linarith) (by linarith)
  exact ⟨⟨ψ, h1.of_le (by norm_cast), h2⟩, h3, h4⟩
noncomputable def pp (a x : ℝ) : ℝ := a ^ 2 * (x + 1) ^ 2 + (1 - a) * (1 + a)
lemma pp_pos {a : ℝ} (ha : a ∈ Ioo (-1) 1) (x : ℝ) : 0 < pp a x := by
  simp only [pp]
  have : 0 < 1 - a := by linarith [ha.2]
  have : 0 < 1 + a := by linarith [ha.1]
  positivity
noncomputable def hh (a t : ℝ) : ℝ := (t * (1 + (a * log t) ^ 2))⁻¹
noncomputable def hh' (a t : ℝ) : ℝ := - pp a (log t) * hh a t ^ 2
lemma hh_nonneg (a : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ hh a t := by dsimp only [hh] ; positivity
lemma hh_deriv (a : ℝ) {t : ℝ} (ht : t ≠ 0) : HasDerivAt (hh a) (hh' a t) t := by
  have e1 : t * (1 + (a * log t) ^ 2) ≠ 0 := mul_ne_zero ht (_root_.ne_of_lt (by positivity)).symm
  have l5 : HasDerivAt (fun t : ℝ => log t) t⁻¹ t := Real.hasDerivAt_log ht
  have l4 : HasDerivAt (fun t : ℝ => a * log t) (a * t⁻¹) t := l5.const_mul _
  have l3 : HasDerivAt (fun t : ℝ => (a * log t) ^ 2) (2 * a ^ 2 * t⁻¹ * log t) t := by
    have hpow := l4.pow 2
    have hpow' : HasDerivAt ((fun t : ℝ => a * log t) ^ 2)
        (2 * a ^ 2 * t⁻¹ * log t) t := hpow.congr_deriv (by ring)
    exact hpow'.congr_of_eventuallyEq (Eventually.of_forall fun s => by simp [Pi.pow_apply])
  have l2 : HasDerivAt (fun t : ℝ => 1 + (a * log t) ^ 2) (2 * a ^ 2 * t⁻¹ * log t) t :=
    l3.const_add _
  have l1 : HasDerivAt (fun t : ℝ => t * (1 + (a * log t) ^ 2))
      (1 + 2 * a ^ 2 * log t + a ^ 2 * log t ^ 2) t := by
    have hprod := (hasDerivAt_id' t).mul l2
    have hprod' : HasDerivAt (((fun x : ℝ => x) * fun t => 1 + (a * Real.log t) ^ 2))
        (pp a (log t)) t := by
      apply hprod.congr_deriv
      rw [show t * (2 * a ^ 2 * t⁻¹ * log t) = 2 * a ^ 2 * log t by
        rw [show t * (2 * a ^ 2 * t⁻¹ * log t) = (t * t⁻¹) * (2 * a ^ 2 * log t) by ring]
        rw [mul_inv_cancel₀ ht, one_mul]]
      simp only [pp]
      ring
    have hprod'' : HasDerivAt (fun t : ℝ => t * (1 + (a * Real.log t) ^ 2))
        (pp a (log t)) t :=
      hprod'.congr_of_eventuallyEq (Eventually.of_forall fun s => by simp [Pi.mul_apply])
    exact hprod''.congr_deriv (by
      simp only [pp]
      ring)
  change HasDerivAt (fun t : ℝ => (t * (1 + (a * log t) ^ 2))⁻¹) (hh' a t) t
  apply (l1.inv e1).congr_deriv
  simp only [hh', pp, hh]
  field_simp [inv_eq_one_div, e1, ht]
  ring
lemma hh_continuous (a : ℝ) : ContinuousOn (hh a) (Ioi 0) :=
  fun t (ht : 0 < t) => (hh_deriv a ht.ne.symm).continuousAt.continuousWithinAt
lemma hh'_nonpos {a x : ℝ} (ha : a ∈ Ioo (-1) 1) : hh' a x ≤ 0 := by
  have := pp_pos ha (log x)
  simp only [hh', neg_mul, Left.neg_nonpos_iff, ge_iff_le]
  positivity
lemma hh_antitone {a : ℝ} (ha : a ∈ Ioo (-1) 1) : AntitoneOn (hh a) (Ioi 0) := by
  have l1 x (hx : x ∈ interior (Ioi 0)) :
      HasDerivWithinAt (hh a) (hh' a x) (interior (Ioi 0)) x := by
    have : x ≠ 0 := by contrapose! hx ; simp [hx]
    exact (hh_deriv a this).hasDerivWithinAt
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi _) (hh_continuous _) l1
    (fun x _ => hh'_nonpos ha)
noncomputable def gg (x i : ℝ) : ℝ := 1 / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹
lemma gg_of_hh {x : ℝ} (hx : x ≠ 0) (i : ℝ) : gg x i = x⁻¹ * hh (1 / (2 * π)) (i / x) := by
  simp only [gg, hh]
  field_simp
lemma gg_le_one (i : ℕ) : gg x i ≤ 1 := by
  by_cases hi : i = 0 <;> simp only [gg, hi, CharP.cast_eq_zero, div_zero, one_div, mul_inv_rev,
    zero_div, Real.log_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero, inv_one, mul_one, zero_le_one]
  have l1 : 1 ≤ (i : ℝ) := by simp ; omega
  have l2 : 1 ≤ 1 + (π⁻¹ * 2⁻¹ * Real.log (↑i / x)) ^ 2 := by
    simp only [le_add_iff_nonneg_right] ; positivity
  rw [← mul_inv] ; apply inv_le_one_of_one_le₀ ; simpa using mul_le_mul l1 l2 zero_le_one (by simp)
lemma one_div_two_pi_mem_Ioo : 1 / (2 * π) ∈ Ioo (-1) 1 := by
  constructor
  · have : 0 < 1 / (2 * π) := by positivity
    linarith
  · rw [div_lt_iff₀ (by positivity : 0 < 2 * π)]
    have hπ : (2 : ℝ) ≤ π := two_le_pi
    nlinarith
lemma cancel_aux {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i * g i ≤ g (n - 1) * (C * n) + (C * (↑(n - 1 - 1) + 1) * g 0
      - C * (↑(n - 1 - 1) + 1) * g (n - 1) -
    ((n - 1 - 1) • (C * g 0) - ∑ x ∈ Finset.range (n - 1 - 1), C * g (x + 1))) := by
  have l1 (n : ℕ) :
      (g n - g (n + 1)) * ∑ i ∈ Finset.range (n + 1), f i ≤ (g n - g (n + 1)) * (C * (n + 1)) := by
    apply mul_le_mul le_rfl (by simpa [cumsum] using hf' (n + 1)) (Finset.sum_nonneg' hf) ?_
    simp only [sub_nonneg] ; apply hg' ; simp
  have l2 (x : ℕ) : C * (↑(x + 1) + 1) - C * (↑x + 1) = C := by simp ; ring
  have l3 (n : ℕ) : 0 ≤ cumsum f n := Finset.sum_nonneg' hf
  convert_to ∑ i ∈ Finset.range n, (g i) • (f i) ≤ _
  · simp [mul_comm]
  rw [Finset.sum_range_by_parts, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  simp_rw [← neg_smul, neg_sub, smul_eq_mul]
  apply _root_.add_le_add
  · exact mul_le_mul le_rfl (hf' n) (l3 n) (hg _)
  · apply Finset.sum_le_sum (fun n _ => l1 n) |>.trans
    have hcomm :
        (∑ i ∈ Finset.range (n - 1), (g i - g (i + 1)) * (C * (↑i + 1))) =
          ∑ i ∈ Finset.range (n - 1), (C * (↑i + 1)) • (g i - g (i + 1)) := by
      simp [smul_eq_mul, mul_comm, mul_left_comm]
    rw [hcomm]
    refine le_of_eq ?_
    rw [Finset.sum_range_by_parts]
    simp_rw [Finset.sum_range_sub', l2, smul_sub, smul_eq_mul, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range]
lemma sum_range_succ (a : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, a (i + 1) = (∑ i ∈ Finset.range (n + 1), a i) - a 0 := by
  have := Finset.sum_range_sub a n
  rw [Finset.sum_sub_distrib, sub_eq_iff_eq_add] at this
  rw [Finset.sum_range_succ, this] ; ring
lemma cancel_aux' {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i * g i ≤
        C * n * g (n - 1)
      + C * cumsum g (n - 1 - 1 + 1)
      - C * (↑(n - 1 - 1) + 1) * g (n - 1)
      := by
  have := cancel_aux hf hg hf' hg' n
  simp only [nsmul_eq_mul, ← Finset.mul_sum, sum_range_succ] at this
  convert this using 1 ; unfold cumsum ; ring
lemma cancel_main' {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hf0 : f 0 = 0) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    cumsum (f * g) n ≤ C * cumsum g n := by
  match n with
  | 0 => simp [cumsum]
  | 1 => specialize hg 0 ; specialize hf' 1 ; simp only [cumsum, Finset.range_one,
    Finset.sum_singleton, hf0, Nat.cast_one, mul_one, Pi.zero_apply, Pi.mul_apply, zero_mul,
    ge_iff_le] at hf' hg ⊢ ; positivity
  | n + 2 =>
      convert cancel_aux' hf hg hf' hg' (n + 2) using 1
      · simp [cumsum, Finset.sum_range_succ, add_comm, add_left_comm]
      · simp [cumsum_succ, Nat.cast_add, Nat.cast_ofNat, add_assoc, add_comm]
        ring
theorem sum_le_integral {x₀ : ℝ} {f : ℝ → ℝ} {n : ℕ} (hf : AntitoneOn f (Ioc x₀ (x₀ + n)))
    (hfi : IntegrableOn f (Icc x₀ (x₀ + n))) :
    (∑ i ∈ Finset.range n, f (x₀ + ↑(i + 1))) ≤ ∫ x in x₀..x₀ + n, f x := by
  cases n with simp only [Nat.cast_add, Nat.cast_one, CharP.cast_eq_zero, add_zero,
      lt_self_iff_false, not_false_eq_true,
    Ioc_eq_empty, Finset.range_zero, Nat.cast_add, Nat.cast_one, Finset.sum_empty,
    intervalIntegral.integral_same, le_refl] at hf ⊢
  | succ n =>
  have : Finset.range (n + 1) = {0} ∪ Finset.Ico 1 (n + 1) := by
    ext i ; by_cases hi : i = 0 <;> simp [hi] ; omega
  simp only [this, Finset.singleton_union, Finset.mem_Ico, nonpos_iff_eq_zero, one_ne_zero,
    lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, and_true, not_false_eq_true,
    Finset.sum_insert, CharP.cast_eq_zero, zero_add, ge_iff_le]
  have l4 : IntervalIntegrable f volume x₀ (x₀ + 1) := by
    apply IntegrableOn.intervalIntegrable
    simp only [le_add_iff_nonneg_right, zero_le_one, uIcc_of_le]
    apply hfi.mono_set
    apply Icc_subset_Icc le_rfl
    simp
  have l5 x (hx : x ∈ Ioc x₀ (x₀ + 1)) : (fun x ↦ f (x₀ + 1)) x ≤ f x := by
    rcases hx with ⟨hx1, hx2⟩
    refine hf ⟨hx1, by linarith⟩ ⟨by linarith, by linarith⟩ hx2
  have l6 : ∫ x in x₀..x₀ + 1, f (x₀ + 1) = f (x₀ + 1) := by simp
  have l1 : f (x₀ + 1) ≤ ∫ x in x₀..x₀ + 1, f x := by
    rw [← l6] ; apply intervalIntegral.integral_mono_ae_restrict (by linarith) (by simp) l4
    apply eventually_of_mem _ l5
    have : (Ioc x₀ (x₀ + 1))ᶜ ∩ Icc x₀ (x₀ + 1) = {x₀} := by
      simp [← sdiff_eq_compl_inter]
    rw [mem_ae_iff, Measure.restrict_apply measurableSet_Ioc.compl, this]
    simp
  have l2 : AntitoneOn (fun x ↦ f (x₀ + x)) (Icc 1 ↑(n + 1)) := by
    intro u ⟨hu1, _⟩ v ⟨_, hv2⟩ huv ; push_cast at hv2
    refine hf ⟨?_, ?_⟩ ⟨?_, ?_⟩ ?_ <;> linarith
  have l3 := @AntitoneOn.sum_le_integral_Ico 1 (n + 1) (fun x => f (x₀ + x)) (by simp)
    (by simpa using l2)
  simp only [Nat.cast_add, Nat.cast_one, intervalIntegral.integral_comp_add_left] at l3
  rw [← intervalIntegral.integral_add_adjacent_intervals]
  · exact _root_.add_le_add l1 l3
  · exact l4
  · apply IntegrableOn.intervalIntegrable
    simp only [add_le_add_iff_left, le_add_iff_nonneg_left, Nat.cast_nonneg, uIcc_of_le]
    apply hfi.mono_set
    apply Icc_subset_Icc
    · linarith
    · simp
lemma hh_integrable_aux (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (IntegrableOn (fun t ↦ a * hh b (t / c)) (Ici 0)) ∧
    (∫ (t : ℝ) in Ioi 0, a * hh b (t / c) = a * c / b * π) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  simp only [hh]
  let g (x : ℝ) := (a * c / b) * Real.arctan (b * log (x / c))
  let g₀ (x : ℝ) := if x = 0 then ((a * c / b) * (- (π / 2))) else g x
  let g' (x : ℝ) := a * (x / c * (1 + (b * Real.log (x / c)) ^ 2))⁻¹
  have l3 (x) (hx : 0 < x) : HasDerivAt Real.log x⁻¹ x := by apply Real.hasDerivAt_log (by linarith)
  have l4 (x) : HasDerivAt (fun t => t / c) (1 / c) x := (hasDerivAt_id x).div_const c
  have l2 (x) (hx : 0 < x) : HasDerivAt (fun t => log (t / c)) x⁻¹ x := by
    have hder :
        HasDerivAt (fun t => log (t / c)) ((x / c)⁻¹ * (1 / c)) x :=
      @HasDerivAt.comp _ _ _ _ _ _ (fun t => t / c) _ _ _
        (l3 (x / c) (by positivity)) (l4 x)
    have heq : c / x * c⁻¹ = x⁻¹ := by
      field_simp [hc.ne', hx.ne']
    simpa [heq] using hder
  have l5 (x) (hx : 0 < x) := (l2 x hx).const_mul b
  have l1 (x) (hx : 0 < x) := (l5 x hx).arctan
  have l6 (x) (hx : 0 < x) : HasDerivAt g (g' x) x := by
    have hder := (l1 x hx).const_mul (a * c / b)
    have heq :
        (a * c / b) * ((1 + (b * log (x / c)) ^ 2)⁻¹ * (b * x⁻¹)) = g' x := by
      simp only [g']
      field_simp [inv_eq_one_div, hb.ne', hc.ne', hx.ne']
    simpa [g, heq] using hder
  have key (x) (hx : 0 < x) : HasDerivAt g₀ (g' x) x := by
    apply (l6 x hx).congr_of_eventuallyEq
    apply eventually_of_mem <| Ioi_mem_nhds hx
    intro y (hy : 0 < y)
    simp [g₀, hy.ne.symm]
  have k1 : Tendsto g₀ atTop (𝓝 ((a * c / b) * (π / 2))) := by
    have : g =ᶠ[atTop] g₀ := by
      apply eventually_of_mem (Ioi_mem_atTop 0)
      intro y (hy : 0 < y)
      simp [g₀, hy.ne.symm]
    apply Tendsto.congr' this
    apply Tendsto.const_mul
    apply (tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
    apply Tendsto.const_mul_atTop hb
    apply tendsto_log_atTop.comp
    apply Tendsto.atTop_div_const hc
    apply tendsto_id
  have k2 : Tendsto g₀ (𝓝[>] 0) (𝓝 (g₀ 0)) := by
    have : g =ᶠ[𝓝[>] 0] g₀ := by
      apply eventually_of_mem self_mem_nhdsWithin
      intro x (hx : 0 < x) ; simp [g₀, hx.ne.symm]
    simp only [g₀]
    apply Tendsto.congr' this
    apply Tendsto.const_mul
    apply (tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp
    apply Tendsto.const_mul_atBot hb
    apply tendsto_log_nhdsGT_zero.comp
    rw [Metric.tendsto_nhdsWithin_nhdsWithin]
    intro ε hε
    refine ⟨c * ε, by positivity, fun x hx1 hx2 => ⟨?_, ?_⟩⟩
    · simp only [mem_Ioi] at hx1 ⊢ ; positivity
    · simp only [dist_zero_right, norm_eq_abs, norm_div, abs_eq_self.mpr hc.le] at hx2 ⊢
      rwa [div_lt_iff₀ hc, mul_comm]
  have k3 : ContinuousWithinAt g₀ (Ici 0) 0 := by
    rw [Metric.continuousWithinAt_iff]
    rw [Metric.tendsto_nhdsWithin_nhds] at k2
    peel k2 with ε hε δ hδ x h
    intro (hx : 0 ≤ x)
    have := le_iff_lt_or_eq.mp hx
    cases this with
    | inl hx => exact h hx
    | inr hx => simp [g₀, hx.symm, hε]
  have k4 : ∀ x ∈ Ioi 0, 0 ≤ g' x := by
    intro x (hx : 0 < x) ; simp only [mul_inv_rev, inv_div, g'] ; positivity
  constructor
  · convert_to IntegrableOn g' _
    exact integrableOn_Ioi_deriv_of_nonneg k3 key k4 k1
  · have := integral_Ioi_of_hasDerivAt_of_nonneg k3 key k4 k1
    simp only [mul_inv_rev, inv_div, mul_neg, ↓reduceIte, sub_neg_eq_add, g', g₀] at this ⊢
    convert this using 1 ; field_simp ; ring
lemma hh_integrable (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    IntegrableOn (fun t ↦ a * hh b (t / c)) (Ici 0) :=
  hh_integrable_aux ha hb hc |>.1
lemma hh_integral (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∫ (t : ℝ) in Ioi 0, a * hh b (t / c) = a * c / b * π :=
  hh_integrable_aux ha hb hc |>.2
lemma hh_integral' : ∫ t in Ioi 0, hh (1 / (2 * π)) t = 2 * π ^ 2 := by
  have := hh_integral (a := 1) (b := 1 / (2 * π)) (c := 1)
    (by positivity) (by positivity) (by positivity)
  convert this using 1 <;> simp ; ring
lemma bound_sum_log {C : ℝ} (hf0 : f 0 = 0) (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤
      C * (1 + ∫ t in Ioi 0, hh (1 / (2 * π)) t) := by
  let ggg (i : ℕ) : ℝ := if i = 0 then 1 else gg x i
  have l0 : x ≠ 0 := by linarith
  have l1 i : 0 ≤ ggg i := by by_cases hi : i = 0 <;> simp only [gg, one_div, mul_inv_rev, hi,
    ↓reduceIte, zero_le_one, ggg] ; positivity
  have l2 : Antitone ggg := by
    intro i j hij ; by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp only [hj, ↓reduceIte, hi,
      le_refl, ggg]
    · exact gg_le_one _
    · omega
    · simp only [gg_of_hh l0]
      gcongr
      apply hh_antitone one_div_two_pi_mem_Ioo
      · simp only [mem_Ioi] ; positivity
      · simp only [mem_Ioi] ; positivity
      · gcongr
  have l3 : 0 ≤ C := by simpa [cumsum, hf0] using hf 1
  have l4 : 0 ≤ ∫ (t : ℝ) in Ioi 0, hh (π⁻¹ * 2⁻¹) t :=
    setIntegral_nonneg measurableSet_Ioi (fun x hx => hh_nonneg _ (LT.lt.le hx))
  have l5 {n : ℕ} : AntitoneOn (fun t ↦ x⁻¹ * hh (1 / (2 * π)) (t / x)) (Ioc 0 n) := by
    intro u ⟨hu1, _⟩ v ⟨hv1, _⟩ huv
    simp only
    apply mul_le_mul le_rfl ?_ (hh_nonneg _ (by positivity)) (by positivity)
    apply hh_antitone one_div_two_pi_mem_Ioo (by simp only [mem_Ioi] ; positivity)
      (by simp only [mem_Ioi] ; positivity)
    apply (div_le_div_iff_of_pos_right (by positivity)).mpr huv
  have l6 {n : ℕ} : IntegrableOn (fun t ↦ x⁻¹ * hh (π⁻¹ * 2⁻¹) (t / x)) (Icc 0 n) volume := by
    apply IntegrableOn.mono_set
      (hh_integrable (by positivity) (by positivity) (by positivity)) Icc_subset_Ici_self
  apply Real.tsum_le_of_sum_range_le (fun n => by positivity) ; intro n
  convert_to ∑ i ∈ Finset.range n, ‖f i‖ * ggg i ≤ _
  · congr ; ext i
    by_cases hi : i = 0
    · simp [hi, hf0]
    · simp only [gg, hi, ↓reduceIte, ggg]
      field_simp
  refine (cancel_main' (fun _ => norm_nonneg _) (by simp [hf0]) l1 hf l2 n).trans ?_
  apply mul_le_mul_of_nonneg_left ?_ l3
  simp only [cumsum, gg_of_hh l0, one_div, mul_inv_rev, ggg]
  by_cases hn : n = 0
  · simp only [hn, Finset.range_zero, Finset.sum_empty] ; positivity
  replace hn : 0 < n := by omega
  have : Finset.range n = {0} ∪ Finset.Ico 1 n := by
    ext i ; simp ; by_cases hi : i = 0 <;> simp [hi, hn] ; omega
  simp only [this, Finset.singleton_union, Finset.mem_Ico, nonpos_iff_eq_zero, one_ne_zero,
    false_and, not_false_eq_true, Finset.sum_insert, ↓reduceIte, add_le_add_iff_left, ge_iff_le]
  have hsum_ico :
      (∑ x_1 ∈ Finset.Ico 1 n,
          if x_1 = 0 then 1 else x⁻¹ * hh (π⁻¹ * 2⁻¹) (↑x_1 / x)) =
        ∑ x_1 ∈ Finset.Ico 1 n, x⁻¹ * hh (π⁻¹ * 2⁻¹) (↑x_1 / x) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_Ico] at hi
    have : i ≠ 0 := by omega
    simp [this]
  rw [hsum_ico]
  simp_rw [Finset.sum_Ico_eq_sum_range, add_comm 1]
  have := @sum_le_integral 0 (fun t => x⁻¹ * hh (π⁻¹ * 2⁻¹) (t / x)) (n - 1)
    (by simpa using l5) (by simpa using l6)
  simp only [zero_add] at this
  apply this.trans
  rw [@intervalIntegral.integral_comp_div ℝ _ _ 0 ↑(n - 1) x (fun t => x⁻¹ * hh (π⁻¹ * 2⁻¹) (t)) l0]
  simp only [zero_div, intervalIntegral.integral_const_mul, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ l0, one_mul]
  have : (0 : ℝ) ≤ ↑(n - 1) / x := by positivity
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  simp only [this, ↓reduceIte, uIoc_of_le, smul_eq_mul, one_mul, ge_iff_le]
  apply integral_mono_measure
  · apply Measure.restrict_mono Ioc_subset_Ioi_self le_rfl
  · apply eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi)
    intro x (hx : 0 < x)
    apply hh_nonneg _ hx.le
  · have := (@hh_integrable 1 (1 / (2 * π)) 1 (by positivity) (by positivity) (by positivity))
    simpa [one_div, mul_inv_rev] using (this.mono_set Ioi_subset_Ici_self).integrable
lemma bound_sum_log0 {C : ℝ} (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤
      C * (1 + ∫ t in Ioi 0, hh (1 / (2 * π)) t) := by
  let f0 i := if i = 0 then 0 else f i
  have l1 : chebyWith C f0 := by
    intro n ; refine Finset.sum_le_sum (fun i _ => ?_) |>.trans (hf n)
    by_cases hi : i = 0 <;> simp [hi, f0]
  have l2 i : ‖f i‖ / i = ‖f0 i‖ / i := by by_cases hi : i = 0 <;> simp [hi, f0]
  simp_rw [l2] ; apply bound_sum_log rfl l1 hx
lemma bound_sum_log' {C : ℝ} (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤ C * (1 + 2 * π ^ 2) := by
  simpa only [hh_integral'] using bound_sum_log0 hf hx
variable (f x) in
lemma summable_fourier_aux (ψ : W21) (i : ℕ) :
    ‖f i / i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (i / x))‖ ≤
      W21.norm ψ * (‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹) := by
  calc
    ‖f i / i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (i / x))‖
        = ‖f i / i‖ * ‖𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (i / x))‖ := by
          rw [norm_mul]
    _ ≤ ‖f i / i‖ * (W21.norm ψ * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left (decay_bounds_key ψ (1 / (2 * π) * log (i / x)))
            (norm_nonneg (f i / i))
    _ = W21.norm ψ * (‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹) := by
          simp only [Complex.norm_div, RCLike.norm_natCast]
          ring
lemma summable_fourier (x : ℝ) (hx : 0 < x) (ψ : W21) (hcheby : cheby f) :
    Summable fun i ↦ ‖f i / ↑i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑i / x))‖ := by
  have l5 : Summable fun i ↦ ‖f i‖ / ↑i * ((1 + (1 / (2 * ↑π) * ↑(Real.log (↑i / x))) ^ 2)⁻¹) := by
    simpa using limiting_fourier_lim1_aux hcheby hx 1 (zero_le_one' ℝ)
  have l6 := summable_fourier_aux x f ψ
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) l6
    (by simpa using l5.const_smul (W21.norm ψ))
lemma bound_I1 (x : ℝ) (hx : 0 < x) (ψ : W21) (hcheby : cheby f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))‖ ≤
    W21.norm ψ • ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ := by
  have l5 : Summable fun i ↦ ‖f i‖ / ↑i * ((1 + (1 / (2 * ↑π) * ↑(Real.log (↑i / x))) ^ 2)⁻¹) := by
    simpa using limiting_fourier_lim1_aux hcheby hx 1 (zero_le_one' ℝ)
  have l6 := summable_fourier_aux x f ψ
  have l1 : Summable fun i ↦ ‖f i / ↑i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑i / x))‖ := by
    exact summable_fourier x hx ψ hcheby
  apply (norm_tsum_le_tsum_norm l1).trans
  calc
    (∑' (i : ℕ), ‖f i / ↑i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑i / x))‖)
        ≤ ∑' (i : ℕ),
            W21.norm ψ * (‖f i‖ / ↑i * (1 + (1 / (2 * π) * Real.log (↑i / x)) ^ 2)⁻¹) :=
          Summable.tsum_mono l1 (by simpa [smul_eq_mul] using l5.const_smul (W21.norm ψ)) l6
    _ = W21.norm ψ *
          ∑' (i : ℕ), ‖f i‖ / ↑i * (1 + (1 / (2 * π) * Real.log (↑i / x)) ^ 2)⁻¹ := by
          simpa [smul_eq_mul] using Summable.tsum_const_smul (W21.norm ψ) l5
lemma bound_I1' {C : ℝ} (x : ℝ) (hx : 1 ≤ x) (ψ : W21) (hcheby : chebyWith C f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))‖ ≤
      W21.norm ψ * C * (1 + 2 * π ^ 2) := by
  apply bound_I1 x (by linarith) ψ ⟨_, hcheby⟩ |>.trans
  rw [smul_eq_mul, mul_assoc]
  apply mul_le_mul le_rfl (bound_sum_log' hcheby hx) ?_ W21.norm_nonneg
  apply tsum_nonneg (fun i => by positivity)
lemma bound_I2 (x : ℝ) (ψ : W21) :
    ‖∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))‖ ≤ W21.norm ψ * (2 * π ^ 2) := by
  have key a : ‖𝓕 (ψ : ℝ → ℂ) (a / (2 * π))‖ ≤ W21.norm ψ * (1 + (a / (2 * π)) ^ 2)⁻¹ :=
    decay_bounds_key ψ _
  have twopi : 0 ≤ 2 * π := by simp [pi_nonneg]
  have l3 : Integrable (fun a ↦ (1 + (a / (2 * π)) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_div (by norm_num [pi_ne_zero])
  have l2 : IntegrableOn (fun i ↦ W21.norm ψ * (1 + (i / (2 * π)) ^ 2)⁻¹) (Ici (-Real.log x)) := by
    exact (l3.const_mul _).integrableOn
  have l1 : IntegrableOn (fun i ↦ ‖𝓕 (ψ : ℝ → ℂ) (i / (2 * π))‖) (Ici (-Real.log x)) := by
    refine ((l3.const_mul (W21.norm ψ)).mono' ?_ ?_).integrableOn
    · exact ((continuous_FourierIntegral ψ).comp (continuous_id.div_const _)).norm.aestronglyMeasurable
    · simp only [norm_norm, key] ; simp
  have l5 : 0 ≤ᵐ[volume] fun a ↦ (1 + (a / (2 * π)) ^ 2)⁻¹ := by
    apply Eventually.of_forall ; intro x ; positivity
  refine (norm_integral_le_integral_norm _).trans <| (setIntegral_mono l1 l2 key).trans ?_
  rw [integral_const_mul] ; gcongr
  · apply W21.norm_nonneg
  refine (setIntegral_le_integral l3 l5).trans ?_
  rw [Measure.integral_comp_div (fun x => (1 + x ^ 2)⁻¹) (2 * π)]
  simp [abs_eq_self.mpr twopi] ; ring_nf ; rfl
lemma bound_main {C : ℝ} (A : ℂ) (x : ℝ) (hx : 1 ≤ x) (ψ : W21)
    (hcheby : chebyWith C f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))‖ ≤
      W21.norm ψ * (C * (1 + 2 * π ^ 2) + ‖A‖ * (2 * π ^ 2)) := by
  have l1 := bound_I1' x hx ψ hcheby
  have l2 := mul_le_mul (le_refl ‖A‖) (bound_I2 x ψ) (by positivity) (by positivity)
  apply norm_sub_le _ _ |>.trans ; rw [norm_mul]
  convert _root_.add_le_add l1 l2 using 1 ; ring
lemma limiting_cor_W21 (ψ : W21) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) := by
  let S1 x (ψ : ℝ → ℂ) := ∑' (n : ℕ), f n / ↑n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑n / x))
  let S2 x (ψ : ℝ → ℂ) := ↑A * ∫ (u : ℝ) in Ici (-Real.log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))
  let S x ψ := S1 x ψ - S2 x ψ ; change Tendsto (fun x ↦ S x ψ) atTop (𝓝 0)
  obtain g := exists_trunc
  let Ψ R := g.scale R * ψ
  have key R : Tendsto (fun x ↦ S x (Ψ R)) atTop (𝓝 0) := limiting_cor (Ψ R) hf hcheby hG hG'
  obtain ⟨C, hcheby⟩ := hcheby
  have hC : 0 ≤ C := by
    have : ‖f 0‖ ≤ C := by simpa [cumsum] using hcheby 1
    have : 0 ≤ ‖f 0‖ := by positivity
    linarith
  have key2 : Tendsto (fun R ↦ W21.norm (ψ - Ψ R)) atTop (𝓝 0) := W21_approximation ψ g
  simp_rw [Metric.tendsto_nhds] at key key2 ⊢ ; intro ε hε
  let M := C * (1 + 2 * π ^ 2) + ‖(A : ℂ)‖ * (2 * π ^ 2)
  obtain ⟨R, hRψ⟩ := (key2 ((ε / 2) / (1 + M)) (by positivity)).exists
  simp only [dist_zero_right, Real.norm_eq_abs, abs_eq_self.mpr W21.norm_nonneg] at hRψ key
  filter_upwards [eventually_ge_atTop 1, key R (ε / 2) (by positivity)] with x hx key
  have key3 : ‖S x (ψ - Ψ R)‖ < ε / 2 := by
    change ‖S x (ψ - W21.ofCS2 (Ψ R)).toFun‖ < ε / 2
    have : 0 < 1 + M := by positivity
    have hbound :
        ‖S x (ψ - W21.ofCS2 (Ψ R)).toFun‖ ≤
          W21.norm (ψ - W21.ofCS2 (Ψ R)).toFun * M := by
      simpa [S, S1, S2, M] using @bound_main f C A x hx (ψ - Ψ R) hcheby
    apply hbound.trans_lt
    have hnorm :
        W21.norm (ψ - W21.ofCS2 (Ψ R)).toFun = W21.norm (ψ.toFun - (Ψ R).toFun) := by
      simp [W21.ofCS2]
    rw [hnorm]
    have hMle : M ≤ 1 + M := by linarith
    apply (mul_le_mul_of_nonneg_left hMle W21.norm_nonneg).trans_lt
    calc
      W21.norm (ψ.toFun - (Ψ R).toFun) * (1 + M)
          < (ε / 2 / (1 + M)) * (1 + M) := mul_lt_mul_of_pos_right hRψ this
      _ = ε / 2 := by field_simp [this.ne']
  have S1_sub_1 x : 𝓕 (⇑ψ - ⇑(Ψ R)) x = 𝓕 (ψ : ℝ → ℂ) x - 𝓕 ⇑(Ψ R) x := by
    have l1 : AEStronglyMeasurable (fun x_1 : ℝ ↦ cexp (-(2 * ↑π * (↑x_1 * ↑x) * I))) volume := by
      refine (Continuous.mul ?_ continuous_const).neg.cexp.aestronglyMeasurable
      apply continuous_const.mul <| contDiff_ofReal.continuous.mul continuous_const
    simp only [Real.fourier_eq', neg_mul, RCLike.inner_apply', conj_trivial, ofReal_neg,
      ofReal_mul, ofReal_ofNat, Pi.sub_apply, smul_eq_mul, mul_sub]
    apply integral_sub
    · apply ψ.hf.bdd_mul (c := 1) l1 ; simp [Complex.norm_exp]
    · apply (Ψ R : W21) |>.hf |>.bdd_mul (c := 1) l1
      simp [Complex.norm_exp]
  have S1_sub : S1 x (ψ - Ψ R) = S1 x ψ - S1 x (Ψ R) := by
    simp only [one_div, mul_inv_rev, S1_sub_1, mul_sub, S1] ; apply Summable.tsum_sub
    · have := summable_fourier x (by positivity) ψ ⟨_, hcheby⟩
      rw [summable_norm_iff] at this
      simpa using this
    · have := summable_fourier x (by positivity) (Ψ R) ⟨_, hcheby⟩
      rw [summable_norm_iff] at this
      simpa using this
  have S2_sub : S2 x (ψ - Ψ R) = S2 x ψ - S2 x (Ψ R) := by
    simp only [S1_sub_1, S2] ; rw [integral_sub]
    · ring
    · exact ψ.integrable_fourier (by positivity) |>.restrict
    · exact (Ψ R : W21).integrable_fourier (by positivity) |>.restrict
  have S_sub : S x (ψ - Ψ R) = S x ψ - S x (Ψ R) := by simp [S, S1_sub, S2_sub] ; ring
  simpa [S_sub, Ψ] using norm_add_le _ _ |>.trans_lt (_root_.add_lt_add key3 key)
lemma limiting_cor_schwartz (ψ : 𝓢(ℝ, ℂ)) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) :=
  limiting_cor_W21 ψ hf hcheby hG hG'
lemma fourier_surjection_on_schwartz (f : 𝓢(ℝ, ℂ)) : ∃ g : 𝓢(ℝ, ℂ), 𝓕 g = f := by
  refine ⟨𝓕⁻ f, ?_⟩
  exact FourierTransform.fourier_fourierInv_eq f
noncomputable def toSchwartz (f : ℝ → ℂ) (h1 : ContDiff ℝ ∞ f)
    (h2 : HasCompactSupport f) : 𝓢(ℝ, ℂ) where
  toFun := f
  smooth' := h1
  decay' k n := by
    have l1 : Continuous (fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) := by
      have : ContDiff ℝ ∞ (iteratedFDeriv ℝ n f) := h1.iteratedFDeriv_right (mod_cast le_top)
      exact Continuous.mul (by continuity) this.continuous.norm
    have l2 : HasCompactSupport (fun x ↦ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) :=
      (h2.iteratedFDeriv _).norm.mul_left
    simpa using l1.bounded_above_of_compact_support l2
@[simp] lemma toSchwartz_apply (f : ℝ → ℂ) {h1 h2 x} : SchwartzMap.mk f h1 h2 x = f x := rfl
lemma comp_exp_support0 {Ψ : ℝ → ℂ} (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    ∀ᶠ x in 𝓝 0, Ψ x = 0 :=
  notMem_tsupport_iff_eventuallyEq.mp (fun h => lt_irrefl 0 <| mem_Ioi.mp (hplus h))
lemma comp_exp_support1 {Ψ : ℝ → ℂ} (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    ∀ᶠ x in atBot, Ψ (exp x) = 0 :=
  Real.tendsto_exp_atBot <| comp_exp_support0 hplus
lemma comp_exp_support2 {Ψ : ℝ → ℂ} (hsupp : HasCompactSupport Ψ) :
    ∀ᶠ (x : ℝ) in atTop, (Ψ ∘ rexp) x = 0 := by
  simp only [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact,
    cocompact_eq_atBot_atTop] at hsupp
  exact Real.tendsto_exp_atTop hsupp.2
theorem comp_exp_support {Ψ : ℝ → ℂ} (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) : HasCompactSupport (Ψ ∘ rexp) := by
  simp only [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact,
    cocompact_eq_atBot_atTop]
  exact ⟨comp_exp_support1 hplus, comp_exp_support2 hsupp⟩
lemma wiener_ikehara_smooth_aux (l0 : Continuous Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) (x : ℝ) (hx : 0 < x) :
    ∫ (u : ℝ) in Ioi (-Real.log x), ↑(rexp u) * Ψ (rexp u) = ∫ (y : ℝ) in Ioi (1 / x), Ψ y := by
  have l1 : ContinuousOn rexp (Ici (-Real.log x)) := by fun_prop
  have l2 : Tendsto rexp atTop atTop := Real.tendsto_exp_atTop
  have l3 t (_ : t ∈ Ioi (-log x)) : HasDerivWithinAt rexp (rexp t) (Ioi t) t :=
    (Real.hasDerivAt_exp t).hasDerivWithinAt
  have l4 : ContinuousOn Ψ (rexp '' Ioi (-Real.log x)) := by fun_prop
  have l5 : IntegrableOn Ψ (rexp '' Ici (-Real.log x)) volume :=
    (l0.integrable_of_hasCompactSupport hsupp).integrableOn
  have l6 : IntegrableOn (fun x ↦ rexp x • (Ψ ∘ rexp) x) (Ici (-Real.log x)) volume := by
    refine (Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_).integrableOn
    change HasCompactSupport (rexp • (Ψ ∘ rexp))
    exact (comp_exp_support hsupp hplus).smul_left
  have := MeasureTheory.integral_deriv_smul_comp_Ioi l1 l2 l3 l4 l5 l6
  simpa [Real.exp_neg, Real.exp_log hx] using this
theorem wiener_ikehara_smooth_sub (h1 : Integrable Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    Tendsto (fun x ↦ (↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y) - ↑A * ∫ (y : ℝ) in Ioi 0, Ψ y)
      atTop (𝓝 0) := by
  obtain ⟨ε, hε, hh⟩ := Metric.eventually_nhds_iff.mp <| comp_exp_support0 hplus
  apply tendsto_nhds_of_eventually_eq ; filter_upwards [eventually_gt_atTop ε⁻¹] with x hxε
  have l1 : Integrable (indicator (Ioi x⁻¹) (fun x : ℝ => Ψ x)) := h1.indicator measurableSet_Ioi
  have l2 : Integrable (indicator (Ioi 0) (fun x : ℝ => Ψ x)) := h1.indicator measurableSet_Ioi
  simp_rw [← MeasureTheory.integral_indicator measurableSet_Ioi, ← mul_sub, ← integral_sub l1 l2]
  simp only [mul_eq_zero, ofReal_eq_zero]
  right
  apply MeasureTheory.integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro t
  simp only [Pi.zero_apply]
  have hε' : 0 < ε⁻¹ := by positivity
  have hx : 0 < x := by linarith
  have hx' : 0 < x⁻¹ := by positivity
  have hεx : x⁻¹ < ε := (inv_lt_comm₀ hε hx).mp hxε
  have l3 : Ioi 0 = Ioc 0 x⁻¹ ∪ Ioi x⁻¹ := by
    ext t ; simp only [mem_Ioi, mem_union, mem_Ioc] ; constructor <;> intro h
    · simp [h, le_or_gt]
    · cases h with
      | inl h => exact h.1
      | inr h => exact hx'.trans h
  have l4 : Disjoint (Ioc 0 x⁻¹) (Ioi x⁻¹) := by simp
  have l5 := Set.indicator_union_of_disjoint l4 Ψ
  rw [l3, l5]
  simp only
  rw [add_comm, sub_add_cancel_left]
  by_cases ht : t ∈ Ioc 0 x⁻¹
  · simp only [ht, indicator_of_mem, neg_eq_zero]
    apply hh ; simp only [mem_Ioc, dist_zero_right, norm_eq_abs] at ht ⊢
    apply hεx.trans_le'
    rw [abs_le] ; constructor <;> linarith
  simp [ht]
lemma wiener_ikehara_smooth (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x - A * ∫ y in Set.Ioi 0, Ψ y)
      atTop (𝓝 0) := by
  let h (x : ℝ) : ℂ := rexp (2 * π * x) * Ψ (exp (2 * π * x))
  have h1 : ContDiff ℝ ∞ h := by
    have : ContDiff ℝ ∞ (fun x : ℝ => (rexp (2 * π * x))) := (contDiff_const.mul contDiff_id).exp
    exact (contDiff_ofReal.comp this).mul (hsmooth.comp this)
  have h2 : HasCompactSupport h := by
    have : 2 * π ≠ 0 := by simp [pi_ne_zero]
    have hprod : HasCompactSupport
        (((fun x : ℝ => cexp (2 * ↑π * ↑x)) * fun x => Ψ (rexp (2 * π * x)))) :=
      (comp_exp_support hsupp hplus).comp_smul this |>.mul_left
    rw [hasCompactSupport_iff_eventuallyEq] at hprod ⊢
    exact hprod.mono fun x hx => by
      simpa [h, Pi.mul_apply] using hx
  obtain ⟨g, hg⟩ := fourier_surjection_on_schwartz (toSchwartz h h1 h2)
  have l1 {y} (hy : 0 < y) : y * Ψ y = 𝓕 g (1 / (2 * π) * Real.log y) := by
    simp only [one_div, mul_inv_rev, hg, toSchwartz, ofReal_exp, ofReal_mul, ofReal_ofNat,
      toSchwartz_apply, ofReal_inv, h]
    field_simp
    norm_cast
    rw [Real.exp_log hy]
  have key := limiting_cor_schwartz g hf hcheby hG hG'
  have l2 : ∀ᶠ x in atTop, ∑' (n : ℕ), f n / ↑n * 𝓕 g (1 / (2 * π) * Real.log (↑n / x)) =
      ∑' (n : ℕ), f n * Ψ (↑n / x) / x := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    congr ; ext n
    by_cases hn : n = 0
    · simp [hn, (comp_exp_support0 hplus).self_of_nhds]
    rw [← l1 (by positivity)]
    have : (n : ℂ) ≠ 0 := by simpa using hn
    have : (x : ℂ) ≠ 0 := by simpa using hx.ne.symm
    simp only [ofReal_div, ofReal_natCast]
    field_simp
  have l3 : ∀ᶠ x in atTop, ↑A * ∫ (u : ℝ) in Ici (-Real.log x), 𝓕 g (u / (2 * π)) =
      ↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    congr 1
    simp only [hg, toSchwartz, ofReal_exp, ofReal_mul, ofReal_ofNat, toSchwartz_apply,
      ofReal_div, h]
    norm_cast ; field_simp; norm_cast
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    exact wiener_ikehara_smooth_aux hsmooth.continuous hsupp hplus x hx
  have l4 : Tendsto (fun x => (↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y) - ↑A * ∫ (y : ℝ) in Ioi 0, Ψ y)
      atTop (𝓝 0) := by
    exact wiener_ikehara_smooth_sub (hsmooth.continuous.integrable_of_hasCompactSupport hsupp) hplus
  simpa [tsum_div_const] using (key.congr' <| EventuallyEq.sub l2 l3) |>.add l4
lemma wiener_ikehara_smooth' (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x) atTop (nhds (A * ∫ y in Set.Ioi 0, Ψ y)) :=
  tendsto_sub_nhds_zero_iff.mp <| wiener_ikehara_smooth hf hcheby hG hG' hsmooth hsupp hplus
local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩
lemma wiener_ikehara_smooth_real {f : ℕ → ℝ} {Ψ : ℝ → ℝ}
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x) atTop (nhds (A * ∫ y in Set.Ioi 0, Ψ y)) := by
  let Ψ' := ofReal ∘ Ψ
  have l1 : ContDiff ℝ ∞ Ψ' := contDiff_ofReal.comp hsmooth
  have l2 : HasCompactSupport Ψ' := hsupp.comp_left rfl
  have l3 : closure (Function.support Ψ') ⊆ Ioi 0 := by rwa [Function.support_comp_eq] ; simp
  have key := (continuous_re.tendsto _).comp
    (@wiener_ikehara_smooth' A Ψ G f hf hcheby hG hG' l1 l2 l3)
  simp at key ; norm_cast at key
lemma interval_approx_inf (ha : 0 < a) (hab : a < b) :
    ∀ᶠ ε in 𝓝[>] 0, ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      closure (Function.support ψ) ⊆ Set.Ioi 0 ∧
        ψ ≤ indicator (Ico a b) 1 ∧ b - a - ε ≤ ∫ y in Ioi 0, ψ y := by
  have l1 : Iio ((b - a) / 3) ∈ 𝓝[>] 0 := nhdsWithin_le_nhds <| Iio_mem_nhds <| by
    rw [← sub_pos] at hab
    positivity
  filter_upwards [self_mem_nhdsWithin, l1] with ε (hε : 0 < ε) (hε' : ε < (b - a) / 3)
  have l2 : a < a + ε / 2 := by simp [hε]
  have l3 : b - ε / 2 < b := by simp [hε]
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := smooth_urysohn_support_Ioo l2 l3
  refine ⟨ψ, h1, h2, ?_, ?_, ?_⟩
  · simp [h5, hab.ne, Icc_subset_Ioi_iff hab.le, ha]
  · exact h4.trans <| indicator_le_indicator_of_subset Ioo_subset_Ico_self (by simp)
  · have l4 : 0 ≤ b - a - ε := by linarith
    have l5 : Icc (a + ε / 2) (b - ε / 2) ⊆ Ioi 0 := by
      intro t ht
      simp only [mem_Icc, mem_Ioi] at ht ⊢
      exact ha.trans <| l2.trans_le <| ht.1
    have l6 : Icc (a + ε / 2) (b - ε / 2) ∩ Ioi 0 = Icc (a + ε / 2) (b - ε / 2) :=
      inter_eq_left.mpr l5
    have l7 : ∫ y in Ioi 0, indicator (Icc (a + ε / 2) (b - ε / 2)) 1 y = b - a - ε := by
      simp only [measurableSet_Icc, integral_indicator_one, measureReal_restrict_apply, l6,
        volume_real_Icc]
      convert max_eq_left l4 using 1 ; ring_nf
    have l8 : IntegrableOn ψ (Ioi 0) volume :=
      (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    rw [← l7] ; apply setIntegral_mono ?_ l8 h3
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Icc]
    apply IntegrableOn.mono ?_ subset_rfl Measure.restrict_le_self
    apply integrableOn_const <;>
    simp
lemma interval_approx_sup (ha : 0 < a) (hab : a < b) :
    ∀ᶠ ε in 𝓝[>] 0, ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      closure (Function.support ψ) ⊆ Set.Ioi 0 ∧
        indicator (Ico a b) 1 ≤ ψ ∧ ∫ y in Ioi 0, ψ y ≤ b - a + ε := by
  have l1 : Iio (a / 2) ∈ 𝓝[>] 0 := nhdsWithin_le_nhds <| Iio_mem_nhds (by linarith)
  filter_upwards [self_mem_nhdsWithin, l1] with ε (hε : 0 < ε) (hε' : ε < a / 2)
  have l2 : a - ε / 2 < a := by linarith
  have l3 : b < b + ε / 2 := by linarith
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := smooth_urysohn_support_Ioo l2 l3
  refine ⟨ψ, h1, h2, ?_, ?_, ?_⟩
  · have l4 : a - ε / 2 < b + ε / 2 := by linarith
    have l5 : ε / 2 < a := by linarith
    simp [h5, l4.ne, Icc_subset_Ioi_iff l4.le, l5]
  · apply le_trans ?_ h3
    apply indicator_le_indicator_of_subset Ico_subset_Icc_self (by simp)
  · have l4 : 0 ≤ b - a + ε := by linarith
    have l5 : Ioo (a - ε / 2) (b + ε / 2) ⊆ Ioi 0 := by intro t ht ; simp at ht ⊢ ; linarith
    have l6 : Ioo (a - ε / 2) (b + ε / 2) ∩ Ioi 0 = Ioo (a - ε / 2) (b + ε / 2) := inter_eq_left.mpr l5
    have l7 : ∫ y in Ioi 0, indicator (Ioo (a - ε / 2) (b + ε / 2)) 1 y = b - a + ε := by
      simp only [measurableSet_Ioo, integral_indicator_one, measureReal_restrict_apply, l6,
        volume_real_Ioo]
      convert max_eq_left l4 using 1 ; ring_nf
    have l8 : IntegrableOn ψ (Ioi 0) volume := (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    rw [← l7]
    refine setIntegral_mono l8 ?_ h4
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioo]
    apply IntegrableOn.mono ?_ subset_rfl Measure.restrict_le_self
    apply integrableOn_const <;>
    simp
lemma WI_summable {f : ℕ → ℝ} {g : ℝ → ℝ} (hg : HasCompactSupport g) (hx : 0 < x) :
    Summable (fun n => f n * g (n / x)) := by
  obtain ⟨M, hM⟩ := hg.bddAbove.mono subset_closure
  apply summable_of_hasFiniteSupport
  unfold Function.HasFiniteSupport
  simp only [Function.support_mul] ; apply Finite.inter_of_right ; rw [finite_iff_bddAbove]
  exact ⟨Nat.ceil (M * x), fun i hi => by simpa using Nat.ceil_mono ((div_le_iff₀ hx).mp (hM hi))⟩
lemma WI_sum_le {f : ℕ → ℝ} {g₁ g₂ : ℝ → ℝ} (hf : 0 ≤ f) (hg : g₁ ≤ g₂) (hx : 0 < x)
    (hg₁ : HasCompactSupport g₁) (hg₂ : HasCompactSupport g₂) :
    (∑' n, f n * g₁ (n / x)) / x ≤ (∑' n, f n * g₂ (n / x)) / x := by
  apply div_le_div_of_nonneg_right ?_ hx.le
  exact Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (hg _) (hf _))
    (WI_summable hg₁ hx) (WI_summable hg₂ hx)
lemma WI_sum_Iab_le {f : ℕ → ℝ} (hpos : 0 ≤ f) {C : ℝ} (hcheby : chebyWith C f) (hb : 0 < b) (hxb : 2 / b < x) :
    (∑' n, f n * indicator (Ico a b) 1 (n / x)) / x ≤ C * 2 * b := by
  have hb' : 0 < 2 / b := by positivity
  have hx : 0 < x := by linarith
  have hxb' : 2 < x * b := (div_lt_iff₀ hb).mp hxb
  have l1 (i : ℕ) (hi : i ∉ Finset.range ⌈b * x⌉₊) : f i * indicator (Ico a b) 1 (i / x) = 0 := by
    simp_all [le_div_iff₀ hx]
  have l2 (i : ℕ) (_ : i ∈ Finset.range ⌈b * x⌉₊) : f i * indicator (Ico a b) 1 (i / x) ≤ |f i| := by
    rw [abs_eq_self.mpr (hpos _)]
    convert_to _ ≤ f i * 1
    · ring
    apply mul_le_mul_of_nonneg_left ?_ (hpos _)
    by_cases hi : (i / x) ∈ (Ico a b) <;> simp [hi]
  rw [tsum_eq_sum l1, div_le_iff₀ hx, mul_assoc, mul_assoc]
  apply Finset.sum_le_sum l2 |>.trans
  have := hcheby ⌈b * x⌉₊ ; simp only [norm_real, norm_eq_abs] at this ; apply this.trans
  have : 0 ≤ C := by have := hcheby 1 ; simp only [cumsum, Finset.range_one, norm_real,
    Finset.sum_singleton, Nat.cast_one, mul_one] at this ; exact (abs_nonneg _).trans this
  refine mul_le_mul_of_nonneg_left ?_ this
  apply (Nat.ceil_lt_add_one (by positivity)).le.trans
  linarith
lemma WI_sum_Iab_le' {f : ℕ → ℝ} (hpos : 0 ≤ f) {C : ℝ} (hcheby : chebyWith C f) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, (∑' n, f n * indicator (Ico a b) 1 (n / x)) / x ≤ C * 2 * b := by
  filter_upwards [eventually_gt_atTop (2 / b)] with x hx using WI_sum_Iab_le hpos hcheby hb hx
lemma le_of_eventually_nhdsWithin {a b : ℝ} (h : ∀ᶠ c in 𝓝[>] b, a ≤ c) : a ≤ b := by
  apply le_of_forall_gt ; intro d hd
  have key : ∀ᶠ c in 𝓝[>] b, c < d := by
    apply eventually_of_mem (U := Iio d) ?_ (fun x hx => hx)
    rw [mem_nhdsWithin]
    refine ⟨Iio d, isOpen_Iio, hd, inter_subset_left⟩
  obtain ⟨x, h1, h2⟩ := (h.and key).exists
  linarith
lemma ge_of_eventually_nhdsWithin {a b : ℝ} (h : ∀ᶠ c in 𝓝[<] b, c ≤ a) : b ≤ a := by
  apply le_of_forall_lt ; intro d hd
  have key : ∀ᶠ c in 𝓝[<] b, c > d := by
    apply eventually_of_mem (U := Ioi d) ?_ (fun x hx => hx)
    rw [mem_nhdsWithin]
    refine ⟨Ioi d, isOpen_Ioi, hd, inter_subset_left⟩
  obtain ⟨x, h1, h2⟩ := (h.and key).exists
  linarith
lemma WI_tendsto_aux (a b : ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun c => c / A - (b - a)) (𝓝[>] (A * (b - a))) (𝓝[>] 0) := by
  rw [Metric.tendsto_nhdsWithin_nhdsWithin]
  intro ε hε
  refine ⟨A * ε, by positivity, ?_⟩
  intro x hx1 hx2
  constructor
  · simpa [lt_div_iff₀' hA]
  · simp only [Real.dist_eq, dist_zero_right, Real.norm_eq_abs] at hx2 ⊢
    have : |x / A - (b - a)| = |x - A * (b - a)| / A := by
      rw [← abs_eq_self.mpr hA.le, ← abs_div, abs_eq_self.mpr hA.le] ; congr ; field_simp
    rwa [this, div_lt_iff₀' hA]
lemma WI_tendsto_aux' (a b : ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun c => (b - a) - c / A) (𝓝[<] (A * (b - a))) (𝓝[>] 0) := by
  rw [Metric.tendsto_nhdsWithin_nhdsWithin]
  intro ε hε
  refine ⟨A * ε, by positivity, ?_⟩
  intro x hx1 hx2
  constructor
  · simpa [div_lt_iff₀' hA]
  · simp only [Real.dist_eq, dist_zero_right, norm_eq_abs] at hx2 ⊢
    have : |(b - a) - x / A| = |A * (b - a) - x| / A := by
      rw [← abs_eq_self.mpr hA.le, ← abs_div, abs_eq_self.mpr hA.le] ; congr ; field_simp
    rwa [this, div_lt_iff₀' hA, ← neg_sub, abs_neg]
theorem residue_nonneg {f : ℕ → ℝ} (hpos : 0 ≤ f)
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm (fun n ↦ ↑(f n)) σ')) (hcheby : cheby fun n ↦ ↑(f n))
    (hG : ContinuousOn G {s | 1 ≤ s.re}) (hG' : EqOn G (fun s ↦ LSeries (fun n ↦ ↑(f n)) s - ↑A / (s - 1)) {s | 1 < s.re}) : 0 ≤ A := by
  let S (g : ℝ → ℝ) (x : ℝ) := (∑' n, f n * g (n / x)) / x
  have hSnonneg {g : ℝ → ℝ} (hg : 0 ≤ g) : ∀ᶠ x : ℝ in atTop, 0 ≤ S g x := by
    filter_upwards [eventually_ge_atTop 0] with x hx
    exact div_nonneg (tsum_nonneg (fun i => mul_nonneg (hpos _) (hg _))) hx
  obtain ⟨ε, ψ, h1, h2, h3, h4, -⟩ := (interval_approx_sup zero_lt_one one_lt_two).exists
  have key := @wiener_ikehara_smooth_real A G f ψ hf hcheby hG hG' h1 h2 h3
  have l2 : 0 ≤ ψ := by apply le_trans _ h4 ; apply indicator_nonneg ; simp
  have l1 : ∀ᶠ x in atTop, 0 ≤ S ψ x := hSnonneg l2
  have l3 : 0 ≤ A * ∫ (y : ℝ) in Ioi 0, ψ y := ge_of_tendsto key l1
  have l4 : 0 < ∫ (y : ℝ) in Ioi 0, ψ y := by
    have r1 : 0 ≤ᵐ[Measure.restrict volume (Ioi 0)] ψ := Eventually.of_forall l2
    have r2 : IntegrableOn (fun y ↦ ψ y) (Ioi 0) volume :=
      (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    have r3 : Ico 1 2 ⊆ Function.support ψ := by intro x hx ; have := h4 x ; simp [hx] at this ⊢ ; linarith
    have r4 : Ico 1 2 ⊆ Function.support ψ ∩ Ioi 0 := by
      simp only [subset_inter_iff, r3, true_and] ; apply Ico_subset_Icc_self.trans ; rw [Icc_subset_Ioi_iff] <;> linarith
    have r5 : 1 ≤ volume (Function.support ψ ∩ Ioi 0) := by
      calc
        (1 : ENNReal) = volume (Ico (1 : ℝ) 2) := by
          simp [Real.volume_Ico]
          norm_num
        _ ≤ volume (Function.support ψ ∩ Ioi 0) := volume.mono r4
    simpa [setIntegral_pos_iff_support_of_nonneg_ae r1 r2] using zero_lt_one.trans_le r5
  have := div_nonneg l3 l4.le ; field_simp at this ; exact this
lemma WienerIkeharaInterval {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * (indicator (Ico a b) 1 (n / x))) / x) atTop (nhds (A * (b - a))) := by
  by_cases hab : a = b
  · simp [hab]
  replace hb : a < b := lt_of_le_of_ne hb hab ; clear hab
  let S (g : ℝ → ℝ) (x : ℝ) :=  (∑' n, f n * g (n / x)) / x
  have hSnonneg {g : ℝ → ℝ} (hg : 0 ≤ g) : ∀ᶠ x : ℝ in atTop, 0 ≤ S g x := by
    filter_upwards [eventually_ge_atTop 0] with x hx
    refine div_nonneg ?_ hx
    refine tsum_nonneg (fun i => mul_nonneg (hpos _) (hg _))
  have hA : 0 ≤ A := residue_nonneg hpos hf hcheby hG hG'
  let Iab : ℝ → ℝ := indicator (Ico a b) 1
  change Tendsto (S Iab) atTop (𝓝 (A * (b - a)))
  have hIab : HasCompactSupport Iab := by simpa [Iab, HasCompactSupport, tsupport, hb.ne] using isCompact_Icc
  have Iab_nonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ S Iab x := hSnonneg (indicator_nonneg (by simp))
  have Iab2 : IsBoundedUnder (· ≤ ·) atTop (S Iab) := by
    obtain ⟨C, hC⟩ := hcheby ; exact ⟨C * 2 * b, WI_sum_Iab_le' hpos hC (by linarith)⟩
  have Iab3 : IsBoundedUnder (· ≥ ·) atTop (S Iab) := ⟨0, Iab_nonneg⟩
  have Iab0 : IsCoboundedUnder (· ≥ ·) atTop (S Iab) := Iab2.isCoboundedUnder_ge
  have Iab1 : IsCoboundedUnder (· ≤ ·) atTop (S Iab) := Iab3.isCoboundedUnder_le
  have sup_le : limsup (S Iab) atTop ≤ A * (b - a) := by
    have l_sup : ∀ᶠ ε in 𝓝[>] 0, limsup (S Iab) atTop ≤ A * (b - a + ε) := by
      filter_upwards [interval_approx_sup ha hb] with ε ⟨ψ, h1, h2, h3, h4, h6⟩
      have l1 : Tendsto (S ψ) atTop _ := wiener_ikehara_smooth_real hf hcheby hG hG' h1 h2 h3
      have l6 : S Iab ≤ᶠ[atTop] S ψ := by
        filter_upwards [eventually_gt_atTop 0] with x hx using WI_sum_le hpos h4 hx hIab h2
      have l5 : IsBoundedUnder (· ≤ ·) atTop (S ψ) := l1.isBoundedUnder_le
      have l3 : limsup (S Iab) atTop ≤ limsup (S ψ) atTop := limsup_le_limsup l6 Iab1 l5
      apply l3.trans ; rw [l1.limsup_eq] ; gcongr
    obtain rfl | h := eq_or_ne A 0
    · simpa using l_sup
    apply le_of_eventually_nhdsWithin
    have key : 0 < A := lt_of_le_of_ne hA h.symm
    filter_upwards [WI_tendsto_aux a b key l_sup] with x hx
    simpa [mul_div_cancel₀ _ h] using hx
  have le_inf : A * (b - a) ≤ liminf (S Iab) atTop := by
    have l_inf : ∀ᶠ ε in 𝓝[>] 0, A * (b - a - ε) ≤ liminf (S Iab) atTop := by
      filter_upwards [interval_approx_inf ha hb] with ε ⟨ψ, h1, h2, h3, h5, h6⟩
      have l1 : Tendsto (S ψ) atTop _ := wiener_ikehara_smooth_real hf hcheby hG hG' h1 h2 h3
      have l2 : S ψ ≤ᶠ[atTop] S Iab := by
        filter_upwards [eventually_gt_atTop 0] with x hx using WI_sum_le hpos h5 hx h2 hIab
      have l4 : IsBoundedUnder (· ≥ ·) atTop (S ψ) := l1.isBoundedUnder_ge
      have l3 : liminf (S ψ) atTop ≤ liminf (S Iab) atTop := liminf_le_liminf l2 l4 Iab0
      apply le_trans ?_ l3 ; rw [l1.liminf_eq] ; gcongr
    obtain rfl | h := eq_or_ne A 0
    · simpa using l_inf
    apply ge_of_eventually_nhdsWithin
    have key : 0 < A := lt_of_le_of_ne hA h.symm
    filter_upwards [WI_tendsto_aux' a b key l_inf] with x hx
    simpa [mul_div_cancel₀ _ h] using hx
  have : liminf (S Iab) atTop ≤ limsup (S Iab) atTop := liminf_le_limsup Iab2 Iab3
  refine tendsto_of_liminf_eq_limsup ?_ ?_ Iab2 Iab3 <;> linarith
lemma lt_ceil_mul_iff (hx : 0 < x) : n < ⌈b * x⌉₊ ↔ n / x < b := by
  rw [div_lt_iff₀ hx, Nat.lt_ceil]
lemma ceil_mul_le_iff (hx : 0 < x) : ⌈a * x⌉₊ ≤ n ↔ a ≤ n / x := by
  rw [le_div_iff₀ hx, Nat.ceil_le]
lemma mem_Ico_iff_div (hx : 0 < x) : n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊ ↔ n / x ∈ Ico a b := by
  rw [Finset.mem_Ico, mem_Ico, ceil_mul_le_iff hx, lt_ceil_mul_iff hx]
lemma tsum_indicator {f : ℕ → ℝ} (hx : 0 < x) :
    ∑' n, f n * (indicator (Ico a b) 1 (n / x)) = ∑ n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n := by
  have l1 : ∀ n ∉ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n * indicator (Ico a b) 1 (↑n / x) = 0 := by
    simp [mem_Ico_iff_div hx] ; tauto
  rw [tsum_eq_sum l1] ; apply Finset.sum_congr rfl ; simp only [mem_Ico_iff_div hx] ; intro n hn ; simp [hn]
lemma WienerIkeharaInterval_discrete {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun x : ℝ ↦ (∑ n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n) / x) atTop (nhds (A * (b - a))) := by
  apply (WienerIkeharaInterval hpos hf hcheby hG hG' ha hb).congr'
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [tsum_indicator hx]
lemma WienerIkeharaInterval_discrete' {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.Ico ⌈a * N⌉₊ ⌈b * N⌉₊, f n) / N) atTop (nhds (A * (b - a))) :=
  WienerIkeharaInterval_discrete hpos hf hcheby hG hG' ha hb |>.comp tendsto_natCast_atTop_atTop
lemma tendsto_mul_ceil_div :
    Tendsto (fun (p : ℝ × ℕ) => ⌈p.1 * p.2⌉₊ / (p.2 : ℝ)) (𝓝[>] 0 ×ˢ atTop) (𝓝 0) := by
  rw [Metric.tendsto_nhds] ; intro δ hδ
  have l1 : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioo 0 (δ / 2) := inter_mem_nhdsWithin _ (Iio_mem_nhds (by positivity))
  have l2 : ∀ᶠ N : ℕ in atTop, 1 ≤ δ / 2 * N := by
    apply Tendsto.eventually_ge_atTop
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  filter_upwards [l1.prod_mk l2] with (ε, N) ⟨⟨hε, h1⟩, h2⟩ ; dsimp only at *
  have l3 : 0 < (N : ℝ) := by
    simp only [Nat.cast_pos, Nat.pos_iff_ne_zero] ; rintro rfl ; simp [zero_lt_one.not_ge] at h2
  have l5 : 0 ≤ ε * ↑N := by positivity
  have l6 : ε * N ≤ δ / 2 * N := mul_le_mul h1.le le_rfl (by positivity) (by positivity)
  simp only [dist_zero_right, norm_div, RCLike.norm_natCast, div_lt_iff₀ l3, gt_iff_lt]
  convert (Nat.ceil_lt_add_one l5).trans_le (add_le_add l6 h2) using 1 ; ring
noncomputable def S (f : ℕ → 𝕜) (ε : ℝ) (N : ℕ) : 𝕜 := (∑ n ∈ Finset.Ico ⌈ε * N⌉₊ N, f n) / N
lemma S_sub_S {f : ℕ → 𝕜} {ε : ℝ} {N : ℕ} (hε : ε ≤ 1) : S f 0 N - S f ε N = cumsum f ⌈ε * N⌉₊ / N := by
  have r1 : Finset.range N = Finset.range ⌈ε * N⌉₊ ∪ Finset.Ico ⌈ε * N⌉₊ N := by
    rw [Finset.range_eq_Ico] ; symm ; rw [Finset.range_eq_Ico]
    exact Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _)
      (Nat.ceil_le.mpr (mul_le_of_le_one_left N.cast_nonneg hε))
  have r2 : Disjoint (Finset.range ⌈ε * N⌉₊) (Finset.Ico ⌈ε * N⌉₊ N) := by
    rw [Finset.range_eq_Ico] ; apply Finset.Ico_disjoint_Ico_consecutive
  simp [S, r1, Finset.sum_union r2, cumsum, add_div]
lemma tendsto_S_S_zero {f : ℕ → ℝ} (hpos : 0 ≤ f) (hcheby : cheby f) :
    TendstoUniformlyOnFilter (S f) (S f 0) (𝓝[>] 0) atTop := by
  rw [Metric.tendstoUniformlyOnFilter_iff] ; intro δ hδ
  obtain ⟨C, hC⟩ := hcheby
  have l1 : ∀ᶠ (p : ℝ × ℕ) in 𝓝[>] 0 ×ˢ atTop, C * ⌈p.1 * p.2⌉₊ / p.2 < δ := by
    have r1 := tendsto_mul_ceil_div.const_mul C
    simp only [mul_div_assoc', mul_zero] at r1 ; exact r1 (Iio_mem_nhds hδ)
  have : Ioc 0 1 ∈ 𝓝[>] (0 : ℝ) := inter_mem_nhdsWithin _ (Iic_mem_nhds zero_lt_one)
  filter_upwards [l1, Eventually.prod_inl this _] with (ε, N) h1 h2
  have l2 : ‖cumsum f ⌈ε * ↑N⌉₊ / ↑N‖ ≤ C * ⌈ε * N⌉₊ / N := by
    have r1 := hC ⌈ε * N⌉₊
    have r2 : 0 ≤ cumsum f ⌈ε * N⌉₊ := by apply cumsum_nonneg hpos
    simp only [norm_real, norm_of_nonneg (hpos _), norm_div,
      norm_of_nonneg r2, Real.norm_natCast] at r1 ⊢
    apply div_le_div_of_nonneg_right r1 (by positivity)
  simpa [Real.dist_eq, ← S_sub_S h2.2] using l2.trans_lt h1
set_option maxHeartbeats 1000000 in
theorem WienerIkeharaTheorem' {f : ℕ → ℝ} (hpos : 0 ≤ f)
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun N => cumsum f N / N) atTop (𝓝 A) := by
  have h_event : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Tendsto (S f ε) atTop (𝓝 (A * (1 - ε))) := by
    have L0 : Ioc 0 1 ∈ 𝓝[>] (0 : ℝ) := inter_mem_nhdsWithin _ (Iic_mem_nhds zero_lt_one)
    apply eventually_of_mem L0
    intro ε hε
    have hdisc := WienerIkeharaInterval_discrete' hpos hf hcheby hG hG' hε.1 hε.2
    exact hdisc.congr' (Eventually.of_forall fun N => by simp [S])
  have hlim : Tendsto (fun ε : ℝ => A * (1 - ε)) (𝓝[>] 0) (𝓝 A) := by
    have hε : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    simpa using (hε.const_sub 1).const_mul A
  have hmain : Tendsto (S f 0) atTop (𝓝 A) :=
    (tendsto_S_S_zero hpos hcheby).tendsto_of_eventually_tendsto h_event hlim
  exact hmain.congr' (Eventually.of_forall fun N => by simp [S, cumsum])
section auto_cheby
variable {f : ℕ → ℝ}
lemma norm_x_cpow_it (x t : ℝ) (hx : 0 < x) : ‖(x : ℂ) ^ (t * I)‖ = 1 := by
  rw [cpow_def_of_ne_zero <| ofReal_ne_zero.mpr hx.ne', ← ofReal_log hx.le]
  convert norm_exp_ofReal_mul_I (t * x.log) using 2
  push_cast; ring_nf
lemma limiting_fourier_aux_gt_zero (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (ψ : CS 2 ℂ) (hx : 0 < x) (σ' : ℝ) (hσ' : 1 < σ') :
    ∑' n, term f σ' n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
    A * (x ^ (1 - σ') : ℝ) * ∫ u in Ici (- log x), rexp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)) =
    ∫ t : ℝ, G (σ' + t * I) * ψ t * x ^ (t * I) := by
  have hint : Integrable ψ := ψ.h1.continuous.integrable_of_hasCompactSupport ψ.h2
  have l8 : Continuous fun t : ℝ ↦ (x : ℂ) ^ (t * I) :=
    continuous_const.cpow (continuous_ofReal.mul continuous_const) (by simp [hx])
  have l4 : Integrable fun t : ℝ ↦ LSeries f (↑σ' + ↑t * I) * ψ t * ↑x ^ (↑t * I) :=
    (((continuous_LSeries_aux (hf _ hσ')).mul ψ.h1.continuous).mul l8).integrable_of_hasCompactSupport
      ψ.h2.mul_left.mul_right
  have e2 (u : ℝ) : σ' + u * I - 1 ≠ 0 := fun h ↦ by
    have := congrArg Complex.re (sub_eq_zero.mp h); simp at this; linarith
  have l5 : Integrable fun a ↦ A * ↑(x ^ (1 - σ')) *
      (↑(x ^ (σ' - 1)) * (1 / (σ' + a * I - 1) * ψ a * x ^ (a * I))) := by
    have : Continuous fun a ↦ A * ↑(x ^ (1 - σ')) *
        (↑(x ^ (σ' - 1)) * (1 / (σ' + a * I - 1) * ψ a * x ^ (a * I))) := by
      simp only [one_div, ← mul_assoc]
      exact ((continuous_const.mul (Continuous.inv₀ (by fun_prop) e2)).mul ψ.h1.continuous).mul l8
    exact this.integrable_of_hasCompactSupport ψ.h2.mul_left.mul_right.mul_left.mul_left
  simp_rw [first_fourier hf hint hx hσ', second_fourier ψ.h1.continuous.measurable hint hx hσ',
    ← integral_const_mul, ← integral_sub l4 l5]
  refine integral_congr_ae (.of_forall fun u ↦ ?_)
  have e1 : 1 < ((σ' : ℂ) + (u : ℂ) * I).re := by simp [hσ']
  simp_rw [hG' e1, sub_mul, ← mul_assoc]
  simp only [one_div, sub_right_inj, mul_eq_mul_right_iff, cpow_eq_zero_iff, ofReal_eq_zero, ne_eq,
    mul_eq_zero, I_ne_zero, or_false]
  field_simp [e2]; norm_cast; simp [mul_assoc, ← rpow_add hx]
theorem limiting_fourier_lim2_gt_zero (A : ℝ) (ψ : W21) (hx : 0 < x) :
    Tendsto (fun σ' ↦ A * ↑(x ^ (1 - σ')) *
      ∫ u in Ici (-Real.log x), rexp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)))
        (𝓝[>] 1) (𝓝 (A * ∫ u in Ici (-Real.log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)))) := by
  obtain ⟨C, hC⟩ := decay_bounds_cor ψ
  refine Tendsto.mul ?_ (tendsto_integral_filter_of_dominated_convergence _
    (.of_forall fun _ ↦ (Continuous.mul (by fun_prop)
      ((continuous_FourierIntegral ψ).comp (continuous_id.div_const _))).aestronglyMeasurable) ?_
    (limiting_fourier_lim2_aux x C) (.of_forall fun u ↦ ?_))
  · suffices Tendsto (fun σ' : ℝ ↦ x ^ (1 - σ')) (𝓝[>] 1) (𝓝 1) by
      simpa using ((continuous_ofReal.tendsto 1).comp this).const_mul ↑A
    have : Tendsto (fun σ' : ℝ ↦ 1 - σ') (𝓝[>] 1) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds (by simpa using (continuous_id.tendsto (1 : ℝ)).const_sub 1)
    simpa using tendsto_const_nhds.rpow this (Or.inl hx.ne')
  · refine eventually_of_mem (Ioo_mem_nhdsGT_of_mem (by norm_num : (1 : ℝ) ∈ Set.Ico 1 2)) fun σ' hσ' ↦ ?_
    obtain ⟨h1, h2⟩ := hσ'
    rw [ae_restrict_iff' measurableSet_Ici]
    refine .of_forall fun t ht ↦ ?_
    simp only [norm_mul, neg_mul, ofReal_exp, ofReal_neg, ofReal_mul, ofReal_sub, ofReal_one,
      norm_exp, neg_re, mul_re, ofReal_re, sub_re, one_re, ofReal_im, sub_im, one_im,
      sub_self, mul_zero, sub_zero]
    refine mul_le_mul ?_ (hC _) (norm_nonneg _) ((abs_nonneg x).trans (le_max_left _ _))
    have hα0 : 0 ≤ σ' - 1 := by linarith
    have hα1 : σ' - 1 ≤ 1 := by linarith
    have hmul1 : (-x.log) * (σ' - 1) ≤ t * (σ' - 1) := mul_le_mul_of_nonneg_right ht hα0
    calc Real.exp (-(t * (σ' - 1)))
        ≤ Real.exp (x.log * (σ' - 1)) := Real.exp_monotone (by linarith)
      _ ≤ max |x| 1 := by
          by_cases hx1 : 1 ≤ x
          · calc _ ≤ Real.exp x.log :=
                Real.exp_monotone (mul_le_of_le_one_right (Real.log_nonneg hx1) hα1)
              _ = |x| := by rw [Real.exp_log hx, abs_of_pos hx]
              _ ≤ _ := le_max_left _ _
          · calc _ ≤ 1 := (Real.exp_monotone (mul_nonpos_of_nonpos_of_nonneg
                  ((Real.log_neg_iff hx).2 (by linarith)).le hα0)).trans_eq Real.exp_zero
              _ ≤ _ := le_max_right _ _
  · suffices Tendsto (fun n ↦ ((rexp (-u * (n - 1))) : ℂ)) (𝓝[>] 1) (𝓝 1) by simpa using this.mul_const _
    refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
    have : Continuous (fun n ↦ ((rexp (-u * (n - 1))) : ℂ)) := by continuity
    simpa using this.tendsto 1
theorem limiting_fourier_lim3_gt_zero
    (hG : ContinuousOn G {s | 1 ≤ s.re}) (ψ : CS 2 ℂ) (hx : 0 < x) :
    Tendsto (fun σ' : ℝ ↦ ∫ t : ℝ, G (σ' + t * I) * ψ t * x ^ (t * I)) (𝓝[>] 1)
      (𝓝 (∫ t : ℝ, G (1 + t * I) * ψ t * x ^ (t * I))) := by
  by_cases hh : tsupport ψ = ∅
  · simp [tsupport_eq_empty_iff.mp hh]
  obtain ⟨a₀, ha₀⟩ := Set.nonempty_iff_ne_empty.mpr hh
  let S : Set ℂ := reProdIm (Icc 1 2) (tsupport ψ)
  have l1 : IsCompact S := Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨isClosed_Icc.reProdIm (isClosed_tsupport ψ), (Metric.isBounded_Icc 1 2).reProdIm ψ.h2.isBounded⟩
  have l2 : S ⊆ {s : ℂ | 1 ≤ s.re} := fun z hz => (mem_reProdIm.mp hz).1.1
  obtain ⟨z, -, hmax⟩ := l1.exists_isMaxOn ⟨1 + a₀ * I, by simp [S, mem_reProdIm, ha₀]⟩ (hG.mono l2).norm
  have hxC : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  refine tendsto_integral_filter_of_dominated_convergence (bound := fun a ↦ ‖G z‖ * ‖ψ a‖)
    (eventually_of_mem (Icc_mem_nhdsGT_of_mem (by norm_num : (1 : ℝ) ∈ Set.Ico 1 2)) fun u hu ↦
      ((hG.comp_continuous (by fun_prop) (by simp [hu.1])).mul ψ.h1.continuous).mul
        (by simpa using Continuous.const_cpow (by fun_prop) (Or.inl hxC)) |>.aestronglyMeasurable)
    (eventually_of_mem (Icc_mem_nhdsGT_of_mem (by norm_num : (1 : ℝ) ∈ Set.Ico 1 2)) fun u hu ↦
      .of_forall fun v ↦ ?_)
    ((continuous_const.mul ψ.h1.continuous.norm).integrable_of_hasCompactSupport ψ.h2.norm.mul_left)
    (.of_forall fun t ↦ ?_)
  · by_cases h : v ∈ tsupport ψ
    · simp_rw [norm_mul, norm_x_cpow_it x v hx, mul_one]
      exact mul_le_mul_of_nonneg_right (isMaxOn_iff.mp hmax _ (by simp [S, mem_reProdIm, hu.1, hu.2, h])) (norm_nonneg _)
    · have : v ∉ Function.support ψ := fun a ↦ h (subset_tsupport ψ a)
      simp [Function.notMem_support.mp this]
  · exact ((hG (1 + t * I) (by simp)).tendsto.comp <| tendsto_nhdsWithin_iff.mpr
      ⟨((continuous_ofReal.tendsto _).add tendsto_const_nhds).mono_left nhdsWithin_le_nhds,
       eventually_nhdsWithin_of_forall fun _ hx' ↦ by simp [(Set.mem_Ioi.mp hx').le]⟩).mul_const _ |>.mul_const _
lemma tendsto_tsum_of_monotone_convergence
    {β : Type*} {f : ℕ → β → ENNReal} {g : β → ENNReal}
    (hmono : ∀ k, Monotone (fun n => f n k))
    (hlim : ∀ k, Tendsto (fun n => f n k) atTop (𝓝 (g k))) :
    Tendsto (fun n => ∑' k, f n k) atTop (𝓝 (∑' k, g k)) := by
  let : MeasurableSpace β := ⊤
  let μ : Measure β := Measure.count
  have hg_iSup (k : β) : (⨆ n : ℕ, f n k) = g k := iSup_eq_of_tendsto (hmono k) (hlim k)
  have h_tend_lint : Tendsto (fun n => ∫⁻ k, f n k ∂μ) atTop (𝓝 (∫⁻ k, (⨆ n, f n k) ∂μ)) := by
    have hmeas : ∀ n, Measurable fun k : β => f n k := fun _ _ _ ↦ trivial
    have hmono_fn : Monotone (fun n => fun k : β => f n k) := fun _ _ hnm k ↦ hmono k hnm
    simpa [lintegral_iSup hmeas hmono_fn] using
      tendsto_atTop_iSup fun _ _ hmn ↦ lintegral_mono fun k ↦ hmono k hmn
  simpa [μ, lintegral_count, hg_iSup] using h_tend_lint
lemma tendsto_tsum_of_monotone_convergence_nhdsGT_one
    {F : ℝ → ℕ → ℝ}
    (hF_nonneg : ∀ σ n, 0 ≤ F σ n)
    (hF_antitone : ∀ n, AntitoneOn (fun σ : ℝ => F σ n) (Set.Ioi (1 : ℝ)))
    (hF_tend : ∀ n, Tendsto (fun σ : ℝ => F σ n) (𝓝[>] (1 : ℝ)) (𝓝 (F 1 n)))
    (hSumm : ∀ σ, 1 < σ → Summable (fun n : ℕ => F σ n))
    (hbounded :
      BoundedAtFilter (𝓝[>] (1 : ℝ)) (fun σ : ℝ => (∑' n : ℕ, F σ n))) :
    Tendsto (fun σ : ℝ => ∑' n : ℕ, F σ n) (𝓝[>] (1 : ℝ)) (𝓝 (∑' n : ℕ, F 1 n)) := by
  let T : ℝ → ℝ := fun σ => ∑' n : ℕ, F σ n
  have hT_antitone : AntitoneOn T (Set.Ioi (1 : ℝ)) := fun a ha b hb hab ↦
    (hSumm b hb).tsum_le_tsum_of_inj (fun n ↦ n) (fun _ _ h ↦ h) (fun c hc ↦ (hc ⟨c, rfl⟩).elim)
      (fun n ↦ hF_antitone n ha hb hab) (hSumm a ha)
  have hT_bdd : BddAbove (T '' Set.Ioi (1 : ℝ)) := by
    obtain ⟨C, hC⟩ := isBigO_iff.1 hbounded
    have hC' : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ), T σ ≤ C := by
      filter_upwards [hC] with σ hσ
      calc T σ ≤ |T σ| := le_abs_self _
        _ = ‖T σ‖ := (Real.norm_eq_abs _).symm
        _ ≤ C * ‖(1 : ℝ → ℝ) σ‖ := hσ
        _ = C := by simp
    obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_inf_iff_superset.1 hC'
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
    have hIoi_sub : Set.Ioi (1 : ℝ) ⊆ V := Filter.mem_principal.mp hV
    have hUsub : U ∩ Set.Ioi (1 : ℝ) ⊆ {σ : ℝ | T σ ≤ C} := fun σ hσ ↦ hUV ⟨hσ.1, hIoi_sub hσ.2⟩
    have hσ0_Ioi : 1 + ε / 2 ∈ Set.Ioi (1 : ℝ) := by simp [half_pos hε]
    have hσ0_leC : T (1 + ε / 2) ≤ C :=
      hUsub ⟨hball (by simp only [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left,
        abs_of_pos (half_pos hε)]; exact half_lt_self hε), hσ0_Ioi⟩
    refine ⟨C, ?_⟩
    rintro _ ⟨σ, hσIoi, rfl⟩
    by_cases hσlt : σ < 1 + ε / 2
    · exact hUsub ⟨hball (by
        simp only [Metric.mem_ball, Real.dist_eq]
        rw [abs_of_pos (sub_pos.2 (Set.mem_Ioi.mp hσIoi))]
        linarith [half_lt_self hε]), hσIoi⟩
    · exact (hT_antitone hσ0_Ioi hσIoi (le_of_not_gt hσlt)).trans hσ0_leC
  have hT_tend_sup : Tendsto T (𝓝[>] (1 : ℝ)) (𝓝 (sSup (T '' Set.Ioi (1 : ℝ)))) :=
    hT_antitone.tendsto_nhdsGT hT_bdd
  let σseq : ℕ → ℝ := fun k => 1 + 1 / (k + 1 : ℝ)
  have hσseq_mem (k) : σseq k ∈ Set.Ioi (1 : ℝ) := by
    simp only [σseq, Set.mem_Ioi, lt_add_iff_pos_right]
    positivity
  have hσseq_tend_nhds : Tendsto σseq atTop (𝓝 (1 : ℝ)) := by
    have : Tendsto (fun k : ℕ => (1 : ℝ) + ((k + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 ((1 : ℝ) + 0)) :=
      tendsto_const_nhds.add (tendsto_inv_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1))
    simp only [add_zero] at this
    convert this using 1; ext k; simp [σseq, one_div]
  have hσseq_tend_nhdsWithin : Tendsto σseq atTop (𝓝[>] (1 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hσseq_tend_nhds
      (.of_forall hσseq_mem)
  have hσseq_antitone : Antitone σseq := fun k₁ k₂ hk ↦ by simp only [σseq]; gcongr
  have hmono_seq (n) : Monotone (fun k => F (σseq k) n) := fun k₁ k₂ hk ↦
    hF_antitone n (hσseq_mem k₂) (hσseq_mem k₁) (hσseq_antitone hk)
  have htend_seq (n) : Tendsto (fun k => F (σseq k) n) atTop (𝓝 (F 1 n)) :=
    (hF_tend n).comp hσseq_tend_nhdsWithin
  have hTseq : Tendsto (fun k : ℕ => T (σseq k)) atTop (𝓝 (T 1)) := by
    have hsum1 : Summable (fun n : ℕ => F (1 : ℝ) n) := by
      obtain ⟨C, hC⟩ := hT_bdd
      refine summable_of_sum_range_le (hF_nonneg 1) fun m ↦ le_of_tendsto
        (tendsto_finsetSum _ fun i _ ↦ hF_tend i)
        (eventually_of_mem self_mem_nhdsWithin fun σ hσ ↦
          ((hSumm σ hσ).sum_le_tsum _ (fun n _ ↦ hF_nonneg σ n)).trans (hC ⟨σ, hσ, rfl⟩))
    have hg_ne_top : (∑' n : ℕ, ENNReal.ofReal (F 1 n)) ≠ ⊤ := hsum1.tsum_ofReal_ne_top
    have hENN : Tendsto (fun k => ∑' n, ENNReal.ofReal (F (σseq k) n)) atTop
        (𝓝 (∑' n, ENNReal.ofReal (F 1 n))) :=
      tendsto_tsum_of_monotone_convergence (fun n _ _ hk ↦ ENNReal.ofReal_le_ofReal (hmono_seq n hk))
        (fun n ↦ ENNReal.tendsto_ofReal (htend_seq n))
    have hrew (σ) : (∑' n, ENNReal.ofReal (F σ n)).toReal = ∑' n, F σ n := by
      rw [ENNReal.tsum_toReal_eq (fun n ↦ by simp)]
      exact tsum_congr fun n ↦ by simp [hF_nonneg σ n]
    simp only [T, ← hrew]; exact (ENNReal.tendsto_toReal hg_ne_top).comp hENN
  have hsSup_eq : sSup (T '' Set.Ioi (1 : ℝ)) = T 1 :=
    tendsto_nhds_unique (hT_tend_sup.comp hσseq_tend_nhdsWithin) hTseq
  simpa [T, hsSup_eq] using hT_tend_sup
lemma limiting_fourier_variant_lim1_aux
    {f : ℕ → ℝ} {x : ℝ} (ψ : CS 2 ℂ)
    (hpos : 0 ≤ f)
    (hf : ∀ (σ : ℝ), 1 < σ → Summable (nterm f σ))
    (hψpos : ∀ y, 0 ≤ (𝓕 (ψ : ℝ → ℂ) y).re ∧ (𝓕 (ψ : ℝ → ℂ) y).im = 0) :
    ∀ (σ : ℝ), 1 < σ →
      Summable (fun n : ℕ =>
        (if n = 0 then 0 else f n / ((n : ℝ) ^ σ)) *
          (𝓕 ψ.toFun (1 / (2 * π) * Real.log ((n : ℝ) / x))).re) := by
  intro σ hσ
  let y : ℕ → ℝ := fun n => (1 / (2 * π)) * Real.log ((n : ℝ) / x)
  let W : ℕ → ℝ := fun n => (𝓕 ψ.toFun (y n)).re
  let base : ℕ → ℝ := fun n => if n = 0 then 0 else f n / ((n : ℝ) ^ σ)
  obtain ⟨C, hC⟩ := decay_bounds_cor (W21.ofCS2 ψ)
  have hC_nonneg : 0 ≤ C := (norm_nonneg _).trans ((hC 0).trans (by simp))
  have hW_nonneg (n : ℕ) : 0 ≤ W n := (hψpos (y n)).1
  have hnorm_four (n : ℕ) : ‖𝓕 ψ.toFun (y n)‖ = W n := by
    have him0 : (𝓕 ψ.toFun (y n)).im = 0 := (hψpos (y n)).2
    rw [show 𝓕 ψ.toFun (y n) = W n by exact Complex.ext rfl him0]
    simp [abs_of_nonneg (hW_nonneg n)]
  have hW_le_C (n : ℕ) : W n ≤ C := by
    rw [← hnorm_four]; exact (hC (y n)).trans (div_le_self hC_nonneg (by nlinarith [sq_nonneg (y n)]))
  have hbase_summ : Summable base := by
    convert hf σ hσ using 1; ext n
    by_cases hn : n = 0 <;> simp [nterm, base, hn, Real.norm_eq_abs, abs_of_nonneg (hpos n)]
  refine (hbase_summ.mul_left C).of_norm_bounded fun n ↦ ?_
  by_cases hn : n = 0
  · simp [base, hn]
  · have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hbase_nonneg : 0 ≤ base n := by
      simp only [base, hn, if_false]
      exact div_nonneg (hpos n) (Real.rpow_pos_of_pos hnpos σ).le
    calc |base n * W n| = base n * W n := abs_of_nonneg (mul_nonneg hbase_nonneg (hW_nonneg n))
      _ ≤ base n * C := mul_le_mul_of_nonneg_left (hW_le_C n) hbase_nonneg
      _ = C * base n := mul_comm _ _
theorem limiting_fourier_variant_lim1
    {f : ℕ → ℝ} {x : ℝ} {ψ : CS 2 ℂ}
    (hpos : 0 ≤ f)
    (hψpos : ∀ y, 0 ≤ (𝓕 (ψ : ℝ → ℂ) y).re ∧ (𝓕 (ψ : ℝ → ℂ) y).im = 0)
    (S : ℝ → ℂ)
    (hSdef :
      ∀ σ' : ℝ,
        S σ' =
          ∑' n : ℕ,
            term (fun n ↦ (f n : ℂ)) (σ' : ℝ) n *
              𝓕 ψ.toFun (π⁻¹ * 2⁻¹ * Real.log ((n : ℝ) / x)))
    (hbounded : BoundedAtFilter (𝓝[>] (1 : ℝ)) (fun σ' : ℝ => ‖S σ'‖))
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) :
    Tendsto
      (fun σ' : ℝ =>
        ∑' n : ℕ,
          term (fun n ↦ (f n : ℂ)) (σ' : ℝ) n *
            𝓕 ψ.toFun (π⁻¹ * 2⁻¹ * Real.log ((n : ℝ) / x)))
      (𝓝[>] (1 : ℝ))
      (𝓝
        (∑' n : ℕ,
          (f n : ℂ) / (n : ℂ) *
            𝓕 ψ.toFun (π⁻¹ * 2⁻¹ * Real.log ((n : ℝ) / x)))) := by
  let y : ℕ → ℝ := fun n => (π⁻¹ * 2⁻¹) * Real.log ((n : ℝ) / x)
  let w : ℕ → ℝ := fun n => (𝓕 ψ.toFun (y n)).re
  have hw_nonneg : ∀ n, 0 ≤ w n := by
    intro n
    exact (hψpos (y n)).1
  have hFour_eq_ofReal : ∀ n, 𝓕 ψ.toFun (y n) = Complex.ofReal (w n) := by
    intro n
    have h := hψpos (y n)
    refine Complex.ext ?_ ?_
    · simp [w]
    · simp [w, h.2]
  let rterm : ℝ → ℕ → ℝ :=
    fun σ n =>
      if h0 : n = 0 then 0 else (f n) / ((n : ℝ) ^ σ) * (w n)
  have summand_eq_ofReal :
      ∀ (σ : ℝ) (n : ℕ),
        term (fun n ↦ (f n : ℂ)) (σ : ℝ) n * 𝓕 ψ.toFun (y n)
          = Complex.ofReal (rterm σ n) := by
    intro σ n
    by_cases hn : n = 0
    · subst hn
      simp [rterm, y]
    · have hnpos : (0 : ℝ) < (n : ℝ) := by
        exact_mod_cast (Nat.pos_of_ne_zero hn)
      have hn0 : 0 ≤ (n : ℝ) := le_of_lt hnpos
      have hcpow :
          ( (n : ℂ) ^ ((σ : ℝ) : ℂ) ) = ( ( (n : ℝ) ^ σ : ℝ) : ℂ ) := by
        simpa using (Complex.ofReal_cpow hn0 σ).symm
      have hpow_ne : ((n : ℝ) ^ σ) ≠ 0 := by
        exact (ne_of_gt (Real.rpow_pos_of_pos hnpos σ))
      calc
        term (fun n ↦ (f n : ℂ)) (σ : ℝ) n * 𝓕 ψ.toFun (y n)
            =
          ((f n : ℂ) / ((n : ℂ) ^ ((σ : ℝ) : ℂ))) * ( (w n : ℝ) : ℂ ) := by
            simp [term, LSeries.term, hn, hFour_eq_ofReal]
        _ =
          ((f n : ℂ) / (((n : ℝ) ^ σ : ℝ) : ℂ)) * ((w n : ℝ) : ℂ) := by
            simp [hcpow]
        _ =
          (( (f n : ℝ) : ℂ) / (((n : ℝ) ^ σ : ℝ) : ℂ)) * ((w n : ℝ) : ℂ) := by
            simp
        _ =
          ( ( (f n : ℝ) / ((n : ℝ) ^ σ) : ℝ) : ℂ ) * ((w n : ℝ) : ℂ) := by
            simp [Complex.ofReal_div]
        _ =
          ( ( (f n : ℝ) / ((n : ℝ) ^ σ) * (w n) : ℝ ) : ℂ ) := by
            simp [Complex.ofReal_mul]
        _ =
          Complex.ofReal (rterm σ n) := by
            simp [rterm, hn]
  let T : ℝ → ℝ := fun σ => ∑' n, rterm σ n
  have tsum_eq_ofReal_T : ∀ σ : ℝ,
      (∑' n : ℕ, term (fun n ↦ (f n : ℂ)) (σ : ℝ) n * 𝓕 ψ.toFun (y n))
        = Complex.ofReal (T σ) := by
    intro σ
    have hcongr :
        (∑' n : ℕ, term (fun n ↦ (f n : ℂ)) (σ : ℝ) n * 𝓕 ψ.toFun (y n))
          = ∑' n : ℕ, (Complex.ofReal (rterm σ n)) := by
      refine tsum_congr ?_
      intro n
      simpa using (summand_eq_ofReal σ n)
    calc
      (∑' n : ℕ, term (fun n ↦ (f n : ℂ)) (σ : ℝ) n * 𝓕 ψ.toFun (y n))
          = ∑' n : ℕ, (Complex.ofReal (rterm σ n)) := hcongr
      _ = Complex.ofReal (∑' n : ℕ, rterm σ n) := by
            simpa using (Complex.ofReal_tsum (fun n : ℕ => rterm σ n)).symm
      _ = Complex.ofReal (T σ) := by rfl
  have hS_ofReal_T : ∀ σ : ℝ, S σ = Complex.ofReal (T σ) := by
    intro σ
    simpa [hSdef σ, y] using (tsum_eq_ofReal_T σ)
  have rterm_nonneg : ∀ σ n, 0 ≤ rterm σ n := by
    intro σ n
    by_cases hn : n = 0
    · subst hn; simp [rterm]
    · have hf : 0 ≤ f n := hpos n
      have hw : 0 ≤ w n := hw_nonneg n
      have hnpos : 0 < (n : ℝ) := by
        exact_mod_cast (Nat.pos_of_ne_zero hn)
      have hden : 0 < (n : ℝ) ^ σ := Real.rpow_pos_of_pos hnpos σ
      have : 0 ≤ (f n) / ((n : ℝ) ^ σ) := div_nonneg hf (le_of_lt hden)
      simp [rterm, hn, mul_nonneg this hw]
  have T_nonneg : ∀ σ, 0 ≤ T σ := by
    intro σ
    exact tsum_nonneg (fun n => rterm_nonneg σ n)
  have hT_eq_normS : ∀ σ, T σ = ‖S σ‖ := by
    intro σ
    have := hS_ofReal_T σ
    calc
      T σ = ‖Complex.ofReal (T σ)‖ := by simp [abs_of_nonneg (T_nonneg σ)]
      _ = ‖S σ‖ := by simp [this]
  have hboundedT : BoundedAtFilter (𝓝[>] (1 : ℝ)) (fun σ : ℝ => T σ) := by
    have : (fun σ : ℝ => T σ) = (fun σ : ℝ => ‖S σ‖) := by
      funext σ; exact hT_eq_normS σ
    simpa [this] using hbounded
  have rterm_antitone : ∀ n, AntitoneOn (fun σ => rterm σ n) (Set.Ioi 1) := by
    intro n σ₁ hσ₁ σ₂ hσ₂ hσ₁₂
    by_cases hn : n = 0
    · subst hn; simp [rterm]
    · have hf : 0 ≤ f n := hpos n
      have hw : 0 ≤ w n := hw_nonneg n
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
      have hpow : (n : ℝ) ^ σ₁ ≤ (n : ℝ) ^ σ₂ :=
        Real.rpow_le_rpow_of_exponent_le hn1 hσ₁₂
      have hinv :
      (1 / ((n : ℝ) ^ σ₂)) ≤ (1 / ((n : ℝ) ^ σ₁)) := by
        have hpos1 : 0 < (n : ℝ) ^ σ₁ := Real.rpow_pos_of_pos hnpos σ₁
        exact one_div_le_one_div_of_le hpos1 hpow
      have hinv_inv : ((n : ℝ) ^ σ₂)⁻¹ ≤ ((n : ℝ) ^ σ₁)⁻¹ := by
        simpa [one_div] using hinv
      have hmul1 :
          (f n) * (((n : ℝ) ^ σ₂)⁻¹) ≤ (f n) * (((n : ℝ) ^ σ₁)⁻¹) :=
        mul_le_mul_of_nonneg_left hinv_inv hf
      have hmul2 :
          ((f n) * (((n : ℝ) ^ σ₂)⁻¹)) * (w n)
            ≤ ((f n) * (((n : ℝ) ^ σ₁)⁻¹)) * (w n) :=
        mul_le_mul_of_nonneg_right hmul1 hw
      simpa [rterm, hn, div_eq_mul_inv, mul_assoc] using hmul2
  have rterm_tend : ∀ n, Tendsto (fun σ : ℝ => rterm σ n) (𝓝[>] (1 : ℝ)) (𝓝 (rterm 1 n)) := by
    intro n
    have hterm :
        Tendsto (fun σ : ℝ => term (fun n ↦ (f n : ℂ)) (σ : ℝ) n)
          (𝓝[>] (1 : ℝ)) (𝓝 ((f n : ℂ) / (n : ℂ))) := by
      by_cases hn : n = 0
      · subst hn
        simp [term, LSeries.term]
      · have hden :
            Tendsto (fun σ : ℝ => ((n : ℂ) ^ ((σ : ℝ) : ℂ))) (𝓝[>] (1 : ℝ)) (𝓝 ((n : ℂ) ^ (1 : ℂ))) := by
          simpa using ((continuous_ofReal.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds).const_cpow
        have hden' :
            Tendsto (fun σ : ℝ => ((n : ℂ) ^ ((σ : ℝ) : ℂ))) (𝓝[>] (1 : ℝ)) (𝓝 (n : ℂ)) := by
          simpa using hden
        have hnC : (n : ℂ) ≠ 0 := by
          exact_mod_cast hn
        have hterm :
            Tendsto (fun σ : ℝ => term (fun n ↦ (f n : ℂ)) (σ : ℝ) n)
              (𝓝[>] (1 : ℝ)) (𝓝 ((f n : ℂ) / (n : ℂ))) := by
          have hnC : (n : ℂ) ≠ 0 := by
            exact_mod_cast hn
          simp only [term, LSeries.term, hn, ↓reduceIte]
          change Tendsto (((fun _ : ℝ => (f n : ℂ)) /
              fun σ : ℝ => (n : ℂ) ^ ((σ : ℝ) : ℂ)))
            (𝓝[>] (1 : ℝ)) (𝓝 ((f n : ℂ) / (n : ℂ)))
          exact tendsto_const_nhds.div hden' hnC
        exact hterm
    have hsummand :
        Tendsto
          (fun σ : ℝ =>
            term (fun n ↦ (f n : ℂ)) (σ : ℝ) n * 𝓕 ψ.toFun (y n))
          (𝓝[>] (1 : ℝ))
          (𝓝 (((f n : ℂ) / (n : ℂ)) * 𝓕 ψ.toFun (y n))) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using (hterm.mul_const (𝓕 ψ.toFun (y n)))
    have hre : ∀ σ, rterm σ n =
        (term (fun n ↦ (f n : ℂ)) (σ : ℝ) n * 𝓕 ψ.toFun (y n)).re := by
      intro σ
      have := congrArg Complex.re (summand_eq_ofReal σ n)
      simpa [Complex.ofReal_re] using this.symm
    have hRe : Tendsto
        (fun σ : ℝ =>
          (term (fun n ↦ (f n : ℂ)) (σ : ℝ) n * 𝓕 ψ.toFun (y n)).re)
        (𝓝[>] (1 : ℝ))
        (𝓝 ((((f n : ℂ) / (n : ℂ)) * 𝓕 ψ.toFun (y n)).re)) :=
      (continuous_re.tendsto _).comp hsummand
    have hlimit_re :
      (f n / (n : ℝ)) * (𝓕 ψ.toFun (y n)).re = rterm 1 n := by
      have h0 :
          (term (fun n ↦ (f n : ℂ)) (1 : ℝ) n * 𝓕 ψ.toFun (y n)).re = rterm 1 n := by
        have := congrArg Complex.re (summand_eq_ofReal (σ := (1 : ℝ)) n)
        simpa [Complex.ofReal_re] using this
      by_cases hn : n = 0
      · subst hn
        simp [rterm, y]
      · have h1 :
            (term (fun n ↦ (f n : ℂ)) (1 : ℝ) n * 𝓕 ψ.toFun (y n)).re
              = (f n / (n : ℝ)) * (𝓕 ψ.toFun (y n)).re := by
          simp [Complex.mul_re, term, LSeries.term, hn, y,
                (hψpos (y n)).2]
        exact (h1.symm.trans h0)
    simpa [hre, hlimit_re] using hRe
  have hSumm_rterm : ∀ σ : ℝ, 1 < σ → Summable (fun n : ℕ => rterm σ n) := by
    simpa [rterm] using limiting_fourier_variant_lim1_aux (ψ := ψ)
      (f := f) (x := x) hpos hf hψpos
  have hT_tend :
      Tendsto T (𝓝[>] (1 : ℝ)) (𝓝 (T 1)) := by
    have :
        Tendsto (fun σ : ℝ => ∑' n : ℕ, rterm σ n)
          (𝓝[>] (1 : ℝ))
          (𝓝 (∑' n : ℕ, rterm (1 : ℝ) n)) := by
      refine tendsto_tsum_of_monotone_convergence_nhdsGT_one
        (F := rterm)
        (hF_nonneg := rterm_nonneg)
        (hF_antitone := rterm_antitone)
        (hF_tend := rterm_tend)
        (hSumm := hSumm_rterm)
        (hbounded := hboundedT)
    simpa [T] using this
  have hToReal :
      Tendsto (fun σ => Complex.ofReal (T σ)) (𝓝[>] (1 : ℝ)) (𝓝 (Complex.ofReal (T 1))) :=
    (continuous_ofReal.tendsto _).comp hT_tend
  have hsource :
      (fun σ : ℝ =>
        ∑' n : ℕ,
          term (fun n ↦ (f n : ℂ)) (σ : ℝ) n * 𝓕 ψ.toFun (y n))
        = fun σ : ℝ => Complex.ofReal (T σ) := by
    funext σ
    exact (tsum_eq_ofReal_T σ)
  have hσ1 :
    (∑' n : ℕ, term (fun n ↦ (f n : ℂ)) (↑(1:ℝ)) n * 𝓕 ψ.toFun (y n))
      = (↑(T 1) : ℂ) :=
    by simpa using (tsum_eq_ofReal_T (σ := (1:ℝ)))
  have hterm1 :
      ∀ n : ℕ, term (fun n ↦ (f n : ℂ)) (1 : ℂ) n = (f n : ℂ) / (n : ℂ) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      simp [term, LSeries.term]
    · simp [term, LSeries.term, hn]
  have hrewrite :
      (∑' n : ℕ,
        term (fun n ↦ (f n : ℂ)) (1 : ℂ) n * 𝓕 ψ.toFun (y n))
        =
      (∑' n : ℕ,
        (f n : ℂ) / (n : ℂ) * 𝓕 ψ.toFun (y n)) := by
    refine tsum_congr ?_
    intro n
    simp [hterm1 n]
  have htarget :
      (∑' n : ℕ,
        (f n : ℂ) / (n : ℂ) * 𝓕 ψ.toFun (y n))
        = (↑(T 1) : ℂ) := by
    exact (hrewrite.symm.trans hσ1)
  simpa [hsource, htarget, y] using hToReal
lemma limiting_fourier_variant
    (hpos : 0 ≤ f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (ψ : CS 2 ℂ)
    (hψpos : ∀ y, 0 ≤ (𝓕 (ψ : ℝ → ℂ) y).re ∧ (𝓕 (ψ : ℝ → ℂ) y).im = 0)
    (hx : 0 < x) :
    ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)) =
      ∫ (t : ℝ), (G (1 + t * I)) * (ψ t) * x ^ (t * I) := by
  have l2 := limiting_fourier_lim2_gt_zero (A := A) (x := x) ψ hx
  have l3 := limiting_fourier_lim3_gt_zero (G := G) (x := x) hG ψ hx
  let S : ℝ → ℂ := fun σ' =>
    ∑' n : ℕ,
      term (fun n ↦ (f n : ℂ)) σ' n *
        𝓕 ψ.toFun (1 / (2 * π) * Real.log ((n : ℝ) / x))
  let Pole : ℝ → ℂ := fun σ' =>
    (A : ℂ) * ((x ^ (1 - σ') : ℝ) : ℂ) *
      ∫ u in Set.Ici (-Real.log x),
        (rexp (-u * (σ' - 1)) : ℂ) *
          𝓕 (W21.ofCS2 ψ).toFun (u / (2 * π))
  let RHS : ℝ → ℂ := fun σ' =>
    ∫ t : ℝ, G (σ' + t * I) * ψ.toFun t * (x : ℂ) ^ (t * I)
  have haux :
    (fun σ' ↦
        ∑' (n : ℕ),
          term (fun n ↦ (f n : ℂ)) (σ' : ℂ) n *
            𝓕 ψ.toFun (π⁻¹ * 2⁻¹ * Real.log ((n : ℝ) / x))
        - (A : ℂ) * ((x ^ (1 - σ') : ℝ) : ℂ) *
          ∫ (u : ℝ) in Ici (-Real.log x),
            cexp (-( (u : ℂ) * ((σ' : ℂ) - 1))) *
              𝓕 (W21.ofCS2 ψ).toFun (u / (2 * π)))
      =ᶠ[𝓝[>] (1 : ℝ)]
    (fun σ' ↦
      ∫ (t : ℝ), G ((σ' : ℂ) + (t : ℂ) * I) * ψ.toFun t * (x : ℂ) ^ ((t : ℂ) * I)) := by
    rw [Filter.EventuallyEq]
    refine eventually_nhdsWithin_of_forall ?_
    intro σ' hσ'
    have hσ' : (1 : ℝ) < σ' := by
      simpa [Set.mem_Ioi] using hσ'
    simpa using (limiting_fourier_aux_gt_zero (G := G) (f := f) (A := A) hG' hf ψ hx σ' hσ')
  have haux' :
    (fun σ' : ℝ => S σ') =ᶠ[𝓝[>] (1 : ℝ)] (fun σ' : ℝ => RHS σ' + Pole σ') := by
    rw [Filter.EventuallyEq] at haux ⊢
    filter_upwards [haux] with σ' hσ'
    have hσ'' : S σ' - Pole σ' = RHS σ' := by
      simpa [S, Pole, RHS] using hσ'
    have hadd : (S σ' - Pole σ') + Pole σ' = RHS σ' + Pole σ' :=
      congrArg (fun z : ℂ => z + Pole σ') hσ''
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hadd
  let Pole₁ : ℂ := (A : ℂ) * ∫ u in Set.Ici (-Real.log x), 𝓕 (W21.ofCS2 ψ).toFun (u / (2 * π))
  let RHS₁ : ℂ := ∫ t : ℝ, G (1 + (t : ℂ) * I) * ψ.toFun t * (x : ℂ) ^ ((t : ℂ) * I)
  have hRHS_le :
      ∀ᶠ σ' : ℝ in 𝓝[>] (1 : ℝ), ‖RHS σ'‖ ≤ ‖RHS₁‖ + 1 := by
    have hball : Metric.ball RHS₁ (1 : ℝ) ∈ 𝓝 RHS₁ := by
      simpa using (Metric.ball_mem_nhds (x := RHS₁) (ε := (1 : ℝ)) (by norm_num))
    have hpre : {σ' : ℝ | RHS σ' ∈ Metric.ball RHS₁ (1 : ℝ)} ∈ (𝓝[>] (1 : ℝ)) :=
      l3 hball
    filter_upwards [hpre] with σ' hmem
    have hdist' : dist (RHS σ') RHS₁ < (1 : ℝ) := by
      simpa [Metric.mem_ball] using hmem
    have hdist : ‖RHS σ' - RHS₁‖ < (1 : ℝ) := by
      simpa [dist_eq_norm] using hdist'
    have htri : ‖RHS σ'‖ ≤ ‖RHS₁‖ + ‖RHS σ' - RHS₁‖ := by
      have h := norm_add_le (RHS σ' - RHS₁) RHS₁
      simpa [sub_add_cancel, add_comm, add_left_comm, add_assoc] using h
    have hle : ‖RHS₁‖ + ‖RHS σ' - RHS₁‖ ≤ ‖RHS₁‖ + (1 : ℝ) := by
      exact add_le_add_right (le_of_lt hdist) ‖RHS₁‖
    exact htri.trans hle
  have hPole_le :
    ∀ᶠ σ' : ℝ in 𝓝[>] (1 : ℝ), ‖Pole σ'‖ ≤ ‖Pole₁‖ + 1 := by
    have hball : Metric.ball Pole₁ 1 ∈ 𝓝 Pole₁ := by
      simpa using (Metric.ball_mem_nhds Pole₁ (by norm_num : (0 : ℝ) < 1))
    have hpre : {σ' : ℝ | Pole σ' ∈ Metric.ball Pole₁ 1} ∈ (𝓝[>] (1 : ℝ)) := l2 hball
    filter_upwards [hpre] with σ' hmem
    have hdist : ‖Pole σ' - Pole₁‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hmem
    have htri : ‖Pole σ'‖ ≤ ‖Pole₁‖ + ‖Pole σ' - Pole₁‖ := by
      have hdecomp : Pole σ' = Pole₁ + (Pole σ' - Pole₁) := by abel
      have hnorm_eq : ‖Pole σ'‖ = ‖Pole₁ + (Pole σ' - Pole₁)‖ := by
        simp [congrArg (fun z : ℂ => ‖z‖) hdecomp]
      calc
        ‖Pole σ'‖ = ‖Pole₁ + (Pole σ' - Pole₁)‖ := hnorm_eq
        _ ≤ ‖Pole₁‖ + ‖Pole σ' - Pole₁‖ := norm_add_le _ _
    have hdist_le : ‖Pole σ' - Pole₁‖ ≤ 1 := le_of_lt hdist
    have hsum : ‖Pole₁‖ + ‖Pole σ' - Pole₁‖ ≤ ‖Pole₁‖ + 1 := by
      simpa [add_comm, add_left_comm, add_assoc] using (add_le_add_left hdist_le ‖Pole₁‖)
    exact htri.trans hsum
  have hS_le :
      ∀ᶠ σ' : ℝ in 𝓝[>] (1 : ℝ),
        ‖S σ'‖ ≤ (‖RHS₁‖ + 1) + (‖Pole₁‖ + 1) := by
    rw [Filter.EventuallyEq] at haux'
    filter_upwards [haux', hRHS_le, hPole_le] with σ' hEq hR hP
    calc
      ‖S σ'‖ = ‖RHS σ' + Pole σ'‖ := by simp [hEq]
      _ ≤ ‖RHS σ'‖ + ‖Pole σ'‖ := norm_add_le _ _
      _ ≤ (‖RHS₁‖ + 1) + (‖Pole₁‖ + 1) := by
        exact add_le_add hR hP
  have hbounded : BoundedAtFilter (𝓝[>] (1 : ℝ)) (fun σ' : ℝ => ‖S σ'‖) := by
    let C : ℝ := ‖RHS₁‖ + 1 + (‖Pole₁‖ + 1)
    simp only [BoundedAtFilter, Asymptotics.IsBigO, Asymptotics.IsBigOWith]
    refine ⟨C, ?_⟩
    filter_upwards [hS_le] with σ' hσ'
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (S σ'))] using hσ'
  have hcoef : (1 / (2 * π) : ℝ) = (π⁻¹ * 2⁻¹ : ℝ) := by field_simp [pi_ne_zero]
  have l1 :=
    limiting_fourier_variant_lim1
      (f := f) (x := x) (ψ := ψ)
      hpos hψpos
      (S := S)
      (hSdef := by
        intro σ
        simp [S, hcoef] )
      hbounded
      hf
  have l1S :
    Tendsto S (𝓝[>] (1 : ℝ))
      (𝓝 (∑' n : ℕ, (f n : ℂ) / (n : ℂ) * 𝓕 ψ.toFun (1 / (2 * π) * Real.log (↑n / x)))) := by
    simpa [S, hcoef] using l1
  have l12 : Tendsto (fun σ' : ℝ => S σ' - Pole σ') (𝓝[>] (1 : ℝ))
    (𝓝 ((∑' n : ℕ, (f n : ℂ) / (n : ℂ) * 𝓕 ψ.toFun (1 / (2 * π) * Real.log (↑n / x))) - Pole₁)) :=
  l1S.sub l2
  have hPole : (Pole : ℝ → ℂ) =ᶠ[𝓝[>] (1 : ℝ)] Pole := by simp
  have haux_sub :
    (fun σ' : ℝ => S σ' - Pole σ') =ᶠ[𝓝[>] (1 : ℝ)] RHS := by
    filter_upwards [haux'] with σ' hσ'
    calc
      S σ' - Pole σ'
          = (RHS σ' + Pole σ') - Pole σ' := by simp [hσ']
      _   = RHS σ' := by simp
  have hlim :=
    tendsto_nhds_unique_of_eventuallyEq (l1S.sub l2) l3 haux_sub
  simpa [Pole₁, RHS₁] using hlim
lemma norm_mul_integral_Ici_le_integral_norm
    (A : ℂ) (F : ℝ → ℂ) (a : ℝ)
    (hF : IntegrableOn F (Set.Ici a))
    (hnorm : Integrable (fun u : ℝ => ‖F u‖)) :
    ‖A * (∫ u in Set.Ici a, F u)‖ ≤ ‖A‖ * (∫ u : ℝ, ‖F u‖) := by
  have hmul : ‖A * (∫ u in Set.Ici a, F u)‖ = ‖A‖ * ‖∫ u in Set.Ici a, F u‖ := by
    simp
  have hnormI :
      ‖∫ u in Set.Ici a, F u‖ ≤ ∫ u in Set.Ici a, ‖F u‖ := by
    have _ : Integrable F (Measure.restrict volume (Set.Ici a)) := hF
    have h :
        ‖∫ u, F u ∂Measure.restrict volume (Set.Ici a)‖
          ≤ ∫ u, ‖F u‖ ∂Measure.restrict volume (Set.Ici a) :=
      norm_integral_le_integral_norm (μ := Measure.restrict volume (Set.Ici a)) (f := F)
    simpa using h
  have hdom :
      (∫ u in Set.Ici a, ‖F u‖) ≤ ∫ u : ℝ, ‖F u‖ := by
    have hEq :
        (∫ u in Set.Ici a, ‖F u‖) =
          ∫ u : ℝ, Set.indicator (Set.Ici a) (fun u => ‖F u‖) u := by
      have h := (integral_indicator (μ := (volume : Measure ℝ))
        (s := Set.Ici a) (f := fun u => ‖F u‖))
      have h' := h measurableSet_Ici
      simpa using h'.symm
    have hind_int :
        Integrable (Set.indicator (Set.Ici a) (fun u => ‖F u‖)) :=
      hnorm.indicator measurableSet_Ici
    have hpoint :
        Set.indicator (Set.Ici a) (fun u => ‖F u‖)
            ≤ᵐ[volume] (fun u : ℝ => ‖F u‖) := by
      filter_upwards with u
      by_cases hu : u ∈ Set.Ici a
      · simp [Set.indicator_of_mem hu]
      · simp [Set.indicator_of_notMem hu]
    have hmono :=
        integral_mono_ae (μ := (volume : Measure ℝ))
          hind_int hnorm hpoint
    simpa [hEq] using hmono
  calc
    ‖A * (∫ u in Set.Ici a, F u)‖
        = ‖A‖ * ‖∫ u in Set.Ici a, F u‖ := hmul
    _   ≤ ‖A‖ * (∫ u in Set.Ici a, ‖F u‖) :=
      mul_le_mul_of_nonneg_left hnormI (by simp)
    _   ≤ ‖A‖ * (∫ u : ℝ, ‖F u‖) :=
      mul_le_mul_of_nonneg_left hdom (by simp)
lemma fourier_decay_of_CS2
    (ψ : CS 2 ℂ) :
    ∃ C : ℝ, ∀ u : ℝ, ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ C / (1 + u ^ 2) := by
  let ψ' : W21 := (ψ : W21)
  obtain ⟨C, hC⟩ :
      ∃ C : ℝ, ∀ u : ℝ, ‖𝓕 (ψ' : ℝ → ℂ) u‖ ≤ C / (1 + u ^ 2) := by
    simpa using (decay_bounds_cor (ψ := ψ'))
  refine ⟨C, ?_⟩
  intro u
  simpa [ψ'] using (hC u)
lemma integrable_norm_fourier_scaled_of_CS2
    (ψ : CS 2 ℂ) :
    Integrable (fun u : ℝ => ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖) := by
  obtain ⟨C, hdecay⟩ := fourier_decay_of_CS2 (ψ := ψ)
  have hC_nonneg : 0 ≤ C := by
    have h0 := hdecay 0
    have hnorm : 0 ≤ ‖𝓕 (ψ : ℝ → ℂ) 0‖ := norm_nonneg _
    have hC' : ‖𝓕 (ψ : ℝ → ℂ) 0‖ ≤ C := by simpa using h0
    exact hnorm.trans hC'
  have hmaj_int : Integrable (fun u : ℝ => (C : ℝ) / (1 + (u / (2 * Real.pi))^2)) := by
    have hbase : Integrable (fun u : ℝ => (1 + u ^ 2)⁻¹) := integrable_inv_one_add_sq
    have hscale :
        Integrable (fun u : ℝ => (1 + (u / (2 * Real.pi)) ^ 2)⁻¹) :=
      hbase.comp_div (by nlinarith [Real.pi_pos])
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, pow_two] using
      hscale.const_mul C
  have hle :
      (fun u : ℝ => ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖)
        ≤ᵐ[volume]
      (fun u : ℝ => (C : ℝ) / (1 + (u / (2 * Real.pi))^2)) := by
    refine Filter.Eventually.of_forall ?_
    intro u
    simpa using (hdecay (u / (2 * Real.pi)))
  have hle_norm :
      (fun u : ℝ => ‖‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖‖)
        ≤ᵐ[volume]
      (fun u : ℝ => ‖(C : ℝ) / (1 + (u / (2 * Real.pi))^2)‖) := by
    refine hle.mono ?_
    intro u hu
    have hden_pos : 0 < 1 + (u / (2 * Real.pi)) ^ 2 := by nlinarith
    have hnonneg : 0 ≤ (C : ℝ) / (1 + (u / (2 * Real.pi))^2) :=
      div_nonneg hC_nonneg hden_pos.le
    have hleft_nonneg : 0 ≤ ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖ := norm_nonneg _
    have hbound : ‖‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖‖ ≤
        (C : ℝ) / (1 + (u / (2 * Real.pi))^2) := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hleft_nonneg] using hu
    have hC_abs : |C| = C := abs_of_nonneg hC_nonneg
    have hden_abs : |1 + (u / (2 * Real.pi))^2| = 1 + (u / (2 * Real.pi))^2 := by
      have : 0 ≤ 1 + (u / (2 * Real.pi))^2 := by nlinarith
      simpa using abs_of_nonneg this
    have hnorm :
        ‖(C : ℝ) / (1 + (u / (2 * Real.pi))^2)‖ =
          (C : ℝ) / (1 + (u / (2 * Real.pi))^2) := by
      have hrec :
          ‖(C : ℝ) / (1 + (u / (2 * Real.pi))^2)‖ =
            |C| / |1 + (u / (2 * Real.pi))^2| := by
        simp [Real.norm_eq_abs]
      simp [hC_abs, hden_abs, hrec]
    simpa [hnorm] using hbound
  have hmaj_int_norm :
      Integrable (fun u : ℝ => ‖(C : ℝ) / (1 + (u / (2 * Real.pi))^2)‖) :=
    hmaj_int.norm
  have hmeas :
      AEStronglyMeasurable (fun u : ℝ => ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖) := by
    have hcont : Continuous fun u : ℝ => 𝓕 (ψ : ℝ → ℂ) u := by
      simpa using continuous_FourierIntegral (ψ : W21)
    have hcont_scaled : Continuous fun u : ℝ => 𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi)) :=
      hcont.comp (by continuity)
    exact hcont_scaled.aestronglyMeasurable.norm
  exact hmaj_int_norm.mono' hmeas hle_norm
lemma exists_bound_norm_G_on_tsupport
    (hG : ContinuousOn G {s : ℂ | 1 ≤ s.re})
    (ψ : CS 2 ℂ) :
    ∃ K : ℝ, ∀ t : ℝ, t ∈ tsupport (ψ : ℝ → ℂ) →
      ‖G (1 + t * Complex.I)‖ ≤ K := by
  let s : Set ℝ := tsupport (ψ : ℝ → ℂ)
  have hscompact : IsCompact s := by
    simpa [s] using (ψ.h2.isCompact : IsCompact (tsupport (ψ : ℝ → ℂ)))
  have hphi_cont : Continuous (fun t : ℝ => (1 : ℂ) + t * Complex.I) := by continuity
  have hphi_maps :
      Set.MapsTo (fun t : ℝ => (1 : ℂ) + t * Complex.I) s {z : ℂ | 1 ≤ z.re} := by
    intro t ht
    simp
  have hGcomp : ContinuousOn (fun t : ℝ => G ((1 : ℂ) + t * Complex.I)) s :=
    hG.comp hphi_cont.continuousOn hphi_maps
  have hnorm_contOn : ContinuousOn (fun t : ℝ => ‖G ((1 : ℂ) + t * Complex.I)‖) s := hGcomp.norm
  have hbdd : BddAbove ((fun t : ℝ => ‖G ((1 : ℂ) + t * Complex.I)‖) '' s) :=
    (hscompact.image_of_continuousOn hnorm_contOn).bddAbove
  refine ⟨sSup ((fun t : ℝ => ‖G ((1 : ℂ) + t * Complex.I)‖) '' s), ?_⟩
  intro t ht
  have : ‖G ((1 : ℂ) + t * Complex.I)‖ ∈
      (fun t : ℝ => ‖G ((1 : ℂ) + t * Complex.I)‖) '' s := ⟨t, ht, rfl⟩
  exact le_csSup hbdd this
lemma norm_integrand_le_K_mul_norm_psi
    {x K : ℝ}
    (hx : 0 < x)
    (hK : ∀ t : ℝ, t ∈ Function.support ψ → ‖G (1 + t * Complex.I)‖ ≤ K) :
    ∀ t : ℝ,
      ‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖ ≤ K * ‖ψ t‖ := by
  intro t
  by_cases ht : t ∈ Function.support ψ
  · have hxnorm : ‖((x : ℂ) ^ (t * Complex.I))‖ = 1 := norm_x_cpow_it x t hx
    calc
      ‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖
          = ‖G (1 + t * Complex.I)‖ * ‖ψ t‖ * ‖((x : ℂ) ^ (t * Complex.I))‖ := by
              simp [mul_left_comm, mul_comm]
      _   = ‖G (1 + t * Complex.I)‖ * ‖ψ t‖ * 1 := by simp [hxnorm]
      _   ≤ K * ‖ψ t‖ := by
            have hGle : ‖G (1 + t * Complex.I)‖ ≤ K := hK t ht
            have : ‖G (1 + t * Complex.I)‖ * ‖ψ t‖ ≤ K * ‖ψ t‖ :=
              mul_le_mul_of_nonneg_right hGle (norm_nonneg _)
            simpa [mul_assoc, mul_left_comm, mul_comm] using this
  · have hψ0 : ψ t = 0 := by
      by_contra hψ0
      exact ht (by simpa [Function.support] using hψ0)
    simp [hψ0, mul_comm]
lemma norm_error_integral_le
    (ψ : ℝ → ℂ) (x K : ℝ)
    (hGline_meas : Measurable (fun t : ℝ => G (1 + t * I)))
    (hψ_meas : AEStronglyMeasurable ψ)
    (hx : 0 < x)
    (hK : ∀ t : ℝ, t ∈ Function.support ψ → ‖G (1 + t * Complex.I)‖ ≤ K)
    (hψ : Integrable (fun t : ℝ => ‖ψ t‖) ) :
    ‖∫ t : ℝ, (G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖
      ≤ K * (∫ t : ℝ, ‖ψ t‖) := by
  have h1 : ‖∫ t : ℝ, (G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖
        ≤ ∫ t : ℝ, ‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖ := by
    simpa using (norm_integral_le_integral_norm
        (f := fun t : ℝ => (G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))))
  have hmeas_main : AEStronglyMeasurable
        (fun t : ℝ => (G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))) := by
    have hG' : AEMeasurable fun t : ℝ => G (1 + t * Complex.I) := hGline_meas.aemeasurable
    have hψ_meas' : AEMeasurable ψ := hψ_meas.aemeasurable
    have hx_ne : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
    have hx_ne' : NeZero (x : ℂ) := ⟨hx_ne⟩
    have hxpow_meas : AEMeasurable fun t : ℝ => ((x : ℂ) ^ (t * Complex.I)) := by
      have hcontℂ : Continuous fun z : ℂ => ((x : ℂ) ^ z) :=
        continuous_const_cpow (z := (x : ℂ))
      have hcont : Continuous fun t : ℝ => ((x : ℂ) ^ ((t : ℂ) * Complex.I)) :=
        hcontℂ.comp (by
          have h : Continuous fun t : ℝ => (t : ℂ) * Complex.I := by
            exact (continuous_ofReal.mul continuous_const).congr fun t => rfl
          simpa [mul_comm] using h)
      exact hcont.measurable.aemeasurable
    have hGψ_meas : AEMeasurable fun t : ℝ => (G (1 + t * Complex.I)) * (ψ t) := hG'.mul hψ_meas'
    have htotal : AEMeasurable (fun t : ℝ =>
            (G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))) :=
      hGψ_meas.mul hxpow_meas
    exact htotal.aestronglyMeasurable
  have hpt : (fun t : ℝ =>
          ‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖)
        ≤ᵐ[volume] (fun t : ℝ => K * ‖ψ t‖) := by
    refine Eventually.of_forall ?_
    intro t
    exact norm_integrand_le_K_mul_norm_psi (hx := hx) (hK := hK) t
  have hR : Integrable (fun t : ℝ => K * ‖ψ t‖) := hψ.const_mul K
  have hL : Integrable (fun t : ℝ =>
        ‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖) := by
      have hpt_norm :
          (fun t : ℝ => ‖‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖‖)
            ≤ᵐ[volume] (fun t : ℝ => K * ‖ψ t‖) := hpt.mono (by
          intro t ht
          simpa [norm_mul, mul_comm, mul_left_comm, mul_assoc] using ht)
      exact hR.mono' hmeas_main.norm hpt_norm
  have h2 : (∫ t : ℝ, ‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖)
        ≤ ∫ t : ℝ, K * ‖ψ t‖ := integral_mono_ae (μ := (volume : Measure ℝ)) hL hR hpt
  have h3 : (∫ t : ℝ, K * ‖ψ t‖) = K * (∫ t : ℝ, ‖ψ t‖) := by
    simp [integral_const_mul]
  calc
    ‖∫ t : ℝ, (G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖
        ≤ ∫ t : ℝ, ‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖ := h1
    _   ≤ ∫ t : ℝ, K * ‖ψ t‖ := h2
    _   = K * (∫ t : ℝ, ‖ψ t‖) := h3
lemma crude_upper_bound
    (hpos : 0 ≤ f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (ψ : CS 2 ℂ)
    (hψpos : ∀ y, 0 ≤ (𝓕 (ψ : ℝ → ℂ) y).re ∧ (𝓕 (ψ : ℝ → ℂ) y).im = 0) :
    ∃ B : ℝ, ∀ x : ℝ, 0 < x → ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))‖ ≤ B := by
  have hψ_int : MeasureTheory.Integrable (ψ : ℝ → ℂ) := by
    simpa using (ψ.h1.continuous.integrable_of_hasCompactSupport ψ.h2)
  have hψ_norm_int : MeasureTheory.Integrable (fun t : ℝ => ‖(ψ : ℝ → ℂ) t‖) :=
    hψ_int.norm
  have hψ_meas : MeasureTheory.AEStronglyMeasurable (ψ : ℝ → ℂ) :=
    hψ_int.aestronglyMeasurable
  rcases exists_bound_norm_G_on_tsupport (G := G) hG ψ with ⟨K, hK_ts⟩
  have hK_support :
      ∀ t : ℝ, t ∈ Function.support (ψ : ℝ → ℂ) → ‖G (1 + t * Complex.I)‖ ≤ K := by
    have hbnG (hKts : ∀ t : ℝ, t ∈ tsupport ψ → ‖G (1 + t * Complex.I)‖ ≤ K) :
      ∀ t : ℝ, t ∈ Function.support ψ → ‖G (1 + t * Complex.I)‖ ≤ K := by
      intro t ht
      exact hKts t ((subset_tsupport ψ) ht)
    exact hbnG hK_ts
  have hGline_meas : Measurable (fun t : ℝ => G (1 + t * Complex.I)) := by
    have hline_cont : Continuous (fun t : ℝ => (1 : ℂ) + t * Complex.I) := by
      continuity
    have hmem : ∀ t : ℝ, ((1 : ℂ) + t * Complex.I) ∈ {s : ℂ | 1 ≤ s.re} := by
      intro t
      simp
    have hcont : Continuous (G ∘ fun t : ℝ => (1 : ℂ) + t * Complex.I) :=
      hG.comp_continuous hline_cont hmem
    simpa [Function.comp_def] using hcont.measurable
  have hF_norm_int :
      MeasureTheory.Integrable (fun u : ℝ => ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖) :=
    integrable_norm_fourier_scaled_of_CS2 ψ
  have hF_meas :
      MeasureTheory.AEStronglyMeasurable
        (fun u : ℝ => 𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))) := by
    have hcont : Continuous fun u : ℝ => 𝓕 (ψ : ℝ → ℂ) u := by
      simpa using continuous_FourierIntegral (ψ : W21)
    have hcont_scaled : Continuous fun u : ℝ => 𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi)) :=
      hcont.comp (by continuity)
    exact hcont_scaled.aestronglyMeasurable
  have hF_int :
      MeasureTheory.Integrable (fun u : ℝ => 𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))) :=
    by
      have hfin_norm :
          MeasureTheory.HasFiniteIntegral
            (fun u : ℝ => ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖) :=
        hF_norm_int.hasFiniteIntegral
      have hfin :
          MeasureTheory.HasFiniteIntegral
            (fun u : ℝ => 𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))) := by
        simpa [MeasureTheory.hasFiniteIntegral_iff_norm] using hfin_norm
      exact ⟨hF_meas, hfin⟩
  refine ⟨K * (∫ t : ℝ, ‖(ψ : ℝ → ℂ) t‖)
            + ‖A‖ * (∫ u : ℝ, ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖), ?_⟩
  intro x hx
  set I : ℂ := ∫ u in Set.Ici (-Real.log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi)) with hI
  have hlim :=
    limiting_fourier_variant (f := f) (A := A) (G := G)
      hpos hG hG' hf ψ hψpos hx
  have hlim' :
      (∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * Real.pi) * Real.log (n / x)))
        - A * I
      = ∫ (t : ℝ), (G (1 + t * Complex.I)) * (ψ t) * x ^ (t * Complex.I) := by
    simpa [hI] using hlim
  have htsum :
      (∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * Real.pi) * Real.log (n / x)))
      = (∫ (t : ℝ), (G (1 + t * Complex.I)) * (ψ t) * x ^ (t * Complex.I)) + A * I := by
    have h' :
        (∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * Real.pi) * Real.log (n / x)))
          = (∫ (t : ℝ), (G (1 + t * Complex.I)) * (ψ t) * x ^ (t * Complex.I)) + A * I :=
      eq_add_of_sub_eq hlim'
    simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using h'
  have hRHS_bound :
      ‖∫ (t : ℝ), (G (1 + t * Complex.I)) * (ψ t) * x ^ (t * Complex.I)‖
        ≤ K * (∫ t : ℝ, ‖(ψ : ℝ → ℂ) t‖) :=
    norm_error_integral_le (G := G) (ψ := (ψ : ℝ → ℂ)) (x := x) (K := K)
      hGline_meas hψ_meas hx hK_support hψ_norm_int
  have hA_bound :
      ‖A * I‖ ≤ ‖A‖ * (∫ u : ℝ, ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖) := by
    have hF_on : MeasureTheory.IntegrableOn
        (fun u : ℝ => 𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi)))
        (Set.Ici (-Real.log x)) :=
      hF_int.integrableOn
    simpa [hI] using
      norm_mul_integral_Ici_le_integral_norm (A := A)
        (F := fun u : ℝ => 𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi)))
        (a := -Real.log x) hF_on hF_norm_int
  have htsum_std :
      (∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * Real.pi) * Real.log ((n : ℝ) / x)))
        = (∫ (t : ℝ), (G (1 + t * Complex.I)) * (ψ t) * x ^ (t * Complex.I)) + A * I := by
    simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using htsum
  have hbound :
      ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ)
          (1 / (2 * Real.pi) * Real.log ((n : ℝ) / x))‖
        ≤ K * (∫ t : ℝ, ‖(ψ : ℝ → ℂ) t‖)
          + ‖A‖ * (∫ u : ℝ, ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖) := by
    have hnorm :
        ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ)
            (1 / (2 * Real.pi) * Real.log ((n : ℝ) / x))‖ =
          ‖(∫ (t : ℝ), (G (1 + t * Complex.I)) * (ψ t) * x ^ (t * Complex.I)) + A * I‖ :=
      congrArg norm htsum_std
    calc
      ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ)
          (1 / (2 * Real.pi) * Real.log ((n : ℝ) / x))‖
          = ‖(∫ (t : ℝ), (G (1 + t * Complex.I)) * (ψ t) * x ^ (t * Complex.I)) + A * I‖ := hnorm
      _ ≤ ‖∫ (t : ℝ), (G (1 + t * Complex.I)) * (ψ t) * x ^ (t * Complex.I)‖ + ‖A * I‖ :=
            norm_add_le _ _
      _ ≤ K * (∫ t : ℝ, ‖(ψ : ℝ → ℂ) t‖)
          + ‖A‖ * (∫ u : ℝ, ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖) :=
            add_le_add hRHS_bound hA_bound
  exact hbound
lemma Real.fourierIntegral_convolution {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    𝓕 (convolution f g (ContinuousLinearMap.mul ℝ ℂ) volume) = 𝓕 f * 𝓕 g := by
  ext y
  simp only [Pi.mul_apply, FourierTransform.fourier, MeasureTheory.convolution,
    VectorFourier.fourierIntegral, ContinuousLinearMap.mul_apply']
  have h_int : Integrable (fun p : ℝ × ℝ ↦ 𝐞 (-(y * p.1)) • (f p.2 * g (p.1 - p.2))) := by
    try simp only [Circle.smul_def, smul_eq_mul]
    refine (Integrable.convolution_integrand (ContinuousLinearMap.mul ℝ ℂ) hf hg).bdd_mul
      (c := 1) ?_ ?_
    · exact (continuous_subtype_val.comp (Real.continuous_fourierChar.comp
        (by fun_prop : Continuous fun p : ℝ × ℝ => -(y * p.1)))).aestronglyMeasurable
    · filter_upwards with p; exact le_of_eq (Circle.norm_coe _)
  calc ∫ v, 𝐞 (-(y * v)) • ∫ t, f t * g (v - t)
      = ∫ v, ∫ t, 𝐞 (-(y * v)) • (f t * g (v - t)) := by
        simp only [Circle.smul_def, smul_eq_mul, ← integral_const_mul]
    _ = ∫ t, ∫ v, 𝐞 (-(y * v)) • (f t * g (v - t)) := integral_integral_swap h_int
    _ = ∫ t, f t • ∫ v, 𝐞 (-(y * v)) • g (v - t) := by
        simp only [Circle.smul_def, smul_eq_mul, mul_left_comm, integral_const_mul]
    _ = ∫ t, f t • ∫ u, 𝐞 (-(y * (u + t))) • g u := by
        congr 1; ext t
        rw [← integral_add_right_eq_self (fun v ↦ 𝐞 (-(y * v)) • g (v - t)) t]; simp
    _ = ∫ t, f t • ∫ u, (𝐞 (-(y * t)) * 𝐞 (-(y * u))) • g u := by
        congr 2 with t; congr 1
        simp only [mul_add, neg_add, mul_comm, Real.fourierChar.map_add_eq_mul]
    _ = ∫ t, 𝐞 (-(y * t)) • f t • ∫ u, 𝐞 (-(y * u)) • g u := by
        congr 1; ext t
        simp only [mul_smul, Circle.smul_def, smul_eq_mul, integral_const_mul]; ring
    _ = (∫ t, 𝐞 (-(y * t)) • f t) * ∫ u, 𝐞 (-(y * u)) • g u := by
        simp only [Circle.smul_def, smul_eq_mul, ← mul_assoc, integral_mul_const]
lemma Real.fourierIntegral_conj_neg {f : ℝ → ℂ} (y : ℝ) :
    𝓕 (fun x ↦ conj (f (-x))) y = conj (𝓕 f y) := by
  simp only [fourier_real_eq]
  have h_conj : ∀ x, 𝐞 (-(x * y)) • conj (f (-x)) = conj (𝐞 (x * y) • f (-x)) := fun x ↦ by
    simp only [Circle.smul_def, Real.fourierChar_apply, map_mul, smul_eq_mul, neg_mul,
      Complex.ofReal_neg, mul_neg]
    congr 1
    rw [← Complex.exp_conj]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, mul_neg]
  calc ∫ x, 𝐞 (-(x * y)) • conj (f (-x))
      = ∫ x, conj (𝐞 (x * y) • f (-x)) := by congr 1; ext x; exact h_conj x
    _ = conj (∫ x, 𝐞 (x * y) • f (-x)) := integral_conj
    _ = conj (∫ x, 𝐞 (-(x * y)) • f x) := by
        rw [← integral_neg_eq_self (fun x => 𝐞 (-(x * y)) • f x)]
        congr 2 with x; ring_nf
lemma auto_cheby_exists_smooth_nonneg_fourier_kernel :
    ∃ (ψ : ℝ → ℂ), ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
    (∀ y, 0 ≤ (𝓕 ψ y).re ∧ (𝓕 ψ y).im = 0) ∧ 0 < (𝓕 ψ 0).re := by
  obtain ⟨φ_real, hφSmooth, hφCompact, hφIcc, _, hφsupp⟩ :=
    smooth_urysohn_support_Ioo (a := 1/2) (b := 1) (c := 1) (d := 2) (by norm_num) (by norm_num)
  let φ : ℝ → ℂ := Complex.ofReal ∘ φ_real
  let φ_rev : ℝ → ℂ := fun x ↦ conj (φ (-x))
  let ψ_fun : ℝ → ℂ := convolution φ φ_rev (ContinuousLinearMap.mul ℝ ℂ) volume
  have hφSmooth' : ContDiff ℝ ∞ φ := contDiff_ofReal.comp hφSmooth
  have hφCompact' : HasCompactSupport φ := hφCompact.comp_left rfl
  have hφRevSmooth : ContDiff ℝ ∞ φ_rev := Complex.conjCLE.contDiff.comp (hφSmooth'.comp contDiff_neg)
  have hφRevCompact : HasCompactSupport φ_rev := (hφCompact'.comp_homeomorph (Homeomorph.neg ℝ)).comp_left (by simp)
  have hφInt : Integrable φ := hφSmooth'.continuous.integrable_of_hasCompactSupport hφCompact'
  have hφRevInt : Integrable φ_rev := hφRevSmooth.continuous.integrable_of_hasCompactSupport hφRevCompact
  have hψSmooth : ContDiff ℝ ∞ ψ_fun := by
    convert hφRevCompact.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
      (hφSmooth'.continuous.locallyIntegrable (μ := volume)) hφRevSmooth
  have hψCompact : HasCompactSupport ψ_fun :=
    HasCompactSupport.convolution (ContinuousLinearMap.mul ℝ ℂ) hφCompact' hφRevCompact
  refine ⟨ψ_fun, hψSmooth, hψCompact, fun y ↦ ?_, ?_⟩
  · rw [Real.fourierIntegral_convolution hφInt hφRevInt, Pi.mul_apply,
      Real.fourierIntegral_conj_neg y, mul_comm, ← Complex.normSq_eq_conj_mul_self]
    exact ⟨Complex.normSq_nonneg _, rfl⟩
  · have hφ_nonneg : ∀ x, 0 ≤ φ_real x := fun x ↦ by
      have hx := hφIcc x; by_cases h : x ∈ Set.Icc (1:ℝ) 1
      · simp only [Set.indicator_of_mem h, Pi.one_apply] at hx; linarith
      · simp only [Set.indicator_of_notMem h] at hx; exact hx
    have hvol_supp : (1 : ENNReal) ≤ volume (Function.support φ_real) := by
      have hsub : Set.Ico (1:ℝ) 2 ⊆ Function.support φ_real := fun x hx ↦
        hφsupp.symm ▸ Set.mem_Ioo.mpr ⟨by linarith [hx.1], hx.2⟩
      calc _ = volume (Set.Ico (1:ℝ) 2) := by simp [Real.volume_Ico]; norm_num
           _ ≤ _ := volume.mono hsub
    have hφint_pos : 0 < ∫ x, φ_real x :=
      (integral_pos_iff_support_of_nonneg_ae (.of_forall hφ_nonneg)
        (hφSmooth.continuous.integrable_of_hasCompactSupport hφCompact)).2
        (lt_of_lt_of_le (by simp) hvol_supp)
    have hFφ0_re : 0 < (𝓕 φ 0).re := by
      simp only [φ, fourier_real_eq, mul_zero, neg_zero, AddChar.map_zero_eq_one, one_smul,
        Function.comp_apply]
      have hint : Integrable (fun x => (φ_real x : ℂ)) :=
        (hφSmooth.continuous.integrable_of_hasCompactSupport hφCompact).ofReal
      calc (∫ x, (φ_real x : ℂ)).re = ∫ x, (φ_real x : ℂ).re := (integral_re hint).symm
        _ = ∫ x, φ_real x := by simp only [Complex.ofReal_re]
        _ > 0 := hφint_pos
    rw [Real.fourierIntegral_convolution hφInt hφRevInt, Pi.mul_apply,
      Real.fourierIntegral_conj_neg 0, mul_comm, ← Complex.normSq_eq_conj_mul_self]
    exact Complex.normSq_pos.2 (fun h ↦ (ne_of_gt hFφ0_re) (by simp [h]))
lemma auto_cheby_fourier_summable (hpos : 0 ≤ f) (hf : ∀ σ', 1 < σ' → Summable (nterm f σ'))
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (ψ : ℝ → ℂ) (hψSmooth : ContDiff ℝ ∞ ψ) (hψCompact : HasCompactSupport ψ)
    (hψpos : ∀ y, 0 ≤ (𝓕 ψ y).re ∧ (𝓕 ψ y).im = 0) (x : ℝ) (hx : 1 ≤ x) :
    Summable fun n ↦ (f n : ℂ) / n * 𝓕 ψ (1 / (2 * π) * Real.log (n / x)) := by
  let ψCS : CS 2 ℂ := ⟨ψ, hψSmooth.of_le (by norm_cast), hψCompact⟩
  let S : ℝ → ℂ := fun σ' ↦ ∑' n, term (f · : ℕ → ℂ) σ' n * 𝓕 ψCS.toFun (1 / (2 * π) * Real.log (n / x))
  let Pole : ℝ → ℂ := fun σ' ↦ (A : ℂ) * (x ^ (1 - σ') : ℝ) *
    ∫ u in Set.Ici (-Real.log x), (rexp (-u * (σ' - 1)) : ℂ) * 𝓕 (W21.ofCS2 ψCS).toFun (u / (2 * π))
  let RHS : ℝ → ℂ := fun σ' ↦ ∫ t : ℝ, G (σ' + t * I) * ψCS.toFun t * (x : ℂ) ^ (t * I)
  have l2 := limiting_fourier_lim2 (A := A) (x := x) ψCS hx
  have l3 := limiting_fourier_lim3 (G := G) hG ψCS hx
  have haux : (fun σ' ↦ S σ' - Pole σ') =ᶠ[𝓝[>] 1] RHS := eventually_nhdsWithin_of_forall fun σ' hσ' ↦ by
    simpa [S, Pole, RHS] using limiting_fourier_aux hG' hf ψCS hx σ' hσ'
  have hS_tendsto : Tendsto S (𝓝[>] 1) (𝓝 (RHS 1 + A * ∫ u in Set.Ici (-Real.log x),
      𝓕 (W21.ofCS2 ψCS).toFun (u / (2 * π)))) := by
    have hS_decomp :
        (fun σ' : ℝ => (S σ' - Pole σ') + Pole σ') =ᶠ[𝓝[>] 1] S := by
      exact Eventually.of_forall fun σ' => by simp
    simpa [Pole, RHS] using ((l3.congr' haux.symm).add l2).congr' hS_decomp
  have hbounded : BoundedAtFilter (𝓝[>] 1) (fun σ' ↦ ‖S σ'‖) := by
    simp only [BoundedAtFilter]
    let L := ‖RHS 1 + A * ∫ u in Set.Ici (-Real.log x), 𝓕 (W21.ofCS2 ψCS).toFun (u / (2 * π))‖
    have : ∀ᶠ σ' in 𝓝[>] 1, ‖S σ'‖ < L + 1 :=
      hS_tendsto.norm.eventually_lt tendsto_const_nhds (lt_add_one L)
    exact Asymptotics.IsBigO.of_bound (L + 1) (by filter_upwards [this] with σ h; simpa using h.le)
  let y : ℕ → ℝ := fun n ↦ (1 / (2 * π)) * Real.log (n / x)
  let w : ℕ → ℝ := fun n ↦ (𝓕 ψCS.toFun (y n)).re
  have hw : ∀ n, 0 ≤ w n := fun n ↦ (hψpos (y n)).1
  let rt : ℝ → ℕ → ℝ := fun σ n ↦ if n = 0 then 0 else f n / (n : ℝ) ^ σ * w n
  have rt_nn σ n : 0 ≤ rt σ n := by
    simp only [rt]; split_ifs with hn
    · rfl
    · exact mul_nonneg (div_nonneg (hpos n) (Real.rpow_pos_of_pos (Nat.cast_pos.mpr
        (Nat.pos_of_ne_zero hn)) σ).le) (hw n)
  have hS_eq σ' (hσ' : 1 < σ') : S σ' = ↑(∑' n, rt σ' n) := by
    rw [Complex.ofReal_tsum]; apply tsum_congr; intro n
    simp only [rt, term, LSeries.term, y, w, one_div, mul_inv_rev]
    split_ifs with hn <;> simp only [hn, CharP.cast_eq_zero, Complex.ofReal_zero, zero_mul,
      Complex.ofReal_mul, Complex.ofReal_div]
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]; congr 1
    exact Complex.ext rfl (hψpos _).2
  have hMono n : AntitoneOn (fun σ ↦ rt σ n) (Set.Ioi 1) := fun σ₁ _ σ₂ _ h ↦ by
    simp only [rt]; split_ifs with hn; · rfl
    apply mul_le_mul_of_nonneg_right _ (hw n)
    apply div_le_div_of_nonneg_left (hpos n) (Real.rpow_pos_of_pos (Nat.cast_pos.mpr
      (Nat.pos_of_ne_zero hn)) σ₁)
    exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hn)) h
  have hT_bdd : BoundedAtFilter (𝓝[>] 1) fun σ ↦ ∑' n, rt σ n := by
    rw [BoundedAtFilter, Asymptotics.isBigO_iff] at hbounded ⊢
    obtain ⟨C, hC⟩ := hbounded
    refine ⟨C, ?_⟩
    filter_upwards [hC, self_mem_nhdsWithin] with σ hnorm hσ
    rw [hS_eq σ hσ] at hnorm; simpa using hnorm
  have hSumm σ (hσ : 1 < σ) : Summable (rt σ ·) := by
    simpa [rt, w, y] using limiting_fourier_variant_lim1_aux ψCS hpos hf hψpos σ hσ
  have hSumm_1 : Summable (rt 1 ·) := by
    let σ_seq : ℕ → ℝ := fun k ↦ 1 + 1 / ((k : ℝ) + 1)
    have hσ_gt k : 1 < σ_seq k := by simp only [σ_seq, lt_add_iff_pos_right, one_div]; positivity
    have h_tendsto : Tendsto σ_seq atTop (𝓝[>] 1) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, by filter_upwards with k; exact hσ_gt k⟩
      have : Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 1)) atTop (𝓝 0) := by
        simp only [one_div]; exact (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).inv_tendsto_atTop
      simpa [σ_seq] using tendsto_const_nhds.add this
    have h_ptwise n : Tendsto (fun k ↦ rt (σ_seq k) n) atTop (𝓝 (rt 1 n)) := by
      simp only [rt]; split_ifs with hn; · exact tendsto_const_nhds
      refine ((tendsto_const_nhds.rpow (tendsto_nhdsWithin_iff.mp h_tendsto).1 (Or.inl ?_)).inv₀
        (by simp [hn])).const_mul (f n) |>.mul_const (w n)
      exact (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)).ne'
    obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp (hT_bdd.comp_tendsto h_tendsto)
    refine summable_of_sum_range_le (c := C) (rt_nn 1) fun m ↦ le_of_tendsto (tendsto_finsetSum _
        fun i _ ↦ h_ptwise i) ?_
    filter_upwards [h_tendsto.eventually self_mem_nhdsWithin, hC] with k hk hCk
    calc ∑ i ∈ Finset.range m, rt (σ_seq k) i
        ≤ ∑' n, rt (σ_seq k) n := (hSumm _ hk).sum_le_tsum _ fun n _ ↦ rt_nn _ n
      _ ≤ |∑' n, rt (σ_seq k) n| := le_abs_self _
      _ ≤ C := by simpa using hCk
  rw [show (fun n ↦ (f n : ℂ) / n * 𝓕 ψ (1 / (2 * π) * Real.log (n / x))) =
      Complex.ofRealCLM ∘ (rt 1 ·) from ?_]
  · exact hSumm_1.map Complex.ofRealCLM Complex.ofRealCLM.continuous
  ext n; simp only [rt, Real.rpow_one, one_div, w, y, Function.comp_apply]
  split_ifs with hn; · simp [hn]
  have him0 : (𝓕 ψCS.toFun ((2 * π)⁻¹ * Real.log (n / x))).im = 0 := (hψpos _).2
  have hre_eq : 𝓕 ψCS.toFun ((2 * π)⁻¹ * Real.log (n / x)) =
      Complex.ofReal ((𝓕 ψCS.toFun ((2 * π)⁻¹ * Real.log (n / x))).re) := by
    rw [← Complex.re_add_im (𝓕 ψCS.toFun _), him0]; simp
  conv_lhs => rw [show ψ = ψCS.toFun from rfl, hre_eq]
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast]
lemma auto_cheby_short_interval_bound (hpos : 0 ≤ f)
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (B : ℝ) (ψ : ℝ → ℂ) (hψSmooth : ContDiff ℝ ∞ ψ) (hψCompact : HasCompactSupport ψ)
    (hψpos : ∀ y, 0 ≤ (𝓕 ψ y).re ∧ (𝓕 ψ y).im = 0) (hψ0 : 0 < (𝓕 ψ 0).re)
    (hB_bound : ∀ x ≥ 1, ‖∑' n, f n / n * 𝓕 ψ (1 / (2 * Real.pi) * Real.log (n / x))‖ ≤ B) :
    ∃ (ε : ℝ) (C : ℝ), ε > 0 ∧ ε < 1 ∧ C > 0 ∧ ∀ x ≥ 1,
      ∑' n, (f n) * (Set.indicator (Set.Ioc ((1 - ε) * x) x) (fun _ ↦ 1) (n : ℝ)) ≤ C * x := by
  have hF : Continuous (𝓕 ψ) := VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by continuity) (hψSmooth.continuous.integrable_of_hasCompactSupport hψCompact)
  have hg : Continuous fun y ↦ (𝓕 ψ y).re := Complex.continuous_re.comp hF
  obtain ⟨δ, hδpos, hball⟩ := Metric.mem_nhds_iff.1 <|
    hg.continuousAt.preimage_mem_nhds (IsOpen.mem_nhds isOpen_Ioi (half_lt_self hψ0))
  let c := (𝓕 ψ 0).re / 2
  have hcpos : 0 < c := by dsimp only [c]; linarith
  have h_psi_ge_c : ∀ y, |y| < δ → c ≤ (𝓕 ψ y).re := fun y hy ↦ (hball (mem_ball_zero_iff.mpr hy)).le
  let ε := 1 - Real.exp (-2 * π * δ)
  have hε : 0 < ε ∧ ε < 1 := by
    have h1 : Real.exp (-2 * π * δ) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
    exact ⟨by simp only [ε]; linarith, by simp only [ε]; linarith [Real.exp_pos (-2 * π * δ)]⟩
  have hB_nonneg : 0 ≤ B := (norm_nonneg _).trans (hB_bound 1 le_rfl)
  refine ⟨ε, B / c + 1, hε.1, hε.2, by positivity, fun x hx ↦ ?_⟩
  have h_summable : Summable fun n ↦ (f n : ℂ) / n * 𝓕 ψ (1 / (2 * π) * Real.log (n / x)) :=
    auto_cheby_fourier_summable hpos hf hG hG' ψ hψSmooth hψCompact hψpos x hx
  have hx_pos : 0 < x := by linarith
  have h_sum_lower : c / x * ∑' n, f n * Set.indicator (Set.Ioc ((1 - ε) * x) x) 1 (n : ℝ)
      ≤ ∑' n, f n / n * (𝓕 ψ (1 / (2 * π) * Real.log (n / x))).re := by
    rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun n ↦ ?_) ?_ ?_
    · by_cases hn : (n : ℝ) ∈ Set.Ioc ((1 - ε) * x) x
      · rw [Set.indicator_of_mem hn, Pi.one_apply, mul_one]
        have hn_pos : 0 < (n : ℝ) := by nlinarith [hn.1, hε.2]
        let y := (1 / (2 * π)) * Real.log (n / x)
        have h_arg_small : |y| < δ := by
          have h2pi : 0 < 2 * π := by linarith [Real.pi_pos]
          simp only [y, abs_mul, abs_div, abs_one, abs_of_pos h2pi]
          field_simp [ne_of_gt h2pi]; rw [mul_comm, abs_lt]
          have h_log_lower : -2 * π * δ < Real.log (n / x) := by
            rw [← Real.log_exp (-2 * π * δ), Real.log_lt_log_iff (Real.exp_pos _) (by positivity)]
            have : Real.exp (-2 * π * δ) = 1 - ε := by simp only [ε]; ring
            rw [this]; field_simp; exact hn.1
          have h_log_upper : Real.log (n / x) ≤ 0 :=
            Real.log_nonpos (by positivity) (div_le_one_of_le₀ hn.2 hx_pos.le)
          constructor <;> nlinarith [Real.pi_pos]
        have h1 : x⁻¹ ≤ (n : ℝ)⁻¹ := by rw [inv_le_inv₀ hx_pos hn_pos]; exact hn.2
        have h2 : c ≤ (𝓕 ψ y).re := h_psi_ge_c y h_arg_small
        have hfn : 0 ≤ f n := hpos n
        have hre : 0 ≤ (𝓕 ψ y).re := (hψpos y).1
        have hn_inv : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr hn_pos.le
        calc c / x * f n = c * x⁻¹ * f n := by rw [div_eq_mul_inv]
          _ ≤ c * (n : ℝ)⁻¹ * f n := by gcongr
          _ ≤ (𝓕 ψ y).re * (n : ℝ)⁻¹ * f n := by gcongr
          _ = (n : ℝ)⁻¹ * (𝓕 ψ y).re * f n := by ring
          _ = f n / n * (𝓕 ψ y).re := by ring
      · rw [Set.indicator_of_notMem hn, mul_zero, mul_zero]
        exact mul_nonneg (div_nonneg (hpos n) (Nat.cast_nonneg n)) (hψpos _).1
    · refine summable_of_hasFiniteSupport <| (Set.finite_le_nat ⌊x⌋₊).subset fun n hn ↦ ?_
      simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or, Set.indicator_apply_ne_zero] at hn
      exact Nat.le_floor hn.2.2.1.2
    · rw [← Complex.summable_ofReal]; convert h_summable using 1; ext n
      rw [Complex.ofReal_mul, Complex.ofReal_div]
      norm_cast
      rw [Complex.ofReal_mul]
      congr 1
      apply Complex.ext
      · simp only [Complex.ofReal_re]
      · simp only [Complex.ofReal_im]; exact (hψpos _).2.symm
  have h_real_eq : ∑' n, f n / n * (𝓕 ψ (1 / (2 * π) * Real.log (n / x))).re =
      (∑' n, (f n : ℂ) / n * 𝓕 ψ (1 / (2 * π) * Real.log (n / x))).re := by
    rw [Complex.re_tsum h_summable]; congr with n
    rw [Complex.mul_re]; norm_cast; simp only [zero_mul, sub_zero]
  calc ∑' n, f n * Set.indicator (Set.Ioc ((1 - ε) * x) x) 1 (n : ℝ)
      = x / c * (c / x * ∑' n, f n * Set.indicator (Set.Ioc ((1 - ε) * x) x) 1 (n : ℝ)) := by
        field_simp [ne_of_gt hcpos, ne_of_gt hx_pos]
    _ ≤ x / c * B := by
        gcongr; rw [h_real_eq] at h_sum_lower
        exact h_sum_lower.trans ((Complex.re_le_norm _).trans (hB_bound x hx))
    _ = (B / c) * x := by field_simp [ne_of_gt hcpos]
    _ ≤ (B / c + 1) * x := by nlinarith
lemma auto_cheby_bootstrap_induction (hpos : 0 ≤ f)
    (h_short : ∃ (ε : ℝ) (C : ℝ), ε > 0 ∧ ε < 1 ∧ C > 0 ∧ ∀ x ≥ 1,
      ∑' n, (f n) * (Set.indicator (Set.Ioc ((1 - ε) * x) x) (fun _ ↦ 1) (n : ℝ)) ≤ C * x) :
    cheby f := by
  obtain ⟨ε, C₀, hε, hε1, hC₀, h_bound⟩ := h_short
  let C := C₀ / ε + f 0 + 1
  have hf0 : (0 : ℝ) ≤ f 0 := hpos 0
  have hdiv : 0 ≤ C₀ / ε := div_nonneg hC₀.le hε.le
  have hC : 0 ≤ C := by linarith
  refine ⟨C, fun n ↦ ?_⟩
  induction n using Nat.strong_induction_on with | h n ih =>
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n
    · simp [cumsum]
    · simp only [cumsum, Finset.sum_range_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hf0,
        Nat.cast_one, mul_one, C]
      linarith
  let x := (n : ℝ) - 1
  have hx : x ≥ 1 := by simp only [x, ge_iff_le, le_sub_iff_add_le]; norm_cast
  let m := ⌊(1 - ε) * x⌋₊ + 1
  have hm_lt : m < n := by
    simp only [m, x]
    have h1 : (1 - ε) * (n - 1 : ℝ) < (n - 1 : ℕ) := by
      calc (1 - ε) * (↑n - 1) < 1 * (↑n - 1) := by gcongr; linarith
        _ = ↑n - 1 := by ring
        _ = ↑(n - 1) := by simp [Nat.cast_sub (by omega : 1 ≤ n)]
    have h2 : ⌊(1 - ε) * (n - 1 : ℝ)⌋₊ < n - 1 :=
      (Nat.floor_lt (mul_nonneg (by linarith) (by linarith : (0 : ℝ) ≤ n - 1))).mpr h1
    omega
  have hm_gt : (m : ℝ) > (1 - ε) * x := by
    simp only [m, Nat.cast_add, Nat.cast_one, gt_iff_lt]
    exact Nat.lt_floor_add_one ((1 - ε) * x)
  have h_decomp : cumsum (fun k ↦ ‖(f k : ℂ)‖) n = cumsum (fun k ↦ ‖(f k : ℂ)‖) m + ∑ k ∈ Finset.Ico m n, f k := by
    simp only [cumsum, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpos _),
      Finset.sum_range_add_sum_Ico _ (by omega : m ≤ n)]
  have h_Ico : ∑ k ∈ Finset.Ico m n, f k ≤ C₀ * x := by
    calc ∑ k ∈ Finset.Ico m n, f k
        = ∑ k ∈ Finset.Ico m n, f k * Set.indicator (Set.Ioc ((1 - ε) * x) x) 1 (k : ℝ) := by
          refine Finset.sum_congr rfl fun k hk ↦ ?_
          have ⟨hkm, hkn⟩ := Finset.mem_Ico.mp hk
          have hk_gt : (k : ℝ) > (1 - ε) * x := by linarith [hm_gt, (Nat.cast_le (α := ℝ)).mpr hkm]
          have hk_le : (k : ℝ) ≤ x := by
            have h1 : k ≤ n - 1 := Nat.le_pred_of_lt hkn
            have h2 : (k : ℝ) ≤ (n - 1 : ℕ) := by exact_mod_cast h1
            simp only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one, x] at h2 ⊢; exact h2
          simp only [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hk_gt, hk_le⟩), Pi.one_apply, mul_one]
      _ ≤ ∑' k, f k * Set.indicator (Set.Ioc ((1 - ε) * x) x) 1 (k : ℝ) := by
          refine Summable.sum_le_tsum _ (fun k _ ↦ mul_nonneg (hpos k) (Set.indicator_nonneg (by simp) _)) ?_
          refine summable_of_hasFiniteSupport <| (Set.finite_le_nat ⌊x⌋₊).subset fun k hk ↦ ?_
          simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or, Set.indicator_apply_ne_zero] at hk
          exact Nat.le_floor hk.2.1.2
      _ ≤ C₀ * x := h_bound x hx
  have hm_le : (m : ℝ) ≤ (1 - ε) * x + 1 := by
    have hpos' : 0 ≤ (1 - ε) * x := mul_nonneg (by linarith) (by linarith : (0 : ℝ) ≤ x)
    simp only [m, Nat.cast_add, Nat.cast_one]
    linarith [Nat.floor_le hpos']
  have hnorm : ∀ k, ‖(f k : ℂ)‖ = f k := fun k ↦ by simp [abs_of_nonneg (hpos k)]
  simp only [hnorm] at h_decomp ih ⊢
  calc cumsum f n = cumsum f m + ∑ k ∈ Finset.Ico m n, f k := h_decomp
    _ ≤ C * m + C₀ * x := by linarith [ih m hm_lt, h_Ico]
    _ ≤ C * ((1 - ε) * x + 1) + C₀ * x := by nlinarith [hC]
    _ = (C * (1 - ε) + C₀) * x + C := by ring
    _ ≤ C * x + C := by
        have : C₀ ≤ C * ε := by
          calc C₀ = (C₀ / ε) * ε := by field_simp [ne_of_gt hε]
            _ ≤ (C₀ / ε + f 0 + 1) * ε := by gcongr; linarith [hpos 0]
            _ = C * ε := by simp only [C]
        nlinarith [hε, hε1, hx]
    _ ≤ C * n := by simp only [x]; ring_nf; linarith [hC]
lemma auto_cheby (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) : cheby f := by
  obtain ⟨ψ_fun, hψSmooth, hψCompact, hψpos, hψ0⟩ := auto_cheby_exists_smooth_nonneg_fourier_kernel
  obtain ⟨B, hB⟩ := crude_upper_bound hpos hG hG' hf ⟨ψ_fun, hψSmooth.of_le ENat.LEInfty.out, hψCompact⟩ hψpos
  exact auto_cheby_bootstrap_induction hpos <| auto_cheby_short_interval_bound hpos hf hG hG' B ψ_fun
    hψSmooth hψCompact hψpos hψ0 fun x hx ↦ hB x (by linarith)
theorem WienerIkeharaTheorem'' (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun N => cumsum f N / N) atTop (𝓝 A) :=
  WienerIkeharaTheorem' hpos hf (auto_cheby (f := f) (A := A) (G := G) hpos hf hG hG') hG hG'
end auto_cheby
theorem WeakPNT_AP_prelim {q : ℕ} {a : ℕ} (hq : q ≥ 1) (ha : Nat.Coprime a q) (ha' : a < q) :
    ∃ G: ℂ → ℂ, (ContinuousOn G {s | 1 ≤ s.re}) ∧
    (Set.EqOn G (fun s ↦ LSeries (fun n ↦ if n % q = a then Λ n else 0) s - 1 /
      ((Nat.totient q) * (s - 1))) {s | 1 < s.re}) := by
  have : NeZero q := NeZero.of_pos hq
  have hG : ∃ G : ℂ → ℂ, ContinuousOn G {s | 1 ≤ s.re} ∧ Set.EqOn G
      (fun s ↦ LSeries (fun n ↦ if (n : ZMod q) = a then Λ n else 0) s - (q.totient : ℂ)⁻¹ / (s - 1)) {s | 1 < s.re} := by
    use vonMangoldt.LFunctionResidueClassAux (a : ZMod q), vonMangoldt.continuousOn_LFunctionResidueClassAux (q := q) (a := a)
    have := vonMangoldt.eqOn_LFunctionResidueClassAux ((ZMod.isUnit_iff_coprime a q).mpr ha)
    convert this using 6; split <;> simp_all
  convert hG using 6
  · simp [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha']
  · rw [inv_eq_one_div, div_div]
lemma summable_vonMangoldt_div_rpow {s : ℝ} (hs : 1 < s) : Summable (fun n ↦ Λ n / n ^ s) := by
  have h_log_bound : ∀ n : ℕ, (Λ n : ℝ) ≤ Real.log n := fun n ↦ vonMangoldt_le_log
  suffices h_log_sum : Summable fun n : ℕ ↦ Real.log n / (n : ℝ) ^ s by
    exact .of_nonneg_of_le (fun n ↦ div_nonneg vonMangoldt_nonneg (by positivity))
      (fun n ↦ div_le_div_of_nonneg_right (h_log_bound n) (by positivity)) h_log_sum
  have h_log_le_n_eps : ∀ ε > 0, ∃ C > 0, ∀ n : ℕ, n ≥ 2 → Real.log n / (n : ℝ) ^ s ≤ C * (n : ℝ) ^ (ε - s) := by
    intro ε hε_pos
    obtain ⟨C, hC_pos, hC⟩ : ∃ C > 0, ∀ n : ℕ, n ≥ 2 → Real.log n ≤ C * (n : ℝ) ^ ε := by
      refine ⟨1 / ε, by positivity, fun n hn ↦ ?_⟩
      have := log_le_sub_one_of_pos (by positivity : 0 < (n : ℝ) ^ ε)
      rw [log_rpow (by positivity)] at this
      nlinarith [rpow_pos_of_pos (by positivity : 0 < (n : ℝ)) ε, mul_div_cancel₀ 1 hε_pos.ne']
    refine ⟨C, hC_pos, fun n hn ↦ ?_⟩
    rw [rpow_sub (by positivity)]
    exact le_trans (div_le_div_of_nonneg_right (hC n hn) (by positivity)) (by rw [div_eq_mul_inv]; ring_nf; norm_num)
  obtain ⟨C, _, hC⟩ : ∃ C > 0, ∀ n : ℕ, n ≥ 2 → Real.log n / (n : ℝ) ^ s ≤ C * (n : ℝ) ^ ((s - 1) / 2 - s) :=
    h_log_le_n_eps ((s - 1) / 2) (by linarith)
  rw [← summable_nat_add_iff 2]
  exact Summable.of_nonneg_of_le (fun n ↦ div_nonneg (log_nonneg (by norm_cast; omega))
    (rpow_nonneg (by positivity) _)) (fun n ↦ hC _ (by omega)) (Summable.mul_left _ <| by
      simpa using summable_nat_add_iff 2 |>.2 <| summable_nat_rpow.2 <| by linarith)
theorem WeakPNT_AP {q : ℕ} {a : ℕ} (hq : q ≥ 1) (ha : a.Coprime q) (ha' : a < q) :
    Tendsto (fun N ↦ cumsum (fun n ↦ if n % q = a then Λ n else 0) N / N) atTop (𝓝 (1 / q.totient)) := by
  have h_summable : ∀ s : ℝ, 1 < s → Summable (fun n ↦ (if n % q = a then Λ n else 0) / n ^ s) := by
    intro s hs
    refine .of_nonneg_of_le (fun n ↦ ?_) (fun n ↦ ?_) (summable_vonMangoldt_div_rpow hs)
    · split_ifs <;> positivity
    · split_ifs <;> norm_num; exact div_nonneg vonMangoldt_nonneg (by positivity)
  obtain ⟨G, hG₁, hG₂⟩ := WeakPNT_AP_prelim hq ha ha'
  convert WienerIkeharaTheorem'' _ _ _ _ using 1
  · use G
  · intro n
    simp_all only [ge_iff_le, one_div, mul_inv_rev, Pi.ofNat_apply]
    split
    next h => subst h; simp_all only [vonMangoldt_nonneg]
    next h => simp_all only [le_refl]
  · intro σ' hσ'
    specialize h_summable σ' hσ'
    simp_all only [ge_iff_le, one_div, mul_inv_rev]
    convert h_summable using 1
    ext
    simp only [nterm, norm_real, norm_eq_abs]
    ring_nf
    split_ifs <;> simp [*, mul_comm]
  · assumption
  · convert hG₂ using 3
    · exact tsum_congr fun n ↦ by cases n <;> aesop
    · norm_num [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
end
section
open ArithmeticFunction hiding log
open Nat hiding log
open Finset
open BigOperators Filter Real Asymptotics MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius ArithmeticFunction.Omega Chebyshev
theorem Asymptotics.IsEquivalent.add_isLittleO'' {α : Type*} {β : Type*} [NormedAddCommGroup β]
    {u : α → β} {v : α → β} {w : α → β} {l : Filter α}
    (huv : Asymptotics.IsEquivalent l u v) (hwu : (u - w) =o[l] v) :
    Asymptotics.IsEquivalent l w v := by
  rw [← sub_sub_self u w]
  exact sub_isLittleO huv hwu
lemma isLittleO_sqrt_mul_log : (fun x : ℝ ↦ x.sqrt * x.log) =o[atTop] _root_.id := by
  have : (fun x : ℝ ↦ x.sqrt * x.log) =o[atTop] fun x ↦ x := by
    refine (isLittleO_mul_iff_isLittleO_div ?_).mpr ?_
    · filter_upwards [eventually_gt_atTop 0] with x hx; exact (sqrt_ne_zero hx.le).mpr hx.ne'
    · convert isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2) using 2
      · rfl
      · rfl
      · rw [← sqrt_eq_rpow, div_sqrt, sqrt_eq_rpow]
  exact this
lemma tendsto_floor_add_one_div_self : Tendsto (fun x : ℝ ↦ (⌊x⌋₊ + 1 : ℝ) / x) atTop (nhds 1) := by
  have h := Asymptotics.isEquivalent_nat_floor (R := ℝ)
  have h' : IsEquivalent atTop (fun x : ℝ ↦ (⌊x⌋₊ : ℝ) + 1) _root_.id :=
    h.add_isLittleO (isLittleO_const_id_atTop 1)
  have hne : ∀ᶠ x : ℝ in atTop, _root_.id x ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact ne_of_gt hx
  convert (isEquivalent_iff_tendsto_one hne).mp h' using 1
  ext x
  rfl
lemma isTheta_self_div_const {c : ℝ} (hc : c ≠ 0) : (fun x : ℝ ↦ x) =Θ[atTop] fun x ↦ x / c := by
  have : (fun x : ℝ ↦ x / c) = fun x ↦ c⁻¹ * x := by ext x; ring
  exact this ▸ (isTheta_const_mul_left (inv_ne_zero hc)).mpr (isTheta_refl ..) |>.symm
lemma filter_prime_Iic_eq_Icc (n : ℕ) : filter Prime (Iic n) = filter Prime (Icc 1 n) := by
  ext p; simp only [mem_filter, mem_Iic, mem_Icc, and_congr_left_iff]
  exact fun hp ↦ ⟨fun h ↦ ⟨hp.one_lt.le, h⟩, fun ⟨_, h⟩ ↦ h⟩
lemma Icc_zero_eq_insert (n : ℕ) : Icc 0 n = insert 0 (Icc 1 n) := by
  ext m; simp [mem_Icc]; omega
noncomputable def R (x : ℝ) : ℝ := Psi x - x
theorem chebyshev_asymptotic_pnt
    {q : ℕ} {a : ℕ} (hq : q ≥ 1) (ha : a.Coprime q) (ha' : a < q) :
    (fun x ↦ ∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), if p % q = a then log p else 0) ~[atTop]
      fun x ↦ x / q.totient := by
  let ψ_aq : ℝ → ℝ := fun x ↦ ∑ n ∈ Icc 1 ⌊x⌋₊, if n % q = a then Λ n else 0
  have htot_pos : (0 : ℝ) < q.totient := cast_pos.mpr (totient_pos.mpr hq)
  have hψ_equiv : ψ_aq ~[atTop] fun x ↦ x / q.totient := by
    have hW := WeakPNT_AP hq ha ha'
    simp only [cumsum, ← Iio_eq_range] at hW
    have hψ_eq x : ψ_aq x = ∑ n ∈ Iio (⌊x⌋₊ + 1), if n % q = a then Λ n else 0 := by
      simp only [ψ_aq, show Icc 1 ⌊x⌋₊ = (Iio (⌊x⌋₊ + 1)).filter (1 ≤ ·) by
        ext n; simp [mem_Icc, mem_filter]; tauto, sum_filter]
      refine sum_congr rfl fun n _ ↦ ?_
      by_cases hn : 1 ≤ n <;> simp only [hn, ↓reduceIte]
      push Not at hn; interval_cases n; simp
    refine (isEquivalent_iff_tendsto_one ?_).mpr ?_
    · filter_upwards [eventually_ge_atTop 1] with x hx; exact div_ne_zero (by linarith) htot_pos.ne'
    have hlim1 : Tendsto (fun x : ℝ ↦ (∑ n ∈ Iio (⌊x⌋₊ + 1), if n % q = a then Λ n else 0) /
        (⌊x⌋₊ + 1 : ℝ)) atTop (nhds (1 / q.totient)) := by
      have heq : (fun x : ℝ ↦ (∑ n ∈ Iio (⌊x⌋₊ + 1), if n % q = a then Λ n else 0) /
          (⌊x⌋₊ + 1 : ℝ)) = (fun N ↦ (∑ n ∈ Iio N, if n % q = a then Λ n else 0) / N) ∘
          (fun x : ℝ ↦ ⌊x⌋₊ + 1) := by ext x; simp [Function.comp_apply]
      exact heq ▸ hW.comp ((tendsto_add_atTop_nat 1).comp tendsto_nat_floor_atTop)
    have hgoal_eq : (ψ_aq / fun x ↦ x / (q.totient : ℝ)) =
        fun x ↦ ψ_aq x / x * q.totient := by ext x; simp only [Pi.div_apply, div_div_eq_mul_div]; ring
    rw [hgoal_eq, show (1 : ℝ) = 1 / q.totient * 1 * q.totient by field_simp]
    refine Tendsto.mul ?_ tendsto_const_nhds
    have heq' : (fun x ↦ ψ_aq x / x) =ᶠ[atTop]
        fun x ↦ (∑ n ∈ Iio (⌊x⌋₊ + 1), if n % q = a then Λ n else 0) / (⌊x⌋₊ + 1 : ℝ) * ((⌊x⌋₊ + 1 : ℝ) / x) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      simp only [hψ_eq]; field_simp
    exact Tendsto.congr' heq'.symm (hlim1.mul tendsto_floor_add_one_div_self)
  refine hψ_equiv.add_isLittleO'' (IsBigO.trans_isLittleO (g := fun x ↦ 2 * x.sqrt * x.log) ?_ ?_)
  · rw [isBigO_iff']; refine ⟨1, one_pos, eventually_atTop.mpr ⟨2, fun x hx ↦ ?_⟩⟩
    simp only [Pi.sub_apply, norm_eq_abs, one_mul]
    have hdiff_nonneg : 0 ≤ ψ_aq x - ∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), if p % q = a then log p else 0 := by
      simp only [ψ_aq, sub_nonneg]
      calc (∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), if p % q = a then log p else (0 : ℝ))
          ≤ ∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), if p % q = a then Λ p else (0 : ℝ) :=
            sum_le_sum fun p hp ↦ by split_ifs <;> simp [vonMangoldt_apply_prime (mem_filter.mp hp).2]
        _ ≤ ∑ n ∈ Icc 1 ⌊x⌋₊, if n % q = a then Λ n else (0 : ℝ) :=
            sum_le_sum_of_subset_of_nonneg
              (fun p hp ↦ by simp only [mem_filter, mem_Iic, mem_Icc] at hp ⊢; exact ⟨hp.2.one_lt.le, hp.1⟩)
              (fun n _ _ ↦ by split_ifs <;> [exact vonMangoldt_nonneg; rfl])
    have hdiff_le : ψ_aq x - (∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), if p % q = a then log p else (0 : ℝ)) ≤ ψ x - θ x := by
      simp only [ψ_aq, Chebyshev.psi_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc]
      conv_rhs => rw [Icc_zero_eq_insert, sum_insert (by simp : (0 : ℕ) ∉ Icc 1 ⌊x⌋₊),
        show Λ 0 = 0 by simp only [ArithmeticFunction.map_zero], zero_add,
        show filter Nat.Prime (insert 0 (Icc 1 ⌊x⌋₊)) = filter Nat.Prime (Icc 1 ⌊x⌋₊) by
          simp [filter_insert, Nat.not_prime_zero]]
      rw [filter_prime_Iic_eq_Icc, ← sum_filter_add_sum_filter_not (Icc 1 ⌊x⌋₊) Nat.Prime,
        show (∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), if p % q = a then log p else (0 : ℝ)) =
          ∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), if p % q = a then Λ p else (0 : ℝ) from
          sum_congr rfl fun p hp ↦ by simp only [mem_filter] at hp; split_ifs <;> simp [vonMangoldt_apply_prime hp.2],
        ← sum_filter_add_sum_filter_not (Icc 1 ⌊x⌋₊) Nat.Prime,
        show (∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), Λ p) = ∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), log p from
          sum_congr rfl fun p hp ↦ vonMangoldt_apply_prime (mem_filter.mp hp).2]
      have h1 : (∑ n ∈ (Icc 1 ⌊x⌋₊).filter (¬Nat.Prime ·), if n % q = a then Λ n else (0 : ℝ)) ≤
          ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (¬Nat.Prime ·), Λ n :=
        sum_le_sum fun n _ ↦ by split_ifs <;> [exact le_refl _; exact vonMangoldt_nonneg]
      linarith
    rw [abs_of_nonneg hdiff_nonneg, abs_of_nonneg (by bound)]
    exact hdiff_le.trans ((le_abs_self _).trans (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith)))
  · simpa only [mul_assoc] using
      (isLittleO_sqrt_mul_log.const_mul_left 2).trans_isTheta (isTheta_self_div_const htot_pos.ne')
end
section
open Filter
namespace Erdos
theorem nth_le_sq_of_count_ge (p : ℕ → Prop) [DecidablePred p]
    (h : ∀ᶠ x : ℕ in atTop, (x : ℝ) / (4 * Real.log x) ≤ Nat.count p x) :
    ∀ᶠ j : ℕ in atTop, (Nat.nth p j : ℝ) ≤ ((j : ℝ) + 2) ^ 2 := by
  have hx : Tendsto (fun j : ℕ => (j + 2) ^ 2) atTop atTop :=
    tendsto_atTop_mono (fun j => by simp only [id_eq]; nlinarith) tendsto_id
  filter_upwards [hx.eventually h, eventually_ge_atTop 255] with j hcount hj
  set y : ℝ := (j : ℝ) + 2 with hy
  have hy257 : (257 : ℝ) ≤ y := by
    have : (255 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    simp only [hy]; linarith
  have hyx : (((j + 2) ^ 2 : ℕ) : ℝ) = y ^ 2 := by push_cast; ring
  have hs0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  have hs2 : Real.sqrt y ^ 2 = y := Real.sq_sqrt (by linarith)
  have hs16 : (16 : ℝ) ≤ Real.sqrt y := by
    have : (16 : ℝ) = Real.sqrt 256 := by
      rw [show (256 : ℝ) = 16 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [this]
    exact Real.sqrt_le_sqrt (by linarith)
  have hlogy : Real.log y ≤ 2 * Real.sqrt y := by
    have hsq : Real.log (Real.sqrt y) ≤ Real.sqrt y - 1 :=
      Real.log_le_sub_one_of_pos (by nlinarith)
    have hls : Real.log (Real.sqrt y) = Real.log y / 2 :=
      Real.log_sqrt (by linarith)
    linarith [hls ▸ hsq]
  have hlogpos : 0 < Real.log y := Real.log_pos (by linarith)
  have hcount' : y ^ 2 / (8 * Real.log y) ≤ (Nat.count p ((j + 2) ^ 2) : ℝ) := by
    have hlog : Real.log (((j + 2) ^ 2 : ℕ) : ℝ) = 2 * Real.log y := by
      rw [hyx, show y ^ 2 = y * y by ring,
        Real.log_mul (by linarith) (by linarith)]
      ring
    rw [hlog, hyx] at hcount
    calc y ^ 2 / (8 * Real.log y) = y ^ 2 / (4 * (2 * Real.log y)) := by ring_nf
    _ ≤ _ := hcount
  have h8 : 8 * Real.log y ≤ y := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ Real.sqrt y - 16 by linarith) hs0]
  have hjy : (j : ℝ) < y ^ 2 / (8 * Real.log y) := by
    rw [lt_div_iff₀ (by positivity)]
    have hjlt : (j : ℝ) < y := by rw [hy]; linarith
    nlinarith [mul_le_mul_of_nonneg_left h8 (Nat.cast_nonneg j : (0 : ℝ) ≤ j),
      mul_lt_mul_of_pos_right hjlt (show (0 : ℝ) < y by linarith)]
  have hjc : j < Nat.count p ((j + 2) ^ 2) := by
    have : (j : ℝ) < (Nat.count p ((j + 2) ^ 2) : ℝ) := lt_of_lt_of_le hjy hcount'
    exact_mod_cast this
  have hnth : Nat.nth p j < (j + 2) ^ 2 := Nat.nth_lt_of_lt_count hjc
  calc (Nat.nth p j : ℝ) ≤ (((j + 2) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hnth.le
  _ = y ^ 2 := hyx
noncomputable def q3 (j : ℕ) : ℕ := Nat.nth (fun n => n.Prime ∧ n % 4 = 3) j
noncomputable def p1 (i : ℕ) : ℕ := Nat.nth (fun n => n.Prime ∧ n % 4 = 1) i
theorem count_mod_four_ge {a : ℕ} (ha : a = 1 ∨ a = 3) :
    ∀ᶠ x : ℕ in atTop,
      (x : ℝ) / (4 * Real.log x) ≤ Nat.count (fun n => n.Prime ∧ n % 4 = a) x := by
  let S : ℝ → ℝ := fun x =>
    ∑ p ∈ Finset.Iic ⌊x⌋₊ with Nat.Prime p, if p % 4 = a then Real.log (p : ℝ) else 0
  have hcheb : Asymptotics.IsEquivalent Filter.atTop S
      (fun x : ℝ => x / (Nat.totient 4 : ℝ)) := by
    exact chebyshev_asymptotic_pnt (by norm_num)
      (by rcases ha with rfl | rfl <;> norm_num)
      (by rcases ha with rfl | rfl <;> norm_num)
  have hSreal : ∀ᶠ x : ℝ in atTop, (2 / 5 : ℝ) * x ≤ S x := by
    have hne : ∀ᶠ x : ℝ in atTop, x / (Nat.totient 4 : ℝ) ≠ 0 := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have hx0 : x ≠ 0 := by linarith
      norm_num [hx0]
    have ht : Tendsto (S / (fun x : ℝ => x / (Nat.totient 4 : ℝ))) atTop
        (nhds (1 : ℝ)) :=
      (Asymptotics.isEquivalent_iff_tendsto_one hne).mp hcheb
    have hratio : ∀ᶠ x : ℝ in atTop,
        (4 / 5 : ℝ) < (S / (fun x : ℝ => x / (Nat.totient 4 : ℝ))) x :=
      ht.eventually
        (isOpen_Ioi.mem_nhds (show (1 : ℝ) ∈ Set.Ioi (4 / 5 : ℝ) by norm_num))
    filter_upwards [hratio, eventually_ge_atTop (1 : ℝ)] with x hxratio hxge
    have hden : 0 < x / (Nat.totient 4 : ℝ) := by
      have htot : (Nat.totient 4 : ℝ) = 2 := by
        norm_num [show Nat.totient 4 = 2 by decide]
      rw [htot]
      linarith
    have hlt : (4 / 5 : ℝ) * (x / (Nat.totient 4 : ℝ)) < S x := by
      have := (lt_div_iff₀ hden).mp hxratio
      simpa [Pi.div_apply] using this
    have htot : (Nat.totient 4 : ℝ) = 2 := by
      norm_num [show Nat.totient 4 = 2 by decide]
    rw [htot] at hlt
    norm_num at hlt
    linarith
  have hSnat : ∀ᶠ n : ℕ in atTop, (2 / 5 : ℝ) * (n : ℝ) ≤ S n :=
    tendsto_natCast_atTop_atTop.eventually hSreal
  have hsucc : ∀ᶠ n : ℕ in atTop,
      ((n + 1 : ℕ) : ℝ) / (4 * Real.log ((n + 1 : ℕ) : ℝ)) ≤
        Nat.count (fun p => p.Prime ∧ p % 4 = a) (n + 1) := by
    filter_upwards [hSnat, eventually_ge_atTop 2] with n hS hn
    have hsum_eq :
        S n =
          ∑ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % 4 = a),
            Real.log (p : ℝ) := by
      change
        (∑ p ∈ Finset.Iic ⌊(n : ℝ)⌋₊ with Nat.Prime p,
            if p % 4 = a then Real.log (p : ℝ) else 0) =
          ∑ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % 4 = a),
            Real.log (p : ℝ)
      rw [Nat.floor_natCast]
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext p
        simp [and_assoc]
      · intro x hx
        rfl
    have hsum_le :
        S n ≤
          (Nat.count (fun p => p.Prime ∧ p % 4 = a) (n + 1) : ℝ) *
            Real.log ((n + 1 : ℕ) : ℝ) := by
      rw [hsum_eq, Nat.count_eq_card_filter_range]
      have hsum := Finset.sum_le_card_nsmul
        ((Finset.range (n + 1)).filter (fun p => p.Prime ∧ p % 4 = a))
        (fun p => Real.log (p : ℝ)) (Real.log ((n + 1 : ℕ) : ℝ)) ?_
      · simpa [nsmul_eq_mul] using hsum
      intro p hp
      have hpmem : p ∈ Finset.range (n + 1) ∧ (p.Prime ∧ p % 4 = a) := by
        simpa using hp
      have hpr : p.Prime := hpmem.2.1
      have hple : p ≤ n := Nat.lt_succ_iff.mp (by simpa using hpmem.1)
      have hp_pos : (0 : ℝ) < p := by exact_mod_cast hpr.pos
      exact Real.log_le_log hp_pos (by exact_mod_cast Nat.le_trans hple (Nat.le_succ n))
    have hlogpos : 0 < Real.log ((n + 1 : ℕ) : ℝ) := by
      exact Real.log_pos (by exact_mod_cast (show 1 < n + 1 by omega))
    rw [div_le_iff₀ (mul_pos (by norm_num) hlogpos)]
    have hnum : ((n + 1 : ℕ) : ℝ) / 4 ≤ (2 / 5 : ℝ) * (n : ℝ) := by
      have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
      push_cast
      nlinarith
    nlinarith [hnum, hS, hsum_le]
  rcases Filter.eventually_atTop.mp hsucc with ⟨N, hN⟩
  refine Filter.eventually_atTop.mpr ⟨N + 1, ?_⟩
  intro x hx
  have hxpos : 0 < x := by omega
  have hNx : N ≤ x - 1 := by omega
  have hx' := hN (x - 1) hNx
  have hxsub : x - 1 + 1 = x := Nat.sub_add_cancel (by omega)
  simpa [hxsub] using hx'
theorem q3_poly_bound : ∀ᶠ j in Filter.atTop, (q3 j : ℝ) ≤ ((j : ℝ) + 2) ^ 2 :=
  nth_le_sq_of_count_ge _ (count_mod_four_ge (Or.inr rfl))
theorem p1_poly_bound : ∀ᶠ i in Filter.atTop, (p1 i : ℝ) ≤ ((i : ℝ) + 2) ^ 2 :=
  nth_le_sq_of_count_ge _ (count_mod_four_ge (Or.inl rfl))
noncomputable def m (t : ℕ) : ℕ := ∏ i ∈ Finset.range t, p1 i
theorem infinite_setOf_q3 : {n | n.Prime ∧ n % 4 = 3}.Infinite := by
  have h : {p : ℕ | p.Prime ∧ p ≡ 3 [MOD 4]}.Infinite :=
    Nat.infinite_setOfPred_prime_and_modEq (by norm_num) (by decide)
  convert! h using 2 with n
theorem infinite_setOf_p1 : {n | n.Prime ∧ n % 4 = 1}.Infinite :=
  Nat.infinite_setOfPred_prime_modEq_one <| by decide
theorem q3_spec (j : ℕ) : (q3 j).Prime ∧ q3 j % 4 = 3 :=
  Nat.nth_mem_of_infinite infinite_setOf_q3 j
theorem p1_spec (i : ℕ) : (p1 i).Prime ∧ p1 i % 4 = 1 :=
  Nat.nth_mem_of_infinite infinite_setOf_p1 i
theorem q3_strictMono : StrictMono q3 :=
  Nat.nth_strictMono infinite_setOf_q3
theorem p1_strictMono : StrictMono p1 :=
  Nat.nth_strictMono infinite_setOf_p1
theorem m_ge (t : ℕ) : 2 ^ t ≤ m t := by
  calc 2 ^ t = ∏ _i ∈ Finset.range t, 2 := by simp
  _ ≤ m t := Finset.prod_le_prod' fun i _ => (p1_spec i).1.two_le
theorem log_m_le : ∃ c₁ : ℝ, 1 ≤ c₁ ∧ ∀ t : ℕ, Real.log (m t) ≤ c₁ * t * Real.log (t + 2) :=
  by
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ i ≥ N, (p1 i : ℝ) ≤ (i + 2) ^ 2 :=
      by
        exact
          Filter.eventually_atTop.mp (p1_poly_bound) |> fun ⟨N, hN⟩ =>
            ⟨N, fun i hi => mod_cast hN i hi⟩;
    set S := ∑ i ∈ Finset.range N, Real.log (p1 i) with hS_def
    have hS_nonneg : 0 ≤ S :=
      by
        exact
          Finset.sum_nonneg fun _ _ =>
            Real.log_nonneg <| mod_cast Nat.Prime.pos <| p1_spec _ |>.1;
    have h_log_m_le : ∀ t : ℕ, Real.log (m t) ≤ S + 2 * t * Real.log (t + 2) :=
      by
        intro t
        have h_log_m_le_step :
          ∀ i < t,
            Real.log (p1 i) ≤ 2 * Real.log (t + 2) + (if i < N then Real.log (p1 i) else 0) :=
          by
            intro i hi
            split_ifs with hiN
            · have hlog : 0 ≤ Real.log ((t : ℝ) + 2) :=
                Real.log_nonneg
                  (by
                    have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
                    linarith)
              linarith
            · simp only [add_zero]
              have hNi : N ≤ i := Nat.le_of_not_gt hiN
              have hp_pos : (0 : ℝ) < p1 i :=
                by
                  exact_mod_cast (p1_spec i).1.pos
              calc
                Real.log (p1 i) ≤ Real.log (((i : ℝ) + 2) ^ 2) :=
                  Real.log_le_log hp_pos (hN i hNi)
                _ = 2 * Real.log ((i : ℝ) + 2) :=
                  by
                    rw [Real.log_pow]
                    norm_num
                _ ≤ 2 * Real.log ((t : ℝ) + 2) :=
                  by
                    gcongr
        have h_log_m_le_step :
          Real.log (m t) ≤
            ∑ i ∈ Finset.range t,
              (2 * Real.log (t + 2) + (if i < N then Real.log (p1 i) else 0)) :=
          by
            convert!
              Finset.sum_le_sum fun i hi => h_log_m_le_step i (Finset.mem_range.mp hi) using
              1;
            rw [← Real.log_prod] <;> norm_cast; norm_num [m];
            exact fun i hi => Nat.Prime.ne_zero (p1_spec i |>.1);
        have h_initial : ∑ i ∈ Finset.range t, (if i < N then Real.log (p1 i) else 0) ≤ S :=
          by
            rw [hS_def]
            rw [← Finset.sum_filter]
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro i hi
              simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
              exact hi.2
            · intro i hiN hi
              exact
                Real.log_nonneg
                  (by
                    exact_mod_cast (p1_spec i).1.one_le)
        calc
          Real.log (m t) ≤
              ∑ i ∈ Finset.range t,
                (2 * Real.log (t + 2) + (if i < N then Real.log (p1 i) else 0)) :=
            h_log_m_le_step
          _ =
              2 * (t : ℝ) * Real.log (t + 2) +
                ∑ i ∈ Finset.range t, (if i < N then Real.log (p1 i) else 0) :=
            by
              simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
                nsmul_eq_mul]
              ring
          _ ≤ S + 2 * t * Real.log (t + 2) :=
            by
              linarith
    refine ⟨Max.max 1 (2 + S / Real.log 3), ?_, ?_⟩ <;> norm_num; intro t;
    specialize h_log_m_le t; rcases eq_or_ne t 0 <;> simp_all +decide only [ge_iff_le,
      CharP.cast_eq_zero, mul_zero, zero_add, zero_mul, add_zero, mul_assoc, ne_eq];
    · unfold m; norm_num;
    · rw [max_def];
      split_ifs <;>
        nlinarith [show (t : ℝ) * Real.log (t + 2) ≥ Real.log 3 by
            exact
              le_trans
                (Real.log_le_log
                  (by
                    positivity)
                  (by
                    norm_cast; linarith [Nat.pos_of_ne_zero ‹_›]))
                (le_mul_of_one_le_left
                  (Real.log_nonneg
                    (by
                      linarith))
                  (mod_cast Nat.one_le_iff_ne_zero.mpr ‹_›)),
          Real.log_pos (show (3 : ℝ) > 1 by norm_num),
          mul_div_cancel₀ (∑ i ∈ Finset.range N, Real.log (p1 i))
            (ne_of_gt (Real.log_pos (show (3 : ℝ) > 1 by norm_num)))];
end Erdos
end
section
section
open IntermediateField
namespace TauCeti.IntermediateField
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
theorem mem_sup_adjoin_sq_of_exists {F : IntermediateField K L} {x y : L}
    (hy : ∃ a b : L, a ∈ F ∧ b ∈ F ∧ y = a + b * x) :
    y ∈ F ⊔ IntermediateField.adjoin K {x} := by
  rcases hy with ⟨a, b, ha, hb, rfl⟩
  have hF : F ≤ F ⊔ IntermediateField.adjoin K {x} := le_sup_left
  have hx : IntermediateField.adjoin K {x} ≤ F ⊔ IntermediateField.adjoin K {x} :=
    le_sup_right
  exact add_mem (hF ha)
    (mul_mem (hF hb) (hx (IntermediateField.mem_adjoin_of_mem K (Set.mem_singleton x))))
private theorem isIntegral_of_sq_mem {F : IntermediateField K L} {x : L} (hx2 : x ^ 2 ∈ F) :
    IsIntegral F x := by
  have hx2_int : IsIntegral F (x ^ 2) := by
    simpa using isIntegral_algebraMap (R := F) (A := L) (x := (⟨x ^ 2, hx2⟩ : F))
  exact IsIntegral.of_pow (by norm_num : 0 < 2) hx2_int
private theorem minpoly_natDegree_le_two_of_sq_mem {F : IntermediateField K L} {x : L}
    (hx2 : x ^ 2 ∈ F) : (minpoly F x).natDegree ≤ 2 := by
  have hpoly_ne : ((Polynomial.X : Polynomial F) ^ 2 - Polynomial.C ⟨x ^ 2, hx2⟩) ≠ 0 := by
    intro hzero; have hdeg := congrArg Polynomial.natDegree hzero; norm_num at hdeg
  have hdeg := minpoly.degree_le_of_ne_zero F x hpoly_ne (by simp)
  rw [Polynomial.degree_X_pow_sub_C (n := 2) (by norm_num)] at hdeg
  exact Polynomial.natDegree_le_iff_degree_le.mpr hdeg
theorem exists_add_mul_of_mem_sup_adjoin_sq {F : IntermediateField K L} {x : L}
    (hx2 : x ^ 2 ∈ F) {y : L}
    (hy : y ∈ F ⊔ IntermediateField.adjoin K {x}) :
    ∃ a b : L, a ∈ F ∧ b ∈ F ∧ y = a + b * x := by
  have hx_int : IsIntegral F x := isIntegral_of_sq_mem hx2
  rw [← IntermediateField.restrictScalars_adjoin_eq_sup K F ({x} : Set L),
    mem_restrictScalars] at hy
  set pb := IntermediateField.adjoin.powerBasis hx_int with hpb
  obtain ⟨f, hfdeg, hf⟩ := pb.exists_eq_aeval ⟨y, hy⟩
  have hdim : pb.dim ≤ 2 := by
    rw [hpb, IntermediateField.adjoin.powerBasis_dim]
    exact minpoly_natDegree_le_two_of_sq_mem hx2
  have hfle : f.natDegree ≤ 1 := by
    have := hfdeg.trans_le hdim
    omega
  rw [hpb, Polynomial.eq_X_add_C_of_natDegree_le_one hfle,
    IntermediateField.adjoin.powerBasis_gen] at hf
  refine ⟨algebraMap F L (f.coeff 0), algebraMap F L (f.coeff 1),
    (f.coeff 0).2, (f.coeff 1).2, ?_⟩
  have hfeq := congrArg (Subtype.val (p := (· ∈ adjoin F {x}))) hf
  rw [AdjoinSimple.coe_aeval_gen_apply] at hfeq
  simp only [Polynomial.aeval_add, Polynomial.aeval_mul, Polynomial.aeval_C,
    Polynomial.aeval_X] at hfeq
  linear_combination hfeq
@[simp]
theorem mem_sup_adjoin_sq {F : IntermediateField K L} {x : L}
    (hx2 : x ^ 2 ∈ F) {y : L} :
    y ∈ F ⊔ IntermediateField.adjoin K {x} ↔
      ∃ a b : L, a ∈ F ∧ b ∈ F ∧ y = a + b * x :=
  ⟨exists_add_mul_of_mem_sup_adjoin_sq hx2, mem_sup_adjoin_sq_of_exists⟩
omit K [Field K] [Algebra K L] in
theorem mul_eq_zero_of_add_mul_sq_mem {S : Type*} [SetLike S L] [SubfieldClass S L] {F : S} {x : L}
    (hx2 : x ^ 2 ∈ F) (hxF : x ∉ F) [NeZero (2 : L)] {a b : L}
    (ha : a ∈ F) (hb : b ∈ F) (hab_mem : (a + b * x) ^ 2 ∈ F) :
    a * b = 0 := by
  by_contra hab
  refine hxF ?_
  have hcross_mem : 2 * a * b * x ∈ F := by
    have hEq : 2 * a * b * x = (a + b * x) ^ 2 - a ^ 2 - b ^ 2 * x ^ 2 := by ring
    rw [hEq]
    exact sub_mem (sub_mem hab_mem (pow_mem ha 2)) (mul_mem (pow_mem hb 2) hx2)
  have hcoef_mem : 2 * a * b ∈ F := mul_mem (mul_mem (natCast_mem (s := F) 2) ha) hb
  have hcoef_ne : 2 * a * b ≠ 0 := by
    have h2ab : (2 : L) * (a * b) ≠ 0 := mul_ne_zero (NeZero.ne (2 : L)) hab
    simpa [mul_assoc] using h2ab
  have hxeq : (2 * a * b)⁻¹ * (2 * a * b * x) = x := by
    rw [← mul_assoc, inv_mul_cancel₀ hcoef_ne, one_mul]
  rw [← hxeq]
  exact mul_mem (inv_mem hcoef_mem) hcross_mem
theorem finrank_adjoin_simple_eq_two_of_sq_mem_notMem (F : IntermediateField K L) {x : L}
    (hx2 : x ^ 2 ∈ F) (hxF : x ∉ F) :
    Module.finrank F (IntermediateField.adjoin F {x}) = 2 := by
  have hx_int : IsIntegral F x := isIntegral_of_sq_mem hx2
  have hfin := IntermediateField.adjoin.finrank hx_int
  have hle : (minpoly F x).natDegree ≤ 2 := minpoly_natDegree_le_two_of_sq_mem hx2
  have hpos : 0 < (minpoly F x).natDegree := minpoly.natDegree_pos hx_int
  have hne1 : (minpoly F x).natDegree ≠ 1 := by
    intro hdeg1
    have hfin1 : Module.finrank F (IntermediateField.adjoin F {x}) = 1 := by
      simpa [hfin] using hdeg1
    have hxbot : x ∈ (⊥ : IntermediateField F L) :=
      (IntermediateField.finrank_adjoin_simple_eq_one_iff).mp hfin1
    rw [IntermediateField.mem_bot] at hxbot
    obtain ⟨y, hy⟩ := hxbot
    exact hxF (hy ▸ y.2)
  omega
private theorem finrank_restrictScalars_eq (F : IntermediateField K L)
    (E : IntermediateField F L) :
    Module.finrank K (E.restrictScalars K) = Module.finrank K E := rfl
theorem finrank_sup_adjoin_simple_eq_mul_two (F : IntermediateField K L) {x : L}
    (hx2 : x ^ 2 ∈ F) (hxF : x ∉ F) :
    Module.finrank K ((F ⊔ IntermediateField.adjoin K {x}) : IntermediateField K L)
      = Module.finrank K F * 2 := by
  have hL : (IntermediateField.adjoin F {x}).restrictScalars K
      = F ⊔ IntermediateField.adjoin K {x} :=
    IntermediateField.restrictScalars_adjoin_eq_sup K F ({x} : Set L)
  have hfinL : Module.finrank F (IntermediateField.adjoin F {x}) = 2 :=
    finrank_adjoin_simple_eq_two_of_sq_mem_notMem F hx2 hxF
  calc Module.finrank K ((F ⊔ IntermediateField.adjoin K {x}) : IntermediateField K L)
      = Module.finrank K ((IntermediateField.adjoin F {x}).restrictScalars K) := by rw [hL]
    _ = Module.finrank K (IntermediateField.adjoin F {x}) := by
        rw [finrank_restrictScalars_eq]
    _ = Module.finrank K F * Module.finrank F (IntermediateField.adjoin F {x}) := by
        rw [Module.finrank_mul_finrank]
    _ = Module.finrank K F * 2 := by rw [hfinL]
end TauCeti.IntermediateField
end
end
section
section
open IntermediateField
namespace TauCeti.Multiquadratic
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
noncomputable def sqrtTower (root : ℕ → L) (n : ℕ) : IntermediateField K L :=
  IntermediateField.adjoin K (root '' Set.Iio n)
theorem sqrtTower_def (root : ℕ → L) (n : ℕ) :
    sqrtTower (K := K) root n = IntermediateField.adjoin K (root '' Set.Iio n) :=
  rfl
@[simp]
theorem sqrtTower_zero (root : ℕ → L) : sqrtTower (K := K) root 0 = ⊥ := by
  simp [sqrtTower]
@[simp]
theorem sqrtTower_succ (root : ℕ → L) (n : ℕ) :
    sqrtTower (K := K) root (n + 1)
      = (sqrtTower (K := K) root n) ⊔ IntermediateField.adjoin K {root n} := by
  rw [sqrtTower, sqrtTower, ← IntermediateField.adjoin_union]
  congr 1
  have hIio : Set.Iio (n + 1) = Set.Iio n ∪ {n} := by
    ext k
    simp only [Set.mem_Iio, Set.mem_union, Set.mem_singleton_iff]
    omega
  rw [hIio, Set.image_union, Set.image_singleton]
@[simp]
theorem sqrtTower_le_iff (root : ℕ → L) (n : ℕ) (F : IntermediateField K L) :
    sqrtTower (K := K) root n ≤ F ↔ ∀ j, j < n → root j ∈ F := by
  rw [sqrtTower, IntermediateField.adjoin_le_iff]
  constructor
  · intro h j hj
    exact h ⟨j, hj, rfl⟩
  · rintro h _ ⟨j, hj, rfl⟩
    exact h j hj
private theorem sqrtTower_sup_adjoin_eq_of_mem (root : ℕ → L) {n : ℕ}
    (hroot : root n ∈ sqrtTower (K := K) root n) :
    sqrtTower (K := K) root n ⊔ IntermediateField.adjoin K {root n}
      = sqrtTower (K := K) root n := by
  rw [sup_eq_left]
  exact IntermediateField.adjoin_le_iff.mpr (by simpa using hroot)
private theorem eq_sq_mul_prod_insert_of_mul_radicand {d : ℕ → K} {n : ℕ} {r s : K}
    {T : Finset ℕ} (hnT : n ∉ T) (hdn : d n ≠ 0) (hmul : r * d n = s ^ 2 * ∏ j ∈ T, d j) :
    r = (s / d n) ^ 2 * ∏ j ∈ insert n T, d j := by
  rw [Finset.prod_insert hnT]
  calc
    r = r * d n / d n := by field_simp
    _ = s ^ 2 * (∏ j ∈ T, d j) / d n := by rw [hmul]
    _ = (s / d n) ^ 2 * (d n * ∏ j ∈ T, d j) := by field_simp
private theorem radicand_ne_zero_of_root_notMem (d : ℕ → K) (root : ℕ → L) {n : ℕ}
    (hroot : root n ^ 2 = algebraMap K L (d n))
    (hnext : root n ∉ sqrtTower (K := K) root n) : d n ≠ 0 := by
  intro hdn
  apply hnext
  have hroot_zero : root n = 0 := by
    apply eq_zero_of_pow_eq_zero
    rw [hroot, hdn, map_zero]
  rw [hroot_zero]
  exact zero_mem _
private theorem exists_sq_mul_prod_of_eq_mul_root (d : ℕ → K) (root : ℕ → L)
    {n : ℕ} {r : K} {y b : L} (hroot : root n ^ 2 = algebraMap K L (d n)) (hdn0 : d n ≠ 0)
    (hb : b ∈ sqrtTower (K := K) root n) (heq : y = b * root n)
    (hy : y ^ 2 = algebraMap K L r)
    (ih : ∀ r : K, ∀ y : L, y ^ 2 = algebraMap K L r → y ∈ sqrtTower (K := K) root n →
      ∃ (T : Finset ℕ) (s : K), ↑T ⊆ Set.Iio n ∧ r = s ^ 2 * ∏ j ∈ T, d j) :
    ∃ (T : Finset ℕ) (s : K), ↑T ⊆ Set.Iio (n + 1) ∧ r = s ^ 2 * ∏ j ∈ T, d j := by
  have hy_mul_mem : y * root n ∈ sqrtTower (K := K) root n := by
    have hy_mul_eq : y * root n = b * algebraMap K L (d n) := by
      calc y * root n = b * root n ^ 2 := by rw [heq]; ring
        _ = b * algebraMap K L (d n) := by rw [hroot]
    rw [hy_mul_eq]
    exact mul_mem hb ((sqrtTower (K := K) root n).algebraMap_mem (d n))
  have hy_mul_sq : (y * root n) ^ 2 = algebraMap K L (r * d n) := by
    rw [map_mul, ← hy, ← hroot]
    ring
  obtain ⟨T, s, hT, hmul⟩ := ih (r * d n) (y * root n) hy_mul_sq hy_mul_mem
  have hnT : n ∉ T := fun hn => Nat.lt_irrefl n (hT hn)
  refine ⟨insert n T, s / d n, ?_, ?_⟩
  · intro j hj
    rw [Finset.mem_coe, Finset.mem_insert] at hj
    rw [Set.mem_Iio]
    rcases hj with rfl | hj
    · omega
    · exact Nat.lt_trans (hT hj) n.lt_succ_self
  · exact eq_sq_mul_prod_insert_of_mul_radicand hnT hdn0 hmul
theorem squareClass_of_sq_mem (d : ℕ → K) (root : ℕ → L)
    (hroot : ∀ j, root j ^ 2 = algebraMap K L (d j)) [NeZero (2 : K)] :
    ∀ n, ∀ r : K, ∀ y : L, y ^ 2 = algebraMap K L r → y ∈ sqrtTower (K := K) root n →
      ∃ (T : Finset ℕ) (s : K), ↑T ⊆ Set.Iio n ∧
        r = s ^ 2 * ∏ j ∈ T, d j := by
  classical
  have : NeZero (2 : L) :=
    NeZero.nat_of_injective (n := 2) (f := algebraMap K L) (algebraMap K L).injective
  intro n
  induction n with
  | zero =>
      intro r y hy hmem
      rw [sqrtTower_zero, IntermediateField.mem_bot] at hmem
      obtain ⟨s, rfl⟩ := hmem
      have h2 : s ^ 2 = r := (algebraMap K L).injective (by simpa using hy)
      exact ⟨∅, s, by simp, by rw [Finset.prod_empty, mul_one, h2]⟩
  | succ n ih =>
      intro r y hy hmem
      rw [sqrtTower_succ] at hmem
      by_cases hnext : root n ∈ sqrtTower (K := K) root n
      · rw [sqrtTower_sup_adjoin_eq_of_mem root hnext] at hmem
        obtain ⟨T, s, hT, heq⟩ := ih r y hy hmem
        exact ⟨T, s, hT.trans (Set.Iio_subset_Iio n.le_succ), heq⟩
      · have hx2 : root n ^ 2 ∈ sqrtTower (K := K) root n := by
          rw [hroot n]
          exact (sqrtTower (K := K) root n).algebraMap_mem (d n)
        obtain ⟨a, b, ha, hb, heq⟩ :=
          TauCeti.IntermediateField.exists_add_mul_of_mem_sup_adjoin_sq hx2 hmem
        have hab_mem : (a + b * root n) ^ 2 ∈ sqrtTower (K := K) root n := by
          rw [← heq, hy]
          exact (sqrtTower (K := K) root n).algebraMap_mem r
        have hab : a * b = 0 :=
          TauCeti.IntermediateField.mul_eq_zero_of_add_mul_sq_mem hx2 hnext ha hb hab_mem
        rcases mul_eq_zero.mp hab with ha0 | hb0
        · exact exists_sq_mul_prod_of_eq_mul_root d root (hroot n)
            (radicand_ne_zero_of_root_notMem d root (hroot n) hnext) hb
            (by rw [heq, ha0, zero_add]) hy ih
        · have hy_mem : y ∈ sqrtTower (K := K) root n := by
            rw [heq, hb0, zero_mul, add_zero]
            exact ha
          obtain ⟨T, s, hT, hres⟩ := ih r y hy hy_mem
          exact ⟨T, s, hT.trans (Set.Iio_subset_Iio n.le_succ), hres⟩
theorem squareClass_of_sqrt_mem (c : ℕ → ℚ) (hc : ∀ j, 0 ≤ c j) :
    ∀ n, ∀ r : ℚ, 0 ≤ r → (Real.sqrt r : ℝ) ∈ sqrtTower (K := ℚ) (fun j => Real.sqrt (c j)) n →
      ∃ (T : Finset ℕ) (s : ℚ), ↑T ⊆ Set.Iio n ∧
        r = s ^ 2 * ∏ j ∈ T, c j := by
  intro n r hr hmem
  apply squareClass_of_sq_mem c (fun j => Real.sqrt (c j)) ?_ n r (Real.sqrt r) ?_ hmem
  · intro j
    have hcj_nonneg : 0 ≤ (c j : ℝ) := by exact_mod_cast hc j
    simpa using Real.sq_sqrt hcj_nonneg
  · have hr_nonneg : 0 ≤ (r : ℝ) := by exact_mod_cast hr
    simpa using Real.sq_sqrt hr_nonneg
end TauCeti.Multiquadratic
end
end
section
namespace Erdos
noncomputable def Kf (g : ℕ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ
    (insert Complex.I ((fun j => ((Real.sqrt (q3 j) : ℝ) : ℂ)) '' Set.Iio g))
theorem Kf_finiteDimensional (g : ℕ) : FiniteDimensional ℚ (Kf g) :=
  by
    refine IntermediateField.finiteDimensional_adjoin ?_
    simp +zetaDelta only [Set.mem_insert_iff, Set.mem_image, Set.mem_Iio, forall_eq_or_imp,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at *
    refine ⟨?_, ?_⟩
    · exact Complex.isIntegral_rat_I
    · intro a ha
      refine ⟨Polynomial.X ^ 2 - Polynomial.C (q3 a : ℚ), ?_, ?_⟩
      · exact Polynomial.monic_X_pow_sub_C _ two_ne_zero
      · norm_num [← Polynomial.C_pow]
        norm_cast
        rw [Real.sq_sqrt <| Nat.cast_nonneg _]
        ring
noncomputable instance (g : ℕ) : NumberField (Kf g) :=
  { to_charZero := inferInstance
    to_finiteDimensional := Kf_finiteDimensional g }
section MultiquadraticDegree
open IntermediateField TauCeti.Multiquadratic
theorem q3_not_squareClass (n : ℕ) (T : Finset ℕ) (hT : ↑T ⊆ Set.Iio n)
    (s : ℚ) : ((q3 n : ℚ)) ≠ s ^ 2 * ∏ j ∈ T, ((q3 j : ℚ)) := by
  classical
  intro h
  have hp : (q3 n).Prime := (q3_spec n).1
  have : Fact (q3 n).Prime := ⟨hp⟩
  have hqn0 : (q3 n : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hs0 : s ≠ 0 := by
    intro hs
    apply hqn0
    simpa [hs] using h
  have hval_factor :
      ∀ j ∈ T, padicValRat (q3 n) (q3 j : ℚ) = 0 := by
    intro j hj
    have hjn : j < n := hT (by simpa using hj)
    have hneq : q3 n ≠ q3 j := by
      exact ne_of_gt (q3_strictMono hjn)
    have : Fact (q3 j).Prime := ⟨(q3_spec j).1⟩
    rw [padicValRat.of_nat, padicValNat_primes hneq]
    norm_num
  have hprod0 : (∏ j ∈ T, (q3 j : ℚ)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (by
      intro j hj
      exact_mod_cast (q3_spec j).1.ne_zero)
  have hprodVal_aux :
      ∀ U : Finset ℕ, ↑U ⊆ Set.Iio n →
        padicValRat (q3 n) (∏ j ∈ U, (q3 j : ℚ)) = 0 := by
    intro U
    refine Finset.induction_on U ?base ?step
    · intro hU
      simp [padicValRat.one]
    · intro a U haU ih hU
      have hqa0 : (q3 a : ℚ) ≠ 0 := by exact_mod_cast (q3_spec a).1.ne_zero
      have hUprod0 : (∏ j ∈ U, (q3 j : ℚ)) ≠ 0 := by
        exact Finset.prod_ne_zero_iff.mpr (by
          intro j hj
          exact_mod_cast (q3_spec j).1.ne_zero)
      have ha_lt : a < n := hU (Finset.mem_insert_self a U)
      have hneq : q3 n ≠ q3 a := by
        exact ne_of_gt (q3_strictMono ha_lt)
      have : Fact (q3 a).Prime := ⟨(q3_spec a).1⟩
      have hvala : padicValRat (q3 n) (q3 a : ℚ) = 0 := by
        rw [padicValRat.of_nat, padicValNat_primes hneq]
        norm_num
      have ih' : padicValRat (q3 n) (∏ j ∈ U, (q3 j : ℚ)) = 0 := by
        exact ih (by
          intro j hj
          exact hU (by simp [hj]))
      rw [Finset.prod_insert haU, padicValRat.mul hqa0 hUprod0,
        hvala, ih', add_zero]
  have hprodVal : padicValRat (q3 n) (∏ j ∈ T, (q3 j : ℚ)) = 0 :=
    hprodVal_aux T hT
  have hval := congrArg (padicValRat (q3 n)) h
  rw [padicValRat.self hp.one_lt, padicValRat.mul (pow_ne_zero 2 hs0) hprod0,
    padicValRat.pow s, hprodVal, add_zero] at hval
  omega
private theorem finrank_adjoin_simple_eq_two_of_sq_mem_notMem
    {E : Type*} [Field E] [Algebra ℚ E] (K : IntermediateField ℚ E) {x : E}
    (hx2 : x ^ 2 ∈ K) (hxK : x ∉ K) :
    Module.finrank K (IntermediateField.adjoin K {x}) = 2 := by
  have hx2_int : IsIntegral K (x ^ 2) := by
    rw [← show algebraMap K E ⟨x ^ 2, hx2⟩ = x ^ 2 from rfl]
    exact isIntegral_algebraMap (R := K) (A := E) (x := ⟨x ^ 2, hx2⟩)
  have hx_int : IsIntegral K x := IsIntegral.of_pow (by norm_num : 0 < 2) hx2_int
  have hfin := IntermediateField.adjoin.finrank hx_int
  have hle : (minpoly K x).natDegree ≤ 2 := by
    let a : K := ⟨x ^ 2, hx2⟩
    have hroot :
        Polynomial.aeval x ((Polynomial.X : Polynomial K) ^ 2 - Polynomial.C a) = 0 := by
      simp [a]
    have hdvd : minpoly K x ∣ ((Polynomial.X : Polynomial K) ^ 2 - Polynomial.C a) :=
      minpoly.dvd K x hroot
    have hpoly_ne : ((Polynomial.X : Polynomial K) ^ 2 - Polynomial.C a) ≠ 0 := by
      intro hzero
      have hdeg := congrArg Polynomial.natDegree hzero
      norm_num at hdeg
    have hdeg_poly :
        (((Polynomial.X : Polynomial K) ^ 2 - Polynomial.C a)).natDegree = 2 := by
      simp
    exact (Polynomial.natDegree_le_of_dvd hdvd hpoly_ne).trans_eq hdeg_poly
  have hpos : 0 < (minpoly K x).natDegree := minpoly.natDegree_pos hx_int
  have hne1 : (minpoly K x).natDegree ≠ 1 := by
    intro hdeg1
    have hfin1 : Module.finrank K (IntermediateField.adjoin K {x}) = 1 := by
      simpa [hfin] using hdeg1
    have hxbot : x ∈ (⊥ : IntermediateField K E) :=
      (IntermediateField.finrank_adjoin_simple_eq_one_iff).mp hfin1
    rw [IntermediateField.mem_bot] at hxbot
    obtain ⟨y, hy⟩ := hxbot
    apply hxK
    rw [← hy]
    exact y.2
  omega
private theorem finrank_sup_adjoin_simple_eq_mul_two
    {E : Type*} [Field E] [Algebra ℚ E] (K : IntermediateField ℚ E) {x : E}
    (hx2 : x ^ 2 ∈ K) (hxK : x ∉ K) :
    Module.finrank ℚ ((K ⊔ IntermediateField.adjoin ℚ ({x} : Set E)) :
      IntermediateField ℚ E) =
      Module.finrank ℚ K * 2 := by
  let : IsScalarTower ℚ K E := by
    refine IsScalarTower.of_algebraMap_eq fun q => ?_
    simp
  let L : IntermediateField K E := IntermediateField.adjoin K {x}
  have hL :
      L.restrictScalars ℚ = K ⊔ IntermediateField.adjoin ℚ ({x} : Set E) := by
    exact IntermediateField.restrictScalars_adjoin_eq_sup ℚ K ({x} : Set E)
  have hfinL : Module.finrank K L = 2 :=
    finrank_adjoin_simple_eq_two_of_sq_mem_notMem K hx2 hxK
  let e : (L.restrictScalars ℚ) ≃ₗ[ℚ] L :=
    { toFun := fun y => ⟨(y : E), y.2⟩
      invFun := fun y => ⟨(y : E), y.2⟩
      left_inv := fun y => rfl
      right_inv := fun y => rfl
      map_add' := fun y z => rfl
      map_smul' := fun q y => rfl }
  calc
    Module.finrank ℚ ((K ⊔ IntermediateField.adjoin ℚ ({x} : Set E)) :
      IntermediateField ℚ E)
        = Module.finrank ℚ (L.restrictScalars ℚ) := by rw [hL]
    _ = Module.finrank ℚ L := e.finrank_eq
    _ = Module.finrank ℚ K * Module.finrank K L := by
      rw [Module.finrank_mul_finrank]
    _ = Module.finrank ℚ K * 2 := by rw [hfinL]
theorem sqrt_q3_notMem_tower (n : ℕ) :
    (Real.sqrt (q3 n) : ℝ) ∉ (TauCeti.Multiquadratic.sqrtTower (K := ℚ) (fun j : ℕ => Real.sqrt ((q3 j : ℚ) : ℝ))) n := by
  intro hmem
  obtain ⟨T, s, hT, heq⟩ :=
    squareClass_of_sqrt_mem (fun j => (q3 j : ℚ))
      (fun j => by
        show (0 : ℚ) ≤ (q3 j : ℚ)
        exact_mod_cast (q3_spec j).1.pos.le) n (q3 n)
      (by exact_mod_cast (q3_spec n).1.pos.le) hmem
  exact q3_not_squareClass n T hT s heq
theorem sqrtTower_finrank (n : ℕ) :
    Module.finrank ℚ ((TauCeti.Multiquadratic.sqrtTower (K := ℚ) (fun j : ℕ => Real.sqrt ((q3 j : ℚ) : ℝ))) n) = 2 ^ n := by
  induction n with
  | zero =>
      rw [sqrtTower_zero]
      exact IntermediateField.finrank_bot
  | succ n ih =>
      rw [sqrtTower_succ]
      have hx2 :
          (Real.sqrt ((q3 n : ℚ) : ℝ)) ^ 2 ∈
            (TauCeti.Multiquadratic.sqrtTower (K := ℚ) (fun j : ℕ => Real.sqrt ((q3 j : ℚ) : ℝ))) n := by
        rw [Real.sq_sqrt]
        · exact SubfieldClass.ratCast_mem _ (q3 n : ℚ)
        · exact_mod_cast (q3_spec n).1.pos.le
      have hxK :
          Real.sqrt ((q3 n : ℚ) : ℝ) ∉
            (TauCeti.Multiquadratic.sqrtTower (K := ℚ) (fun j : ℕ => Real.sqrt ((q3 j : ℚ) : ℝ))) n := by
        simpa using sqrt_q3_notMem_tower n
      rw [finrank_sup_adjoin_simple_eq_mul_two
        ((TauCeti.Multiquadratic.sqrtTower (K := ℚ) (fun j : ℕ => Real.sqrt ((q3 j : ℚ) : ℝ))) n) hx2 hxK, ih]
      rw [pow_succ]
theorem Kf_finrank (g : ℕ) : Module.finrank ℚ (Kf g) = 2 ^ (g + 1) := by
  let φ : ℝ →ₐ[ℚ] ℂ := Complex.ofRealHom.toRatAlgHom
  let Kr : IntermediateField ℚ ℝ := (TauCeti.Multiquadratic.sqrtTower (K := ℚ) (fun j : ℕ => Real.sqrt ((q3 j : ℚ) : ℝ))) g
  let Kc : IntermediateField ℚ ℂ := Kr.map φ
  have hKc_fin : Module.finrank ℚ Kc = 2 ^ g := by
    let e : Kr.toSubalgebra ≃ₐ[ℚ] Kc.toSubalgebra :=
      (Kr.toSubalgebra.equivMapOfInjective φ φ.injective).trans
        (Subalgebra.equivOfEq _ _ (by dsimp [Kc]))
    have hfin : Module.finrank ℚ Kc.toSubalgebra = Module.finrank ℚ Kr.toSubalgebra :=
      e.toLinearEquiv.finrank_eq.symm
    let eKc : Kc.toSubalgebra ≃ₗ[ℚ] Kc :=
      { toFun := fun y => ⟨(y : ℂ), y.2⟩
        invFun := fun y => ⟨(y : ℂ), y.2⟩
        left_inv := fun y => rfl
        right_inv := fun y => rfl
        map_add' := fun y z => rfl
        map_smul' := fun q y => rfl }
    let eKr : Kr.toSubalgebra ≃ₗ[ℚ] Kr :=
      { toFun := fun y => ⟨(y : ℝ), y.2⟩
        invFun := fun y => ⟨(y : ℝ), y.2⟩
        left_inv := fun y => rfl
        right_inv := fun y => rfl
        map_add' := fun y z => rfl
        map_smul' := fun q y => rfl }
    calc
      Module.finrank ℚ Kc = Module.finrank ℚ Kc.toSubalgebra := eKc.finrank_eq.symm
      _ = Module.finrank ℚ Kr.toSubalgebra := hfin
      _ = Module.finrank ℚ Kr := eKr.finrank_eq
      _ = 2 ^ g := by
        dsimp [Kr]
        rw [sqrtTower_finrank]
  have hKc :
      Kc =
        IntermediateField.adjoin ℚ
          ((fun j => ((Real.sqrt (q3 j) : ℝ) : ℂ)) '' Set.Iio g) := by
    dsimp [Kc, Kr]
    rw [sqrtTower_def, IntermediateField.adjoin_map]
    congr 1
    ext z
    constructor
    · rintro ⟨x, ⟨j, hj, rfl⟩, rfl⟩
      exact ⟨j, hj, by simp [φ, RingHom.toRatAlgHom_apply]⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Real.sqrt (q3 j : ℚ), ⟨j, hj, rfl⟩, by
        simp [φ, RingHom.toRatAlgHom_apply]⟩
  have hKf :
      Kf g = Kc ⊔ IntermediateField.adjoin ℚ ({Complex.I} : Set ℂ) := by
    rw [hKc, Kf, ← IntermediateField.adjoin_union]
    congr 1
    ext z
    constructor
    · intro hz
      rw [Set.mem_insert_iff] at hz
      rw [Set.mem_union, Set.mem_singleton_iff]
      tauto
    · intro hz
      rw [Set.mem_union, Set.mem_singleton_iff] at hz
      rw [Set.mem_insert_iff]
      tauto
  have hI2 : Complex.I ^ 2 ∈ Kc := by
    rw [sq, Complex.I_mul_I]
    exact neg_mem (one_mem Kc)
  have hInot : Complex.I ∉ Kc := by
    intro hI
    dsimp [Kc] at hI
    rw [IntermediateField.mem_map] at hI
    obtain ⟨y, hy, hyI⟩ := hI
    have him := congrArg Complex.im hyI
    simp [φ, RingHom.toRatAlgHom_apply] at him
  rw [hKf, finrank_sup_adjoin_simple_eq_mul_two Kc hI2 hInot, hKc_fin]
  rw [pow_succ]
end MultiquadraticDegree
theorem Kf_isTotallyComplex (g : ℕ) : NumberField.IsTotallyComplex (Kf g) := by
  have hI : Complex.I ∈ Kf g :=
    IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
  refine ⟨fun v => ?_⟩
  rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex]
  intro hreal
  have hφ : NumberField.ComplexEmbedding.conjugate v.embedding = v.embedding :=
    NumberField.ComplexEmbedding.isReal_iff.mp
      (NumberField.InfinitePlace.isReal_iff.mp hreal)
  set x : Kf g := ⟨Complex.I, hI⟩ with hx
  have hx2 : x ^ 2 = -1 := by
    apply Subtype.ext
    push_cast [hx, sq, Complex.I_mul_I]
    ring
  set z : ℂ := v.embedding x with hz
  have key : z ^ 2 = -1 := by
    rw [hz, ← map_pow, hx2, map_neg, map_one]
  have hconj : (starRingEnd ℂ) z = z := by
    have := RingHom.congr_fun hφ x
    simpa [hz, NumberField.ComplexEmbedding.conjugate_coe_eq] using this
  have him : z.im = 0 := Complex.conj_eq_iff_im.mp hconj
  have hre : z.re ^ 2 = -1 := by
    have h := congrArg Complex.re key
    simp only [pow_two, Complex.mul_re, him, mul_zero, sub_zero, Complex.neg_re,
      Complex.one_re] at h
    rw [← pow_two] at h
    exact h
  nlinarith [sq_nonneg z.re, hre]
noncomputable instance (g : ℕ) : NumberField.IsTotallyComplex (Kf g) :=
  Kf_isTotallyComplex g
theorem Kf_isGalois (g : ℕ) : IsGalois ℚ (Kf g) :=
  by
    apply_rules [IsGalois.mk]; apply_rules [normal_iff.mpr]; intro x
    have h_integral : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
    have h_splits : (Polynomial.map (algebraMap ℚ (Kf g)) (minpoly ℚ x)).Splits :=
      by
        have h_minpoly :
          ∀
            s ∈
              (IntermediateField.adjoin ℚ
                  (insert Complex.I
                    ((fun j => ((Real.sqrt (q3 j) : ℝ) : ℂ)) '' Set.Iio g))).toSubalgebra,
            (Polynomial.map (algebraMap ℚ (Kf g)) (minpoly ℚ s)).Splits :=
          by
            apply IntermediateField.splits_of_mem_adjoin; intro x hx
            have h_minpoly : (Polynomial.map (algebraMap ℚ (Kf g)) (minpoly ℚ x)).Splits :=
              by
                rcases hx with (rfl | ⟨j, hj, rfl⟩);
                · rw [show minpoly ℚ Complex.I = Polynomial.X ^ 2 + 1 from ?_];
                  · rw [Polynomial.splits_iff_exists_multiset];
                    use
                      {⟨Complex.I,
                          by
                            exact IntermediateField.subset_adjoin ℚ _ (Set.mem_insert _ _)⟩,
                        ⟨-Complex.I,
                          by
                            exact
                              Subalgebra.neg_mem _
                                (IntermediateField.subset_adjoin ℚ _ <| Set.mem_insert _ _)⟩}
                    generalize_proofs at *; refine Polynomial.funext fun x => ?_; ext;
                    norm_num; ring_nf; norm_num [sub_eq_add_neg]; ring;
                  · refine Eq.symm (minpoly.eq_of_irreducible_of_monic ?_ ?_ ?_);
                    ·
                      have h_cyclotomic : Polynomial.X ^ 2 + 1 = Polynomial.cyclotomic 4 ℚ :=
                        by
                          rw [show (4 : ℕ) = 2 ^ 2 by norm_num,
                            Polynomial.cyclotomic_prime_pow_eq_geom_sum];
                          · norm_num
                          · norm_num
                      exact
                        h_cyclotomic ▸
                          Polynomial.cyclotomic.irreducible_rat
                            (by
                              decide);
                    · norm_num;
                    · erw [Polynomial.Monic, Polynomial.leadingCoeff_X_pow_add_C]; norm_num;
                · have h_minpoly :
                    minpoly ℚ ((Real.sqrt (q3 j) : ℝ) : ℂ) =
                      Polynomial.X ^ 2 - Polynomial.C (q3 j : ℚ) :=
                    by
                      refine Eq.symm (minpoly.eq_of_irreducible_of_monic ?_ ?_ ?_);
                      ·
                        have h_irred : ¬∃ (r : ℚ), r ^ 2 = q3 j :=
                          by
                            have h_not_square : ¬∃ (r : ℤ), r ^ 2 = q3 j :=
                              by
                                have := q3_spec j;
                                exact fun ⟨r, hr⟩ =>
                                  by
                                    have := congr_arg (· % 4) hr;
                                    norm_num [sq, Int.add_emod, Int.mul_emod] at this;
                                    have := Int.emod_nonneg r four_pos.ne';
                                    have := Int.emod_lt_of_pos r four_pos;
                                    interval_cases r % 4 <;> norm_cast at * <;>
                                      simp_all +decide;
                            exact fun ⟨r, hr⟩ =>
                              h_not_square
                                ⟨r.num,
                                  by
                                    simpa only [sq, Rat.mul_self_num, Rat.num_natCast] using
                                      congr_arg Rat.num hr⟩;
                        have h_irred :
                          ∀ p q : Polynomial ℚ,
                            p.degree > 0 →
                              q.degree > 0 →
                                p * q = Polynomial.X ^ 2 - Polynomial.C (q3 j : ℚ) → False :=
                          by
                            intros p q hp hq h_eq
                            have h_deg : p.degree = 1 ∧ q.degree = 1 :=
                              by
                                have h_deg : p.degree + q.degree = 2 :=
                                  by
                                    rw [← Polynomial.degree_mul, h_eq,
                                        Polynomial.degree_sub_C] <;>
                                      norm_num;
                                rw [Polynomial.degree_eq_natDegree
                                    (Polynomial.ne_zero_of_degree_gt hp),
                                  Polynomial.degree_eq_natDegree
                                    (Polynomial.ne_zero_of_degree_gt hq)] at *;
                                norm_cast at *;
                                exact
                                  ⟨by
                                      linarith,
                                    by
                                      linarith⟩;
                            obtain ⟨r, hr⟩ : ∃ r : ℚ, p.eval r = 0 :=
                              by
                                exact Polynomial.exists_root_of_degree_eq_one h_deg.1;
                            exact
                              h_irred
                                ⟨r,
                                  by
                                    replace h_eq := congr_arg (Polynomial.eval r) h_eq;
                                    norm_num [hr] at h_eq; linarith⟩;
                        constructor <;> contrapose! h_irred;
                        · exact
                            absurd (Polynomial.degree_eq_zero_of_isUnit h_irred)
                              (by
                                erw [Polynomial.degree_X_pow_sub_C] <;> norm_num);
                        · obtain ⟨a, b, h₁, h₂, h₃⟩ := h_irred;
                          exact
                            ⟨a, b,
                              not_le.mp fun h =>
                                h₂ <|
                                  Polynomial.isUnit_iff_degree_eq_zero.mpr <|
                                    le_antisymm h <|
                                      le_of_not_gt fun h' =>
                                        by
                                          { apply_fun Polynomial.eval 0 at h₁; aesop
                                        },
                              not_le.mp fun h =>
                                h₃ <|
                                  Polynomial.isUnit_iff_degree_eq_zero.mpr <|
                                    le_antisymm h <|
                                      le_of_not_gt fun h' =>
                                        by
                                          { apply_fun Polynomial.eval 0 at h₁; aesop
                                        },
                              h₁.symm, trivial⟩;
                      · norm_num [← Complex.ofReal_pow];
                      · erw [Polynomial.Monic, Polynomial.leadingCoeff_X_pow_sub_C]; norm_num;
                  rw [h_minpoly, Polynomial.splits_iff_exists_multiset];
                  refine
                      ⟨{⟨(Real.sqrt (q3 j) : ℝ), ?_⟩, ⟨-(Real.sqrt (q3 j) : ℝ), ?_⟩}, ?_⟩ <;>
                    norm_num;
                  any_goals
                    exact
                      IntermediateField.subset_adjoin ℚ _
                        (Set.mem_insert_of_mem _ <| Set.mem_image_of_mem _ hj);
                  refine Polynomial.funext fun x => ?_;
                  erw [Polynomial.leadingCoeff_X_pow_sub_C] <;> norm_num; ring_nf; ext;
                  norm_num; ring_nf; norm_num [← Complex.ofReal_pow]
            exact
              ⟨by
                  cases hx <;> simp_all +decide only [Complex.ext_iff, Complex.I_re, Complex.I_im,
                    Set.mem_image, Set.mem_Iio, Complex.ofReal_re, Complex.ofReal_im];
                  · rw [show x = Complex.I by
                        simpa [Complex.ext_iff] using ‹x.re = 0 ∧ x.im = 1›];
                    exact
                      ⟨Polynomial.X ^ 2 + 1,
                        by
                          exact Polynomial.monic_X_pow_add_C _ two_ne_zero,
                        by
                          norm_num⟩;
                  · obtain ⟨j, hj, hx₁, hx₂⟩ := ‹_›;
                    use Polynomial.X ^ 2 - Polynomial.C (q3 j : ℚ); norm_num [hx₁, hx₂];
                    ring_nf;
                    exact
                      ⟨Polynomial.monic_X_pow_sub_C _ two_ne_zero,
                        by
                          rw [show x = Real.sqrt (q3 j) by
                              simp [Complex.ext_iff, hx₁.symm, hx₂.symm]];
                          norm_num [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]⟩,
                h_minpoly⟩;
        have hx2 := h_minpoly x x.2
        rwa [show minpoly ℚ (x : ℂ) = minpoly ℚ x from
            minpoly.algHom_eq (Kf g).val (Kf g).val.injective x] at hx2
    exact ⟨h_integral, h_splits⟩
theorem Kf_aut_involutive (g : ℕ) (σ : Kf g ≃ₐ[ℚ] Kf g) : σ * σ = 1 := by
  have hext : ((σ * σ : Kf g ≃ₐ[ℚ] Kf g) : Kf g →ₐ[ℚ] Kf g)
      = ((1 : Kf g ≃ₐ[ℚ] Kf g) : Kf g →ₐ[ℚ] Kf g) := by
    refine IntermediateField.algHom_ext_of_eq_adjoin ℚ (S := Kf g)
      (s := insert Complex.I ((fun j => ((Real.sqrt (q3 j) : ℝ) : ℂ)) '' Set.Iio g))
      rfl ?_
    intro x hx
    set y : Kf g := ⟨x, (rfl : Kf g = _).ge (IntermediateField.subset_adjoin _ _ hx)⟩
      with hy
    have hsq : ∃ c : ℚ, y ^ 2 = algebraMap ℚ (Kf g) c := by
      rcases hx with rfl | ⟨j, hj, rfl⟩
      · refine ⟨-1, Subtype.ext ?_⟩
        push_cast [hy]
        simp [Complex.I_sq]
      · refine ⟨(q3 j : ℚ), Subtype.ext ?_⟩
        push_cast [hy]
        rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
        norm_num
    obtain ⟨c, hc⟩ := hsq
    have h1 : (σ y) ^ 2 = y ^ 2 := by
      rw [← map_pow, hc, AlgEquiv.commutes]
    have h2 : σ y = y ∨ σ y = -y := sq_eq_sq_iff_eq_or_eq_neg.mp h1
    change σ (σ y) = y
    rcases h2 with h | h
    · rw [h, h]
    · rw [h, map_neg, h, neg_neg]
  exact AlgEquiv.coe_toAlgHom_injective hext
theorem Kf_isAbelianGalois (g : ℕ) : IsAbelianGalois ℚ (Kf g) := by
  have := Kf_isGalois g
  refine { is_comm := ⟨fun a b => ?_⟩ }
  exact Commute.of_orderOf_dvd_two
    (fun σ => orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact Kf_aut_involutive g σ)) a b
noncomputable instance (g : ℕ) : IsAbelianGalois ℚ (Kf g) :=
  Kf_isAbelianGalois g
noncomputable example (g : ℕ) : NumberField.IsCMField (Kf g) := inferInstance
end Erdos
end
section
section
open scoped Classical
namespace TauCeti.NumberField
private def prodLeTuples (n : ℕ) (X : ℝ) : Set (Fin n → ℕ) :=
  {d : Fin n → ℕ | (∀ i, 0 < d i) ∧ (∏ i, (d i : ℝ)) ≤ X}
@[simp]
private theorem mem_prodLeTuples {n : ℕ} {X : ℝ} {d : Fin n → ℕ} :
    d ∈ prodLeTuples n X ↔ (∀ i, 0 < d i) ∧ (∏ i, (d i : ℝ)) ≤ X := Iff.rfl
private theorem prodLeTuples_finite (n : ℕ) (X : ℝ) : (prodLeTuples n X).Finite := by
  apply Set.Finite.subset (Set.finite_Icc (1 : Fin n → ℕ) (fun _ => ⌊X⌋₊))
  rintro d ⟨hpos, hprod⟩
  refine ⟨fun i => hpos i, fun i => Nat.le_floor ?_⟩
  exact le_trans (mod_cast Finset.single_le_prod' (fun a _ => hpos a) (Finset.mem_univ i)) hprod
private theorem sum_one_div_sq_le_two (N : ℕ) :
    ∑ j ∈ Finset.Icc 1 N, (1 : ℝ) / (j : ℝ) ^ 2 ≤ 2 := by
  have hconv : ∑ j ∈ Finset.Icc 1 N, (1 : ℝ) / (j : ℝ) ^ 2 ≤ Real.pi ^ 2 / 6 := by
    simpa using sum_le_hasSum (Finset.Icc 1 N) (fun n _ => by positivity)
      (by simpa using hasSum_zeta_two)
  have hpi : Real.pi < 3.4 := by pi_upper_bound [7 / 5]
  nlinarith [hconv, Real.pi_pos, hpi]
private theorem prodLeTuples_succ_eq_iUnion (n : ℕ) (X : ℝ) :
    prodLeTuples (n + 1) X = ⋃ j ∈ Finset.Icc 1 ⌊X⌋₊,
      (fun e => Fin.snoc e j) '' (prodLeTuples n (X / j)) := by
  ext d; simp only [prodLeTuples, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_image,
    Finset.mem_Icc]
  constructor <;> intro h
  · refine ⟨d (Fin.last n), ⟨h.1 _, Nat.le_floor ?_⟩, Fin.init d, ⟨?_, ?_⟩,
      Fin.snoc_init_self d⟩
    · refine le_trans ?_ h.2
      rw [Fin.prod_univ_castSucc]
      exact le_mul_of_one_le_left (Nat.cast_nonneg _)
        (mod_cast Finset.one_le_prod' fun i _ => h.1 _)
    · exact fun i => h.1 _
    · rw [le_div_iff₀ (mod_cast h.1 (Fin.last n))]
      rw [Fin.prod_univ_castSucc] at h
      simpa [Fin.init] using h.2
  · obtain ⟨j, ⟨hj1, -⟩, e, ⟨hepos, heprod⟩, rfl⟩ := h
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
    refine ⟨fun i => ?_, ?_⟩
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · rw [Fin.snoc_last]; exact hj1
      · rw [Fin.snoc_castSucc]; exact hepos i
    · rw [Fin.prod_univ_castSucc, Fin.snoc_last]
      simp only [Fin.snoc_castSucc]
      rw [le_div_iff₀ hj0] at heprod
      linarith [heprod]
private theorem prodLeTuples_succ_ncard_le (n : ℕ) (X : ℝ) : (prodLeTuples (n + 1) X).ncard ≤
      ∑ j ∈ Finset.Icc 1 ⌊X⌋₊, (prodLeTuples n (X / j)).ncard := by
  rw [prodLeTuples_succ_eq_iUnion]
  exact (Finset.set_ncard_biUnion_le _ _).trans
    (Finset.sum_le_sum fun j _ => Set.ncard_image_le (prodLeTuples_finite _ _))
private theorem prodLeTuples_ncard_le (n : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    ((prodLeTuples n X).ncard : ℝ) ≤ X ^ 2 * 2 ^ n := by
  induction n generalizing X with
  | zero =>
      have huniv : prodLeTuples 0 X = Set.univ := by
        ext d; simp [prodLeTuples, Subsingleton.elim d 0, hX]
      rw [huniv, Set.ncard_univ, Nat.card_unique, pow_zero, Nat.cast_one, mul_one]
      nlinarith [hX, sq_nonneg (X - 1)]
  | succ n ih =>
      refine le_trans (Nat.cast_le.mpr (prodLeTuples_succ_ncard_le n X)) ?_
      push_cast
      refine le_trans (Finset.sum_le_sum fun i hi => ih ?_) ?_
      · rw [le_div_iff₀ (by exact_mod_cast (Finset.mem_Icc.mp hi).1)]
        simpa using le_trans (mod_cast (Finset.mem_Icc.mp hi).2) (Nat.floor_le (by linarith))
      · have h_sum : ∑ j ∈ Finset.Icc 1 ⌊X⌋₊, (X / (j : ℝ)) ^ 2 * 2 ^ n
            = X ^ 2 * 2 ^ n * ∑ j ∈ Finset.Icc 1 ⌊X⌋₊, (1 / (j : ℝ)) ^ 2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
        rw [h_sum, pow_succ]
        calc X ^ 2 * 2 ^ n * ∑ j ∈ Finset.Icc 1 ⌊X⌋₊, (1 / (j : ℝ)) ^ 2
            ≤ X ^ 2 * 2 ^ n * 2 :=
              mul_le_mul_of_nonneg_left (by simpa using sum_one_div_sq_le_two ⌊X⌋₊)
                (by positivity)
          _ = X ^ 2 * (2 ^ n * 2) := by ring
section RankinCount
open _root_.NumberField Ideal IsDedekindDomain UniqueFactorizationMonoid
noncomputable section
variable (F : Type*) [Field F] [NumberField F]
private def absNormUnder (P : Ideal (𝓞 F)) : ℕ := Ideal.absNorm (Ideal.under ℤ P)
private def primeCoord (P : Ideal (𝓞 F)) : ℕ :=
  (IsDedekindDomain.primesOverFinset (Ideal.under ℤ P) (𝓞 F)).toList.idxOf P
private def encodeIdeal (I : Ideal (𝓞 F)) (i : Fin (Module.finrank ℚ F)) : ℕ :=
  ∏ P ∈ (normalizedFactors I).toFinset.filter (fun P => primeCoord F P = i.val),
    (absNormUnder F P) ^ ((normalizedFactors I).count P)
private theorem mem_primesOverFinset_under {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    P ∈ IsDedekindDomain.primesOverFinset (Ideal.under ℤ P) (𝓞 F) := by
  have hP_max : P.IsMaximal := Ideal.IsPrime.isMaximal hP hP0
  rw [ IsDedekindDomain.mem_primesOverFinset_iff ];
  · constructor;
    · exact hP;
    · constructor;
      rfl;
  · exact Ideal.under_ne_bot (A := ℤ) hP0
private theorem card_primesOverFinset_le_finrank {p : Ideal ℤ} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    (IsDedekindDomain.primesOverFinset p (𝓞 F)).card ≤ Module.finrank ℚ F :=
  calc (IsDedekindDomain.primesOverFinset p (𝓞 F)).card
      = ∑ _q : p.primesOver (𝓞 F), 1 := by
        rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ,
          ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
          ← IsDedekindDomain.coe_primesOverFinset hp0 (𝓞 F), Set.ncard_coe_finset]
    _ ≤ ∑ q : p.primesOver (𝓞 F), q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ :=
        Finset.sum_le_sum fun q _ => Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero (Ideal.ramificationIdx_pos q.1 ℤ).ne'
            (Ideal.inertiaDeg_pos q.1 ℤ).ne')
    _ = Module.finrank ℤ (𝓞 F) := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 F)
    _ = Module.finrank ℚ F := NumberField.RingOfIntegers.rank F
private theorem primeCoord_lt {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    primeCoord F P < Module.finrank ℚ F := by
  have hp0 : Ideal.under ℤ P ≠ ⊥ := Ideal.under_ne_bot (A := ℤ) hP0
  have hmax : (Ideal.under ℤ P).IsMaximal := Ideal.IsPrime.isMaximal (IsPrime.under ℤ P) hp0
  calc primeCoord F P
      < (IsDedekindDomain.primesOverFinset (Ideal.under ℤ P) (𝓞 F)).toList.length := by
        rw [primeCoord]
        exact List.idxOf_lt_length_iff.mpr
          (Finset.mem_toList.mpr (mem_primesOverFinset_under F hP hP0))
    _ = (IsDedekindDomain.primesOverFinset (Ideal.under ℤ P) (𝓞 F)).card := Finset.length_toList _
    _ ≤ Module.finrank ℚ F := card_primesOverFinset_le_finrank F hp0
omit [NumberField F] in
private theorem under_eq_of_absNormUnder_eq {P Q : Ideal (𝓞 F)}
    (hr : absNormUnder F P = absNormUnder F Q) :
    Ideal.under ℤ P = Ideal.under ℤ Q := by
  have hr' : Ideal.absNorm (Ideal.under ℤ P) = Ideal.absNorm (Ideal.under ℤ Q) := hr
  rw [← Int.ideal_span_absNorm_eq_self (Ideal.under ℤ P),
    ← Int.ideal_span_absNorm_eq_self (Ideal.under ℤ Q), hr']
private theorem prime_eq_of_absNormUnder_eq_of_primeCoord_eq {P Q : Ideal (𝓞 F)}
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hQ : Q.IsPrime) (hQ0 : Q ≠ ⊥)
    (hr : absNormUnder F P = absNormUnder F Q) (hc : primeCoord F P = primeCoord F Q) : P = Q := by
  have hUeq : Ideal.under ℤ P = Ideal.under ℤ Q := under_eq_of_absNormUnder_eq F hr
  set l := (IsDedekindDomain.primesOverFinset (Ideal.under ℤ P) (𝓞 F)).toList with hl
  have hPl : P ∈ l := Finset.mem_toList.mpr (mem_primesOverFinset_under F hP hP0)
  have hQl : Q ∈ l := by
    rw [hl, hUeq]
    exact Finset.mem_toList.mpr (mem_primesOverFinset_under F hQ hQ0)
  have hidx : l.idxOf P = l.idxOf Q := by
    have hP' : l.idxOf P = primeCoord F P := by rw [primeCoord, hl]
    have hQ' : l.idxOf Q = primeCoord F Q := by rw [primeCoord, hl, hUeq]
    rw [hP', hQ', hc]
  exact (List.idxOf_inj hPl).mp hidx
private theorem encodeIdeal_pos {I : Ideal (𝓞 F)}
    (i : Fin (Module.finrank ℚ F)) : 0 < encodeIdeal F I i := by
  refine Finset.prod_pos fun P hP => ?_
  rw [Finset.mem_filter, Multiset.mem_toFinset] at hP
  have hPp : P.IsPrime := isPrime_of_prime (prime_of_normalized_factor P hP.1)
  have hP0 : P ≠ ⊥ := ne_zero_of_mem_normalizedFactors hP.1
  have := hPp
  have : NeZero P := ⟨hP0⟩
  exact pow_pos (by simpa [absNormUnder] using (Nat.absNorm_under_prime P).pos) _
private theorem prod_encodeIdeal_eq {I : Ideal (𝓞 F)} :
    ∏ i, encodeIdeal F I i =
      ∏ P ∈ (normalizedFactors I).toFinset,
        (absNormUnder F P) ^ ((normalizedFactors I).count P) := by
  have h_sum : ∏ i : Fin (Module.finrank ℚ F), encodeIdeal F I i =
      ∏ P ∈ (normalizedFactors I).toFinset, ∏ i : Fin (Module.finrank ℚ F),
        if primeCoord F P = i.val then
          (absNormUnder F P) ^ ((normalizedFactors I).count P)
        else 1 := by
    rw [Finset.prod_comm, Finset.prod_congr rfl]
    unfold encodeIdeal
    simp +decide [Finset.prod_ite]
  rw [h_sum]
  refine Finset.prod_congr rfl fun P hP => ?_
  have hPp : P.IsPrime :=
    isPrime_of_prime (prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP))
  have hP0 : P ≠ ⊥ := ne_zero_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP)
  rw [Fintype.prod_eq_single ⟨primeCoord F P, primeCoord_lt F hPp hP0⟩]
  · simp
  · intro i hi
    have hcoord : primeCoord F P ≠ i.val := by
      intro hval
      exact hi (Fin.ext hval.symm)
    simp [hcoord]
private theorem prod_encodeIdeal_le_absNorm {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    ∏ i, encodeIdeal F I i ≤ Ideal.absNorm I := by
  rw [prod_encodeIdeal_eq F]
  have h_prod_le : ∏ P ∈ (normalizedFactors I).toFinset,
      (Ideal.absNorm P) ^ ((normalizedFactors I).count P) ≤ Ideal.absNorm I := by
    have h_prod_le : ∏ P ∈ (normalizedFactors I).toFinset,
          (Ideal.absNorm P) ^ ((normalizedFactors I).count P)
        = Ideal.absNorm (∏ P ∈ (normalizedFactors I).toFinset,
          P ^ ((normalizedFactors I).count P)) := by
      simp only [map_prod, map_pow]
    have hI_eq : ∏ P ∈ (normalizedFactors I).toFinset,
        P ^ ((normalizedFactors I).count P) = I := by
      rw [← Finset.prod_multiset_count, Ideal.prod_normalizedFactors_eq_self hI]
    exact le_of_eq (h_prod_le.trans (by rw [hI_eq]))
  refine le_trans ?_ h_prod_le
  gcongr with Q hQ
  have hQ0 : Q ≠ ⊥ := ne_zero_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hQ)
  exact Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hQ0))
    (by simpa [absNormUnder] using Int.absNorm_under_dvd_absNorm Q)
private theorem count_eq_padicValNat {I : Ideal (𝓞 F)} {P : Ideal (𝓞 F)}
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) : (normalizedFactors I).count P =
      padicValNat (absNormUnder F P)
        (encodeIdeal F I ⟨primeCoord F P, primeCoord_lt F hP hP0⟩) := by
  classical
  have := hP
  have : NeZero P := ⟨hP0⟩
  have hpp : (absNormUnder F P).Prime := by simpa [absNormUnder] using Nat.absNorm_under_prime P
  have hfact : ∀ Q ∈ (normalizedFactors I).toFinset.filter
      (fun Q => primeCoord F Q = primeCoord F P),
      (absNormUnder F Q) ^ ((normalizedFactors I).count Q) ≠ 0 := by
    intro Q hQ
    rw [Finset.mem_filter, Multiset.mem_toFinset] at hQ
    have hQp : Q.IsPrime := isPrime_of_prime (prime_of_normalized_factor Q hQ.1)
    have hQ0 : Q ≠ ⊥ := ne_zero_of_mem_normalizedFactors hQ.1
    have := hQp
    have : NeZero Q := ⟨hQ0⟩
    exact pow_ne_zero _ (by simpa [absNormUnder] using (Nat.absNorm_under_prime Q).pos.ne')
  rw [eq_comm, ← Nat.factorization_def _ hpp]
  simp only [encodeIdeal]
  rw [Nat.factorization_prod hfact]
  rw [Finset.sum_apply']
  rw [Finset.sum_eq_single P]
  · rw [hpp.factorization_pow, Finsupp.single_apply]
    simp
  · intro Q hQ hQP
    rw [Finset.mem_filter, Multiset.mem_toFinset] at hQ
    have hQp : Q.IsPrime := isPrime_of_prime (prime_of_normalized_factor Q hQ.1)
    have hQ0 : Q ≠ ⊥ := ne_zero_of_mem_normalizedFactors hQ.1
    have hrb : absNormUnder F Q ≠ absNormUnder F P := fun h =>
      hQP (prime_eq_of_absNormUnder_eq_of_primeCoord_eq F hQp hQ0 hP hP0 h hQ.2)
    have := hQp
    have : NeZero Q := ⟨hQ0⟩
    have hQbelow : (absNormUnder F Q).Prime := by
      simpa [absNormUnder] using Nat.absNorm_under_prime Q
    rw [hQbelow.factorization_pow, Finsupp.single_apply]
    simp [hrb]
  · intro hPnot
    rw [Finset.mem_filter, Multiset.mem_toFinset] at hPnot
    rw [not_and] at hPnot
    have hPmem : P ∉ normalizedFactors I := fun hmem => (hPnot hmem) rfl
    rw [Multiset.count_eq_zero_of_notMem hPmem]
    simp
private theorem encodeIdeal_injOn :
    Set.InjOn (encodeIdeal F) {I : Ideal (𝓞 F) | I ≠ ⊥} := by
  intro I hI J hJ h_eq
  have hcount : ∀ {P : Ideal (𝓞 F)}, P.IsPrime → P ≠ ⊥ →
      (normalizedFactors I).count P = (normalizedFactors J).count P := by
    intro P hPp hP0
    rw [count_eq_padicValNat F hPp hP0, count_eq_padicValNat F hPp hP0, h_eq]
  have hms : normalizedFactors I = normalizedFactors J := by
    refine Multiset.ext.mpr fun P => ?_
    by_cases hmem : P ∈ normalizedFactors I ∨ P ∈ normalizedFactors J
    · obtain hP | hP := hmem
      · have hPp : P.IsPrime := isPrime_of_prime (prime_of_normalized_factor P hP)
        have hP0 : P ≠ ⊥ := ne_zero_of_mem_normalizedFactors hP
        exact hcount hPp hP0
      · have hPp : P.IsPrime := isPrime_of_prime (prime_of_normalized_factor P hP)
        have hP0 : P ≠ ⊥ := ne_zero_of_mem_normalizedFactors hP
        exact hcount hPp hP0
    · rw [not_or] at hmem
      rw [Multiset.count_eq_zero_of_notMem hmem.1, Multiset.count_eq_zero_of_notMem hmem.2]
  rw [← Ideal.prod_normalizedFactors_eq_self hI, ← Ideal.prod_normalizedFactors_eq_self hJ, hms]
end
end RankinCount
open _root_.NumberField in
private theorem ideal_ncard_le_prodLeTuples_ncard (F : Type*) [Field F] [NumberField F] {X : ℝ} :
    {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X}.ncard ≤
      (prodLeTuples (Module.finrank ℚ F) X).ncard := by
  classical
  refine Set.ncard_le_ncard_of_injOn (encodeIdeal F) ?_ ?_ (prodLeTuples_finite _ _)
  · rintro I ⟨hI0, hIX⟩
    refine ⟨fun i => encodeIdeal_pos F i, ?_⟩
    calc (∏ i, (encodeIdeal F I i : ℝ))
        = ((∏ i, encodeIdeal F I i : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (Ideal.absNorm I : ℝ) := by exact_mod_cast prod_encodeIdeal_le_absNorm F hI0
      _ ≤ X := hIX
  · intro I hI J hJ h
    exact encodeIdeal_injOn F hI.1 hJ.1 h
open _root_.NumberField in
theorem card_ideal_absNorm_le (F : Type*) [Field F] [NumberField F] {X : ℝ} (hX : 1 ≤ X) :
    {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X}.Finite ∧
      (({I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X}.ncard : ℝ)) ≤
        X ^ 2 * 2 ^ Module.finrank ℚ F := by
  refine ⟨?_, ?_⟩
  · apply Set.Finite.subset (Ideal.finite_setOfPred_absNorm_le ⌊X⌋₊)
    rintro I ⟨-, hI⟩
    exact Nat.le_floor hI
  · calc ((({I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X}).ncard : ℝ))
        ≤ ((prodLeTuples (Module.finrank ℚ F) X).ncard : ℝ) := by
          exact_mod_cast ideal_ncard_le_prodLeTuples_ncard F (X := X)
      _ ≤ X ^ 2 * 2 ^ Module.finrank ℚ F := prodLeTuples_ncard_le _ hX
section Consumer
open scoped _root_.NumberField
open Module _root_.NumberField
end Consumer
end TauCeti.NumberField
end
end
section
section
namespace TauCeti
private theorem index_powMonoidHom_range_le_of_closure_eq_top {G : Type*} [CommGroup G]
    {S : Finset G} {n : ℕ} (hn : n ≠ 0) (hS : Subgroup.closure (S : Set G) = ⊤) :
    (powMonoidHom n : G →* G).range.index ≤ n ^ S.card := by
  classical
  set H := (powMonoidHom n : G →* G).range with hH
  have : Group.FG G := Group.fg_iff'.mpr ⟨S.card, S, rfl, hS⟩
  have : Group.FG (G ⧸ H) := Group.fg_of_surjective (QuotientGroup.mk'_surjective H)
  have hpow : ∀ q : G ⧸ H, q ^ n = 1 := fun q =>
    QuotientGroup.induction_on q fun g => by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact ⟨g, by rw [powMonoidHom_apply]⟩
  have hcard : Nat.card (G ⧸ H) ∣ n ^ Group.rank (G ⧸ H) :=
    card_dvd_exponent_pow_rank' (G ⧸ H) hpow
  have hrank : Group.rank (G ⧸ H) ≤ S.card :=
    (Group.rank_le_of_surjective (QuotientGroup.mk' H) (QuotientGroup.mk'_surjective H)).trans
      (Group.rank_le hS)
  calc H.index
      = Nat.card (G ⧸ H) := Subgroup.index_eq_card H
    _ ≤ n ^ Group.rank (G ⧸ H) := Nat.le_of_dvd (pow_pos (Nat.pos_of_ne_zero hn) _) hcard
    _ ≤ n ^ S.card := Nat.pow_le_pow_right (Nat.pos_of_ne_zero hn) hrank
theorem square_eq_powMonoidHom_two_range {G : Type*} [CommGroup G] :
    Subgroup.square G = (powMonoidHom 2 : G →* G).range := by
  ext g
  rw [Subgroup.mem_square, MonoidHom.mem_range]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h, by rw [powMonoidHom_apply, sq]⟩
  · rintro ⟨h, rfl⟩
    exact ⟨h, by rw [powMonoidHom_apply, sq]⟩
theorem index_square_le_of_closure_eq_top {G : Type*} [CommGroup G]
    {S : Finset G} (hS : Subgroup.closure (S : Set G) = ⊤) :
    (Subgroup.square G).index ≤ 2 ^ S.card := by
  rw [square_eq_powMonoidHom_two_range]
  exact index_powMonoidHom_range_le_of_closure_eq_top (by norm_num) hS
end TauCeti
end
end
section
section
namespace TauCeti
variable (G : Type*) [CommGroup G]
abbrev ElementaryTwoQuotient : Type _ :=
  ModN (Additive G) 2
instance [Finite G] : Finite (ElementaryTwoQuotient G) :=
  Finite.of_surjective _ (QuotientAddGroup.mk'_surjective _)
variable {G}
def elementaryTwoQuotientMkAdd : Additive G →+ ElementaryTwoQuotient G :=
  ModN.mkQ 2
def elementaryTwoQuotientMk (g : G) : ElementaryTwoQuotient G :=
  elementaryTwoQuotientMkAdd (Additive.ofMul g)
private theorem mem_range_lsmul_two_iff (a : Additive G) :
    a ∈ LinearMap.range (LinearMap.lsmul ℤ (Additive G) ↑(2 : ℕ)) ↔
      IsSquare (Additive.toMul a) := by
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨Additive.toMul b, ?_⟩
    have hmul := congr_arg Additive.toMul hb
    simpa [toMul_zsmul, zpow_two, pow_two] using hmul.symm
  · rintro ⟨b, hb⟩
    refine ⟨Additive.ofMul b, ?_⟩
    apply Additive.toMul.injective
    simpa [toMul_zsmul, zpow_two, pow_two] using hb.symm
@[simp] theorem elementaryTwoQuotientMk_eq_zero_iff (g : G) :
    elementaryTwoQuotientMk g = 0 ↔ IsSquare g := by
  rw [elementaryTwoQuotientMk, elementaryTwoQuotientMkAdd, ModN.mkQ]
  simp only [AddMonoidHom.coe_coe, Submodule.mkQ_apply]
  rw [Submodule.Quotient.mk_eq_zero]
  exact mem_range_lsmul_two_iff (Additive.ofMul g)
protected def elementaryTwoQuotientLinearLiftEquiv [AddCommGroup H] [Module (ZMod 2) H] :
    (ElementaryTwoQuotient G →ₗ[ZMod 2] H) ≃ {φ : Additive G →+ H // ∀ g, 2 • φ g = 0} :=
  ModN.liftEquiv'
@[simp] theorem elementaryTwoQuotientMk_mul (g h : G) :
    elementaryTwoQuotientMk (g * h) = elementaryTwoQuotientMk g + elementaryTwoQuotientMk h := by
  simp only [elementaryTwoQuotientMk, ofMul_mul, AddMonoidHom.map_add]
@[simp] theorem elementaryTwoQuotientMk_one : elementaryTwoQuotientMk (1 : G) = 0 := by
  simp only [elementaryTwoQuotientMk, ofMul_one, AddMonoidHom.map_zero]
@[simp] theorem elementaryTwoQuotientMk_inv (g : G) :
    elementaryTwoQuotientMk g⁻¹ = -elementaryTwoQuotientMk g := by
  simp only [elementaryTwoQuotientMk, ofMul_inv, map_neg]
@[simp] theorem elementaryTwoQuotientMk_div (g h : G) :
    elementaryTwoQuotientMk (g / h) = elementaryTwoQuotientMk g - elementaryTwoQuotientMk h := by
  simp only [elementaryTwoQuotientMk, ofMul_div, map_sub]
@[simp] theorem elementaryTwoQuotientMk_pow (g : G) (n : ℕ) :
    elementaryTwoQuotientMk (g ^ n) = n • elementaryTwoQuotientMk g := by
  simp only [elementaryTwoQuotientMk, ofMul_pow, map_nsmul]
theorem elementaryTwoQuotientMk_surjective :
    Function.Surjective (elementaryTwoQuotientMk : G → ElementaryTwoQuotient G) := by
  intro x
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact ⟨Additive.toMul a, rfl⟩
variable {H : Type*} [CommGroup H]
noncomputable def elementaryTwoQuotientMap (f : G →* H) :
    ElementaryTwoQuotient G →ₗ[ZMod 2] ElementaryTwoQuotient H :=
  (TauCeti.elementaryTwoQuotientLinearLiftEquiv (G := G) (H := ElementaryTwoQuotient H)).symm
    ⟨{ toFun := fun g => elementaryTwoQuotientMk (f (Additive.toMul g))
       map_zero' := by
        change elementaryTwoQuotientMk (f 1) = 0
        simp
       map_add' := by
        intro g h
        change elementaryTwoQuotientMk (f (Additive.toMul (g + h))) =
          elementaryTwoQuotientMk (f (Additive.toMul g)) +
            elementaryTwoQuotientMk (f (Additive.toMul h))
        simp },
      fun g => by
        change 2 • elementaryTwoQuotientMk (f (Additive.toMul g)) = 0
        rw [← elementaryTwoQuotientMk_pow]
        exact (elementaryTwoQuotientMk_eq_zero_iff _).2
          ⟨f (Additive.toMul g), by rw [pow_two]⟩⟩
@[simp] theorem elementaryTwoQuotientMap_mk (f : G →* H) (g : G) :
    elementaryTwoQuotientMap f (elementaryTwoQuotientMk g) =
      elementaryTwoQuotientMk (f g) := by
  rfl
@[simp] theorem elementaryTwoQuotientMap_id_apply (x : ElementaryTwoQuotient G) :
    elementaryTwoQuotientMap (MonoidHom.id G) x = x := by
  obtain ⟨g, rfl⟩ := elementaryTwoQuotientMk_surjective (G := G) x
  simp
variable {K : Type*} [CommGroup K]
@[simp] theorem elementaryTwoQuotientMap_comp_apply (f : G →* H) (g : H →* K)
    (x : ElementaryTwoQuotient G) :
    elementaryTwoQuotientMap (g.comp f) x =
      elementaryTwoQuotientMap g (elementaryTwoQuotientMap f x) := by
  obtain ⟨a, rfl⟩ := elementaryTwoQuotientMk_surjective (G := G) x
  simp
noncomputable def elementaryTwoQuotientCongr (e : G ≃* H) :
    ElementaryTwoQuotient G ≃ₗ[ZMod 2] ElementaryTwoQuotient H where
  toLinearMap := elementaryTwoQuotientMap e.toMonoidHom
  invFun := elementaryTwoQuotientMap e.symm.toMonoidHom
  left_inv x := by
    obtain ⟨g, rfl⟩ := elementaryTwoQuotientMk_surjective (G := G) x
    simp
  right_inv x := by
    obtain ⟨h, rfl⟩ := elementaryTwoQuotientMk_surjective (G := H) x
    simp
@[simp] theorem elementaryTwoQuotientCongr_mk (e : G ≃* H) (g : G) :
    elementaryTwoQuotientCongr e (elementaryTwoQuotientMk g) = elementaryTwoQuotientMk (e g) := by
  exact elementaryTwoQuotientMap_mk e.toMonoidHom g
@[simp] theorem elementaryTwoQuotientCongr_symm_mk (e : G ≃* H) (h : H) :
    (elementaryTwoQuotientCongr e).symm (elementaryTwoQuotientMk h) =
      elementaryTwoQuotientMk (e.symm h) := by
  exact elementaryTwoQuotientMap_mk e.symm.toMonoidHom h
@[simp] theorem elementaryTwoQuotientCongr_refl_apply (x : ElementaryTwoQuotient G) :
    elementaryTwoQuotientCongr (MulEquiv.refl G) x = x :=
  elementaryTwoQuotientMap_id_apply x
@[simp] theorem elementaryTwoQuotientCongr_trans_apply (e : G ≃* H) (e' : H ≃* K)
    (x : ElementaryTwoQuotient G) :
    elementaryTwoQuotientCongr (e.trans e') x =
      elementaryTwoQuotientCongr e' (elementaryTwoQuotientCongr e x) :=
  elementaryTwoQuotientMap_comp_apply e.toMonoidHom e'.toMonoidHom x
variable (G)
noncomputable def twoRank : ℕ :=
  Module.finrank (ZMod 2) (ElementaryTwoQuotient G)
@[simp] theorem twoRank_def :
    twoRank G = Module.finrank (ZMod 2) (ElementaryTwoQuotient G) := rfl
section FiniteCardinality
variable [Finite G]
end FiniteCardinality
end TauCeti
end
end
section
section
open Module Polynomial
namespace TauCeti
namespace Algebra
theorem trace_eq_zero_of_sq_algebraMap_of_not_mem_range {F L : Type*} [Field F] [Field L]
    [Algebra F L] [FiniteDimensional F L] {x : L} {r : F}
    (hx2 : x ^ 2 = algebraMap F L r) (hx : x ∉ (algebraMap F L).range) :
    Algebra.trace F L x = 0 := by
  have hmonic : (X ^ 2 - C r).Monic := Polynomial.monic_X_pow_sub_C r (by norm_num)
  have haeval : aeval x (X ^ 2 - C r : F[X]) = 0 := by simp [hx2]
  have hdvd : minpoly F x ∣ (X ^ 2 - C r) := minpoly.dvd F x haeval
  have hint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have hne : (X ^ 2 - C r : F[X]) ≠ 0 := Polynomial.X_pow_sub_C_ne_zero (by norm_num) r
  have hdeg2 : (minpoly F x).natDegree = 2 := by
    have hle : (minpoly F x).natDegree ≤ 2 := by
      have := Polynomial.natDegree_le_of_dvd hdvd hne
      simpa [Polynomial.natDegree_X_pow_sub_C] using this
    have hge : 2 ≤ (minpoly F x).natDegree := by
      by_contra h
      rw [not_le] at h
      interval_cases hh : (minpoly F x).natDegree
      · exact (minpoly.natDegree_pos hint).ne' hh
      · exact hx (minpoly.natDegree_eq_one_iff.mp hh)
    omega
  have heq : minpoly F x = X ^ 2 - C r :=
    (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hmonic hdvd
      (by rw [hdeg2, Polynomial.natDegree_X_pow_sub_C])).symm
  rw [trace_eq_finrank_mul_minpoly_nextCoeff, heq]
  have hnc : (X ^ 2 - C r : F[X]).nextCoeff = 0 := by
    rw [Polynomial.nextCoeff_of_natDegree_pos
      (by rw [Polynomial.natDegree_X_pow_sub_C]; norm_num)]
    simp [Polynomial.coeff_X_pow]
  rw [hnc]; simp
variable {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L]
end Algebra
namespace NumberField
theorem trace_eq_zero_of_sq_ratCast {K : Type*} [Field K] [NumberField K]
    {x : K} {r : ℚ} (hx2 : x ^ 2 = algebraMap ℚ K r) (hx : x ∉ (algebraMap ℚ K).range) :
    Algebra.trace ℚ K x = 0 :=
  TauCeti.Algebra.trace_eq_zero_of_sq_algebraMap_of_not_mem_range hx2 hx
alias trace_eq_zero_of_sq_ratCast_of_not_mem_range := trace_eq_zero_of_sq_ratCast
end TauCeti.NumberField
end
end
section
section
variable (K L : Type*) [Field K]
variable [Field L] [Algebra K L] [Algebra.IsQuadraticExtension K L]
namespace Algebra.IsQuadraticExtension
end Algebra.IsQuadraticExtension
end
end
section
section
open Module
namespace TauCeti.NumberField.Internal
end TauCeti.NumberField.Internal
end
end
section
section
open Module
namespace TauCeti
namespace NumberField
theorem abs_discr_le_of_basis_isIntegral {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ K)
    (hb : ∀ i, IsIntegral ℤ (b i)) :
    |(NumberField.discr K : ℚ)| ≤ |Algebra.discr ℚ (b : ι → K)| := by
  classical
  set c := NumberField.integralBasis K with hc
  obtain ⟨e, -⟩ : ∃ _ : Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K) ≃ ι, True := by
    refine ⟨Fintype.equivOfCardEq ?_, trivial⟩
    rw [← Module.finrank_eq_card_basis c, ← Module.finrank_eq_card_basis b]
  set P : Matrix ι ι ℚ := (c.reindex e).toMatrix b with hPdef
  have hdiscc : Algebra.discr ℚ (c.reindex e) = (NumberField.discr K : ℚ) := by
    rw [Module.Basis.coe_reindex, Algebra.discr_reindex, hc, NumberField.coe_discr]
  have hP : Algebra.discr ℚ b = P.det ^ 2 * (NumberField.discr K : ℚ) := by
    rw [← hdiscc]
    convert Algebra.discr_of_matrix_vecMul (c.reindex e) P using 2
    convert (Module.Basis.toMatrix_map_vecMul (c.reindex e) b).symm using 1
  obtain ⟨d, hd⟩ : ∃ d : ℤ, P.det = d := by
    have hP_int : ∀ i j, ∃ z : ℤ, P i j = z := by
      intro i j
      obtain ⟨y, hy⟩ : ∃ y : NumberField.RingOfIntegers K, b j = algebraMap _ K y :=
        ⟨⟨b j, hb j⟩, rfl⟩
      refine ⟨(NumberField.RingOfIntegers.basis K).repr y (e.symm i), ?_⟩
      rw [hPdef, Module.Basis.toMatrix_apply, Module.Basis.repr_reindex_apply, hc, hy]
      simp
    choose f hf using hP_int
    exact ⟨(Matrix.of f).det, by simp [hf, Matrix.det_apply']⟩
  rw [hP, abs_mul, hd]
  rcases eq_or_ne d 0 with hd0 | hd0
  · exact absurd (by rw [hP, hd, hd0]; push_cast; ring)
      (Algebra.discr_not_zero_of_basis ℚ b)
  · refine le_mul_of_one_le_left (abs_nonneg _) ?_
    rw [abs_pow]
    exact one_le_pow₀ (by exact_mod_cast Int.one_le_abs hd0)
end TauCeti.NumberField
end
end
section
section
open scoped NumberField
open Module NumberField NumberField.Units
namespace TauCeti.NumberField
theorem units_sq_index_le (F : Type*) [Field F] [NumberField F] :
    (Subgroup.square (𝓞 F)ˣ).index ≤ 2 ^ Module.finrank ℚ F := by
  classical
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := torsion F)
  set S : Finset (𝓞 F)ˣ :=
    insert (ζ : (𝓞 F)ˣ) (Finset.image (fundSystem F) Finset.univ) with hSdef
  have hζS : (ζ : (𝓞 F)ˣ) ∈ Subgroup.closure (S : Set (𝓞 F)ˣ) :=
    Subgroup.subset_closure (Finset.mem_coe.mpr (Finset.mem_insert_self _ _))
  have hgen : Subgroup.closure (S : Set (𝓞 F)ˣ) = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← closure_fundSystem_sup_torsion_eq_top F, sup_le_iff]
    refine ⟨Subgroup.closure_mono ?_, ?_⟩
    · rw [hSdef]
      simp only [Finset.coe_insert, Finset.coe_image, Finset.coe_univ, Set.image_univ]
      exact Set.subset_insert _ _
    · intro t ht
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hζ ⟨t, ht⟩)
      have ht' : (ζ : (𝓞 F)ˣ) ^ n = t := by
        simpa [SubgroupClass.coe_zpow] using congrArg Subtype.val hn
      rw [← ht']
      exact zpow_mem hζS n
  refine (TauCeti.index_square_le_of_closure_eq_top hgen).trans
    (Nat.pow_le_pow_right (by norm_num) ?_)
  calc S.card ≤ (Finset.image (fundSystem F) Finset.univ).card + 1 := Finset.card_insert_le _ _
    _ ≤ rank F + 1 := by
        gcongr
        exact Finset.card_image_le.trans_eq (by rw [Finset.card_univ, Fintype.card_fin])
    _ ≤ Module.finrank ℚ F := by
        have h1 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F
        have h2 := InfinitePlace.card_add_two_mul_card_eq_rank F
        have h3 : 0 < Fintype.card (InfinitePlace F) :=
          Fintype.card_pos_iff.mpr ⟨Classical.arbitrary _⟩
        simp only [rank]
        omega
end TauCeti.NumberField
end
end
section
section
open scoped NumberField
open Module _root_.NumberField
namespace TauCeti.NumberField
private lemma minkowski_factor_sq_mul_two_pow_le_four_pow {n s : ℕ} (h : 2 * s ≤ n) :
    (4 / Real.pi) ^ (2 * s) * ((n.factorial / n ^ n : ℝ)) ^ 2 * 2 ^ n ≤ 4 ^ n := by
  refine le_trans (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (by positivity) ?_)
    (by positivity)) ?_
  · have h_factorial_le_pow : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by
      exact_mod_cast Nat.factorial_le_pow n
    exact pow_le_one₀ (by positivity) (div_le_one_of_le₀ h_factorial_le_pow (by positivity))
  · have h_pi_le_two : (4 : ℝ) / Real.pi ≤ 2 := by
      rw [div_le_iff₀] <;> linarith [Real.pi_gt_three]
    have h_four : (4 : ℝ) = 2 ^ 2 := by norm_num
    refine le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity)
      h_pi_le_two _)
      (by positivity)) ?_
    rw [h_four, ← pow_mul, ← pow_add]
    gcongr <;> norm_num
    linarith
theorem classNumber_le_bound (F : Type*) [Field F] [NumberField F] :
    (NumberField.classNumber F : ℝ) ≤
      |(NumberField.discr F : ℝ)| * 4 ^ Module.finrank ℚ F := by
  have := @NumberField.exists_ideal_in_class_of_norm_le F _ _
  choose f hf using this
  have h_card : (Set.ncard (Set.image (fun C => (f C : Ideal (𝓞 F))) Set.univ)) ≤
      (4 / Real.pi) ^ (2 * InfinitePlace.nrComplexPlaces F) *
        ((Module.finrank ℚ F).factorial / (Module.finrank ℚ F) ^ Module.finrank ℚ F) ^ 2 *
        |(discr F : ℝ)| * 2 ^ Module.finrank ℚ F := by
    have h_card : (Set.ncard {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤
        (4 / Real.pi) ^ InfinitePlace.nrComplexPlaces F *
          ((Module.finrank ℚ F).factorial / (Module.finrank ℚ F) ^ Module.finrank ℚ F *
            Real.sqrt |(discr F : ℝ)|)}) ≤
        (4 / Real.pi) ^ (2 * InfinitePlace.nrComplexPlaces F) *
          ((Module.finrank ℚ F).factorial / (Module.finrank ℚ F) ^ Module.finrank ℚ F) ^ 2 *
          |(discr F : ℝ)| * 2 ^ Module.finrank ℚ F := by
      convert card_ideal_absNorm_le F _ |>.2 using 1
      · ring_nf; norm_num [Real.sq_sqrt <| abs_nonneg _]
      · refine le_trans ?_ (hf 1 |>.2)
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_ne_zero_of_nonZeroDivisors _)
    refine le_trans ?_ h_card
    gcongr
    · convert card_ideal_absNorm_le F _ |>.1 using 1
      refine le_trans ?_ (hf 1 |>.2)
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_ne_zero_of_nonZeroDivisors _)
    · simp only [Set.image_univ]
      exact Set.range_subset_iff.mpr fun C =>
        ⟨by intro h; simpa [h] using f C |>.2, hf C |>.2⟩
  refine le_trans ?_ (h_card.trans ?_)
  · rw [Set.ncard_image_of_injective _ fun x y hxy => ?_, Set.ncard_univ]
    · norm_num [classNumber]
    · have := hf x; have := hf y; aesop
  ·
    suffices h_simp : (4 / Real.pi) ^ (2 * InfinitePlace.nrComplexPlaces F) *
        ((Module.finrank ℚ F).factorial / (Module.finrank ℚ F) ^ Module.finrank ℚ F) ^ 2 *
        2 ^ Module.finrank ℚ F ≤ 4 ^ Module.finrank ℚ F by
      convert mul_le_mul_of_nonneg_left h_simp (abs_nonneg (discr F : ℝ)) using 1; ring
    have := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank F
    exact minkowski_factor_sq_mul_two_pow_le_four_pow (by linarith)
end TauCeti.NumberField
end
end
section
namespace Erdos
section Multiquadratic
open Polynomial Module
theorem trace_eq_zero_of_sq_ratCast {K : Type*} [Field K] [NumberField K] {x : K} {r : ℚ}
    (hx2 : x ^ 2 = algebraMap ℚ K r) (hx : x ∉ (algebraMap ℚ K).range) :
    Algebra.trace ℚ K x = 0 := by
  have hmonic : (X ^ 2 - C r).Monic := Polynomial.monic_X_pow_sub_C r (by norm_num)
  have haeval : aeval x (X ^ 2 - C r : ℚ[X]) = 0 := by simp [hx2]
  have hdvd : minpoly ℚ x ∣ (X ^ 2 - C r) := minpoly.dvd ℚ x haeval
  have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have hne : (X ^ 2 - C r : ℚ[X]) ≠ 0 := Polynomial.X_pow_sub_C_ne_zero (by norm_num) r
  have hdeg2 : (minpoly ℚ x).natDegree = 2 := by
    have hle : (minpoly ℚ x).natDegree ≤ 2 := by
      have := Polynomial.natDegree_le_of_dvd hdvd hne
      simpa [Polynomial.natDegree_X_pow_sub_C] using this
    have hge : 2 ≤ (minpoly ℚ x).natDegree := by
      by_contra h
      push Not at h
      interval_cases hh : (minpoly ℚ x).natDegree
      · exact (minpoly.natDegree_pos hint).ne' hh
      · exact hx (minpoly.natDegree_eq_one_iff.mp hh)
    omega
  have heq : minpoly ℚ x = X ^ 2 - C r :=
    (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hmonic hdvd
      (by rw [hdeg2, Polynomial.natDegree_X_pow_sub_C])).symm
  rw [trace_eq_finrank_mul_minpoly_nextCoeff, heq]
  have hnc : (X ^ 2 - C r : ℚ[X]).nextCoeff = 0 := by
    rw [Polynomial.nextCoeff_of_natDegree_pos
      (by rw [Polynomial.natDegree_X_pow_sub_C]; norm_num)]
    simp [Polynomial.coeff_X_pow]
  rw [hnc]; simp
variable (g : ℕ)
noncomputable def mqGenC : Option (Fin g) → ℂ
  | none => Complex.I
  | some j => ((Real.sqrt (q3 j) : ℝ) : ℂ)
theorem mqGenC_mem (k : Option (Fin g)) : mqGenC g k ∈ Kf g := by
  cases k with
  | none => exact IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
  | some j => exact IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ ⟨j, j.2, rfl⟩)
noncomputable def mqGen (k : Option (Fin g)) : Kf g := ⟨mqGenC g k, mqGenC_mem g k⟩
noncomputable def mqSq : Option (Fin g) → ℚ
  | none => -1
  | some j => (q3 j : ℚ)
noncomputable def mqB (S : Finset (Option (Fin g))) : Kf g := ∏ k ∈ S, mqGen g k
noncomputable def mqRS (S : Finset (Option (Fin g))) : ℚ := ∏ k ∈ S, mqSq g k
theorem mqGen_sq (k : Option (Fin g)) :
    (mqGen g k) ^ 2 = algebraMap ℚ (Kf g) (mqSq g k) := by
  cases k with
  | none =>
    apply Subtype.ext
    simp only [mqGen, mqGenC, mqSq]
    push_cast
    simp [Complex.I_sq]
  | some j =>
    apply Subtype.ext
    simp only [mqGen, mqGenC, mqSq]
    push_cast
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    norm_cast
theorem mqB_sq (S : Finset (Option (Fin g))) :
    (mqB g S) ^ 2 = algebraMap ℚ (Kf g) (mqRS g S) := by
  unfold mqB mqRS;
  rw [ ← Finset.prod_pow, map_prod ];
  exact Finset.prod_congr rfl fun x hx => mqGen_sq g x
theorem mqGen_isIntegral (k : Option (Fin g)) : IsIntegral ℤ (mqGen g k) := by
  rcases k with ( _ | k );
  · refine ⟨ Polynomial.X ^ 2 + 1, ?_, ?_ ⟩;
    · erw [ Polynomial.Monic, Polynomial.leadingCoeff_X_pow_add_C ] ; norm_num;
    · simp +decide only [algebraMap_int_eq, eval₂_add, eval₂_X_pow, eval₂_one];
      apply Subtype.ext
      norm_num [mqGen, mqGenC, Complex.I_sq]
  · refine ⟨ Polynomial.X ^ 2 - Polynomial.C ( q3 k : ℤ ), ?_, ?_ ⟩;
    · erw [ Polynomial.Monic, Polynomial.leadingCoeff_X_pow_sub_C ] ; norm_num;
    · simp +decide [ sub_eq_zero, mqGen_sq ];
      norm_cast
theorem mqB_isIntegral (S : Finset (Option (Fin g))) : IsIntegral ℤ (mqB g S) := by
  convert! IsIntegral.prod _ fun k hk => mqGen_isIntegral g k
theorem mqRS_ne_zero (S : Finset (Option (Fin g))) : mqRS g S ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr ?_;
  rintro ( _ | j ) <;> norm_num [ mqSq ];
  exact fun _ => Nat.Prime.ne_zero ( q3_spec j |>.1 )
theorem mqRS_not_isSquare {U : Finset (Option (Fin g))} (hU : U.Nonempty) :
    ¬IsSquare (mqRS g U) :=
  by
    by_cases hnone : none ∈ U <;> simp_all +decide only [IsSquare, not_exists];
    · have h_prod_pos : 0 < ∏ k ∈ U.erase none, (mqSq g k : ℚ) :=
        by
          refine Finset.prod_pos fun k hk => ?_
          cases k <;> simp_all +decide only [Finset.mem_erase,
            ne_eq, not_true_eq_false, and_true, reduceCtorEq, not_false_eq_true, true_and, mqSq,
            Nat.cast_pos];
          exact Nat.Prime.pos (q3_spec _ |>.1);
      unfold mqRS;
      rw [← Finset.insert_erase hnone, Finset.prod_insert (Finset.notMem_erase _ _)];
      exact fun x hx =>
        by
          rw [show mqSq g none = -1 by rfl] at hx; nlinarith;
    ·
      obtain ⟨N, hN⟩ : ∃ N : ℕ, mqRS g U = N ∧ Squarefree N ∧ N ≠ 1 :=
        by
          refine ⟨∏ k ∈ U, k.elim 1 (fun j => q3 j), ?_, ?_, ?_⟩ <;> norm_num [mqRS];
          · refine Finset.prod_congr rfl fun x hx => ?_;
            rcases x with (_ | j) <;> simp_all +decide [mqSq];
          ·
            have h_squarefree :
              ∀ {S : Finset ℕ}, (∀ p ∈ S, Nat.Prime p) → Squarefree (∏ p ∈ S, p) :=
              by
                intros S hS;
                induction S using Finset.induction <;>
                  simp_all +decide only [Finset.prod_empty, isUnit_iff_eq_one, IsUnit.squarefree,
                    Finset.mem_insert, or_true, implies_true, forall_const, forall_eq_or_imp,
                    not_false_eq_true, Finset.prod_insert, Nat.squarefree_mul_iff, and_true];
                exact
                  ⟨Nat.Coprime.prod_right fun p hp =>
                      hS.1.coprime_iff_not_dvd.mpr fun h =>
                        ‹¬_› <|
                          by
                            have := Nat.prime_dvd_prime_iff_eq hS.1 (hS.2 p hp); aesop,
                    hS.1.squarefree⟩;
            convert h_squarefree _ using 1; rotate_left;
            · exact Finset.image (fun k => k.elim 1 fun j => q3 j) U;
            · simp +zetaDelta only [Finset.mem_image, forall_exists_index, and_imp,
                forall_apply_eq_imp_iff₂] at *;
              intro a ha; cases a <;> simp_all +decide [q3_spec];
            · rw [Finset.prod_image]; intro x hx y hy hxy
              cases x with
              | none => exact False.elim (hnone hx)
              | some x =>
                cases y with
                | none => exact False.elim (hnone hy)
                | some y => exact congrArg some (Fin.ext (q3_strictMono.injective hxy))
          · obtain ⟨x, hx⟩ := hU
            refine ⟨x, hx, ?_⟩
            cases x with
            | none => exact False.elim (hnone hx)
            | some x => exact (q3_spec x).1.ne_one
      intro x hx;
      have :=
        Rat.isSquare_natCast_iff.mp
          (show IsSquare (N : ℚ) from
            ⟨x,
              by
                linarith⟩);
      simp_all +decide [isSquare_iff_exists_sq]; rcases this with ⟨r, rfl⟩;
      simp_all +decide [sq, Nat.squarefree_mul_iff]; tauto
theorem mqB_notMem_range {U : Finset (Option (Fin g))} (hU : U.Nonempty) :
    mqB g U ∉ (algebraMap ℚ (Kf g)).range := by
  intro h
  obtain ⟨q, hq⟩ := h
  have hq_sq : q ^ 2 = mqRS g U := by
    apply (algebraMap ℚ (Kf g)).injective
    rw [map_pow, hq]
    exact mqB_sq g U
  exact mqRS_not_isSquare g hU ⟨q, by rw [← hq_sq, sq]⟩
theorem trace_mqB_zero {U : Finset (Option (Fin g))} (hU : U.Nonempty) :
    Algebra.trace ℚ (Kf g) (mqB g U) = 0 := by
  exact trace_eq_zero_of_sq_ratCast (mqB_sq g U) (mqB_notMem_range g hU)
theorem trace_mqB_mul_of_ne {S T : Finset (Option (Fin g))} (h : S ≠ T) :
    Algebra.trace ℚ (Kf g) (mqB g S * mqB g T) = 0 :=
  by
    have h_symm_diff_nonempty : (S \ T ∪ T \ S).Nonempty :=
      by
        contrapose! h; aesop;
    have h_claim :
      mqB g S * mqB g T =
        algebraMap ℚ (Kf g) (∏ k ∈ S ∩ T, mqSq g k) * mqB g (S \ T ∪ T \ S) :=
      by
        have h_claim :
          mqB g S * mqB g T = (∏ k ∈ S ∪ T, mqGen g k) * (∏ k ∈ S ∩ T, mqGen g k) :=
          by
            simp +decide only [mqB]; rw [← Finset.prod_union_inter];
        rw [h_claim, show S ∪ T = (S \ T ∪ T \ S) ∪ (S ∩ T) from ?_, Finset.prod_union];
        · simp +decide only [map_prod, eq_ratCast]; rw [mul_assoc, ← Finset.prod_mul_distrib];
          rw [mul_comm]; congr; ext; simp +decide [← sq, mqGen_sq];
        · exact
            Finset.disjoint_left.mpr
              (by
                aesop);
        · grind;
    convert congr_arg (fun x : Kf g => Algebra.trace ℚ (Kf g) x) h_claim using 1;
    rw [← Algebra.smul_def, LinearMap.map_smul, trace_mqB_zero _ h_symm_diff_nonempty,
      smul_zero]
theorem trace_mqB_mul_self (S : Finset (Option (Fin g))) :
    Algebra.trace ℚ (Kf g) (mqB g S * mqB g S)
      = (finrank ℚ (Kf g) : ℚ) * mqRS g S := by
  convert congr_arg ( fun x : Kf g => Algebra.trace ℚ ( Kf g ) x ) ( mqB_sq g S ) using 1;
  · rw [ sq ];
  · rw [ Algebra.trace_algebraMap ];
    norm_num [ Algebra.smul_def ]
theorem traceMatrix_mqB :
    Algebra.traceMatrix ℚ (mqB g) =
      Matrix.diagonal (fun S => (finrank ℚ (Kf g) : ℚ) * mqRS g S) :=
  by
    convert Matrix.ext _; intro S T;
    by_cases h : S = T <;>
      simp +decide [h, Algebra.traceMatrix_apply, Algebra.traceForm_apply,
        trace_mqB_mul_of_ne, trace_mqB_mul_self];
theorem discr_mqB_ne_zero : Algebra.discr ℚ (mqB g) ≠ 0 :=
  by
    rw [Algebra.discr_def, traceMatrix_mqB g];
    simp +zetaDelta only [Matrix.det_diagonal, ne_eq] at *;
    exact
      Finset.prod_ne_zero_iff.mpr fun S _ =>
        mul_ne_zero (Nat.cast_ne_zero.mpr <| ne_of_gt <| Module.finrank_pos) <|
          mqRS_ne_zero g S
theorem mqB_linearIndependent : LinearIndependent ℚ (mqB g) := by
  by_contra h
  exact discr_mqB_ne_zero g (Algebra.discr_zero_of_not_linearIndependent ℚ h)
theorem mq_Kf_finrank_le : finrank ℚ (Kf g) ≤ 2 ^ (g + 1) := by
  exact (Kf_finrank g).le
theorem Kf_card_index : Fintype.card (Finset (Option (Fin g))) = 2 ^ (g + 1) := by
  rw [Fintype.card_finset, Fintype.card_option, Fintype.card_fin]
theorem mq_Kf_finrank_eq : finrank ℚ (Kf g) = 2 ^ (g + 1) := by
  refine le_antisymm (mq_Kf_finrank_le g) ?_
  have h := (mqB_linearIndependent g).fintype_card_le_finrank
  rwa [Kf_card_index] at h
theorem mqRS_abs_le (S : Finset (Option (Fin g))) :
    |mqRS g S| ≤ ∏ j ∈ Finset.range g, (q3 j : ℚ) :=
  by
    have h_abs : |mqRS g S| = ∏ k ∈ S, |mqSq g k| :=
      by
        rw [← Finset.abs_prod, show mqRS g S = ∏ k ∈ S, mqSq g k by rfl];
    have h_abs_ge_one : ∀ k : Option (Fin g), 1 ≤ |mqSq g k| :=
      by
        intro k; rcases k with (_ | j) <;> norm_num [mqSq];
        exact Nat.Prime.pos (q3_spec j |>.1);
    have h_prod_le_prod_univ : ∏ k ∈ S, |mqSq g k| ≤ ∏ k ∈ Finset.univ, |mqSq g k| :=
      by
        rw [← Finset.prod_sdiff (Finset.subset_univ S)];
        exact
          le_mul_of_one_le_left (Finset.prod_nonneg fun _ _ => abs_nonneg _)
            (le_trans
              (by
                norm_num)
              (Finset.prod_le_prod
                (fun _ _ =>
                  by
                    norm_num)
                fun _ _ => h_abs_ge_one _));
    simp_all +decide only [ge_iff_le];
    exact
      h_prod_le_prod_univ.trans
        (by
          rw [Finset.prod_range]; simp +decide [mqSq])
theorem abs_discr_mqB_le :
    |Algebra.discr ℚ (mqB g)| ≤
      (4 ^ (g + 1) * ∏ j ∈ Finset.range g, (q3 j : ℚ)) ^ 2 ^ (g + 1) :=
  by
    rw [Algebra.discr_def, traceMatrix_mqB]; norm_num [Finset.abs_prod, abs_mul];
    refine
        le_trans
          (Finset.prod_le_prod ?_ fun x _ =>
            mul_le_mul_of_nonneg_left (mqRS_abs_le g x) (Nat.cast_nonneg _))
          ?_ <;>
      norm_num [mq_Kf_finrank_eq];
    gcongr; decide +revert
end Multiquadratic
theorem Kf_discr_le (g : ℕ) :
    |(NumberField.discr (Kf g) : ℝ)| ≤
      (4 ^ (g + 1) * ∏ j ∈ Finset.range g, (q3 j : ℝ)) ^ 2 ^ (g + 1) := by
  classical
  have hli := mqB_linearIndependent g
  have hcard : Fintype.card (Finset (Option (Fin g))) = Module.finrank ℚ (Kf g) := by
    rw [mq_Kf_finrank_eq, Kf_card_index]
  set bas := basisOfLinearIndependentOfCardEqFinrank hli hcard with hbas_def
  have hbas : ⇑bas = mqB g := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hint : ∀ i, IsIntegral ℤ (bas i) := by
    intro i
    rw [show bas i = mqB g i from congrFun hbas i]
    exact mqB_isIntegral g i
  have h1 : |(NumberField.discr (Kf g) : ℚ)| ≤ |Algebra.discr ℚ (mqB g)| := by
    have h := TauCeti.NumberField.abs_discr_le_of_basis_isIntegral bas hint
    rwa [hbas] at h
  have h2 := abs_discr_mqB_le g
  have h3 : |(NumberField.discr (Kf g) : ℚ)| ≤
      (4 ^ (g + 1) * ∏ j ∈ Finset.range g, (q3 j : ℚ)) ^ 2 ^ (g + 1) := le_trans h1 h2
  exact_mod_cast h3
theorem Kf_one_lt_finrank (g : ℕ) : 1 < Module.finrank ℚ (Kf g) :=
  by
    have h_deg :
      2 * NumberField.InfinitePlace.nrComplexPlaces (Kf g) = Module.finrank ℚ (Kf g) :=
      by
        rw [NumberField.IsTotallyComplex.finrank];
    linarith [show 0 < NumberField.InfinitePlace.nrComplexPlaces (Kf g) from
        by
          linarith [show 0 < Module.finrank ℚ (Kf g) from Module.finrank_pos]];
theorem q3_log_sum_le :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ g : ℕ, ∑ j ∈ Finset.range g, Real.log (q3 j) ≤ C * (g + 1) * Real.log (g + 2) :=
  by
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ j ≥ N, (q3 j : ℝ) ≤ (j + 2) ^ 2 :=
      by
        exact Filter.eventually_atTop.mp (q3_poly_bound);
    refine ⟨(∑ j ∈ Finset.range N, Real.log (q3 j)) / Real.log 2 + 2, ?_, ?_⟩;
    · exact
        add_nonneg
          (div_nonneg
            (Finset.sum_nonneg fun _ _ =>
              Real.log_nonneg (mod_cast Nat.Prime.pos (q3_spec _ |>.1)))
            (Real.log_nonneg
              (by
                norm_num)))
          zero_le_two;
    · intro g
      by_cases hg : g ≤ N;
      · refine
          le_trans
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hg) fun _ _ _ =>
              Real.log_nonneg <| mod_cast Nat.Prime.pos <| q3_spec _ |>.1)
            ?_;
        refine
          le_trans ?_
            (mul_le_mul_of_nonneg_left
              (Real.log_le_log
                (by
                  positivity)
                (show (g : ℝ) + 2 ≥ 2 by linarith))
              (by
                exact
                  mul_nonneg
                      (add_nonneg
                        (div_nonneg
                            (Finset.sum_nonneg fun _ _ =>
                              Real.log_nonneg <| mod_cast Nat.Prime.pos <| q3_spec _ |>.1) <|
                          Real.log_nonneg <|
                            by
                              norm_num)
                        zero_le_two) <|
                    by
                      positivity));
        nlinarith [Real.log_pos one_lt_two,
          mul_div_cancel₀ (∑ j ∈ Finset.range N, Real.log (q3 j))
            (ne_of_gt (Real.log_pos one_lt_two)),
          show (g : ℝ) + 1 ≥ 1 by linarith,
          show (∑ j ∈ Finset.range N, Real.log (q3 j)) ≥ 0 by
            exact
              Finset.sum_nonneg fun _ _ =>
                Real.log_nonneg <| mod_cast Nat.Prime.pos <| q3_spec _ |>.1];
      ·
        have h_tail :
          ∑ j ∈ Finset.Ico N g, Real.log (q3 j) ≤ 2 * (g - N) * Real.log (g + 2) :=
          by
            have h_tail : ∀ j ∈ Finset.Ico N g, Real.log (q3 j) ≤ 2 * Real.log (g + 2) :=
              by
                intros j hj
                have h_log_bound : Real.log (q3 j) ≤ Real.log ((j + 2) ^ 2) :=
                  by
                    exact
                      Real.log_le_log (Nat.cast_pos.mpr (Nat.Prime.pos (q3_spec j |>.1)))
                        (hN j (Finset.mem_Ico.mp hj |>.1));
                exact
                  h_log_bound.trans
                    (by
                      rw [Real.log_pow]; norm_num;
                      exact
                        Real.log_le_log
                          (by
                            positivity)
                          (by
                            norm_cast; linarith [Finset.mem_Ico.mp hj]));
            convert! Finset.sum_le_sum h_tail; norm_num [Nat.cast_sub (le_of_not_ge hg)];
            ring;
        have h_head :
          ∑ j ∈ Finset.range N, Real.log (q3 j) ≤
            (∑ j ∈ Finset.range N, Real.log (q3 j)) / Real.log 2 * (g + 1) *
              Real.log (g + 2) :=
          by
            rw [div_mul_eq_mul_div, div_mul_eq_mul_div,
              le_div_iff₀
                (by
                  positivity)];
            rw [mul_assoc];
            exact
              mul_le_mul_of_nonneg_left
                (by
                  nlinarith [Real.log_pos one_lt_two,
                    Real.log_le_log
                      (by
                        positivity)
                      (by
                          linarith :
                        (g : ℝ) + 2 ≥ 2),
                    show (g : ℝ) ≥ N + 1 by norm_cast; linarith])
                (Finset.sum_nonneg fun _ _ =>
                  Real.log_nonneg <|
                    mod_cast
                      Nat.Prime.pos <|
                        by
                          have := q3_spec ‹_›; aesop);
        rw [← Finset.sum_range_add_sum_Ico _ (show N ≤ g from le_of_not_ge hg)];
        nlinarith [show 0 ≤ Real.log (g + 2) by
            exact
              Real.log_nonneg
                (by
                  linarith),
          show (N : ℝ) ≤ g by norm_cast; linarith]
theorem log_discr_Kf_le :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ g : ℕ,
          Real.log |(NumberField.discr (Kf g) : ℝ)| ≤
            C * 2 ^ g * (g + 1) * Real.log (g + 2) :=
  by
    obtain ⟨C, hC⟩ :
      ∃ C : ℝ,
        0 ≤ C ∧
          ∀ g ≥ 100,
            Real.log |(NumberField.discr (Kf g) : ℝ)| ≤
              C * 2 ^ g * (g + 1) * Real.log (g + 2) :=
      by
        have := q3_log_sum_le; obtain ⟨C, hC₀, hC⟩ := this; use 2 * (2 + C);
        refine
          ⟨by
              positivity,
            fun g hg => ?_⟩;
        have := Kf_discr_le g; refine le_trans (Real.log_le_log (?_) this) ?_;
        · exact abs_pos.mpr (mod_cast NumberField.discr_ne_zero _);
        · rw [Real.log_pow, Real.log_mul, Real.log_prod] <;> norm_cast <;> norm_num;
          · rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring_nf at *;
            nlinarith [hC g, show (0 : ℝ) ≤ 2 ^ g by positivity,
              show (0 : ℝ) ≤ g * 2 ^ g by positivity, show (0 : ℝ) ≤ C * 2 ^ g by positivity,
              show (0 : ℝ) ≤ C * g * 2 ^ g by positivity, Real.log_pos one_lt_two,
              Real.log_le_log
                (by
                  positivity)
                (by
                    linarith :
                  (2 : ℝ) + g ≥ 2)];
          · exact fun x hx => Nat.Prime.ne_zero (q3_spec x |>.1);
          · exact Finset.prod_ne_zero_iff.mpr fun i hi => Nat.Prime.ne_zero <| q3_spec i |>.1;
    obtain ⟨C', hC'⟩ :
      ∃ C' : ℝ,
        0 ≤ C' ∧
          ∀ g < 100,
            Real.log |(NumberField.discr (Kf g) : ℝ)| ≤
              C' * 2 ^ g * (g + 1) * Real.log (g + 2) :=
      by
        have h_finite :
          ∃ C' : ℝ,
            ∀ g < 100,
              Real.log |(NumberField.discr (Kf g) : ℝ)| ≤
                C' * 2 ^ g * (g + 1) * Real.log (g + 2) :=
          by
            have h_discr_bound :
              ∀ g < 100,
                ∃ C_g : ℝ,
                  Real.log |(NumberField.discr (Kf g) : ℝ)| ≤
                    C_g * 2 ^ g * (g + 1) * Real.log (g + 2) :=
              by
                intro g hg;
                use
                  Real.log |(NumberField.discr (Kf g) : ℝ)| /
                    (2 ^ g * (g + 1) * Real.log (g + 2));
                rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div];
                rw [le_div_iff₀]
                · ring_nf; norm_num;
                · exact
                    mul_pos
                      (mul_pos
                        (pow_pos
                          (by
                            norm_num)
                          _)
                        (by
                          positivity))
                      (Real.log_pos
                        (by
                          linarith))
            choose! C' hC' using h_discr_bound; use sSup (Set.image C' (Finset.range 100));
            intro g hg; refine le_trans (hC' g hg) ?_; gcongr;
            · exact
                Real.log_nonneg
                  (by
                    linarith);
            · exact
                le_csSup
                    (by
                      exact Set.Finite.bddAbove <| Set.toFinite _) <|
                  Set.mem_image_of_mem _ <| Finset.mem_coe.mpr <| Finset.mem_range.mpr hg;
        exact
          ⟨Max.max h_finite.choose 0, le_max_right _ _, fun g hg =>
            le_trans (h_finite.choose_spec g hg)
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right (le_max_left _ _)
                    (by
                      positivity))
                  (by
                    positivity))
                (Real.log_nonneg
                  (by
                    linarith)))⟩;
    exact
      ⟨Max.max C C', le_max_of_le_left hC.1, fun g =>
        if hg : g < 100 then
          le_trans (hC'.2 g hg)
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (le_max_right _ _)
                  (by
                    positivity))
                (by
                  positivity))
              (Real.log_nonneg
                (by
                  linarith)))
        else
          le_trans (hC.2 g (le_of_not_gt hg))
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (le_max_left _ _)
                  (by
                    positivity))
                (by
                  positivity))
              (Real.log_nonneg
                (by
                  linarith)))⟩
theorem log_classNumber_le_log_discr :
    ∃ a b : ℝ,
      0 ≤ a ∧
        ∀ g : ℕ,
          Real.log (NumberField.classNumber (Kf g)) ≤
            a * Real.log |(NumberField.discr (Kf g) : ℝ)| + b :=
  by
    refine
        ⟨1 + (Real.log 4 / Real.log (3 * Real.pi / 4)),
          (Real.log 4 / Real.log (3 * Real.pi / 4)) * Real.log (9 / 4), ?_, ?_⟩ <;>
      norm_num;
    · exact
        add_nonneg zero_le_one
          (div_nonneg
            (Real.log_nonneg
              (by
                norm_num))
            (Real.log_nonneg
              (by
                linarith [Real.pi_gt_three])));
    · intro g
      have h1 :
        Real.log (NumberField.classNumber (Kf g)) ≤
          Real.log (|NumberField.discr (Kf g)|) + Module.finrank ℚ (Kf g) * Real.log 4 :=
        by
          have h1 :
            (NumberField.classNumber (Kf g) : ℝ) ≤
              |(NumberField.discr (Kf g) : ℝ)| * 4 ^ Module.finrank ℚ (Kf g) :=
            by
              convert TauCeti.NumberField.classNumber_le_bound (Kf g) using 1;
          convert Real.log_le_log (Nat.cast_pos.mpr <| NumberField.classNumber_pos _) h1 using
            1;
          rw [Real.log_mul
              (by
                exact ne_of_gt <| abs_pos.mpr <| mod_cast NumberField.discr_ne_zero _)
              (by
                positivity),
            Real.log_pow];
      have h2 :
        (4 / 9 : ℝ) * (3 * Real.pi / 4) ^ Module.finrank ℚ (Kf g) ≤
          |NumberField.discr (Kf g)| :=
        by
          convert NumberField.abs_discr_ge (Kf_one_lt_finrank g) using 1;
      have h3 :
        Real.log (4 / 9) + Module.finrank ℚ (Kf g) * Real.log (3 * Real.pi / 4) ≤
          Real.log (|NumberField.discr (Kf g)|) :=
        by
          convert
            Real.log_le_log
              (by
                positivity)
              h2 using
            1;
          · norm_num [Real.log_mul, Real.log_pow]
          · norm_num [abs_mul, abs_of_nonneg, Real.log_nonneg]
      rw [show (9 / 4 : ℝ) = (4 / 9)⁻¹ by norm_num, Real.log_inv];
      norm_num [abs_of_nonneg, Real.log_nonneg] at *;
      nlinarith [show 0 < Real.log 4 / Real.log (3 * Real.pi / 4) by
          exact
            div_pos
              (Real.log_pos
                (by
                  norm_num))
              (Real.log_pos
                (by
                  linarith [Real.pi_gt_three])),
        mul_div_cancel₀ (Real.log 4)
          (ne_of_gt
            (Real.log_pos
              (by
                  linarith [Real.pi_gt_three] :
                1 < 3 * Real.pi / 4)))]
theorem log_classNumber_Kf_le :
    ∃ c₀ : ℝ,
      1 ≤ c₀ ∧
        ∀ g : ℕ,
          Real.log (NumberField.classNumber (Kf g)) ≤
            c₀ * 2 ^ g * (g + 1) * Real.log (g + 2) :=
  by
    obtain ⟨a, b, ha, hab⟩ := log_classNumber_le_log_discr
    obtain ⟨C, hC, hCg⟩ := log_discr_Kf_le
    use a * C + |b| / Real.log 2 + 1; refine ⟨?_, fun g => le_trans (hab g) ?_⟩;
    · exact
        le_add_of_nonneg_left
          (add_nonneg (mul_nonneg ha hC)
            (div_nonneg (abs_nonneg b)
              (Real.log_nonneg
                (by
                  norm_num))));
    ·
      have hL_pos : Real.log 2 ≤ 2 ^ g * (g + 1) * Real.log (g + 2) :=
        by
          exact
            le_trans
              (Real.log_le_log
                (by
                  norm_num)
                (by
                  linarith))
              (le_mul_of_one_le_left
                (Real.log_nonneg
                  (by
                    linarith))
                (one_le_mul_of_one_le_of_one_le
                  (one_le_pow₀
                    (by
                      norm_num))
                  (by
                    linarith)));
      cases abs_cases b <;>
        nlinarith [show 0 ≤ a * C by positivity, show 0 ≤ |b| / Real.log 2 by positivity,
          mul_div_cancel₀ (|b| : ℝ) (ne_of_gt (Real.log_pos one_lt_two)), hCg g,
          Real.log_pos one_lt_two]
end Erdos
end
section
section
open scoped Classical
namespace TauCeti.DedekindDomain
variable {R : Type*} [CommRing R] [IsDedekindDomain R]
include R
private theorem isPrime_not_dvd_prod (p : IsDedekindDomain.HeightOneSpectrum R)
    {T : Finset (IsDedekindDomain.HeightOneSpectrum R)} (hpT : p ∉ T) :
    ¬ p.asIdeal ∣ ∏ q ∈ T, q.asIdeal := by
  have := p.isPrime
  have hpprime : Prime p.asIdeal := p.prime
  rw [Prime.dvd_finsetProd_iff hpprime]
  rintro ⟨q, hqT, hpq⟩
  have heq : q.asIdeal = p.asIdeal := q.isMaximal.eq_of_le p.isMaximal.ne_top (Ideal.le_of_dvd hpq)
  exact hpT (IsDedekindDomain.HeightOneSpectrum.ext heq ▸ hqT)
omit R [CommRing R] [IsDedekindDomain R] in
private theorem notMem_pair_of_apply_involutive {α : Type*} [DecidableEq α] {f : α → α}
    {p q x : α} (hqdef : q = f p) (hinvolx : f (f x) = x) (hinvolp : f (f p) = p)
    (hxnotpair : x ∉ ({p, q} : Finset α)) : f x ∉ ({p, q} : Finset α) := by
  rw [Finset.mem_insert, Finset.mem_singleton]
  rintro (h | h)
  ·
    refine hxnotpair ?_
    rw [Finset.mem_insert, Finset.mem_singleton]
    exact Or.inr <| calc
      x = f (f x) := hinvolx.symm
      _ = f p := by rw [h]
      _ = q := hqdef.symm
  ·
    refine hxnotpair ?_
    rw [Finset.mem_insert, Finset.mem_singleton]
    exact Or.inl <| calc
      x = f (f x) := hinvolx.symm
      _ = f q := by rw [h]
      _ = f (f p) := by rw [hqdef]
      _ = p := hinvolp
omit [IsDedekindDomain R] in
private lemma asIdeal_equivOfRingEquiv (σ : R ≃+* R) (p : IsDedekindDomain.HeightOneSpectrum R) :
    (IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ p).asIdeal =
      Ideal.map σ p.asIdeal := by
  ext x
  change σ.symm x ∈ p.asIdeal ↔ x ∈ Ideal.map σ p.asIdeal
  exact Ideal.symm_apply_mem_of_equiv_iff
private theorem disjoint_image_mul_asIdeal {p q : IsDedekindDomain.HeightOneSpectrum R}
    {G' : Finset (Ideal R)} (hpq : q ≠ p) (hpFree : ∀ A ∈ G', ¬ p.asIdeal ∣ A) :
    Disjoint (G'.image (· * p.asIdeal)) (G'.image (· * q.asIdeal)) := by
  rw [Finset.disjoint_left]
  rintro A hAp hAq
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hAp
  obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp hAq
  have hpdvd : p.asIdeal ∣ b := by
    have hpdvd' : p.asIdeal ∣ b * q.asIdeal := hab.symm ▸ dvd_mul_left p.asIdeal a
    rcases ((Ideal.prime_iff_isPrime p.ne_bot).mpr p.isPrime).dvd_or_dvd hpdvd' with h | h
    · exact h
    · exact absurd (q.isMaximal.eq_of_le p.isMaximal.ne_top (Ideal.le_of_dvd h))
        (fun hpqIdeal => hpq (IsDedekindDomain.HeightOneSpectrum.ext hpqIdeal))
  exact hpFree b hb hpdvd
omit R [CommRing R] [IsDedekindDomain R] in
private lemma two_pow_div_two_le_two_mul_two_pow_div_two_of_le_add_two {m n : ℕ} (hmn : n ≤ m + 2) :
    2 ^ (n / 2) ≤ 2 * 2 ^ (m / 2) := by
  rw [← pow_succ']
  exact Nat.pow_le_pow_right (by norm_num) (by omega)
omit R [CommRing R] [IsDedekindDomain R] in
private theorem mul_map_eq_prod_of_mem_image_union {R : Type*} [CommSemiring R] {σ : R →+* R}
    {prodS prodS' P Q : Ideal R} {G' : Finset (Ideal R)}
    (hqIdeal : Q = Ideal.map σ P) (hmapq : Ideal.map σ Q = P) (hprodS : prodS = prodS' * P * Q)
    (hprod' : ∀ a ∈ G', a * Ideal.map σ a = prodS') {A : Ideal R}
    (hA : A ∈ G'.image (· * P) ∪ G'.image (· * Q)) :
    A * Ideal.map σ A = prodS := by
  rw [Finset.mem_union] at hA
  rcases hA with hA | hA
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hA
    rw [Ideal.map_mul, ← hqIdeal, hprodS, ← hprod' a ha]; ring
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hA
    rw [Ideal.map_mul, hmapq, hprodS, ← hprod' a ha]; ring
private lemma two_pow_le_card_union_image_mul {G' : Finset (Ideal R)}
    {p q : IsDedekindDomain.HeightOneSpectrum R}
    (hdisj : Disjoint (G'.image (· * p.asIdeal)) (G'.image (· * q.asIdeal)))
    {n m : ℕ} (hcard' : 2 ^ (m / 2) ≤ G'.card) (hnm : n ≤ m + 2) :
    2 ^ (n / 2) ≤ ((G'.image (· * p.asIdeal)) ∪ (G'.image (· * q.asIdeal))).card := by
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ (fun _ _ h => mul_right_cancel₀ p.ne_bot h),
    Finset.card_image_of_injective _ (fun _ _ h => mul_right_cancel₀ q.ne_bot h)]
  calc 2 ^ (n / 2) ≤ 2 * 2 ^ (m / 2) :=
        two_pow_div_two_le_two_mul_two_pow_div_two_of_le_add_two hnm
    _ ≤ G'.card + G'.card := by omega
omit [IsDedekindDomain R] in
private lemma mem_sdiff_pair_of_invariant {σ : R ≃+* R}
    {S : Finset (IsDedekindDomain.HeightOneSpectrum R)} {p q : IsDedekindDomain.HeightOneSpectrum R}
    (hqdef : q = IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ p)
    (hinv : ∀ x ∈ S, IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ x ∈ S)
    (hinvol : ∀ x ∈ S, IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ
      (IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ x) = x) (hpS : p ∈ S) :
    ∀ x ∈ S \ {p, q}, IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ x ∈ S \ {p, q} := by
  intro x hx
  have hxS := (Finset.mem_sdiff.mp hx).1
  refine Finset.mem_sdiff.mpr ⟨hinv x hxS, ?_⟩
  exact notMem_pair_of_apply_involutive
    (f := IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ) hqdef (hinvol x hxS)
    (hinvol p hpS) (Finset.mem_sdiff.mp hx).2
private theorem exists_transversal_family_of_sdiff_pair (σ : R ≃+* R)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum R)}
    {p : IsDedekindDomain.HeightOneSpectrum R} (hpS : p ∈ S)
    (hqS : IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ p ∈ S)
    (hpq : IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ p ≠ p)
    (hinvol : IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ
      (IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ p) = p) {G' : Finset (Ideal R)}
    (hcard' : 2 ^ ((S \ {p, IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ p}).card / 2)
      ≤ G'.card)
    (hprod' : ∀ A ∈ G', A * Ideal.map σ A =
      ∏ x ∈ S \ {p, IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ p}, x.asIdeal) :
    ∃ G : Finset (Ideal R), 2 ^ (S.card / 2) ≤ G.card ∧
      ∀ A ∈ G, A * Ideal.map σ A = ∏ x ∈ S, x.asIdeal := by
  set q := IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ p with hqdef
  have hpair : ({p, q} : Finset (IsDedekindDomain.HeightOneSpectrum R)) ⊆ S :=
    Finset.insert_subset_iff.mpr ⟨hpS, Finset.singleton_subset_iff.mpr hqS⟩
  have hqIdeal : q.asIdeal = Ideal.map σ p.asIdeal := by
    rw [hqdef]; exact asIdeal_equivOfRingEquiv σ p
  have hprodS : ∏ x ∈ S, x.asIdeal
      = (∏ x ∈ S \ {p, q}, x.asIdeal) * p.asIdeal * q.asIdeal := by
    rw [← Finset.prod_sdiff hpair, Finset.prod_pair hpq.symm, mul_assoc]
  have hcardS : (S \ {p, q}).card = S.card - 2 := by
    have h := Finset.card_sdiff_add_card_eq_card hpair
    rw [Finset.card_pair hpq.symm] at h
    omega
  have hpS' : p ∉ S \ {p, q} := fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_insert_self _ _)
  refine ⟨(G'.image (· * p.asIdeal)) ∪ (G'.image (· * q.asIdeal)), ?_, ?_⟩
  ·
    have hdisj : Disjoint (G'.image (· * p.asIdeal)) (G'.image (· * q.asIdeal)) :=
      disjoint_image_mul_asIdeal hpq (fun A hA hpA =>
        isPrime_not_dvd_prod p hpS' (hprod' A hA ▸ dvd_mul_of_dvd_left hpA (Ideal.map σ A)))
    exact two_pow_le_card_union_image_mul hdisj hcard' (by omega)
  · have hmapq : Ideal.map σ q.asIdeal = p.asIdeal := by
      rw [← asIdeal_equivOfRingEquiv σ q]
      exact congr_arg IsDedekindDomain.HeightOneSpectrum.asIdeal hinvol
    exact fun A hA =>
      mul_map_eq_prod_of_mem_image_union (σ := (σ : R →+* R)) hqIdeal hmapq hprodS hprod' hA
theorem exists_transversal_family (σ : R ≃+* R) (S : Finset (IsDedekindDomain.HeightOneSpectrum R))
    (hinv : ∀ p ∈ S, IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ p ∈ S) (hinvol : ∀ p ∈ S,
      IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ
        (IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ p) = p)
    (hfree : ∀ p ∈ S, IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ p ≠ p) :
    ∃ G : Finset (Ideal R), 2 ^ (S.card / 2) ≤ G.card ∧
      ∀ A ∈ G, A * Ideal.map σ A = ∏ p ∈ S, p.asIdeal := by
  induction S using Finset.strongInduction with
  | _ S ih =>
  rcases S.eq_empty_or_nonempty with rfl | hS
  · refine ⟨{1}, by simp, fun A hA => ?_⟩
    rw [Finset.mem_singleton.mp hA, Finset.prod_empty, one_mul, Ideal.one_eq_top, Ideal.map_top]
  obtain ⟨p, hpS⟩ := hS
  set q := IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ p with hqdef
  have hqS : q ∈ S := hinv p hpS
  have hS'sub : S \ {p, q} ⊂ S :=
    Finset.sdiff_ssubset (Finset.insert_subset_iff.mpr ⟨hpS, Finset.singleton_subset_iff.mpr hqS⟩)
      ⟨p, Finset.mem_insert_self _ _⟩
  have hmem' : ∀ {x}, x ∈ S \ {p, q} → x ∈ S := fun hx => (Finset.mem_sdiff.mp hx).1
  obtain ⟨G', hcard', hprod'⟩ := ih _ hS'sub (mem_sdiff_pair_of_invariant hqdef hinv hinvol hpS)
    (fun x hx => hinvol x (hmem' hx)) (fun x hx => hfree x (hmem' hx))
  exact exists_transversal_family_of_sdiff_pair σ hpS hqS (hfree p hpS) (hinvol p hpS)
    hcard' hprod'
end TauCeti.DedekindDomain
end
end
section
open NumberField IsCMField
namespace Erdos
theorem Kf_aut_sq (g : ℕ) (σ : Kf g ≃ₐ[ℚ] Kf g) : σ ^ 2 = 1 :=
  by
    have h2 : ∀ x : Kf g, σ (σ x) = x :=
      by
        have h_fixed_subfield :
          ∀ t : Kf g, (t : ℂ) ^ 2 ∈ Set.range (algebraMap ℚ ℂ) → σ (σ t) = t :=
          by
            intro t ht
            obtain ⟨q, hq⟩ := ht
            have h_sigma_sq_t : (σ t) ^ 2 = t ^ 2 :=
              by
                convert
                  congr_arg (σ : Kf g → Kf g)
                    (show t ^ 2 = (algebraMap ℚ (Kf g)) q from ?_) using
                  1; · simp +decide [map_pow];
                · simp_all +decide [← Subtype.coe_inj];
                · exact Subtype.ext <| hq.symm;
            have h_sigma_t_cases : σ t = t ∨ σ t = -t :=
              by
                exact eq_or_eq_neg_of_sq_eq_sq _ _ h_sigma_sq_t;
            cases h_sigma_t_cases <;> simp_all +decide [sq];
        have h_adjoin :
          IntermediateField.adjoin ℚ
              (insert Complex.I ((fun j => ((Real.sqrt (q3 j) : ℝ) : ℂ)) '' Set.Iio g)) =
            Kf g :=
          by
            rfl;
        intro x;
        have h_gen :
          ∀ t ∈ insert Complex.I ((fun j => ((Real.sqrt (q3 j) : ℝ) : ℂ)) '' Set.Iio g),
            ∃ t' : Kf g, (t' : ℂ) = t ∧ σ (σ t') = t' :=
          by
            intro t ht
            refine ⟨⟨t, h_adjoin ▸ IntermediateField.subset_adjoin ℚ _ ht⟩, rfl, ?_⟩
            rcases ht with rfl | ⟨j, hj, rfl⟩
            · exact
                h_fixed_subfield _
                  ⟨-1,
                    by
                      norm_num [Complex.ext_iff]⟩
            · refine h_fixed_subfield _ ⟨(q3 j : ℚ), ?_⟩
              rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg (q3 j))]
              push_cast
              ring
        have h_gen :
          ∀
            t ∈
              IntermediateField.adjoin ℚ
                (insert Complex.I ((fun j => ((Real.sqrt (q3 j) : ℝ) : ℂ)) '' Set.Iio g)),
            ∃ t' : Kf g, (t' : ℂ) = t ∧ σ (σ t') = t' :=
          by
            intro t ht; induction ht using IntermediateField.adjoin_induction;
            · exact h_gen _ ‹_›;
            · exact
                ⟨algebraMap ℚ (Kf g) ‹_›,
                  by
                    simp +decide,
                  by
                    simp +decide⟩;
            · rename_i hx hy; obtain ⟨t₁, ht₁, ht₁'⟩ := hx; obtain ⟨t₂, ht₂, ht₂'⟩ := hy;
              use t₁ + t₂; aesop;
            · rename_i t ht ih; obtain ⟨t', ht', ht''⟩ := ih; use t'⁻¹; aesop;
            · rename_i hx hy; obtain ⟨t₁, ht₁, ht₁'⟩ := hx; obtain ⟨t₂, ht₂, ht₂'⟩ := hy;
              use t₁ * t₂; aesop;
        obtain ⟨t', ht₁, ht₂⟩ := h_gen x (h_adjoin.symm ▸ x.2)
        have : t' = x := Subtype.ext ht₁
        rwa [this] at ht₂
    refine AlgEquiv.ext fun x => ?_
    rw [pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply, h2 x]
theorem Kf_eq_one_of_fixes_gens (g : ℕ) (σ : Kf g ≃ₐ[ℚ] Kf g)
    (h :
      ∀ t : Kf g,
        (↑t ∈ insert Complex.I ((fun j => ((Real.sqrt (q3 j) : ℝ) : ℂ)) '' Set.Iio g)) →
          σ t = t) :
    σ = 1 :=
  by
    have h_gen : ∀ t : Kf g, ∃ t' : Kf g, (t' : ℂ) = t ∧ σ t' = t' :=
      by
        have h_ind :
          ∀
            t ∈
              IntermediateField.adjoin ℚ
                (insert Complex.I ((fun j => ((Real.sqrt (q3 j) : ℝ) : ℂ)) '' Set.Iio g)),
            ∃ t' : Kf g, (t' : ℂ) = t ∧ σ t' = t' :=
          by
            intro t ht; induction ht using IntermediateField.adjoin_induction;
            · rename_i x hx
              exact ⟨⟨x, IntermediateField.subset_adjoin ℚ _ hx⟩, rfl, h _ hx⟩
            · exact ⟨⟨_, Subalgebra.algebraMap_mem _ _⟩, rfl, σ.commutes _⟩;
            · rename_i hx hy ihx ihy; obtain ⟨t₁, rfl, ht₁⟩ := ihx;
              obtain ⟨t₂, rfl, ht₂⟩ := ihy; use t₁ + t₂; simp +decide [ht₁, ht₂];
            · rename_i x hx ih; obtain ⟨t', rfl, ht'⟩ := ih; use t'⁻¹; aesop;
            · rename_i hx hy; obtain ⟨t₁, ht₁, ht₁'⟩ := hx; obtain ⟨t₂, ht₂, ht₂'⟩ := hy;
              use t₁ * t₂; aesop;
        exact fun t => h_ind t t.2;
    ext t; specialize h_gen t; aesop;
open scoped NumberField
open NumberField IsCMField in
theorem inertia_fixes_gen (g : ℕ) (p : ℕ) (P : Ideal (𝓞 (Kf g)))
    [P.LiesOver (Ideal.span {(p : ℤ)})] (σ : Kf g ≃ₐ[ℚ] Kf g)
    (hσ : ∀ x : 𝓞 (Kf g), σ • x - x ∈ P) (t : Kf g) (c : ℤ) (hc : (t : ℂ) ^ 2 = (c : ℂ))
    (hpc : ¬(p : ℤ) ∣ 4 * c) : σ t = t :=
  by
    have h_sigma_t : σ t = t ∨ σ t = -t :=
      by
        have h_sigma_t : σ t ^ 2 = t ^ 2 :=
          by
            have h_sigma_sq : σ (t ^ 2) = t ^ 2 :=
              by
                erw [show t ^ 2 = algebraMap ℤ (Kf g) c from Subtype.ext hc];
                simp +decide;
            simpa using h_sigma_sq;
        exact eq_or_eq_neg_of_sq_eq_sq _ _ h_sigma_t;
    by_contra h_contra
    have h_neg : σ t = -t :=
      by
        exact h_sigma_t.resolve_left h_contra;
    obtain ⟨xt, hxt⟩ : ∃ xt : 𝓞 (Kf g), (xt : Kf g) = t :=
      by
        refine ⟨⟨t, ?_⟩, rfl⟩;
        refine ⟨Polynomial.X ^ 2 - Polynomial.C c, ?_, ?_⟩ <;> norm_num;
        · erw [Polynomial.Monic, Polynomial.leadingCoeff_X_pow_sub_C]; norm_num;
        · erw [Polynomial.eval₂_C]; aesop;
    have h_diff : σ • xt - xt = -2 * xt :=
      by
        ext;
        simp only [map_sub, AddSubgroupClass.coe_sub, neg_mul, map_neg, map_mul,
          NegMemClass.coe_neg, IntermediateField.coe_mul];
        erw [show
            (algebraMap (𝓞 (Kf g)) (Kf g)) (σ • xt) = σ (algebraMap (𝓞 (Kf g)) (Kf g) xt) from
            rfl];
        norm_num [h_neg, hxt]; ring_nf; norm_cast;
    have h_four_xt_sq : 4 * xt ^ 2 ∈ P :=
      by
        have h_four_xt_sq : (-2 * xt) * (-2 * xt) ∈ P :=
          by
            exact P.mul_mem_left _ (h_diff ▸ hσ xt);
        convert h_four_xt_sq using 1; ring;
    have h_four_c : 4 * xt ^ 2 = algebraMap ℤ (𝓞 (Kf g)) (4 * c) :=
      by
        ext; simp [hxt, hc];
    have := ‹P.LiesOver (Ideal.span {(p : ℤ)})›.over;
    simp_all +decide only [or_true, ne_eq, neg_mul, algebraMap_int_eq, eq_intCast, Int.cast_mul,
      Int.cast_ofNat, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false];
    replace this := SetLike.ext_iff.mp this (4 * c);
    simp_all +decide [Ideal.mem_span_singleton];
theorem p_prime_facts {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) :
    (p : ℤ) ≠ 0 ∧ (Ideal.span {(p : ℤ)}) ≠ ⊥ ∧ (Ideal.span {(p : ℤ)}).IsPrime
      ∧ (Ideal.span {(p : ℤ)}).IsMaximal ∧ ¬ (p : ℤ) ∣ 4 := by
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp0 : (Ideal.span {(p : ℤ)}) ≠ ⊥ := by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpz
  have hpprime : (Ideal.span {(p : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime hpz]; exact_mod_cast Nat.prime_iff_prime_int.mp hp
  have hp4dvd : ¬ (p : ℤ) ∣ 4 := by
    intro h
    have h4 : p ∣ 4 := by exact_mod_cast h
    have hp2 : 2 ≤ p := hp.two_le
    have := Nat.le_of_dvd (by norm_num) h4
    interval_cases p <;> omega
  exact ⟨hpz, hp0, hpprime, hpprime.isMaximal hp0, hp4dvd⟩
theorem Kf_inertia_eq_bot (g : ℕ) (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1)
    (P : Ideal (𝓞 (Kf g))) [P.LiesOver (Ideal.span {(p : ℤ)})] :
    Ideal.inertia (Kf g ≃ₐ[ℚ] Kf g) P = ⊥ := by
  obtain ⟨hpz, hp0, hpprime, hpmax, hp4dvd⟩ := p_prime_facts hp hp4
  rw [eq_bot_iff]
  intro σ hσmem
  have hσ : ∀ x : 𝓞 (Kf g), σ • x - x ∈ P := by
    simpa using AddSubgroup.mem_inertia.mp hσmem
  rw [Subgroup.mem_bot]
  apply Kf_eq_one_of_fixes_gens g σ
  intro t ht
  rcases ht with ht | ⟨j, hj, ht⟩
  · refine inertia_fixes_gen g p P σ hσ t (-1) ?_ ?_
    · rw [ht]; rw [Complex.I_sq]; push_cast; ring
    · simpa using hp4dvd
  · refine inertia_fixes_gen g p P σ hσ t (q3 j) ?_ ?_
    · rw [← ht, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg (q3 j))]; push_cast; ring
    · rw [show (4 * (q3 j : ℤ)) = ((4 * q3 j : ℕ) : ℤ) by push_cast; ring, Int.natCast_dvd_natCast,
        Nat.Prime.dvd_mul hp]
      push Not
      refine ⟨by simpa using (by exact_mod_cast hp4dvd : ¬ p ∣ (4:ℕ)), ?_⟩
      intro h
      have := (Nat.prime_dvd_prime_iff_eq hp (q3_spec j).1).mp h
      have := (q3_spec j).2
      omega
theorem Kf_ramificationIdxIn_eq_one (g : ℕ) (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1) :
    Ideal.ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 (Kf g)) = 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hpz, hp0, hpprime, hpmax, hp4dvd⟩ := p_prime_facts hp hp4
  have : (Ideal.span {(p : ℤ)}).IsMaximal := hpmax
  obtain ⟨⟨P, hPprime, hPlies⟩⟩ :=
    (inferInstance : Nonempty (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (Kf g))))
  have := hPprime
  have := hPlies
  have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P
  have : P.IsMaximal := hPprime.isMaximal hPne
  have : Finite (ℤ ⧸ Ideal.span {(p : ℤ)}) :=
    Finite.of_equiv _ (Int.quotientSpanEquivZMod (p : ℤ)).symm.toEquiv
  have : Finite (𝓞 (Kf g) ⧸ P) := inferInstance
  let : Field (ℤ ⧸ Ideal.span {(p : ℤ)}) := Ideal.Quotient.field _
  let : Field (𝓞 (Kf g) ⧸ P) := Ideal.Quotient.field _
  have : Module.Finite (ℤ ⧸ Ideal.span {(p : ℤ)}) (𝓞 (Kf g) ⧸ P) := Module.Finite.of_finite
  have : Algebra.IsAlgebraic (ℤ ⧸ Ideal.span {(p : ℤ)}) (𝓞 (Kf g) ⧸ P) :=
    Algebra.IsAlgebraic.of_finite _ _
  have : PerfectField (ℤ ⧸ Ideal.span {(p : ℤ)}) := PerfectField.ofFinite
  have : Algebra.IsSeparable (ℤ ⧸ Ideal.span {(p : ℤ)}) (𝓞 (Kf g) ⧸ P) := inferInstance
  rw [← Ideal.card_inertia_eq_ramificationIdxIn (G := Kf g ≃ₐ[ℚ] Kf g)
        (Ideal.span {(p : ℤ)}) P, Kf_inertia_eq_bot g p hp hp4 P, Subgroup.card_bot]
noncomputable def primesOverP1 (g i : ℕ) : Finset (Ideal (𝓞 (Kf g))) :=
  haveI : (Ideal.span {((p1 i : ℤ))}).IsMaximal :=
    (p_prime_facts (p1_spec i).1 (p1_spec i).2).2.2.2.1
  IsDedekindDomain.primesOverFinset (Ideal.span {((p1 i : ℤ))}) (𝓞 (Kf g))
open scoped Pointwise in
theorem Kf_inertiaDegIn_le_two (g : ℕ) (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1) :
    Ideal.inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 (Kf g)) ≤ 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsGalois ℚ (Kf g) := Kf_isGalois g
  obtain ⟨hpz, hp0, hpprime, hpmax, hp4dvd⟩ := p_prime_facts hp hp4
  have : (Ideal.span {(p : ℤ)}).IsMaximal := hpmax
  obtain ⟨⟨P, hPprime, hPlies⟩⟩ :=
    (inferInstance : Nonempty (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (Kf g))))
  have := hPprime
  have := hPlies
  have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P
  have : P.IsMaximal := hPprime.isMaximal hPne
  have : Finite (ℤ ⧸ Ideal.span {(p : ℤ)}) :=
    Finite.of_equiv _ (Int.quotientSpanEquivZMod (p : ℤ)).symm.toEquiv
  have : Finite (𝓞 (Kf g) ⧸ P) := inferInstance
  let : Field (ℤ ⧸ Ideal.span {(p : ℤ)}) := Ideal.Quotient.field _
  let : Field (𝓞 (Kf g) ⧸ P) := Ideal.Quotient.field _
  have : Module.Finite (ℤ ⧸ Ideal.span {(p : ℤ)}) (𝓞 (Kf g) ⧸ P) := Module.Finite.of_finite
  have : Algebra.IsAlgebraic (ℤ ⧸ Ideal.span {(p : ℤ)}) (𝓞 (Kf g) ⧸ P) :=
    Algebra.IsAlgebraic.of_finite _ _
  have : PerfectField (ℤ ⧸ Ideal.span {(p : ℤ)}) := PerfectField.ofFinite
  have : Algebra.IsSeparable (ℤ ⧸ Ideal.span {(p : ℤ)}) (𝓞 (Kf g) ⧸ P) := inferInstance
  have hcard := Ideal.card_stabilizer_eq (G := Kf g ≃ₐ[ℚ] Kf g) (Ideal.span {(p : ℤ)}) P
  rw [Kf_ramificationIdxIn_eq_one g p hp hp4, one_mul] at hcard
  rw [← hcard]
  have hquot := Ideal.Quotient.stabilizerQuotientInertiaEquiv
    (G := Kf g ≃ₐ[ℚ] Kf g) (Ideal.span {(p : ℤ)}) P
  have hinbot : Ideal.inertia (Kf g ≃ₐ[ℚ] Kf g) P = ⊥ := Kf_inertia_eq_bot g p hp hp4 P
  have hcard2 : Nat.card (MulAction.stabilizer (Kf g ≃ₐ[ℚ] Kf g) P)
      = Nat.card ((𝓞 (Kf g) ⧸ P) ≃ₐ[ℤ ⧸ Ideal.span {(p : ℤ)}] (𝓞 (Kf g) ⧸ P)) := by
    have h1 : Nat.card ((Ideal.inertia (Kf g ≃ₐ[ℚ] Kf g) P).subgroupOf
        (MulAction.stabilizer (Kf g ≃ₐ[ℚ] Kf g) P)) = 1 := by
      rw [hinbot, Subgroup.bot_subgroupOf]
      exact Subgroup.card_bot
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (s := (Ideal.inertia (Kf g ≃ₐ[ℚ] Kf g) P).subgroupOf
        (MulAction.stabilizer (Kf g ≃ₐ[ℚ] Kf g) P)), h1, mul_one]
    exact Nat.card_congr hquot.toEquiv
  rw [hcard2]
  have hexp : ∀ x : ((𝓞 (Kf g) ⧸ P) ≃ₐ[ℤ ⧸ Ideal.span {(p : ℤ)}] (𝓞 (Kf g) ⧸ P)),
      x ^ 2 = 1 := by
    intro x
    obtain ⟨y, rfl⟩ := hquot.surjective x
    obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective y
    have hσ : σ ^ 2 = 1 := by
      apply Subtype.ext
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact Kf_aut_sq g (σ : Kf g ≃ₐ[ℚ] Kf g)
    rw [← map_pow, ← QuotientGroup.mk_pow, hσ]
    exact map_one hquot
  have hcyc : IsCyclic ((𝓞 (Kf g) ⧸ P) ≃ₐ[ℤ ⧸ Ideal.span {(p : ℤ)}] (𝓞 (Kf g) ⧸ P)) :=
    inferInstance
  have hdvd : Nat.card ((𝓞 (Kf g) ⧸ P) ≃ₐ[ℤ ⧸ Ideal.span {(p : ℤ)}] (𝓞 (Kf g) ⧸ P)) ∣ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one hexp
  exact Nat.le_of_dvd (by norm_num) hdvd
theorem Kf_card_primesOver_ge (g : ℕ) (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1) :
    2 ^ g ≤ (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (Kf g))).ncard := by
  have : IsGalois ℚ (Kf g) := Kf_isGalois g
  obtain ⟨hpz, hp0, hpprime, hpmax, hp4dvd⟩ := p_prime_facts hp hp4
  have : (Ideal.span {(p : ℤ)}).IsMaximal := hpmax
  have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (Ideal.span {(p : ℤ)}) (𝓞 (Kf g)) (Kf g ≃ₐ[ℚ] Kf g)
  have hG : Nat.card (Kf g ≃ₐ[ℚ] Kf g) = 2 ^ (g + 1) := by
    simpa [Nat.card_eq_fintype_card, Kf_finrank] using IsGalois.card_aut_eq_finrank ℚ (Kf g)
  have he := Kf_ramificationIdxIn_eq_one g p hp hp4
  have hf := Kf_inertiaDegIn_le_two g p hp hp4
  rw [hG, he, one_mul] at hfund
  have h2 : (2 : ℕ) ^ (g + 1) = 2 ^ g * 2 := by rw [pow_succ]
  nlinarith [(Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (Kf g))).ncard.zero_le,
    Nat.zero_le (Ideal.inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 (Kf g)))]
theorem Kf_conj_primesOver_ne (g : ℕ) (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1)
    (P : Ideal (𝓞 (Kf g)))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (Kf g))) :
    Ideal.map (ringOfIntegersComplexConj (Kf g)) P ≠ P := by
  intro hEq
  obtain ⟨hPprime, hPlies⟩ := hP
  have : Fact p.Prime := ⟨hp⟩
  have hImem : Complex.I ∈ Kf g :=
    IntermediateField.subset_adjoin ℚ _ (Set.mem_insert _ _)
  have hiK2 : (⟨Complex.I, hImem⟩ : Kf g) ^ 2 = -1 := by
    ext
    push_cast
    exact Complex.I_sq
  have hint : IsIntegral ℤ (⟨Complex.I, hImem⟩ : Kf g) := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C 1,
      Polynomial.monic_X_pow_add_C 1 two_ne_zero, ?_⟩
    simp [hiK2]
  set iO : 𝓞 (Kf g) := ⟨_, hint⟩ with hiOdef
  have hiO2 : iO ^ 2 = -1 := by
    have hK : (iO : Kf g) ^ 2 = -1 := hiK2
    exact_mod_cast hK
  have hconjK : NumberField.IsCMField.complexConj (Kf g) (⟨Complex.I, hImem⟩ : Kf g)
      = -(⟨Complex.I, hImem⟩ : Kf g) := by
    have h1 := NumberField.IsCMField.complexEmbedding_complexConj
      (K := Kf g) ((Kf g).val.toRingHom) (⟨Complex.I, hImem⟩ : Kf g)
    apply Subtype.ext
    rw [show ((-(⟨Complex.I, hImem⟩ : Kf g) : Kf g) : ℂ) = -Complex.I from rfl,
      ← Complex.conj_I]
    exact h1
  have hconj_iO : ringOfIntegersComplexConj (Kf g) iO = -iO := by
    have hcoe : ((ringOfIntegersComplexConj (Kf g) iO : 𝓞 (Kf g)) : Kf g)
        = ((-iO : 𝓞 (Kf g)) : Kf g) := by
      rw [NumberField.IsCMField.coe_ringOfIntegersComplexConj]
      push_cast
      exact_mod_cast hconjK
    exact_mod_cast hcoe
  obtain ⟨y, hy'⟩ : IsSquare (-1 : ZMod p) :=
    (ZMod.exists_sq_eq_neg_one_iff).mpr (by omega)
  have hy : y ^ 2 = -1 := by rw [pow_two]; exact hy'.symm
  set a : ℤ := (y.val : ℤ) with hadef
  have hpa : (p : ℤ) ∣ a ^ 2 + 1 := by
    have hz : ((a ^ 2 + 1 : ℤ) : ZMod p) = 0 := by
      push_cast
      rw [show ((y.val : ℤ) : ZMod p) = y by push_cast; simp]
      rw [hy]
      ring
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
  have hpP : algebraMap ℤ (𝓞 (Kf g)) (p : ℤ) ∈ P := by
    have hmem : ((p : ℤ)) ∈ P.under ℤ := by
      rw [← hPlies.over]
      exact Ideal.mem_span_singleton_self _
    exact hmem
  have haP : algebraMap ℤ (𝓞 (Kf g)) (a ^ 2 + 1) ∈ P := by
    obtain ⟨k, hk⟩ := hpa
    rw [hk, map_mul]
    exact Ideal.mul_mem_right _ _ hpP
  have hsplit : (iO - algebraMap ℤ _ a) * (iO + algebraMap ℤ _ a) ∈ P := by
    have hfactor : (iO - algebraMap ℤ (𝓞 (Kf g)) a) * (iO + algebraMap ℤ (𝓞 (Kf g)) a)
        = -(algebraMap ℤ (𝓞 (Kf g)) (a ^ 2 + 1)) := by
      have hcast : algebraMap ℤ (𝓞 (Kf g)) (a ^ 2 + 1)
          = (algebraMap ℤ (𝓞 (Kf g)) a) ^ 2 + 1 := by
        push_cast [map_add, map_pow, map_one]
        ring
      rw [hcast]
      linear_combination hiO2
    rw [hfactor]
    exact neg_mem haP
  have hconjmem : ∀ x ∈ P, ringOfIntegersComplexConj (Kf g) x ∈ P := by
    intro x hx
    rw [← hEq]
    exact Ideal.mem_map_of_mem _ hx
  have hconj_int : ∀ n : ℤ, ringOfIntegersComplexConj (Kf g) (algebraMap ℤ _ n)
      = algebraMap ℤ (𝓞 (Kf g)) n := fun n => by
    simp [algebraMap_int_eq, map_intCast]
  have h2iO : (2 : 𝓞 (Kf g)) * iO ∈ P := by
    rcases hPprime.mem_or_mem hsplit with hc | hc
    · have hcc := hconjmem _ hc
      rw [map_sub, hconj_iO, hconj_int] at hcc
      have := sub_mem hc hcc
      have heq2 : (iO - algebraMap ℤ (𝓞 (Kf g)) a) - (-iO - algebraMap ℤ (𝓞 (Kf g)) a)
          = 2 * iO := by ring
      rwa [heq2] at this
    · have hcc := hconjmem _ hc
      rw [map_add, hconj_iO, hconj_int] at hcc
      have := sub_mem hc hcc
      have heq2 : (iO + algebraMap ℤ (𝓞 (Kf g)) a) - (-iO + algebraMap ℤ (𝓞 (Kf g)) a)
          = 2 * iO := by ring
      rwa [heq2] at this
  have h4 : algebraMap ℤ (𝓞 (Kf g)) 4 ∈ P := by
    have hprod : ((2 : 𝓞 (Kf g)) * iO) * ((2 : 𝓞 (Kf g)) * iO) ∈ P :=
      Ideal.mul_mem_left _ _ h2iO
    have heq4 : ((2 : 𝓞 (Kf g)) * iO) * ((2 : 𝓞 (Kf g)) * iO)
        = -(algebraMap ℤ (𝓞 (Kf g)) 4) := by
      have h4c : algebraMap ℤ (𝓞 (Kf g)) 4 = 4 := by norm_num [algebraMap_int_eq]
      rw [h4c]
      linear_combination 4 * hiO2
    rw [heq4] at hprod
    simpa using neg_mem hprod
  have hdvd : (p : ℤ) ∣ 4 := by
    have hmem : (4 : ℤ) ∈ P.under ℤ := h4
    rw [← hPlies.over] at hmem
    exact Ideal.mem_span_singleton.mp hmem
  have hdvd' : p ∣ 4 := by exact_mod_cast hdvd
  have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow (n := 2) (by simpa using hdvd')
  have hpe : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2
  omega
theorem span_p1_eq_prod (g i : ℕ) :
    Ideal.span {((p1 i : ℕ) : 𝓞 (Kf g))} = ∏ P ∈ primesOverP1 g i, P :=
  by
    classical
    have : Fact (p1 i).Prime := ⟨(p1_spec i).1⟩
    have : IsGalois ℚ (Kf g) := Kf_isGalois g
    obtain ⟨hpz, hp0, hpprime, hpmax, hp4dvd⟩ := p_prime_facts (p1_spec i).1 (p1_spec i).2
    have : (Ideal.span {((p1 i : ℤ))}).IsMaximal := hpmax
    set I : Ideal (𝓞 (Kf g)) :=
      Ideal.map (algebraMap ℤ (𝓞 (Kf g))) (Ideal.span {(p1 i : ℤ)}) with hI
    have hIspan : I = Ideal.span {((p1 i : ℕ) : 𝓞 (Kf g))} :=
      by
        rw [hI, Ideal.map_span, Set.image_singleton]
        norm_num [algebraMap_int_eq]
    have hIne : I ≠ ⊥ :=
      by
        rw [hIspan, Ne, Ideal.span_singleton_eq_bot]
        exact_mod_cast (p1_spec i).1.ne_zero
    have hmemiff :
      ∀ {P : Ideal (𝓞 (Kf g))},
        P ∈ primesOverP1 g i ↔ P ∈ Ideal.primesOver (Ideal.span {(p1 i : ℤ)}) (𝓞 (Kf g)) :=
      fun {P} => IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 (Kf g))
    have hcount :
      ∀ P ∈ primesOverP1 g i, (UniqueFactorizationMonoid.normalizedFactors I).count P = 1 :=
      by
        intro P hP
        obtain ⟨hPp, hPlies⟩ := hmemiff.mp hP
        have := hPp
        have := hPlies
        have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P
        rw [←
          Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
            (Ideal.span {(p1 i : ℤ)}) P
            (by
              simpa [hI] using hIne)]
        rw [←
          Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(p1 i : ℤ)}) P
            (Kf g ≃ₐ[ℚ] Kf g)]
        exact Kf_ramificationIdxIn_eq_one g (p1 i) (p1_spec i).1 (p1_spec i).2
    have htofin :
      (UniqueFactorizationMonoid.normalizedFactors I).toFinset = primesOverP1 g i :=
      by
        rw [show
            primesOverP1 g i =
              IsDedekindDomain.primesOverFinset (Ideal.span {(p1 i : ℤ)}) (𝓞 (Kf g))
            from rfl]
        rw [IsDedekindDomain.primesOverFinset,
          UniqueFactorizationMonoid.factors_eq_normalizedFactors]
    have hnodup : (UniqueFactorizationMonoid.normalizedFactors I).Nodup :=
      by
        rw [Multiset.nodup_iff_count_le_one]
        intro P
        by_cases hP : P ∈ UniqueFactorizationMonoid.normalizedFactors I
        · exact le_of_eq (hcount P (htofin ▸ Multiset.mem_toFinset.mpr hP))
        · simp [Multiset.count_eq_zero_of_notMem hP]
    have hval : (primesOverP1 g i).val = UniqueFactorizationMonoid.normalizedFactors I :=
      by
        rw [← htofin, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]
    rw [← hIspan, Finset.prod_eq_multiset_prod]
    rw [hval, Multiset.map_id']
    exact (Ideal.prod_normalizedFactors_eq_self hIne).symm
theorem Kf_span_m_eq_prod (g t : ℕ) :
    Ideal.span {((m t : ℕ) : 𝓞 (Kf g))} =
      ∏ i ∈ Finset.range t, ∏ P ∈ primesOverP1 g i, P := by
  have hcast : ((m t : ℕ) : 𝓞 (Kf g)) = ∏ i ∈ Finset.range t, ((p1 i : ℕ) : 𝓞 (Kf g)) := by
    rw [m]
    push_cast
    rfl
  rw [hcast, ← Ideal.prod_span_singleton]
  exact Finset.prod_congr rfl fun i _ => span_p1_eq_prod g i
theorem exists_ideal_family (g t : ℕ) (hg : 1 ≤ g) :
    ∃ F : Finset (Ideal (𝓞 (Kf g))),
      (2 : ℝ) ^ (t * 2 ^ (g - 1)) ≤ F.card ∧
      ∀ A ∈ F,
        A * Ideal.map (ringOfIntegersComplexConj (Kf g)) A =
          Ideal.span {(m t : 𝓞 (Kf g))} := by
  classical
  set σ : 𝓞 (Kf g) ≃+* 𝓞 (Kf g) :=
    (ringOfIntegersComplexConj (Kf g)).toRingEquiv with hσdef
  have hσ_eq : ∀ A : Ideal (𝓞 (Kf g)),
      Ideal.map σ A = Ideal.map (ringOfIntegersComplexConj (Kf g)) A := fun A => rfl
  set S : Finset (Ideal (𝓞 (Kf g))) :=
    (Finset.range t).biUnion (fun i => primesOverP1 g i) with hSdef
  have hmem : ∀ {i : ℕ} {P : Ideal (𝓞 (Kf g))}, P ∈ primesOverP1 g i →
      P ∈ Ideal.primesOver (Ideal.span {(p1 i : ℤ)}) (𝓞 (Kf g)) := by
    intro i P hP
    obtain ⟨hpz, hp0, hpprime, hpmax, _⟩ := p_prime_facts (p1_spec i).1 (p1_spec i).2
    have : (Ideal.span {((p1 i : ℤ))}).IsMaximal := hpmax
    exact (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 (Kf g))).mp hP
  have hσ_fix : ∀ n : ℤ, σ.symm (algebraMap ℤ (𝓞 (Kf g)) n) = algebraMap ℤ (𝓞 (Kf g)) n := by
    intro n
    rw [algebraMap_int_eq]
    exact map_intCast (σ.symm : 𝓞 (Kf g) →+* 𝓞 (Kf g)) n
  have hconj_under : ∀ {i : ℕ} {P : Ideal (𝓞 (Kf g))},
      P ∈ Ideal.primesOver (Ideal.span {(p1 i : ℤ)}) (𝓞 (Kf g)) →
      Ideal.map σ P ∈ Ideal.primesOver (Ideal.span {(p1 i : ℤ)}) (𝓞 (Kf g)) := by
    intro i P hP
    obtain ⟨hPp, hPlies⟩ := hP
    refine ⟨Ideal.map_isPrime_of_equiv σ, ⟨?_⟩⟩
    have hunder : Ideal.under ℤ (Ideal.map σ P) = Ideal.under ℤ P := by
      ext n
      simp only [Ideal.mem_comap]
      rw [← Ideal.comap_symm, Ideal.mem_comap, hσ_fix]
    rw [hunder]
    exact hPlies.over
  have hdisj : ∀ i ∈ Finset.range t, ∀ j ∈ Finset.range t, i ≠ j →
      Disjoint (primesOverP1 g i) (primesOverP1 g j) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro P hPi hPj
    obtain ⟨hPp, hPliesi⟩ := hmem hPi
    obtain ⟨_, hPliesj⟩ := hmem hPj
    have hspan : Ideal.span {(p1 i : ℤ)} = Ideal.span {(p1 j : ℤ)} := by
      rw [hPliesi.over, hPliesj.over]
    have hassoc : Associated ((p1 i : ℤ)) ((p1 j : ℤ)) :=
      Ideal.span_singleton_eq_span_singleton.mp hspan
    have hnat : p1 i = p1 j := by
      have := Int.associated_iff_natAbs.mp hassoc
      simpa using this
    exact hij (p1_strictMono.injective hnat)
  have hSprime : ∀ P ∈ S, P.IsPrime := by
    intro P hP
    obtain ⟨i, hi, hPi⟩ := Finset.mem_biUnion.mp hP
    exact (hmem hPi).1
  have hSne : ∀ P ∈ S, P ≠ ⊥ := by
    intro P hP
    obtain ⟨i, hi, hPi⟩ := Finset.mem_biUnion.mp hP
    obtain ⟨hpz, hp0, _, hpmax, _⟩ := p_prime_facts (p1_spec i).1 (p1_spec i).2
    have := (hmem hPi).2
    exact Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P
  have hSinv : ∀ P ∈ S, Ideal.map σ P ∈ S := by
    intro P hP
    obtain ⟨i, hi, hPi⟩ := Finset.mem_biUnion.mp hP
    refine Finset.mem_biUnion.mpr ⟨i, hi, ?_⟩
    obtain ⟨hpz, hp0, hpprime, hpmax, _⟩ := p_prime_facts (p1_spec i).1 (p1_spec i).2
    have : (Ideal.span {((p1 i : ℤ))}).IsMaximal := hpmax
    exact (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 (Kf g))).mpr
      (hconj_under (hmem hPi))
  have hcc : ∀ x : 𝓞 (Kf g), σ (σ x) = x := by
    intro x
    have h1 := NumberField.IsCMField.coe_ringOfIntegersComplexConj (Kf g) (σ x)
    have h2 := NumberField.IsCMField.coe_ringOfIntegersComplexConj (Kf g) x
    have h3 := NumberField.IsCMField.complexConj_apply_apply (Kf g) (x : Kf g)
    have hco : ((σ (σ x) : 𝓞 (Kf g)) : Kf g) = ((x : 𝓞 (Kf g)) : Kf g) := by
      rw [show ((σ (σ x) : 𝓞 (Kf g)) : Kf g)
          = NumberField.IsCMField.complexConj (Kf g) ((σ x : 𝓞 (Kf g)) : Kf g) from h1,
        show ((σ x : 𝓞 (Kf g)) : Kf g)
          = NumberField.IsCMField.complexConj (Kf g) ((x : 𝓞 (Kf g)) : Kf g) from h2, h3]
    exact_mod_cast hco
  have hsymm_self : ∀ y, σ.symm y = σ y := by
    intro y
    apply σ.injective
    rw [RingEquiv.apply_symm_apply]
    exact (hcc y).symm
  have hSinvol : ∀ P ∈ S, Ideal.map σ (Ideal.map σ P) = P := by
    intro P _
    ext x
    rw [← Ideal.comap_symm, ← Ideal.comap_symm, Ideal.mem_comap, Ideal.mem_comap]
    rw [hsymm_self, hsymm_self, hcc x]
  have hSfree : ∀ P ∈ S, Ideal.map σ P ≠ P := by
    intro P hP
    obtain ⟨i, hi, hPi⟩ := Finset.mem_biUnion.mp hP
    rw [hσ_eq]
    exact Kf_conj_primesOver_ne g (p1 i) (p1_spec i).1 (p1_spec i).2 P (hmem hPi)
  obtain ⟨G, hGcard, hGprod⟩ : ∃ G : Finset (Ideal (𝓞 (Kf g))),
      2 ^ (S.card / 2) ≤ G.card ∧
        ∀ A ∈ G, A * Ideal.map σ A = ∏ p ∈ S, p := by
    set f : {p // p ∈ S} → IsDedekindDomain.HeightOneSpectrum (𝓞 (Kf g)) :=
      fun x => ⟨x.1, hSprime x.1 x.2, hSne x.1 x.2⟩ with hf
    have hfinj : Function.Injective f := fun x y h =>
      Subtype.ext (congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal h)
    set S' : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 (Kf g))) :=
      S.attach.image f with hS'
    have hEqIdeal : ∀ q : IsDedekindDomain.HeightOneSpectrum (𝓞 (Kf g)),
        (IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ q).asIdeal
          = Ideal.map σ q.asIdeal := by
      intro q
      ext x
      change σ.symm x ∈ q.asIdeal ↔ x ∈ Ideal.map σ q.asIdeal
      exact Ideal.symm_apply_mem_of_equiv_iff
    have hmem : ∀ q, q ∈ S' ↔ q.asIdeal ∈ S := by
      intro q
      rw [hS', Finset.mem_image]
      constructor
      · rintro ⟨x, -, rfl⟩; exact x.2
      · intro hq; exact ⟨⟨q.asIdeal, hq⟩, Finset.mem_attach _ _,
          IsDedekindDomain.HeightOneSpectrum.ext rfl⟩
    have hcard : S'.card = S.card := by
      rw [hS', Finset.card_image_of_injective _ hfinj, Finset.card_attach]
    have hprod : ∏ q ∈ S', q.asIdeal = ∏ p ∈ S, p := by
      rw [hS', Finset.prod_image (fun x _ y _ h => hfinj h)]
      exact Finset.prod_attach S (fun p => p)
    have hinv' : ∀ q ∈ S', IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ q ∈ S' := by
      intro q hq; rw [hmem, hEqIdeal]; exact hSinv q.asIdeal ((hmem q).mp hq)
    have hinvol' : ∀ q ∈ S',
        IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ
          (IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ q) = q := by
      intro q hq
      apply IsDedekindDomain.HeightOneSpectrum.ext
      rw [hEqIdeal, hEqIdeal]; exact hSinvol q.asIdeal ((hmem q).mp hq)
    have hfree' : ∀ q ∈ S', IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv σ q ≠ q := by
      intro q hq h
      exact hSfree q.asIdeal ((hmem q).mp hq)
        (hEqIdeal q ▸ congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal h)
    obtain ⟨G, hGcard, hGprod⟩ :=
      TauCeti.DedekindDomain.exists_transversal_family σ S' hinv' hinvol' hfree'
    exact ⟨G, hcard ▸ hGcard, fun A hA => by rw [hGprod A hA, hprod]⟩
  refine ⟨G, ?_, ?_⟩
  · have hScard : t * 2 ^ g ≤ S.card := by
      rw [hSdef, Finset.card_biUnion hdisj]
      calc t * 2 ^ g = ∑ _i ∈ Finset.range t, 2 ^ g := by
            rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
      _ ≤ ∑ i ∈ Finset.range t, (primesOverP1 g i).card := by
            refine Finset.sum_le_sum fun i _ => ?_
            have hge := Kf_card_primesOver_ge g (p1 i) (p1_spec i).1 (p1_spec i).2
            obtain ⟨hpz, hp0, hpprime, hpmax, _⟩ :=
              p_prime_facts (p1_spec i).1 (p1_spec i).2
            have : (Ideal.span {((p1 i : ℤ))}).IsMaximal := hpmax
            rwa [← IsDedekindDomain.coe_primesOverFinset hp0 (𝓞 (Kf g)),
              Set.ncard_coe_finset] at hge
    have hhalf : t * 2 ^ (g - 1) ≤ S.card / 2 := by
      have h2g : 2 ^ g = 2 ^ (g - 1) * 2 := by
        rw [← pow_succ]
        congr 1
        omega
      rw [h2g, ← mul_assoc] at hScard
      omega
    calc (2 : ℝ) ^ (t * 2 ^ (g - 1)) ≤ (2 : ℝ) ^ (S.card / 2) := by
          exact pow_le_pow_right₀ (by norm_num) hhalf
    _ ≤ G.card := by exact_mod_cast hGcard
  · intro A hA
    rw [← hσ_eq, hGprod A hA, hSdef, Finset.prod_biUnion hdisj]
    exact (Kf_span_m_eq_prod g t).symm
end Erdos
end
section
open NumberField IsCMField
namespace Erdos
theorem absNorm_map_conj (g : ℕ) (A : Ideal (𝓞 (Kf g))) :
    Ideal.absNorm (Ideal.map (ringOfIntegersComplexConj (Kf g)) A) = Ideal.absNorm A :=
  by
    have h_card :
      Nat.card (𝓞 (Kf g) ⧸ A) =
        Nat.card (𝓞 (Kf g) ⧸ Ideal.map (ringOfIntegersComplexConj (Kf g)) A) :=
      by
        refine Nat.card_congr (Quotient.congr (ringOfIntegersComplexConj (Kf g)).toEquiv ?_)
        simp +decide only [AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe]; intro a₁ a₂;
        simp only [Submodule.quotientRel_def]
        rw [← map_sub]; rw [Ideal.mem_map_iff_of_surjective];
        · exact
            ⟨fun h => ⟨_, h, rfl⟩,
              by
                rintro ⟨x, hx, hx'⟩;
                exact (ringOfIntegersComplexConj (Kf g)).injective hx' ▸ hx⟩;
        · exact AlgEquiv.surjective _;
    convert! h_card.symm using 1
theorem place_mul_conj (g : ℕ) (z : 𝓞 (Kf g)) (w : InfinitePlace (Kf g)) :
    w (algebraMap (𝓞 (Kf g)) (Kf g) (z * ringOfIntegersComplexConj (Kf g) z))
      = (w (algebraMap (𝓞 (Kf g)) (Kf g) z)) ^ 2 := by
  rw [map_mul, map_mul, sq]
  congr 1
  have h : algebraMap (𝓞 (Kf g)) (Kf g) (ringOfIntegersComplexConj (Kf g) z)
      = complexConj (Kf g) (algebraMap (𝓞 (Kf g)) (Kf g) z) :=
    coe_ringOfIntegersComplexConj (Kf g) z
  rw [h, infinitePlace_complexConj]
theorem absNorm_span_natCast (g : ℕ) (n : ℕ) :
    Ideal.absNorm (Ideal.span {((n : ℕ) : 𝓞 (Kf g))}) = n ^ 2 ^ (g + 1) := by
  have h_norm : Algebra.norm ℤ (n : (𝓞 (Kf g))) = n ^ (Module.finrank ℚ (Kf g)) := by
    erw [ Algebra.norm_apply ];
    erw [ show ( Algebra.lmul ℤ ( 𝓞 ( Kf g ) ) ) n = ( n : ℤ ) • LinearMap.id from ?_ ];
    · erw [ LinearMap.det_smul ] ; norm_num;
      rw [ ← NumberField.RingOfIntegers.rank ];
    · ext; simp [Algebra.lmul];
  convert congr_arg Int.natAbs h_norm using 1;
  · rw [ Ideal.absNorm_span_singleton ];
  · norm_num [ Kf_finrank ]
theorem absNorm_of_mul_conj (g : ℕ) (A : Ideal (𝓞 (Kf g))) (n : ℕ)
    (h : A * Ideal.map (ringOfIntegersComplexConj (Kf g)) A = Ideal.span {((n : ℕ) : 𝓞 (Kf g))}) :
    Ideal.absNorm A = n ^ 2 ^ g := by
  apply_fun Ideal.absNorm at h;
  rw [ Ideal.absNorm.map_mul ] at h;
  rw [ absNorm_map_conj, absNorm_span_natCast ] at h;
  rw [ ← sq_eq_sq₀ ] <;> first | positivity | ring_nf at * ; aesop;
theorem prod_place_mul_conj (g : ℕ) (y : 𝓞 (Kf g)) :
    ∏ w : InfinitePlace (Kf g),
        w (algebraMap (𝓞 (Kf g)) (Kf g) (y * ringOfIntegersComplexConj (Kf g) y))
      = (Ideal.absNorm (Ideal.span {y}) : ℝ) := by
  have htc := Kf_isTotallyComplex g
  convert NumberField.InfinitePlace.prod_eq_abs_norm (algebraMap (𝓞 (Kf g)) (Kf g) y) using 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [place_mul_conj g y w, IsTotallyComplex.mult_eq w]
  · rw [Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int]
    push_cast [Int.abs_eq_natAbs]
    exact_mod_cast Nat.cast_natAbs (Algebra.norm ℤ y)
theorem exists_fiber_card_ge {α β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
    (s : Finset α) (f : α → β) :
    ∃ y : β, s.card ≤ {x ∈ s | f x = y}.card * Fintype.card β := by
  obtain ⟨y₀, -, hy₀⟩ := Finset.exists_max_image (Finset.univ : Finset β)
    (fun y => {x ∈ s | f x = y}.card) Finset.univ_nonempty
  refine ⟨y₀, ?_⟩
  calc s.card = ∑ y : β, {x ∈ s | f x = y}.card := by
              rw [← Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (f x))]
    _ ≤ ∑ _y : β, {x ∈ s | f x = y₀}.card :=
              Finset.sum_le_sum (fun y _ => hy₀ y (Finset.mem_univ y))
    _ = {x ∈ s | f x = y₀}.card * Fintype.card β := by
              rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
theorem Kf_maximalReal_finrank (g : ℕ) :
    Module.finrank ℚ (maximalRealSubfield (Kf g)) = 2 ^ g := by
  have h1 : Module.finrank ℚ (Kf g) = 2 ^ (g + 1) := Kf_finrank g
  have h2 : Module.finrank (maximalRealSubfield (Kf g)) (Kf g) = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have h3 := Module.finrank_mul_finrank ℚ (maximalRealSubfield (Kf g)) (Kf g)
  rw [h1, h2, pow_succ] at h3
  omega
theorem units_sq_quot_finite (F : Type) [Field F] [NumberField F] :
    Finite ((𝓞 F)ˣ ⧸ (MonoidHom.range (powMonoidHom 2 : (𝓞 F)ˣ →* (𝓞 F)ˣ))) :=
  by
    classical
    have h_fg : AddGroup.FG (Additive ((𝓞 F)ˣ ⧸ (powMonoidHom 2 : (𝓞 F)ˣ →* (𝓞 F)ˣ).range)) :=
      by
        have h_finite_gen : Monoid.FG ((𝓞 F)ˣ) :=
          by
            grind +suggestions;
        convert AddGroup.fg_iff_addMonoid_fg.mpr _; obtain ⟨S, hS⟩ := h_finite_gen;
        refine ⟨S.image (fun x => QuotientGroup.mk x), ?_⟩;
        simp_all +decide only [SetLike.ext_iff, Submonoid.mem_top, iff_true,
          AddSubmonoid.mem_closure, AddSubmonoid.mem_top, Additive.forall]; intro a S_1 hS_1;
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a;
        simp_all +decide only [Submonoid.mem_closure, Set.subset_def, SetLike.mem_coe,
          Additive.forall];
        specialize
          hS x
            (Submonoid.comap (QuotientGroup.mk' (powMonoidHom 2 |> MonoidHom.range))
              (AddSubmonoid.toSubmonoid S_1))
        exact hS fun s hs => hS_1 _ (Finset.mem_image.mpr ⟨s, hs, rfl⟩)
    have h_add_group :
      ∀ (G : Type) [AddCommGroup G] [AddGroup.FG G], (∀ g : G, 2 • g = 0) → Finite G :=
      by
        intros G _ _ hG
        have h_vector_space : Module (ZMod 2) G := AddCommGroup.zmodModule hG
        have h_finite_dim : FiniteDimensional (ZMod 2) G :=
          by
            have h_fg : Module.Finite (ZMod 2) G :=
              by
                obtain ⟨s, hs⟩ := ‹AddGroup.FG G›; use s;
                simp_all +decide only [SetLike.ext_iff, AddSubgroup.mem_closure,
                  AddSubgroup.mem_top, iff_true, Submodule.mem_top]; intro x;
                specialize
                  hs x (Submodule.toAddSubgroup (Submodule.span (ZMod 2) (s : Set G)));
                simp_all +decide [Set.subset_def, Submodule.mem_span];
            lia;
        exact Finite.of_equiv _ ((Module.finBasis (ZMod 2) G).equivFun.symm.toEquiv);
    convert!
      h_add_group (Additive (((𝓞 F) ˣ) ⧸ (powMonoidHom 2 : ((𝓞 F) ˣ) →* (𝓞 F) ˣ).range)) _;
    rintro ⟨a⟩;
    exact
      QuotientGroup.eq.mpr
        (by
          aesop);
theorem units_square_pigeonhole (g : ℕ) {α : Type*} (F₁ : Finset α)
    (ν : α → (𝓞 (maximalRealSubfield (Kf g)))ˣ) :
    ∃ F₂ : Finset α,
      F₂ ⊆ F₁ ∧
        F₁.card ≤ F₂.card * 2 ^ 2 ^ g ∧
          ∀ A ∈ F₂,
            ∀ A' ∈ F₂, ∃ δ : (𝓞 (maximalRealSubfield (Kf g)))ˣ, ν A * (ν A')⁻¹ = δ ^ 2 :=
  by
    classical
    obtain ⟨y, hy⟩ :
      ∃ y :
        (𝓞 (↥(maximalRealSubfield (Kf g))))ˣ ⧸
          MonoidHom.range
            (powMonoidHom 2 :
              (𝓞 (↥(maximalRealSubfield (Kf g))))ˣ →* (𝓞 (↥(maximalRealSubfield (Kf g))))ˣ),
        F₁.card ≤ (Finset.filter (fun A => QuotientGroup.mk (ν A) = y) F₁).card * 2 ^ 2 ^ g :=
      by
        have h_finite :
          Finite
            ((𝓞 (↥(maximalRealSubfield (Kf g))))ˣ ⧸
              MonoidHom.range
                (powMonoidHom 2 :
                  (𝓞 (↥(maximalRealSubfield (Kf g))))ˣ →*
                    (𝓞 (↥(maximalRealSubfield (Kf g))))ˣ)) :=
          by
            convert units_sq_quot_finite (maximalRealSubfield (Kf g));
        have h_finite :
          Fintype
            ((𝓞 (↥(maximalRealSubfield (Kf g))))ˣ ⧸
              MonoidHom.range
                (powMonoidHom 2 :
                  (𝓞 (↥(maximalRealSubfield (Kf g))))ˣ →*
                    (𝓞 (↥(maximalRealSubfield (Kf g))))ˣ)) :=
          by
            exact Fintype.ofFinite _;
        have h_finite :
          Fintype.card
              ((𝓞 (↥(maximalRealSubfield (Kf g))))ˣ ⧸
                MonoidHom.range
                  (powMonoidHom 2 :
                    (𝓞 (↥(maximalRealSubfield (Kf g))))ˣ →*
                      (𝓞 (↥(maximalRealSubfield (Kf g))))ˣ)) ≤
            2 ^ 2 ^ g :=
          by
            have hsq :
              MonoidHom.range (powMonoidHom 2 : (𝓞 (↥(maximalRealSubfield (Kf g))))ˣ →* _) =
                Subgroup.square ((𝓞 (↥(maximalRealSubfield (Kf g))))ˣ) :=
              by
                ext x
                rw [MonoidHom.mem_range, Subgroup.mem_square]
                constructor <;> rintro ⟨h, rfl⟩ <;>
                  exact
                    ⟨h,
                      by
                        rw [powMonoidHom_apply, sq]⟩
            rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, hsq]
            exact
              (TauCeti.NumberField.units_sq_index_le (↥(maximalRealSubfield (Kf g)))).trans
                (pow_le_pow_right₀
                  (by
                    decide)
                  (Kf_maximalReal_finrank g).le)
        have := @exists_fiber_card_ge;
        exact
          Exists.elim (this F₁ (fun A => QuotientGroup.mk (ν A))) fun y hy =>
            ⟨y, hy.trans (Nat.mul_le_mul_left _ h_finite)⟩;
    refine ⟨Finset.filter (fun A => QuotientGroup.mk (ν A) = y) F₁, ?_, hy, ?_⟩
    · exact Finset.filter_subset _ _
    · intro A hA A' hA'
      obtain ⟨δ, hδ⟩ : ∃ δ : (𝓞 (↥(maximalRealSubfield (Kf g))))ˣ, (ν A)⁻¹ * (ν A') = δ ^ 2 :=
        by
          have h_eq :
            (ν A)⁻¹ * ν A' ∈
              MonoidHom.range
                (powMonoidHom 2 :
                  (𝓞 (↥(maximalRealSubfield (Kf g))))ˣ →*
                    (𝓞 (↥(maximalRealSubfield (Kf g))))ˣ) :=
            by
              rw [← QuotientGroup.eq_one_iff] at *; aesop;
          exact
            h_eq.imp fun x hx =>
              by
                simpa [sq] using hx.symm;
      generalize_proofs at *;
      (exact
          ⟨δ⁻¹,
            by
              simpa [mul_comm] using congr_arg Inv.inv hδ⟩)
theorem descent_unit (g : ℕ) (a b : 𝓞 (Kf g)) (ha : ringOfIntegersComplexConj (Kf g) a = a)
    (hb : ringOfIntegersComplexConj (Kf g) b = b) (hb0 : b ≠ 0)
    (hab : Ideal.span { a } = Ideal.span { b }) :
    ∃ u : (𝓞 (maximalRealSubfield (Kf g)))ˣ,
      algebraMap (𝓞 (maximalRealSubfield (Kf g))) (𝓞 (Kf g))
            (u : 𝓞 (maximalRealSubfield (Kf g))) *
          b =
        a :=
  by
    obtain ⟨u, hu⟩ : ∃ u : (𝓞 (Kf g))ˣ, a = u * b :=
      by
        have := Ideal.span_singleton_eq_span_singleton.mp hab; obtain ⟨u, hu⟩ := this.symm;
        exact
          ⟨u,
            by
              rw [← hu, mul_comm]⟩;
    have h_fixed : (complexConj (Kf g)) (u : Kf g) = (u : Kf g) :=
      by
        have h_conj_u :
          (ringOfIntegersComplexConj (Kf g)) (u : (𝓞 (Kf g))) = (u : (𝓞 (Kf g))) :=
          by
            simp_all +decide [ringOfIntegersComplexConj];
        convert! congr_arg (algebraMap (𝓞 (Kf g)) (Kf g)) h_conj_u using 1;
    have := @Units.complexConj_eq_self_iff (Kf g); obtain ⟨v, hv⟩ := this u |>.1 h_fixed;
    use v; simp +decide only [RingOfIntegers.ext_iff, map_mul];
    convert! congr_arg (fun x : Kf g => x * b) hv using 1;
    exact congr_arg (algebraMap (𝓞 (Kf g)) (Kf g)) hu
theorem ringConj_ringConj (g : ℕ) (x : 𝓞 (Kf g)) :
    ringOfIntegersComplexConj (Kf g) (ringOfIntegersComplexConj (Kf g) x) = x := by
  apply RingOfIntegers.ext
  rw [coe_ringOfIntegersComplexConj, coe_ringOfIntegersComplexConj, complexConj_apply_apply]
theorem norm_constant_subfamily (g : ℕ) {α : Type*} (F₁ : Finset α) (y : α → 𝓞 (Kf g))
    (hy0 : ∀ A ∈ F₁, y A ≠ 0)
    (hassoc :
      ∀ A ∈ F₁,
        ∀ A' ∈ F₁,
          Ideal.span {y A * ringOfIntegersComplexConj (Kf g) (y A)} =
            Ideal.span {y A' * ringOfIntegersComplexConj (Kf g) (y A')}) :
    ∃ (F₂ : Finset α) (μ : 𝓞 (Kf g)),
      F₂ ⊆ F₁ ∧
        F₁.card ≤ F₂.card * 2 ^ 2 ^ g ∧
          ∀ A ∈ F₂,
            ∃ z : 𝓞 (Kf g),
              Ideal.span { z } = Ideal.span {y A} ∧
                z * ringOfIntegersComplexConj (Kf g) z = μ :=
  by
    classical
    by_cases hF₁ : F₁.Nonempty;
    · obtain ⟨A₀, hA₀⟩ : ∃ A₀ ∈ F₁, True :=
        by
          exact ⟨hF₁.choose, hF₁.choose_spec, trivial⟩;
      have hU :
        ∀ A ∈ F₁,
          ∃ U : (𝓞 (maximalRealSubfield (Kf g)))ˣ,
            algebraMap (𝓞 (maximalRealSubfield (Kf g))) (𝓞 (Kf g))
                  (U : 𝓞 (maximalRealSubfield (Kf g))) *
                (y A₀ * ringOfIntegersComplexConj (Kf g) (y A₀)) =
              y A * ringOfIntegersComplexConj (Kf g) (y A) :=
        by
          intro A hA
          apply
            descent_unit g (y A * ringOfIntegersComplexConj (Kf g) (y A))
              (y A₀ * ringOfIntegersComplexConj (Kf g) (y A₀))
              (by
                rw [map_mul, ringConj_ringConj]; exact mul_comm _ _)
              (by
                grind +suggestions)
              (by
                simp_all +decide [mul_eq_zero])
              (by
                exact hassoc A hA A₀ hA₀.1);
      choose! U hU using hU; obtain ⟨F₂, hF₂⟩ := units_square_pigeonhole g F₁ U;
      obtain ⟨A₁, hA₁⟩ : ∃ A₁ ∈ F₂, True :=
        by
          exact
            Exists.elim
              (Finset.card_pos.mp
                (by
                  nlinarith [Finset.card_pos.mpr hF₁, Nat.one_le_pow (2 ^ g) 2 zero_lt_two]))
              fun x hx => ⟨x, hx, trivial⟩;
      refine
        ⟨F₂, y A₁ * (ringOfIntegersComplexConj (Kf g)) (y A₁), hF₂.1, hF₂.2.1, fun A hA =>
          ?_⟩;
      obtain ⟨δ, hδ⟩ := hF₂.2.2 A hA A₁ hA₁.1;
      refine
        ⟨y A *
            (Units.map
              (algebraMap (𝓞 (maximalRealSubfield (Kf g))) (𝓞 (Kf g)) |> RingHom.toMonoidHom)
              δ⁻¹),
          ?_, ?_⟩;
      · exact Ideal.span_singleton_mul_right_unit (Units.isUnit _) _
      · have hδ_eq :
          algebraMap (𝓞 (maximalRealSubfield (Kf g))) (𝓞 (Kf g)) (U A) =
            (algebraMap (𝓞 (maximalRealSubfield (Kf g))) (𝓞 (Kf g)) δ) ^ 2 *
              algebraMap (𝓞 (maximalRealSubfield (Kf g))) (𝓞 (Kf g)) (U A₁) :=
          by
            replace hδ :=
              congr_arg
                (fun x : (𝓞 (maximalRealSubfield (Kf g))) ˣ =>
                  (algebraMap (𝓞 (maximalRealSubfield (Kf g))) (𝓞 (Kf g))) x)
                hδ;
            simp_all +decide only [ne_eq, and_true, pow_two, Units.val_mul, map_mul, mul_assoc]
            simp_all +decide only [← mul_assoc];
            rw [← hδ, mul_assoc]; simp +decide [← map_mul];
        simp_all +decide [mul_assoc, mul_comm, mul_left_comm];
        simp_all +decide [← mul_assoc, ← hU A (hF₂.1 hA), ← hU A₁ (hF₂.1 hA₁)];
        simp +decide [sq, mul_assoc]; simp +decide [← mul_assoc, ← map_mul];
    · aesop
theorem stage1 (g : ℕ) (F : Finset (Ideal (𝓞 (Kf g)))) (hF : ∀ A ∈ F, A ≠ ⊥) :
    ∃ (b : Ideal (𝓞 (Kf g))) (F₁ : Finset (Ideal (𝓞 (Kf g)))) (y :
      Ideal (𝓞 (Kf g)) → 𝓞 (Kf g)),
      b ≠ ⊥ ∧
        F₁ ⊆ F ∧
          F.card ≤ F₁.card * NumberField.classNumber (Kf g) ∧
            ∀ A ∈ F₁, y A ≠ 0 ∧ Ideal.span {y A} = A * b :=
  by
    classical
    set φ : Ideal (𝓞 (Kf g)) → ClassGroup (𝓞 (Kf g)) := fun A =>
      if h : A ≠ ⊥ then ClassGroup.mk0 ⟨A, mem_nonZeroDivisors_of_ne_zero h⟩ else 1;
    obtain ⟨c, hc⟩ :
      ∃ c : ClassGroup (𝓞 (Kf g)),
        F.card ≤
          (Finset.filter (fun A => φ A = c) F).card * Fintype.card (ClassGroup (𝓞 (Kf g))) :=
      by
        convert exists_fiber_card_ge F φ;
    obtain ⟨b', hb'⟩ :
      ∃ b' : { x : Ideal (𝓞 (Kf g)) // x ∈ nonZeroDivisors (Ideal (𝓞 (Kf g))) },
        ClassGroup.mk0 b' = c⁻¹ :=
      by
        have := ClassGroup.mk0_surjective (c⁻¹); exact this;
    refine ⟨b', Finset.filter (fun A => φ A = c) F, ?_⟩;
    simp +zetaDelta only [ne_eq, Finset.filter_subset, Finset.mem_filter, and_imp, true_and,
      exists_and_left] at *;
    refine ⟨?_, ?_, ?_⟩;
    · exact fun h =>
        by
          simpa [h] using b'.2;
    · convert! hc using 1;
    · have h_principal :
        ∀ A ∈ F, φ A = c → ∃ a : 𝓞 (Kf g), A * b' = Ideal.span {a} ∧ a ≠ 0 := by
          intro A hA hAc
          have hA0 : A ≠ ⊥ := hF A hA
          have hclass : ClassGroup.mk0 ⟨A, mem_nonZeroDivisors_of_ne_zero hA0⟩ =
              (ClassGroup.mk0 b')⁻¹ := by
            simpa only [φ, dif_pos hA0, hb', inv_inv] using hAc
          obtain ⟨a, ha0, ha⟩ := ClassGroup.mk0_eq_mk0_inv_iff.mp hclass
          exact ⟨a, ha, ha0⟩
      choose! a ha₁ ha₂ using h_principal;
      exact ⟨a, fun A hA hA' => ⟨ha₂ A hA hA', ha₁ A hA hA' ▸ rfl⟩⟩
theorem arithmetic_construction (g t : ℕ) (hg : 1 ≤ g) (_ht : 1 ≤ t) :
    ∃ (b : Ideal (𝓞 (Kf g))) (μ : Kf g) (Z : Finset (𝓞 (Kf g))),
      b ≠ ⊥ ∧
        μ ≠ 0 ∧
          (∀ z ∈ Z, z ∈ b) ∧
            (∀ z ∈ Z,
                ∀ w : InfinitePlace (Kf g), (w (algebraMap (𝓞 (Kf g)) (Kf g) z)) ^ 2 = w μ) ∧
              (∏ w : InfinitePlace (Kf g), w μ) = (m t : ℝ) ^ 2 ^ g * (Ideal.absNorm b : ℝ) ∧
                (2 : ℝ) ^ (t * 2 ^ (g - 1)) ≤
                  (Z.card : ℝ) * (NumberField.classNumber (Kf g)) * 2 ^ 2 ^ g :=
  by
    classical
    set conj := ringOfIntegersComplexConj (Kf g)
    set m := m t;
    obtain ⟨F, hFcard, hF⟩ := exists_ideal_family g t hg;
    obtain ⟨b, F₁, y, hb, hF₁, hF₁card, hy⟩ :=
      stage1 g F
        (by
          intro A hA hA'; specialize hF A hA; simp_all +decide only [Ideal.map_bot,
            Submodule.mul_bot];
          rw [eq_comm, Ideal.span_singleton_eq_bot] at hF; norm_cast at hF;
          exact
            absurd hF <|
              ne_of_gt <| Finset.prod_pos fun i hi => Nat.Prime.pos <| p1_spec i |>.1);
    have hassoc :
      ∀ A ∈ F₁, ∀ A' ∈ F₁, Ideal.span {y A * conj (y A)} = Ideal.span {y A' * conj (y A')} :=
      by
        intros A hA A' hA'
        have h_eq :
          Ideal.span {y A * conj (y A)} =
            Ideal.span {(m : 𝓞 (Kf g))} * (b * Ideal.map conj b) :=
          by
            have h_eq :
              Ideal.span {y A * conj (y A)} =
                Ideal.span {y A} * Ideal.map conj (Ideal.span {y A}) :=
              by
                simp +decide [Ideal.span_singleton_mul_span_singleton, Ideal.map_span];
            rw [h_eq, hy A hA |>.2]; rw [← hF A (hF₁ hA)]; rw [Ideal.map_mul]; ring
        have h_eq' :
          Ideal.span {y A' * conj (y A')} =
            Ideal.span {(m : 𝓞 (Kf g))} * (b * Ideal.map conj b) :=
          by
            have h_eq' :
              Ideal.span {y A' * conj (y A')} =
                Ideal.span {y A'} * Ideal.map conj (Ideal.span {y A'}) :=
              by
                simp +decide [Ideal.map_span, Ideal.span_singleton_mul_span_singleton];
            rw [h_eq', hy A' hA' |>.2, Ideal.map_mul]; rw [← hF A' (hF₁ hA')]; ring
        rw [h_eq, h_eq'];
    obtain ⟨F₂, μ₀, hF₂, hF₂card, hz⟩ :=
      norm_constant_subfamily g F₁ y (fun A hA => (hy A hA).1) hassoc;
    obtain ⟨zf, hzf⟩ :
      ∃ zf : Ideal (𝓞 (Kf g)) → 𝓞 (Kf g),
        ∀ A ∈ F₂, Ideal.span {zf A} = Ideal.span {y A} ∧ zf A * conj (zf A) = μ₀ :=
      by
        exact
          ⟨fun A => if hA : A ∈ F₂ then Classical.choose (hz A hA) else 0, fun A hA =>
            by
              simpa [hA] using Classical.choose_spec (hz A hA)⟩;
    refine ⟨b, algebraMap (𝓞 (Kf g)) (Kf g) μ₀, F₂.image zf, hb, ?_, ?_, ?_, ?_⟩;
    ·
      have hμ₀_nonzero : μ₀ ≠ 0 :=
        by
          obtain ⟨A, hA⟩ : ∃ A ∈ F₂, True :=
            by
              contrapose! hFcard; simp_all +decide [Finset.eq_empty_of_forall_notMem hFcard];
          intro hμ₀_zero
          have hzf_zero : zf A = 0 :=
            by
              simp_all +decide;
          have := hzf A hA.1; simp_all +decide only [ne_eq, mul_eq_zero,
            EmbeddingLike.map_eq_zero_iff, or_self, exists_eq_right,
            Submodule.span_zero_singleton, and_true, map_zero, mul_zero];
          exact
            hy A (hF₂ hA) |>.1
              (by
                simpa using this.symm);
      intro h
      exact
        hμ₀_nonzero
          (IsFractionRing.injective (𝓞 (Kf g)) (Kf g)
            (by
              rw [map_zero]; exact h))
    · simp +zetaDelta only [Finset.mem_image, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂] at *; intro A hA;
      have hzfA_in_b : Ideal.span {zf A} ≤ b :=
        by
          rw [hzf A hA |>.1, hy A (hF₂ hA) |>.2]; exact Ideal.mul_le_right (I := A)
      exact hzfA_in_b <| Ideal.mem_span_singleton_self _;
    · simp +zetaDelta only [Finset.mem_image, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂] at *;
      intro A hA w; rw [← hzf A hA |>.2]; rw [← place_mul_conj];
    · refine ⟨?_, ?_⟩;
      · obtain ⟨A₀, hA₀⟩ : ∃ A₀ ∈ F₂, True :=
          by
            contrapose! hFcard; simp_all +decide [Finset.eq_empty_of_forall_notMem hFcard];
        have h_norm : Ideal.absNorm (Ideal.span {zf A₀}) = m ^ 2 ^ g * Ideal.absNorm b :=
          by
            have h_norm : Ideal.absNorm A₀ = m ^ 2 ^ g :=
              by
                apply absNorm_of_mul_conj g A₀ m (hF A₀ (hF₁ (hF₂ hA₀.left)));
            grind;
        have h_norm :
          ∏ w : InfinitePlace (Kf g),
              w (algebraMap (𝓞 (Kf g)) (Kf g) (zf A₀ * conj (zf A₀))) =
            (Ideal.absNorm (Ideal.span {zf A₀}) : ℝ) :=
          by
            convert prod_place_mul_conj g (zf A₀) using 1;
        aesop;
      · rw [Finset.card_image_of_injOn];
        · norm_cast at *;
          nlinarith [show 0 < classNumber (Kf g) from
              Nat.pos_of_ne_zero
                (by
                  aesop)];
        · intro A hA A' hA' h_eq; have := hzf A hA; have := hzf A' hA'; simp_all +decide;
          have := hy A (hF₂ hA); have := hy A' (hF₂ hA'); simp_all +decide;
end Erdos
end
section
namespace Erdos
open scoped Classical in
noncomputable def unitDist (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (P.offDiag.filter (fun pq => dist pq.1 pq.2 = 1)).card / 2
open scoped Classical in
noncomputable def unitPairsC (P : Finset ℂ) : ℕ :=
  (P.offDiag.filter (fun pq => dist pq.1 pq.2 = 1)).card
open scoped Classical in
theorem two_mul_unitDist (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    2 * unitDist P = (P.offDiag.filter (fun pq => dist pq.1 pq.2 = 1)).card :=
  by
    rw [unitDist, Nat.mul_div_cancel'];
    have h_pair :
      ∃ S : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)),
        {pq ∈ P.offDiag | dist pq.1 pq.2 = 1} = S ∪ S.image Prod.swap ∧
          Disjoint S (S.image Prod.swap) :=
      by
        refine
          ⟨Finset.filter (fun pq => pq.1 0 < pq.2 0 ∨ pq.1 0 = pq.2 0 ∧ pq.1 1 < pq.2 1)
              (Finset.filter (fun pq => dist pq.1 pq.2 = 1) (P.offDiag)),
            ?_, ?_⟩;
        · ext ⟨x, y⟩; simp +decide [dist_comm];
          cases lt_trichotomy (x 0) (y 0) <;> cases lt_trichotomy (x 1) (y 1) <;>
            simp_all +decide [dist_eq_norm, EuclideanSpace.norm_eq];
          · aesop;
          · aesop;
          · grind +revert;
          · grind;
        · norm_num [Finset.disjoint_right]; grind;
    obtain ⟨S, hS₁, hS₂⟩ := h_pair;
    rw [hS₁, Finset.card_union_of_disjoint hS₂,
      Finset.card_image_of_injective _ Prod.swap_injective];
    simp +decide [← two_mul];
noncomputable def complexToPlane : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Complex.orthonormalBasisOneI.repr
theorem exists_euclidean_copy (P : Finset ℂ) :
    ∃ Q : Finset (EuclideanSpace ℝ (Fin 2)),
      Q.card = P.card ∧ 2 * unitDist Q = unitPairsC P := by
  classical
  let Q := Finset.image (fun z => complexToPlane z) P
  refine ⟨Q, Finset.card_image_of_injective _ complexToPlane.injective, ?_⟩
  rw [two_mul_unitDist]
  unfold unitPairsC
  apply Finset.card_bij
      (fun pq _ => (complexToPlane.symm pq.1, complexToPlane.symm pq.2))
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_filter, Finset.mem_offDiag, Q, Finset.mem_image] at hab ⊢
    rcases hab with ⟨⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩, hxy⟩, hdist⟩
    have hne : x ≠ y := fun h => hxy (congrArg complexToPlane h)
    simpa using (show (x ∈ P ∧ y ∈ P ∧ x ≠ y) ∧ dist x y = 1 from
      ⟨⟨hx, hy, hne⟩, by simpa using hdist⟩)
  · rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd h
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨complexToPlane.symm.injective h.1, complexToPlane.symm.injective h.2⟩
  · rintro ⟨x, y⟩ hxy
    refine ⟨(complexToPlane x, complexToPlane y), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_offDiag, Q, Finset.mem_image] at hxy ⊢
      exact ⟨⟨⟨x, hxy.1.1, rfl⟩, ⟨y, hxy.1.2.1, rfl⟩,
        fun h => hxy.1.2.2 (complexToPlane.injective h)⟩, by simpa using hxy.2⟩
    · simp
end Erdos
end
section
namespace Erdos
section GeometricCore
variable {ι : Type} [Fintype ι]
def box (r : ι → ℝ) (c : ℝ) : Set (ι → ℂ) :=
  {x | ∀ i, ‖x i‖ ≤ c * r i}
private lemma cell_index_mem {c ε : ℝ} (hε : 0 < ε) {ri : ℝ} (hri : 0 < ri) {t : ℝ}
    (ht : |t| ≤ c * ri) :
    ⌊(t + c * ri) / (ε * ri / Real.sqrt 2)⌋ ∈
      Finset.Icc (0 : ℤ) ((⌊2 * Real.sqrt 2 * c / ε⌋₊ : ℕ) : ℤ) :=
  by
    refine
      Finset.mem_Icc.mpr
        ⟨Int.floor_nonneg.mpr ?_, Int.le_of_lt_add_one (Int.floor_lt.mpr ?_)⟩;
    · exact
        div_nonneg
          (by
            linarith [abs_le.mp ht])
          (by
            positivity);
    · rw [div_lt_iff₀] <;> norm_num;
      · rw [← mul_div_assoc, lt_div_iff₀] <;>
          nlinarith [Nat.lt_floor_add_one (2 * Real.sqrt 2 * c / ε), Real.sqrt_nonneg 2,
            Real.sq_sqrt zero_le_two, mul_pos hε hri,
            mul_div_cancel₀ (2 * Real.sqrt 2 * c) hε.ne', abs_le.mp ht];
      · positivity
private lemma cell_index_diff {c ε : ℝ} (hε : 0 < ε) {ri : ℝ} (hri : 0 < ri) {a b : ℝ}
    (h : ⌊(a + c * ri) / (ε * ri / Real.sqrt 2)⌋ = ⌊(b + c * ri) / (ε * ri / Real.sqrt 2)⌋) :
    |a - b| < ε * ri / Real.sqrt 2 :=
  by
    rw [Int.floor_eq_iff] at h; rw [abs_lt];
    constructor <;>
      nlinarith [Int.floor_le ((b + c * ri) / (ε * ri / Real.sqrt 2)),
        Int.lt_floor_add_one ((b + c * ri) / (ε * ri / Real.sqrt 2)),
        show 0 < ε * ri / Real.sqrt 2 by positivity,
        mul_div_cancel₀ (a + c * ri) (show ε * ri / Real.sqrt 2 ≠ 0 by positivity),
        mul_div_cancel₀ (b + c * ri) (show ε * ri / Real.sqrt 2 ≠ 0 by positivity)];
private lemma norm_lt_of_re_im_bound {z : ℂ} {d : ℝ} (hd : 0 ≤ d)
    (hre : |z.re| < d) (him : |z.im| < d) : ‖z‖ < d * Real.sqrt 2 := by
  rw [ ← Real.sqrt_sq ( show 0 ≤ d by assumption ) ];
  rw [ ← Real.sqrt_mul <| by positivity ] ; refine Real.sqrt_lt_sqrt ?_ ?_;
  · exact Complex.normSq_nonneg _;
  · nlinarith [ abs_lt.mp hre, abs_lt.mp him, Complex.normSq_apply z ]
private lemma cellCount_le {c ε : ℝ} (hε : 0 < ε) (hεc : ε ≤ c) :
    ((⌊2 * Real.sqrt 2 * c / ε⌋₊ : ℕ) : ℝ) + 1 ≤ 4 * c / ε :=
  by
    by_contra h_contra;
    exact
      h_contra <|
        by
          have :=
            Nat.floor_le
              (show 0 ≤ 2 * Real.sqrt 2 * c / ε by
                exact
                  div_nonneg
                      (mul_nonneg (mul_nonneg zero_le_two <| Real.sqrt_nonneg _) <|
                        by
                          linarith) <|
                    by
                      linarith);
          rw [le_div_iff₀ <|
              by
                linarith] at *;
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two,
            mul_div_cancel₀ (2 * Real.sqrt 2 * c) <| ne_of_gt hε];
theorem finite_and_card_le_of_separated (r : ι → ℝ) (hr : ∀ i, 0 < r i) {c ε : ℝ} (hε : 0 < ε)
    (hεc : ε ≤ c) {S : Set (ι → ℂ)} (hS : S ⊆ box r c)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∃ i, ε * r i < ‖x i - y i‖) :
    S.Finite ∧ (S.ncard : ℝ) ≤ (4 * c / ε) ^ (2 * Fintype.card ι) :=
  by
    classical
    set δ : ι → ℝ := fun i => ε * r i / Real.sqrt 2
    set K : ℤ := (⌊2 * Real.sqrt 2 * c / ε⌋₊ : ℤ)
    set T : Finset (ι → ℤ × ℤ) :=
      Fintype.piFinset (fun _ : ι => (Finset.Icc (0 : ℤ) K) ×ˢ (Finset.Icc (0 : ℤ) K));
    set g : (ι → ℂ) → (ι → ℤ × ℤ) := fun x i =>
      (⌊((x i).re + c * r i) / δ i⌋, ⌊((x i).im + c * r i) / δ i⌋)
    have hg : ∀ x ∈ S, g x ∈ T :=
      by
        intro x hx; simp +zetaDelta only [ne_eq, Fintype.mem_piFinset, Finset.mem_product,
          Finset.mem_Icc] at *; intro i;
        exact
          ⟨⟨cell_index_mem hε (hr i)
                    (show |(x i |> Complex.re)| ≤ c * r i from
                      by
                        simpa using Complex.abs_re_le_norm (x i) |> le_trans <| hS hx i) |>
                  Finset.mem_Icc.mp |>
                And.left,
              cell_index_mem hε (hr i)
                    (show |(x i |> Complex.re)| ≤ c * r i from
                      by
                        simpa using Complex.abs_re_le_norm (x i) |> le_trans <| hS hx i) |>
                  Finset.mem_Icc.mp |>
                And.right⟩,
            ⟨cell_index_mem hε (hr i)
                    (show |(x i |> Complex.im)| ≤ c * r i from
                      by
                        simpa using Complex.abs_im_le_norm (x i) |> le_trans <| hS hx i) |>
                  Finset.mem_Icc.mp |>
                And.left,
              cell_index_mem hε (hr i)
                    (show |(x i |> Complex.im)| ≤ c * r i from
                      by
                        simpa using Complex.abs_im_le_norm (x i) |> le_trans <| hS hx i) |>
                  Finset.mem_Icc.mp |>
                And.right⟩⟩;
    have hg_inj : Set.InjOn g S :=
      by
        intros x hx y hy hxy
        by_contra hxy_ne
        obtain ⟨i, hi⟩ := hsep x hx y hy hxy_ne
        have h_diff : ‖x i - y i‖ < δ i * Real.sqrt 2 :=
          by
            apply norm_lt_of_re_im_bound;
            · exact div_nonneg (mul_nonneg hε.le (le_of_lt (hr i))) (Real.sqrt_nonneg _);
            · convert! cell_index_diff hε (hr i) _ using 1;
              exacts [c,
                by
                  simpa using! congr_arg Prod.fst (congr_fun hxy i)];
            · convert! cell_index_diff hε (hr i) _ using 1;
              exacts [c,
                by
                  simpa using! congr_arg Prod.snd (congr_fun hxy i)];
        rw [div_mul_cancel₀ _
            (by
              positivity)] at h_diff;
        linarith;
    have h_finite : S.Finite :=
      by
        exact
          Set.Finite.of_finite_image
            (Set.Finite.subset (Finset.finite_toSet T) (Set.image_subset_iff.mpr hg)) hg_inj
    have h_card : (S.ncard : ℝ) ≤ T.card :=
      by
        have := Set.InjOn.ncard_image hg_inj;
        exact_mod_cast
          this ▸ Set.ncard_le_ncard (show g '' S ⊆ T from Set.image_subset_iff.mpr hg) |>
              le_trans <|
            by
              simp +decide [Set.ncard_eq_toFinset_card'];
    refine ⟨h_finite, h_card.trans ?_⟩;
    convert
      pow_le_pow_left₀
        (by
          positivity)
        (cellCount_le hε hεc) (2 * Fintype.card ι) using
      1;
    norm_num [Finset.card_univ, pow_mul]; erw [Fintype.card_piFinset]; norm_num [pow_mul];
    norm_cast; ring_nf!
    rw [pow_mul']; norm_cast; ring_nf!
theorem lattice_inter_box_finite_card (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (Λ : AddSubgroup (ι → ℂ)) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ2 : ρ ≤ 2)
    (hsep : ∀ x ∈ Λ, x ≠ 0 → ∃ i, ρ * r i < ‖x i‖) :
    ((Λ : Set (ι → ℂ)) ∩ box r 2).Finite ∧
      (((Λ : Set (ι → ℂ)) ∩ box r 2).ncard : ℝ) ≤ (8 / ρ) ^ (2 * Fintype.card ι) :=
  by
    convert
      finite_and_card_le_of_separated r hr (show 0 < ρ by linarith) (show ρ ≤ 2 by linarith)
        (show (Λ : Set (ι → ℂ)) ∩ box r 2 ⊆ box r 2 by exact Set.inter_subset_right) _ using
      1; · norm_num;
    · exact fun x hx y hy hxy =>
        hsep (x - y) (Λ.sub_mem hx.1 hy.1) (sub_ne_zero_of_ne hxy) |> fun ⟨i, hi⟩ =>
          ⟨i,
            by
              simpa using hi⟩
theorem ncard_box_two_le_doubling (r : ι → ℝ) (hr : ∀ i, 0 < r i) (Λ : AddSubgroup (ι → ℂ))
    (hfin : ((Λ : Set (ι → ℂ)) ∩ box r 2).Finite) :
    (((Λ : Set (ι → ℂ)) ∩ box r 2).ncard : ℝ) ≤
      64 ^ Fintype.card ι * ((Λ : Set (ι → ℂ)) ∩ box r 1).ncard :=
  by
    classical
    set A : Set (ι → ℂ) := Λ ∩ box r 2
    set B : Set (ι → ℂ) := Λ ∩ box r 1;
    obtain ⟨sA, hsA⟩ : ∃ sA : Finset (ι → ℂ), A = sA :=
      by
        exact ⟨hfin.toFinset, hfin.coe_toFinset.symm⟩
    obtain ⟨sB, hsB⟩ : ∃ sB : Finset (ι → ℂ), B = sB :=
      by
        have hBfin : B.Finite :=
          by
            exact
              hfin.subset fun x hx =>
                ⟨hx.1, fun i =>
                  le_trans (hx.2 i)
                    (mul_le_mul_of_nonneg_right
                      (by
                        norm_num)
                      (le_of_lt (hr i)))⟩
        exact
          ⟨hBfin.toFinset,
            by
              simp⟩
    simp_all +decide only [Finset.finite_toSet, Set.ncard_eq_toFinset_card', Finset.toFinset_coe];
    have h_card_le_mul_card_image :
      sA.card ≤
        sB.card *
          (sA.image
              (fun x => fun i =>
                (⌊(x i).re / (2 * r i / 3)⌋, ⌊(x i).im / (2 * r i / 3)⌋))).card :=
      by
        have h_card_le_mul_card_image :
          ∀
            b ∈
              sA.image
                (fun x => fun i => (⌊(x i).re / (2 * r i / 3)⌋, ⌊(x i).im / (2 * r i / 3)⌋)),
            (sA.filter
                  (fun a =>
                    (fun x i => (⌊(x i).re / (2 * r i / 3)⌋, ⌊(x i).im / (2 * r i / 3)⌋)) a =
                      b)).card ≤
              sB.card :=
          by
            intro b hb
            obtain ⟨x₀, hx₀⟩ :
              ∃ x₀ ∈ sA,
                (fun x i => (⌊(x i).re / (2 * r i / 3)⌋, ⌊(x i).im / (2 * r i / 3)⌋)) x₀ =
                  b :=
              by
                aesop
            have h_fiber :
              ∀ y ∈ sA,
                (fun x i => (⌊(x i).re / (2 * r i / 3)⌋, ⌊(x i).im / (2 * r i / 3)⌋)) y = b →
                  y - x₀ ∈ sB :=
              by
                intro y hy hyb
                have h_diff : ∀ i, ‖(y i - x₀ i)‖ ≤ r i :=
                  by
                    intro i
                    have h_diff_re : |(y i).re - (x₀ i).re| ≤ 2 * r i / 3 :=
                      by
                        have h_diff_re :
                          ⌊(y i).re / (2 * r i / 3)⌋ = ⌊(x₀ i).re / (2 * r i / 3)⌋ :=
                          by
                            replace hyb := congr_fun hyb i; replace hx₀ := congr_fun hx₀.2 i;
                            aesop;
                        rw [Int.floor_eq_iff] at h_diff_re; rw [abs_le];
                        constructor <;>
                          nlinarith [hr i,
                            Int.floor_le ((x₀ i |> Complex.re) / (2 * r i / 3)),
                            Int.lt_floor_add_one ((x₀ i |> Complex.re) / (2 * r i / 3)),
                            mul_div_cancel₀ ((y i |> Complex.re))
                              (by
                                  linarith [hr i] :
                                (2 * r i / 3) ≠ 0),
                            mul_div_cancel₀ ((x₀ i |> Complex.re))
                              (by
                                  linarith [hr i] :
                                (2 * r i / 3) ≠ 0)];
                    have h_diff_im : |(y i).im - (x₀ i).im| ≤ 2 * r i / 3 :=
                      by
                        have h_diff_im :
                          ⌊(y i).im / (2 * r i / 3)⌋ = ⌊(x₀ i).im / (2 * r i / 3)⌋ :=
                          by
                            replace hyb := congr_fun hyb i; replace hx₀ := congr_fun hx₀.2 i;
                            aesop;
                        rw [Int.floor_eq_iff] at h_diff_im; rw [abs_le];
                        constructor <;>
                          nlinarith [hr i,
                            Int.floor_le ((x₀ i |> Complex.im) / (2 * r i / 3)),
                            Int.lt_floor_add_one ((x₀ i |> Complex.im) / (2 * r i / 3)),
                            mul_div_cancel₀ ((y i |> Complex.im))
                              (by
                                  linarith [hr i] :
                                (2 * r i / 3) ≠ 0),
                            mul_div_cancel₀ ((x₀ i |> Complex.im))
                              (by
                                  linarith [hr i] :
                                (2 * r i / 3) ≠ 0)];
                    norm_num [Complex.normSq, Complex.norm_def] at *;
                    exact
                      Real.sqrt_le_iff.mpr
                        ⟨by
                            linarith [hr i],
                          by
                            nlinarith [abs_le.mp h_diff_re, abs_le.mp h_diff_im]⟩;
                exact
                  hsB.subset
                    ⟨Λ.sub_mem (hsA.symm.subset hy |>.1) (hsA.symm.subset hx₀.1 |>.1),
                      fun i =>
                      by
                        simpa using h_diff i⟩
            have h_fiber_card :
              (sA.filter
                    (fun a =>
                      (fun x i => (⌊(x i).re / (2 * r i / 3)⌋, ⌊(x i).im / (2 * r i / 3)⌋))
                          a =
                        b)).card ≤
                (sB.image (fun y => y + x₀)).card :=
              by
                exact
                  Finset.card_le_card fun x hx =>
                    Finset.mem_image.mpr
                      ⟨x - x₀,
                        h_fiber x (Finset.mem_filter.mp hx |>.1)
                          (Finset.mem_filter.mp hx |>.2),
                        by
                          simp +decide⟩;
            exact h_fiber_card.trans (Finset.card_image_le);
        exact Finset.card_le_mul_card_image sA sB.card h_card_le_mul_card_image
    have h_image_subset_T :
      sA.image (fun x => fun i => (⌊(x i).re / (2 * r i / 3)⌋, ⌊(x i).im / (2 * r i / 3)⌋)) ⊆
        Fintype.piFinset (fun _ : ι => (Finset.Icc (-3 : ℤ) 3) ×ˢ (Finset.Icc (-3 : ℤ) 3)) :=
      by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
        simp only [Int.reduceNeg, Fintype.mem_piFinset, Finset.mem_product, Finset.mem_Icc];
        intro i
        have h_bound : |(y i).re| ≤ 2 * r i ∧ |(y i).im| ≤ 2 * r i :=
          by
            exact
              ⟨le_trans (Complex.abs_re_le_norm _) (hsA.symm.subset hy |>.2 i),
                le_trans (Complex.abs_im_le_norm _) (hsA.symm.subset hy |>.2 i)⟩;
        exact
          ⟨⟨Int.le_floor.2 <|
                by
                  norm_num;
                  nlinarith [abs_le.mp h_bound.1, hr i,
                    mul_div_cancel₀ ((y i |> Complex.re))
                      (by
                          linarith [hr i] :
                        (2 * r i / 3) ≠ 0)],
              Int.le_of_lt_add_one <|
                Int.floor_lt.2 <|
                  by
                    norm_num;
                    nlinarith [abs_le.mp h_bound.1, hr i,
                      mul_div_cancel₀ ((y i |> Complex.re))
                        (by
                            linarith [hr i] :
                          (2 * r i / 3) ≠ 0)]⟩,
            ⟨Int.le_floor.2 <|
                by
                  norm_num;
                  nlinarith [abs_le.mp h_bound.2, hr i,
                    mul_div_cancel₀ ((y i |> Complex.im))
                      (by
                          linarith [hr i] :
                        (2 * r i / 3) ≠ 0)],
              Int.le_of_lt_add_one <|
                Int.floor_lt.2 <|
                  by
                    norm_num;
                    nlinarith [abs_le.mp h_bound.2, hr i,
                      mul_div_cancel₀ ((y i |> Complex.im))
                        (by
                            linarith [hr i] :
                          (2 * r i / 3) ≠ 0)]⟩⟩;
    have h_card_T :
      (Fintype.piFinset
            (fun _ : ι => (Finset.Icc (-3 : ℤ) 3) ×ˢ (Finset.Icc (-3 : ℤ) 3))).card ≤
        64 ^ Fintype.card ι :=
      by
        simp +decide only [Int.reduceNeg, Fintype.card_piFinset, Finset.card_product,
          Int.card_Icc, Int.reduceAdd, sub_neg_eq_add, Int.reduceToNat, Nat.reduceMul,
          Finset.prod_const, Finset.card_univ];
        gcongr; norm_num;
    exact_mod_cast
      h_card_le_mul_card_image.trans
            (Nat.mul_le_mul_left _
              (Finset.card_le_card h_image_subset_T |> le_trans <| h_card_T)) |>
          le_trans <|
        by
          ring_nf; norm_num;
variable (i₀ : ι)
noncomputable def proj (r : ι → ℝ) (i₀ : ι) (x : ι → ℂ) : ℂ :=
  x i₀ / (r i₀ : ℂ)
omit [Fintype ι] in
theorem le_unitPairsC_of_translates (r : ι → ℝ) (hr : ∀ i, 0 < r i) (Λ : AddSubgroup (ι → ℂ))
    (hinj : ∀ x ∈ Λ, x i₀ = 0 → x = 0) (hfin : ((Λ : Set (ι → ℂ)) ∩ box r 2).Finite)
    (Z : Finset (ι → ℂ)) (hZΛ : ∀ z ∈ Z, z ∈ Λ) (hZr : ∀ z ∈ Z, ∀ i, ‖z i‖ = r i) :
    (hfin.toFinset.image (proj r i₀)).card = ((Λ : Set (ι → ℂ)) ∩ box r 2).ncard ∧
      Z.card * ((Λ : Set (ι → ℂ)) ∩ box r 1).ncard ≤
        unitPairsC (hfin.toFinset.image (proj r i₀)) :=
  by
    classical
    refine ⟨?_, ?_⟩;
    · rw [Finset.card_image_of_injOn, ← Set.ncard_coe_finset, hfin.coe_toFinset];
      intro x hx y hy; specialize hinj (x - y); simp_all +decide only [Set.Finite.coe_toFinset,
        Set.mem_inter_iff, SetLike.mem_coe, Pi.sub_apply, sub_eq_zero];
      simp_all +decide only [proj, ne_eq, Complex.ofReal_eq_zero, ne_of_gt (hr i₀),
        not_false_eq_true, div_eq_iff, isUnit_iff_ne_zero, IsUnit.div_mul_cancel];
      exact fun h => hinj (Λ.sub_mem hx.1 hy.1) h;
    · let pairs :=
        Finset.image (fun p : (ι → ℂ) × (ι → ℂ) => (p.2 i₀ / r i₀, (p.2 + p.1) i₀ / r i₀))
          (Z ×ˢ (hfin.toFinset.filter fun x => ∀ i, ‖x i‖ ≤ r i))
      refine le_trans (b := pairs.card) ?_ (Finset.card_mono ?_) <;> dsimp only [pairs]
      swap
      · intro;
        simp +decide only [Pi.add_apply, Finset.mem_image, Finset.mem_product,
          Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_inter_iff, SetLike.mem_coe,
          Prod.exists, Finset.mem_offDiag, ne_eq, forall_exists_index, and_imp];
        rintro x y hx hy hxy hy' rfl; simp_all +decide only [box, Set.mem_ofPred_eq, proj];
        refine
            ⟨⟨⟨y, ⟨hy, hxy⟩, rfl⟩, ⟨y + x, ⟨Λ.add_mem hy (hZΛ x hx), fun i => ?_⟩, ?_⟩, ?_⟩,
              ?_⟩ <;>
          simp_all +decide only [Pi.add_apply, add_div, left_eq_add, div_eq_zero_iff,
            Complex.ofReal_eq_zero, ne_of_gt, or_false, dist_self_add_right, Complex.norm_div,
            Complex.norm_real, Real.norm_eq_abs];
        · exact
            le_trans (norm_add_le _ _)
              (by
                linarith [hy' i, hZr x hx i]);
        · exact fun h =>
            by
              have := hZr x hx i₀; norm_num [h] at this; linarith [hr i₀];
        · rw [abs_of_pos (hr i₀), div_self (ne_of_gt (hr i₀))];
      · rw [Finset.card_image_of_injOn];
        · simp +zetaDelta only [Finset.card_product] at *; gcongr;
          rw [← Set.ncard_coe_finset]; fapply Set.ncard_le_ncard;
          · simp +contextual only [box, one_mul, Finset.coe_filter, Set.Finite.mem_toFinset,
            Set.mem_inter_iff, SetLike.mem_coe, Set.mem_ofPred_eq, Set.subset_def, true_and,
            implies_true, and_true, and_imp];
            exact fun x hx hx' i =>
              le_trans (hx' i)
                (le_mul_of_one_le_left (le_of_lt (hr i))
                  (by
                    norm_num));
          · exact
              hfin.toFinset.finite_toSet.subset fun x hx =>
                by
                  aesop;
        · intro p hp q hq h; simp_all +decide only [Finset.coe_product, Finset.coe_filter,
          Set.Finite.mem_toFinset, Set.mem_inter_iff, SetLike.mem_coe, Set.mem_prod,
          Set.mem_ofPred_eq, Pi.add_apply, Prod.mk.injEq, ne_eq, Complex.ofReal_eq_zero,
          ne_of_gt (hr _), not_false_eq_true, div_eq_iff, isUnit_iff_ne_zero,
          IsUnit.div_mul_cancel];
          have h_eq : p.1 = q.1 :=
            by
              specialize hinj (p.1 - q.1); simp_all +decide only [Pi.sub_apply, sub_eq_iff_eq_add,
                zero_add];
              exact
                hinj
                  (by
                    simpa using Λ.sub_mem (hZΛ _ hp.1) (hZΛ _ hq.1))
                  (by
                    aesop);
          specialize hinj (p.2 - q.2); simp_all +decide only [Pi.sub_apply, sub_self,
            sub_eq_iff_eq_add, zero_add, forall_const, true_and, add_left_inj, and_self];
          exact Prod.ext h_eq (hinj (Λ.sub_mem hp.1.1 hq.2.1.1))
theorem geometric_core (r : ι → ℝ) (hr : ∀ i, 0 < r i) (Λ : AddSubgroup (ι → ℂ)) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ2 : ρ ≤ 2) (hsep : ∀ x ∈ Λ, x ≠ 0 → ∃ i, ρ * r i < ‖x i‖)
    (hinj : ∀ x ∈ Λ, x i₀ = 0 → x = 0) (Z : Finset (ι → ℂ)) (hZΛ : ∀ z ∈ Z, z ∈ Λ)
    (hZr : ∀ z ∈ Z, ∀ i, ‖z i‖ = r i) :
    ∃ (n : ℕ) (Q : Finset (EuclideanSpace ℝ (Fin 2))),
      Q.card = n ∧
        Z.card ≤ n ∧
          (n : ℝ) ≤ (8 / ρ) ^ (2 * Fintype.card ι) ∧
            (Z.card : ℝ) * n ≤ 2 * 64 ^ Fintype.card ι * unitDist Q :=
  by
    obtain ⟨hfin, hupper⟩ := lattice_inter_box_finite_card r hr Λ hρ0 hρ2 hsep;
    obtain ⟨hcard, hpairs⟩ := le_unitPairsC_of_translates i₀ r hr Λ hinj hfin Z hZΛ hZr;
    obtain ⟨Q, hQcard, hQunit⟩ := exists_euclidean_copy (hfin.toFinset.image (proj r i₀));
    refine ⟨Q.card, Q, rfl, ?_, ?_, ?_⟩ <;> norm_cast at * <;> simp_all +decide only [mul_comm,
      zero_mem, Pi.zero_apply];
    · refine
        le_trans ?_
          (Set.ncard_le_ncard (show (↑Z : Set (ι → ℂ)) ⊆ (Λ : Set (ι → ℂ)) ∩ box r 2 from ?_)
            hfin);
      · rw [Set.ncard_coe_finset];
      · exact fun x hx =>
          ⟨hZΛ x hx, fun i =>
            by
              simpa [hZr x hx i] using
                by
                  nlinarith [hr i]⟩;
    · have hdbl := ncard_box_two_le_doubling r hr Λ hfin; norm_cast at *; simp_all +decide;
      nlinarith [pow_pos
          (by
              norm_num :
            (0 : ℕ) < 64)
          (Fintype.card ι)]
end GeometricCore
end Erdos
end
section
open NumberField IsCMField
namespace Erdos
noncomputable def mink (g : ℕ) :
    𝓞 (Kf g) →+* (NumberField.InfinitePlace (Kf g) → ℂ) :=
  RingHom.pi fun w => w.embedding.comp (algebraMap (𝓞 (Kf g)) (Kf g))
theorem Kf_finrank_le (g : ℕ) : Module.finrank ℚ (Kf g) ≤ 2 ^ (g + 1) := by
  exact (Kf_finrank g).le
theorem Kf_card_le (g : ℕ) :
    Fintype.card (NumberField.InfinitePlace (Kf g)) ≤ 2 ^ g := by
  have h_card : Fintype.card (InfinitePlace (Kf g)) * 2 ≤ Module.finrank ℚ (Kf g) := by
    convert! NumberField.IsTotallyComplex.finrank ( Kf g ) |> le_of_eq using 1;
    · have := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces ( Kf g );
      convert! NumberField.IsTotallyComplex.finrank ( Kf g ) |> Eq.symm using 1;
      rw [ this, mul_comm, NumberField.IsTotallyComplex.nrRealPlaces_eq_zero ] ; norm_num;
    · convert! NumberField.IsTotallyComplex.finrank ( Kf g ) using 1;
  linarith [ Kf_finrank_le g, pow_succ' 2 g ]
theorem mink_apply (g : ℕ) (y : 𝓞 (Kf g)) (w : NumberField.InfinitePlace (Kf g)) :
    mink g y w = w.embedding (algebraMap (𝓞 (Kf g)) (Kf g) y) := rfl
theorem norm_mink_apply (g : ℕ) (y : 𝓞 (Kf g)) (w : NumberField.InfinitePlace (Kf g)) :
    ‖mink g y w‖ = w (algebraMap (𝓞 (Kf g)) (Kf g) y) := by
  rw [mink_apply]; exact NumberField.InfinitePlace.norm_embedding_eq w _
theorem mink_injective (g : ℕ) : Function.Injective (mink g) := by
  intro a c h
  have hi : (Classical.arbitrary (NumberField.InfinitePlace (Kf g))).embedding
        (algebraMap (𝓞 (Kf g)) (Kf g) a)
      = (Classical.arbitrary (NumberField.InfinitePlace (Kf g))).embedding
        (algebraMap (𝓞 (Kf g)) (Kf g) c) := by
    have hc := congrFun h (Classical.arbitrary _)
    rwa [mink_apply, mink_apply] at hc
  exact RingOfIntegers.coe_injective
    ((Classical.arbitrary (NumberField.InfinitePlace (Kf g))).embedding.injective hi)
theorem absNorm_le_prod_places (g : ℕ) (b : Ideal (𝓞 (Kf g))) (y : 𝓞 (Kf g)) (hy : y ∈ b)
    (hy0 : y ≠ 0) :
    (Ideal.absNorm b : ℝ) ≤
      ∏ w : NumberField.InfinitePlace (Kf g), (w (algebraMap (𝓞 (Kf g)) (Kf g) y)) ^ 2 :=
  by
    have h1 :
      ∏ w : NumberField.InfinitePlace (Kf g), (w (algebraMap (𝓞 (Kf g)) (Kf g) y)) ^ 2 =
        (Ideal.absNorm (Ideal.span { y }) : ℝ) :=
      by
        convert
          NumberField.InfinitePlace.prod_eq_abs_norm (algebraMap (𝓞 (Kf g)) (Kf g) y) using 1;
        · refine Finset.prod_congr rfl fun w hw => ?_;
          have h_complex : w.IsComplex := NumberField.IsTotallyComplex.isComplex w
          rw [NumberField.InfinitePlace.mult]; aesop;
        · have := Algebra.coe_norm_int y; norm_cast at *; aesop;
    refine h1 ▸ mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero ?_) ?_; · simp +decide [hy0];
    · exact
        Ideal.absNorm_dvd_absNorm_of_le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hy))
theorem mink_sep_aux (g t : ℕ) (b : Ideal (𝓞 (Kf g))) (μ : Kf g) (y : 𝓞 (Kf g)) (hy : y ∈ b)
    (hy0 : y ≠ 0)
    (hprod :
      (∏ w : NumberField.InfinitePlace (Kf g), w μ) =
        (m t : ℝ) ^ 2 ^ g * (Ideal.absNorm b : ℝ))
    (ρ : ℝ)
    (hkey :
      ρ ^ (2 * Fintype.card (NumberField.InfinitePlace (Kf g))) * (m t : ℝ) ^ 2 ^ g < 1) :
    ∃ w : NumberField.InfinitePlace (Kf g), ρ * Real.sqrt (w μ) < ‖mink g y w‖ :=
  by
    contrapose! hkey; simp_all +decide only [ne_eq];
    have h_contradiction :
      (Ideal.absNorm b : ℝ) ≤
        ρ ^ (2 * Fintype.card (InfinitePlace (Kf g))) * (∏ w : InfinitePlace (Kf g), (w μ)) :=
      by
        have h_contradiction :
          (∏ w : InfinitePlace (Kf g), (w (algebraMap (𝓞 (Kf g)) (Kf g) y)) ^ 2) ≤
            (ρ ^ 2) ^ (Fintype.card (InfinitePlace (Kf g))) *
              (∏ w : InfinitePlace (Kf g), (w μ)) :=
          by
            have h_prod_le :
              ∀ w : InfinitePlace (Kf g),
                (w (algebraMap (𝓞 (Kf g)) (Kf g) y)) ^ 2 ≤ (ρ * Real.sqrt (w μ)) ^ 2 :=
              by
                exact fun w =>
                  by
                    simpa only [← norm_mink_apply] using
                      pow_le_pow_left₀
                        (by
                          positivity)
                        (hkey w) 2;
            convert! Finset.prod_le_prod (fun _ _ => sq_nonneg _) fun w _ => h_prod_le w using
              1;
            norm_num [mul_pow, Finset.prod_mul_distrib];
        convert! le_trans (absNorm_le_prod_places g b y hy hy0) h_contradiction using 1; ring;
    by_cases hb : Ideal.absNorm b = 0 <;> simp_all +decide;
    · rw [Ideal.absNorm_eq_zero_iff] at hb; aesop;
    · nlinarith [show 0 < (Ideal.absNorm b : ℝ) by positivity]
theorem rpow_balance_lt {B0 : ℝ} (hB0 : 1 ≤ B0) {d : ℕ} (hd : 1 ≤ d) :
    ((1 / 2 : ℝ) * B0 ^ (-(1 : ℝ) / (2 * (d : ℝ)))) ^ (2 * d) * B0 < 1 :=
  by
    rw [mul_pow];
    rw [← Real.rpow_natCast _ (2 * d), ← Real.rpow_natCast _ (2 * d), ←
      Real.rpow_mul
        (by
          positivity),
      mul_comm];
    ring_nf; norm_num [show d ≠ 0 by positivity]; norm_cast;
    norm_num [mul_comm, Real.rpow_mul];
    rw [← mul_assoc,
      inv_mul_cancel₀
        (by
          positivity),
      one_mul];
    exact
      pow_lt_one₀
        (by
          positivity)
        (by
          norm_num)
        (by
          positivity)
theorem rpow_balance_le {B0 : ℝ} (hB0 : 1 ≤ B0) {d : ℕ} (hd : 1 ≤ d) :
    (8 / ((1 / 2 : ℝ) * B0 ^ (-(1 : ℝ) / (2 * (d : ℝ))))) ^ (2 * d) = (256 : ℝ) ^ d * B0 :=
  by
    ring_nf at *;
    norm_num [pow_mul', ← Real.rpow_natCast,
      ←
        Real.rpow_mul
          (by
              positivity :
            0 ≤ B0),
      mul_assoc, mul_comm, mul_left_comm];
    norm_num [show d ≠ 0 by linarith]; norm_num [Real.rpow_neg_one]
theorem box_count_bound {M : ℝ} (hM : 0 ≤ M) {d g : ℕ} (hd : d ≤ 2 ^ g) :
    (256 : ℝ) ^ d * M ^ 2 ^ g ≤ (32 * Real.sqrt M) ^ (2 * 2 ^ g) :=
  by
    rw [mul_pow, pow_mul]; norm_num [Real.sq_sqrt hM]; ring_nf;
    rw [pow_mul', Real.sq_sqrt hM];
    exact
      mul_le_mul_of_nonneg_left
        (le_trans
          (pow_le_pow_left₀
            (by
              norm_num)
            (by
              norm_num)
            _)
          (pow_le_pow_right₀
            (by
              norm_num)
            hd))
        (by
          positivity)
theorem exists_good_pointset (g t : ℕ) (hg : 1 ≤ g) (ht : 1 ≤ t) :
    ∃ (n : ℕ) (Q : Finset (EuclideanSpace ℝ (Fin 2))),
      Q.card = n ∧
      (2 : ℝ) ^ (t * 2 ^ (g - 1)) ≤
        (n : ℝ) * (NumberField.classNumber (Kf g)) * 2 ^ 2 ^ g ∧
      (n : ℝ) ≤ (32 * Real.sqrt (m t)) ^ (2 * 2 ^ g) ∧
      (2 : ℝ) ^ (t * 2 ^ (g - 1)) * (n : ℝ) ≤
        (NumberField.classNumber (Kf g) : ℝ) * 2 ^ 2 ^ g *
          (2 * 64 ^ 2 ^ g) * unitDist Q := by
  classical
  obtain ⟨b, μ, Z, hb, hμ, hZb, hZplace, hprodμ, hZcard⟩ :=
    arithmetic_construction g t hg ht
  set d : ℕ := Fintype.card (NumberField.InfinitePlace (Kf g)) with hd_def
  have hd_le : d ≤ 2 ^ g := Kf_card_le g
  have hd_pos : 1 ≤ d := Fintype.card_pos
  have hM1 : (1 : ℝ) ≤ (m t : ℝ) := by
    have : 1 ≤ m t := Finset.one_le_prod' (fun i _ => (p1_spec i).1.pos)
    exact_mod_cast this
  have hM0 : (0 : ℝ) ≤ (m t : ℝ) := by linarith
  set B0 : ℝ := (m t : ℝ) ^ 2 ^ g with hB0_def
  have hB0 : (1 : ℝ) ≤ B0 := by rw [hB0_def]; exact one_le_pow₀ hM1
  have hB0pos : (0 : ℝ) < B0 := lt_of_lt_of_le one_pos hB0
  set ρ : ℝ := (1 / 2 : ℝ) * B0 ^ (-(1 : ℝ) / (2 * (d : ℝ))) with hρ_def
  have hρ0 : 0 < ρ := by rw [hρ_def]; positivity
  have hρ2 : ρ ≤ 2 := by
    rw [hρ_def]
    have hle1 : B0 ^ (-(1 : ℝ) / (2 * (d : ℝ))) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos hB0
      apply div_nonpos_of_nonpos_of_nonneg (by norm_num)
      positivity
    nlinarith [Real.rpow_pos_of_pos hB0pos (-(1 : ℝ) / (2 * (d : ℝ)))]
  set r : NumberField.InfinitePlace (Kf g) → ℝ := fun w => Real.sqrt (w μ) with hr_def
  have hr : ∀ w, 0 < r w := by
    intro w; rw [hr_def]
    exact Real.sqrt_pos.mpr (NumberField.InfinitePlace.pos_iff.mpr hμ)
  set i0 : NumberField.InfinitePlace (Kf g) := Classical.arbitrary _ with hi0_def
  set Λ : AddSubgroup (NumberField.InfinitePlace (Kf g) → ℂ) :=
    AddSubgroup.map ((mink g).toAddMonoidHom) (b.toAddSubgroup) with hΛ_def
  have hΛ_mem : ∀ x, x ∈ Λ ↔ ∃ y ∈ b, mink g y = x := by
    intro x
    rw [hΛ_def, AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
  set Z' : Finset (NumberField.InfinitePlace (Kf g) → ℂ) := Z.image (mink g) with hZ'_def
  have hZ'card : Z'.card = Z.card := by
    rw [hZ'_def]; exact Finset.card_image_of_injective Z (mink_injective g)
  have hsep : ∀ x ∈ Λ, x ≠ 0 → ∃ i, ρ * r i < ‖x i‖ := by
    intro x hx hx0
    rw [hΛ_mem] at hx
    obtain ⟨y, hyb, rfl⟩ := hx
    have hy0 : y ≠ 0 := by rintro rfl; exact hx0 (by simp)
    have hkey : ρ ^ (2 * d) * (m t : ℝ) ^ 2 ^ g < 1 := by
      rw [hρ_def, ← hB0_def]; exact rpow_balance_lt hB0 hd_pos
    obtain ⟨w, hw⟩ := mink_sep_aux g t b μ y hyb hy0 hprodμ ρ hkey
    exact ⟨w, hw⟩
  have hinj : ∀ x ∈ Λ, x i0 = 0 → x = 0 := by
    intro x hx hx0
    rw [hΛ_mem] at hx
    obtain ⟨y, hyb, rfl⟩ := hx
    rw [mink_apply] at hx0
    have hz : algebraMap (𝓞 (Kf g)) (Kf g) y = 0 :=
      i0.embedding.injective (by rw [hx0]; simp)
    have hy0 : y = 0 := RingOfIntegers.coe_injective (by rw [hz]; simp)
    rw [hy0]; simp
  have hZΛ : ∀ z ∈ Z', z ∈ Λ := by
    intro z hz
    rw [hZ'_def, Finset.mem_image] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    rw [hΛ_mem]; exact ⟨y, hZb y hy, rfl⟩
  have hZr : ∀ z ∈ Z', ∀ i, ‖z i‖ = r i := by
    intro z hz i
    rw [hZ'_def, Finset.mem_image] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    have h2 := hZplace y hy i
    have hnn : 0 ≤ i (algebraMap (𝓞 (Kf g)) (Kf g) y) := apply_nonneg i _
    rw [norm_mink_apply]
    change i (algebraMap (𝓞 (Kf g)) (Kf g) y) = Real.sqrt (i μ)
    rw [← h2, Real.sqrt_sq hnn]
  obtain ⟨n, Q, hQcard, hZn, hnbound, hpairs⟩ :=
    geometric_core i0 r hr Λ hρ0 hρ2 hsep hinj Z' hZΛ hZr
  have hZnR : (Z.card : ℝ) ≤ (n : ℝ) := by
    have h := hZn; rw [hZ'card] at h; exact_mod_cast h
  refine ⟨n, Q, hQcard, ?_, ?_, ?_⟩
  ·
    calc (2 : ℝ) ^ (t * 2 ^ (g - 1))
          ≤ (Z.card : ℝ) * (NumberField.classNumber (Kf g)) * 2 ^ 2 ^ g := hZcard
      _ ≤ (n : ℝ) * (NumberField.classNumber (Kf g)) * 2 ^ 2 ^ g := by gcongr
  ·
    have hbox : (8 / ρ) ^ (2 * d) = (256 : ℝ) ^ d * B0 := by
      rw [hρ_def]; exact rpow_balance_le hB0 hd_pos
    calc (n : ℝ) ≤ (8 / ρ) ^ (2 * d) := hnbound
      _ = (256 : ℝ) ^ d * B0 := hbox
      _ = (256 : ℝ) ^ d * (m t : ℝ) ^ 2 ^ g := by rw [hB0_def]
      _ ≤ (32 * Real.sqrt (m t)) ^ (2 * 2 ^ g) := box_count_bound hM0 hd_le
  ·
    have hpairs' : (Z.card : ℝ) * n ≤ 2 * 64 ^ d * unitDist Q := by
      rw [← hZ'card]; exact hpairs
    calc (2 : ℝ) ^ (t * 2 ^ (g - 1)) * (n : ℝ)
          ≤ ((Z.card : ℝ) * (NumberField.classNumber (Kf g)) * 2 ^ 2 ^ g) * (n : ℝ) := by
            gcongr
      _ = (NumberField.classNumber (Kf g) : ℝ) * 2 ^ 2 ^ g * ((Z.card : ℝ) * (n : ℝ)) := by
            ring
      _ ≤ (NumberField.classNumber (Kf g) : ℝ) * 2 ^ 2 ^ g * (2 * 64 ^ d * unitDist Q) := by
            gcongr
      _ ≤ (NumberField.classNumber (Kf g) : ℝ) * 2 ^ 2 ^ g * (2 * 64 ^ 2 ^ g * unitDist Q) := by
            gcongr
            norm_num
      _ = (NumberField.classNumber (Kf g) : ℝ) * 2 ^ 2 ^ g * (2 * 64 ^ 2 ^ g) * unitDist Q := by
            ring
end Erdos
end
section
namespace Erdos
section Assembly
theorem key_inequality {C : ℝ} (hC : 0 < C) {g t : ℕ} {n ν h M : ℝ} (hn16 : 16 ≤ n)
    (hν : 0 < ν) (hh : 1 ≤ h)
    (hM : 3 ≤ M)
    (hlower : (2 : ℝ) ^ (t * 2 ^ (g - 1)) ≤ n * h * 2 ^ 2 ^ g)
    (hupper : n ≤ (32 * Real.sqrt M) ^ (2 * 2 ^ g))
    (hpairs : (2 : ℝ) ^ (t * 2 ^ (g - 1)) * n ≤ h * 2 ^ 2 ^ g * (2 * 64 ^ 2 ^ g) * ν)
    (hg1 : 1 ≤ g) (_ht5 : 5 ≤ t) (hth : (8 : ℝ) * (Real.log h / 2 ^ g + 8) ≤ t)
    (hgC : 40 * C * (Real.log M + 8) ≤ (t : ℝ) * g * Real.log 2 ^ 2)
    (hMn : Real.log n ≤ 2 * 2 ^ g * (Real.log 32 + Real.log M / 2)) :
    n ^ (1 + C / Real.log (Real.log n)) < ν :=
  by
    have hH : Real.log h ≤ (t : ℝ) * 2 ^ g / 8 - 8 * 2 ^ g :=
      by
        nlinarith [show (0 : ℝ) < 2 ^ g by positivity,
          div_mul_cancel₀ (Real.log h) (show (2 ^ g : ℝ) ≠ 0 by positivity)];
    have h_log_n_ge_d : Real.log n ≥ 2 ^ g :=
      by
        have h_log_lower :
          Real.log (2 ^ (t * 2 ^ (g - 1))) ≤ Real.log (n * h * 2 ^ (2 ^ g)) :=
          by
            gcongr;
        rcases g with (_ | g) <;> simp_all +decide [pow_succ, mul_assoc];
        rw [Real.log_mul
            (by
              positivity)
            (by
              positivity),
          Real.log_mul
            (by
              positivity)
            (by
              positivity),
          Real.log_pow] at h_log_lower;
        norm_num at *;
        nlinarith [Real.log_two_gt_d9, show (t : ℝ) ≥ 5 by norm_cast,
          show (2 ^ g : ℝ) ≥ 1 by exact one_le_pow₀ one_le_two,
          show (Real.log h : ℝ) ≥ 0 by exact Real.log_nonneg hh];
    have h_log_log_n_ge_g_log_2 : Real.log (Real.log n) ≥ g * Real.log 2 :=
      by
        simpa using
          Real.log_le_log
            (by
              positivity)
            h_log_n_ge_d;
    have h_log_nu_ge : Real.log ν ≥ Real.log n + (t * 2 ^ g / 4) * Real.log 2 :=
      by
        have h_log_nu_ge :
          Real.log ν ≥
            Real.log n + (t * 2 ^ g / 2) * Real.log 2 - Real.log h - 7 * 2 ^ g * Real.log 2 -
              Real.log 2 :=
          by
            have h_log_nu_ge :
              Real.log (2 ^ (t * 2 ^ (g - 1)) * n) ≤
                Real.log (h * 2 ^ (2 ^ g) * (2 * 64 ^ (2 ^ g)) * ν) :=
              by
                exact
                  Real.log_le_log
                    (by
                      positivity)
                    hpairs;
            rw [Real.log_mul, Real.log_mul, Real.log_mul] at h_log_nu_ge <;> try positivity;
            rw [Real.log_mul
                (by
                  positivity)
                (by
                  positivity),
              Real.log_mul
                (by
                  positivity)
                (by
                  positivity)] at h_log_nu_ge;
            norm_num at *;
            rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow] at h_log_nu_ge;
            rcases g with (_ | g) <;> norm_num [pow_succ'] at *; linarith;
        have h_log_2_bounds : 1 / 2 < Real.log 2 ∧ Real.log 2 < 1 :=
          by
            exact
              ⟨Real.log_two_gt_d9.trans_le' <|
                  by
                    norm_num,
                Real.log_two_lt_d9.trans_le <|
                  by
                    norm_num⟩;
        nlinarith [show (t : ℝ) ≥ 5 by norm_cast,
          show (2 : ℝ) ^ g ≥ 2 by
            exact
              le_trans
                (by
                  norm_num)
                (pow_le_pow_right₀
                  (by
                    norm_num)
                  hg1),
          mul_le_mul_of_nonneg_left h_log_2_bounds.1.le (show (0 : ℝ) ≤ 2 ^ g by positivity),
          mul_le_mul_of_nonneg_left h_log_2_bounds.2.le (show (0 : ℝ) ≤ 2 ^ g by positivity)];
    have h_term_gt : (t * 2 ^ g / 4) * Real.log 2 > C * Real.log n / Real.log (Real.log n) :=
      by
        have h_bound :
          C * Real.log n / Real.log (Real.log n) ≤
            C * (2 ^ g * (Real.log M + 10)) / (g * Real.log 2) :=
          by
            gcongr;
            · exact
                mul_nonneg hC.le
                  (mul_nonneg (pow_nonneg zero_le_two _)
                    (add_nonneg
                      (Real.log_nonneg
                        (by
                          linarith))
                      (by
                        norm_num)));
            · rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow] at hMn; norm_num at *;
              nlinarith [Real.log_le_sub_one_of_pos zero_lt_two, Real.log_pos one_lt_two,
                pow_pos (zero_lt_two' ℝ) g];
        refine lt_of_le_of_lt h_bound ?_;
        rw [div_lt_iff₀
            (by
              positivity)];
        nlinarith [show 0 < (2 : ℝ) ^ g by positivity, show 0 < (t : ℝ) * 2 ^ g by positivity,
          show 0 < (g : ℝ) * Real.log 2 by positivity, Real.log_pos one_lt_two,
          Real.log_le_sub_one_of_pos zero_lt_two,
          mul_le_mul_of_nonneg_left
              (show (Real.log M : ℝ) ≥ 0 by
                exact
                  Real.log_nonneg <|
                    by
                      linarith) <|
            show 0 ≤ (2 : ℝ) ^ g by positivity];
    rw [Real.rpow_def_of_pos
        (by
          positivity)];
    rw [←
      Real.log_lt_log_iff
        (by
          positivity)
        (by
          positivity),
      Real.log_exp];
    ring_nf at *; linarith
private theorem exists_params (C : ℝ) (hC : 0 < C) (c₀ c₁ : ℝ) (hc₀ : 1 ≤ c₀) (hc₁ : 1 ≤ c₁)
    (N : ℕ) :
    ∃ g t : ℕ,
      1 ≤ g ∧
        5 ≤ t ∧
          8 * (c₀ * (g + 1) * Real.log (g + 2) + 8) ≤ (t : ℝ) ∧
            40 * C * (c₁ * (t : ℝ) * Real.log (t + 2) + 8) ≤ (t : ℝ) * g * Real.log 2 ^ 2 ∧
              Real.log ((max N 16 : ℕ) : ℝ) + c₀ * 2 ^ g * (g + 1) * Real.log (g + 2) +
                  2 ^ g * Real.log 2 ≤
                (t : ℝ) * 2 ^ (g - 1) * Real.log 2 :=
  by
    have h_second :
      ∃ G : ℕ,
        ∀ g ≥ G,
          40 * C *
              (c₁ * (Nat.ceil (8 * (c₀ * (g + 1) * Real.log (g + 2) + 8) + 5)) *
                (Real.log (Nat.ceil (8 * (c₀ * (g + 1) * Real.log (g + 2) + 8) + 5) + 2) +
                  8)) ≤
            (Nat.ceil (8 * (c₀ * (g + 1) * Real.log (g + 2) + 8) + 5)) * g *
              (Real.log 2) ^ 2 :=
      by
        have h_simplify :
          ∃ G : ℕ,
            ∀ g ≥ G,
              Real.log (Nat.ceil (8 * (c₀ * (g + 1) * Real.log (g + 2) + 8) + 5) + 2) ≤
                2 * Real.log (g + 2) + Real.log (8 * c₀ + 70) :=
          by
            have h_simplify :
              ∃ G : ℕ,
                ∀ g ≥ G,
                  Nat.ceil (8 * (c₀ * (g + 1) * Real.log (g + 2) + 8) + 5) + 2 ≤
                    (g + 2) ^ 2 * (8 * c₀ + 70) :=
              by
                refine ⟨8, fun g hg => ?_⟩; ring_nf;
                nlinarith [Nat.ceil_lt_add_one
                    (show 0 ≤ 69 + c₀ * g * Real.log (2 + g) * 8 + c₀ * Real.log (2 + g) * 8
                      by
                      exact
                        add_nonneg
                          (add_nonneg
                            (by
                              positivity)
                            (mul_nonneg
                              (mul_nonneg
                                (mul_nonneg
                                  (by
                                    positivity)
                                  (by
                                    positivity))
                                (Real.log_nonneg
                                  (by
                                    linarith)))
                              (by
                                positivity)))
                          (mul_nonneg
                            (mul_nonneg
                              (by
                                positivity)
                              (Real.log_nonneg
                                (by
                                  linarith)))
                            (by
                              positivity))),
                  Real.log_le_sub_one_of_pos
                    (by
                        positivity :
                      0 < (2 : ℝ) + g),
                  mul_le_mul_of_nonneg_left (show (g : ℝ) ≥ 8 by norm_cast)
                    (show 0 ≤ c₀ by positivity)];
            obtain ⟨G, hG⟩ := h_simplify; use G; intro g hg;
            have :=
              Real.log_le_log
                (by
                  positivity)
                (hG g hg);
            rw [Real.log_mul
                (by
                  positivity)
                (by
                  positivity),
              Real.log_pow] at this;
            norm_num at *; linarith;
        obtain ⟨G, hG⟩ := h_simplify;
        have h_bound :
          ∃ G' : ℕ,
            ∀ g ≥ G',
              40 * C * (c₁ * (2 * Real.log (g + 2) + Real.log (8 * c₀ + 70) + 8)) ≤
                g * (Real.log 2) ^ 2 :=
          by
            have h_bound :
              Filter.Tendsto
                (fun g : ℕ =>
                  (40 * C * (c₁ * (2 * Real.log (g + 2) + Real.log (8 * c₀ + 70) + 8))) /
                    (g : ℝ))
                Filter.atTop (nhds 0) :=
              by
                have h_log_div_g :
                  Filter.Tendsto (fun g : ℕ => (Real.log (g + 2)) / (g : ℝ)) Filter.atTop
                    (nhds 0) :=
                  by
                    have h_log_div_g :
                      Filter.Tendsto (fun g : ℕ => Real.log (g : ℝ) / (g : ℝ)) Filter.atTop
                        (nhds 0) :=
                      by
                        suffices h_change_var :
                          Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y))
                            (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0)
                          from
                          by
                            exact
                              h_change_var.comp
                                  (Filter.map_mono tendsto_natCast_atTop_atTop) |>
                                fun h =>
                                h.congr
                                  (by
                                    intros; simp +decide; ring_nf);
                        norm_num; apply tendsto_nhdsWithin_of_tendsto_nhds
                        have h :
                          Filter.Tendsto (fun y : ℝ => -(y * Real.log y)) (nhds 0)
                            (nhds (-(0 * Real.log 0))) :=
                          (Real.continuous_mul_log.neg.tendsto 0).congr'
                            (Filter.Eventually.of_forall fun _ => rfl)
                        simpa only [zero_mul, neg_zero] using h
                    have h_log_div_g_split :
                      Filter.Tendsto
                        (fun g : ℕ =>
                          (Real.log (g : ℝ) / (g : ℝ)) +
                            (Real.log (1 + 2 / (g : ℝ)) / (g : ℝ)))
                        Filter.atTop (nhds 0) :=
                      by
                        simpa [div_eq_mul_inv] using
                          h_log_div_g.add
                            (Filter.Tendsto.mul
                              (Filter.Tendsto.log
                                (tendsto_const_nhds.add
                                  (tendsto_const_nhds.mul tendsto_inv_atTop_nhds_zero_nat))
                                (by
                                  norm_num))
                              tendsto_inv_atTop_nhds_zero_nat);
                    refine
                      h_log_div_g_split.congr'
                        (by
                          filter_upwards [Filter.eventually_gt_atTop 0] with g hg using
                            by
                              rw [show (g : ℝ) + 2 = g * (1 + 2 / g) by
                                  rw [mul_add,
                                    mul_div_cancel₀ _
                                      (by
                                        positivity)];
                                  ring];
                              rw [Real.log_mul
                                  (by
                                    positivity)
                                  (by
                                    positivity)];
                              ring);
                convert
                    h_log_div_g.const_mul (40 * C * c₁ * 2) |> Filter.Tendsto.add <|
                      show
                        Filter.Tendsto
                          (fun g : ℕ =>
                            (40 * C * c₁ * (Real.log (8 * c₀ + 70) + 8)) / (g : ℝ))
                          Filter.atTop (nhds 0)
                        from tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop using
                    2 <;>
                  ring;
            have := h_bound.eventually (gt_mem_nhds <| show 0 < Real.log 2 ^ 2 by positivity);
            rw [Filter.eventually_atTop] at this; rcases this with ⟨G', hG'⟩;
            exact
              ⟨G' + 1, fun g hg =>
                by
                  have :=
                    hG' g
                      (by
                        linarith);
                  rw [div_lt_iff₀
                      (by
                        norm_cast; linarith)] at this;
                  linarith⟩;
        obtain ⟨G', hG'⟩ := h_bound; use Max.max G G'; intros g hg;
        specialize hG g (le_trans (le_max_left _ _) hg);
        specialize hG' g (le_trans (le_max_right _ _) hg); norm_num at *;
        nlinarith [show (0 : ℝ) ≤ ⌈8 * (c₀ * (g + 1) * Real.log (g + 2) + 8) + 5⌉₊ * c₁ * C by
            positivity];
    obtain ⟨G, hG⟩ := h_second;
    obtain ⟨G', hG'⟩ :
      ∃ G' : ℕ,
        ∀ g ≥ G',
          Real.log (max N 16) + c₀ * 2 ^ g * (g + 1) * Real.log (g + 2) + 2 ^ g * Real.log 2 ≤
            (Nat.ceil (8 * (c₀ * (g + 1) * Real.log (g + 2) + 8) + 5)) * 2 ^ (g - 1) *
              Real.log 2 :=
      by
        suffices h_div :
          ∃ G' : ℕ,
            ∀ g ≥ G',
              Real.log (max N 16) / 2 ^ (g - 1) + 2 * c₀ * (g + 1) * Real.log (g + 2) +
                  2 * Real.log 2 ≤
                (Nat.ceil (8 * (c₀ * (g + 1) * Real.log (g + 2) + 8) + 5)) * Real.log 2
          from
          by
            obtain ⟨G', hG'⟩ := h_div; use G' + 1; intros g hg;
            specialize
              hG' g
                (by
                  linarith);
            rcases g <;> norm_num [pow_succ'] at *;
            rw [div_add', div_add', div_le_iff₀] at hG' <;>
              first
              | positivity
              | linarith;
        have h_log_div :
          Filter.Tendsto (fun g : ℕ => Real.log (max N 16) / 2 ^ (g - 1)) Filter.atTop
            (nhds 0) :=
          by
            exact
              tendsto_const_nhds.div_atTop
                (tendsto_pow_atTop_atTop_of_one_lt one_lt_two |> Filter.Tendsto.comp <|
                  Filter.tendsto_sub_atTop_nat 1);
        have h_bound :
          ∃ G' : ℕ,
            ∀ g ≥ G',
              2 * c₀ * (g + 1) * Real.log (g + 2) + 2 * Real.log 2 ≤
                (8 * (c₀ * (g + 1) * Real.log (g + 2) + 8) + 5) * Real.log 2 -
                  2 * Real.log 2 :=
          by
            use 16; intro g hg; ring_nf; have := Real.log_two_gt_d9; norm_num at *;
            nlinarith [show (g : ℝ) ≥ 16 by norm_cast,
              show (c₀ : ℝ) * Real.log (2 + g) ≥ 0 by
                exact
                  mul_nonneg
                    (by
                      positivity)
                    (Real.log_nonneg
                      (by
                        linarith)),
              show (c₀ : ℝ) * g * Real.log (2 + g) ≥ 0 by
                exact
                  mul_nonneg
                    (mul_nonneg
                      (by
                        positivity)
                      (by
                        positivity))
                    (Real.log_nonneg
                      (by
                        linarith))];
        obtain ⟨G', hG'⟩ := h_bound;
        have := h_log_div.eventually (gt_mem_nhds <| show 0 < 2 * Real.log 2 by positivity);
        obtain ⟨G'', hG''⟩ := Filter.eventually_atTop.mp this;
        exact
          ⟨Max.max G' G'', fun g hg =>
            by
              nlinarith [hG' g (le_trans (le_max_left _ _) hg),
                hG'' g (le_trans (le_max_right _ _) hg),
                Nat.le_ceil (8 * (c₀ * (g + 1) * Real.log (g + 2) + 8) + 5),
                Real.log_pos one_lt_two]⟩;
    refine
        ⟨G + G' + 1, ⌈8 * (c₀ * (G + G' + 1 + 1) * Real.log (G + G' + 1 + 2) + 8) + 5⌉₊, ?_,
          ?_, ?_, ?_, ?_⟩ <;>
      norm_num;
    · exact
        Nat.succ_le_of_lt
          (Nat.lt_ceil.mpr
            (by
              norm_num;
              nlinarith [show 0 ≤ c₀ * (G + G' + 1 + 1) * Real.log (G + G' + 1 + 2) by
                  exact
                    mul_nonneg
                      (mul_nonneg
                        (by
                          positivity)
                        (by
                          positivity))
                      (Real.log_nonneg
                        (by
                          linarith))]));
    · linarith [Nat.le_ceil
          (8 * (c₀ * (G + G' + 1 + 1) * Real.log (G + G' + 1 + 2) + 8) + 5)];
    · convert!
            le_trans _
              (hG (G + G' + 1)
                (by
                  linarith)) using
            1 <;>
          push_cast <;>
        ring_nf;
      gcongr;
      exact
        le_trans
          (le_mul_of_one_le_right
            (by
              positivity)
            hc₁)
          (le_mul_of_one_le_right
            (by
              positivity)
            (Nat.one_le_cast.mpr
              (Nat.ceil_pos.mpr
                (by
                  nlinarith [show 0 ≤ c₀ * G * Real.log (3 + G + G') by
                      exact
                        mul_nonneg
                          (mul_nonneg
                            (by
                              positivity)
                            (Nat.cast_nonneg _))
                          (Real.log_nonneg
                            (by
                              linarith)),
                    show 0 ≤ c₀ * G' * Real.log (3 + G + G') by
                      exact
                        mul_nonneg
                          (mul_nonneg
                            (by
                              positivity)
                            (Nat.cast_nonneg _))
                          (Real.log_nonneg
                            (by
                              linarith)),
                    show 0 ≤ c₀ * Real.log (3 + G + G') by
                      exact
                        mul_nonneg
                          (by
                            positivity)
                          (Real.log_nonneg
                            (by
                              linarith))]))));
    · exact_mod_cast
        hG' (G + G' + 1)
          (by
            linarith)
theorem erdos_unit_distance_uniform_constant_false :
    ∀ C : ℝ,
      0 < C →
        ∀ N : ℕ,
          ∃ (n : ℕ) (P : Finset (EuclideanSpace ℝ (Fin 2))),
            N ≤ n ∧
              P.card = n ∧ (n : ℝ) ^ (1 + C / Real.log (Real.log n)) < (unitDist P : ℝ) :=
  by
    intro C hC N;
    obtain ⟨g, t, hg1, ht5, h2, h3, h4⟩ :=
      exists_params C hC (Classical.choose (log_classNumber_Kf_le))
        (Classical.choose (log_m_le)) (Classical.choose_spec (log_classNumber_Kf_le)).left
        (Classical.choose_spec (log_m_le)).left (max N 16);
    obtain ⟨n, Q, hQcard, hL, hU, hP⟩ :=
      exists_good_pointset g t hg1
        (by
            omega :
          1 ≤ t);
    have hn_ge_max : (max (max N 16) 16 : ℝ) ≤ n :=
      by
        have h_log :
          Real.log
              ((max (max N 16) 16 : ℝ) * (NumberField.classNumber (Kf g)) * 2 ^ (2 ^ g)) ≤
            Real.log (2 ^ (t * 2 ^ (g - 1))) :=
          by
            rw [Real.log_mul, Real.log_mul] <;> norm_num;
            · have := Classical.choose_spec (log_classNumber_Kf_le) |>.2 g; norm_num at *;
              linarith;
            · positivity;
            · exact ne_of_gt (NumberField.classNumber_pos _);
            · exact
                ⟨by
                    positivity,
                  by
                    exact ne_of_gt <| NumberField.classNumber_pos _⟩;
        rw [Real.log_le_log_iff] at h_log <;> norm_cast at * <;> norm_num at *;
        · constructor <;>
            nlinarith [show 0 < NumberField.classNumber (Kf g) * 2 ^ 2 ^ g by
                exact
                  mul_pos (Nat.cast_pos.mpr (NumberField.classNumber_pos _))
                    (pow_pos
                      (by
                        norm_num)
                      _),
              le_max_left N 16, le_max_right N 16];
        · grind +qlia;
    refine ⟨n, Q, ?_, hQcard, ?_⟩;
    · exact_mod_cast le_trans (le_max_of_le_left (le_max_left _ _)) hn_ge_max;
    · apply_rules [key_inequality];
      any_goals linarith [le_max_left (max (N : ℝ) 16) 16, le_max_right (max (N : ℝ) 16) 16];
      any_goals exact Nat.one_le_cast.mpr (NumberField.classNumber_pos _);
      · contrapose! hP;
        exact
          lt_of_le_of_lt
            (mul_nonpos_of_nonneg_of_nonpos
              (by
                positivity)
              hP)
            (by
              exact
                mul_pos
                  (by
                    positivity)
                  (Nat.cast_pos.mpr
                    (by
                      linarith [show n > 0 from
                          Nat.cast_pos.mp
                            (lt_of_lt_of_le
                              (by
                                positivity)
                              hn_ge_max)])));
      · norm_cast;
        exact
          le_trans
            (by
              decide)
            (m_ge t |>
              le_trans
                (pow_le_pow_right₀
                  (by
                    decide)
                  ht5));
      · have := Classical.choose_spec (log_classNumber_Kf_le);
        nlinarith [this.2 g, show (0 : ℝ) < 2 ^ g by positivity,
          div_mul_cancel₀ (Real.log (NumberField.classNumber (Kf g) : ℝ))
            (show (2 : ℝ) ^ g ≠ 0 by positivity)];
      · refine le_trans ?_ h3; gcongr; exact Classical.choose_spec (log_m_le) |>.2 t;
      · refine
          le_trans
            (Real.log_le_log
              (by
                linarith [le_max_left (max (N : ℝ) 16) 16, le_max_right (max (N : ℝ) 16) 16])
              hU)
            ?_;
        rw [Real.log_pow, Real.log_mul, Real.log_sqrt] <;> ring_nf <;> norm_num; · linarith;
        · exact Finset.prod_ne_zero_iff.mpr fun i hi => Nat.Prime.ne_zero <| p1_spec i |>.1
end Assembly
end Erdos
end
section
namespace Erdos90b
abbrev Point := EuclideanSpace ℝ (Fin 2)
noncomputable abbrev unitDistancePairs (P : Finset Point) : ℕ :=
  Erdos.unitDist P
theorem not_erdos_90 :
    ∀ C : ℝ, 0 < C → ∀ N : ℕ,
      ∃ (n : ℕ) (P : Finset Point),
        N ≤ n ∧ P.card = n ∧
          (n : ℝ) ^ (1 + C / Real.log (Real.log n)) <
            (unitDistancePairs P : ℝ) := by
  simpa only [unitDistancePairs] using
    Erdos.erdos_unit_distance_uniform_constant_false
end Erdos90b
alias _root_.Erdos90b.erdos_90b := _root_.Erdos90b.not_erdos_90
end


namespace KBridge90
open Filter Asymptotics
open scoped EuclideanGeometry

theorem out_dist (a b : ℝ²) :
    dist (Quot.out (s(a, b) : Sym2 ℝ²)).1 (Quot.out (s(a, b) : Sym2 ℝ²)).2 = dist a b := by
  have h : (s((Quot.out (s(a, b) : Sym2 ℝ²)).1, (Quot.out (s(a, b) : Sym2 ℝ²)).2) : Sym2 ℝ²)
      = s(a, b) := Quot.out_eq _
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, dist_comm]

theorem unitDist_le (P : Finset ℝ²) : Erdos.unitDist P ≤ unitDistNum P := by
  classical
  unfold Erdos.unitDist unitDistNum
  set A := P.offDiag.filter (fun pq => dist pq.1 pq.2 = 1) with hA
  have h1 : A.card ≤ 2 * (A.image (fun pq => (s(pq.1, pq.2) : Sym2 ℝ²))).card := by
    apply Finset.card_le_mul_card_image
    intro z hz
    obtain ⟨⟨a, b⟩, _, rfl⟩ := Finset.mem_image.mp hz
    calc (A.filter (fun x => (s(x.1, x.2) : Sym2 ℝ²) = s(a, b))).card
        ≤ ({(a, b), (b, a)} : Finset (ℝ² × ℝ²)).card := by
          apply Finset.card_le_card
          intro x hx
          rw [Finset.mem_filter] at hx
          rcases Sym2.eq_iff.mp hx.2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
          · simp [← e1, ← e2]
          · simp [← e1, ← e2]
      _ ≤ 2 := Finset.card_le_two
  have h2 : (A.image (fun pq => (s(pq.1, pq.2) : Sym2 ℝ²))).card ≤
      (P.sym2.filter (fun p => dist p.out.1 p.out.2 = 1)).card := by
    apply Finset.card_le_card
    intro z hz
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hz
    rw [hA, Finset.mem_filter, Finset.mem_offDiag] at hab
    rw [Finset.mem_filter, Finset.mk_mem_sym2_iff]
    exact ⟨⟨hab.1.1, hab.1.2.1⟩, by simp only at hab ⊢; rw [out_dist]; exact hab.2⟩
  have : A.card / 2 ≤ (A.image (fun pq => (s(pq.1, pq.2) : Sym2 ℝ²))).card :=
    Nat.div_le_of_le_mul h1
  convert this.trans h2 using 2

theorem bridge : type_of% @Erdos90.erdos_90 := by
  rintro ⟨O, hO, hEq⟩
  obtain ⟨C, hC, hw⟩ := hO.exists_pos
  have hb := hw.bound
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp ((hb.and hEq).and (eventually_ge_atTop 16))
  obtain ⟨n, P, hn, hcard, hlt⟩ := Erdos90b.not_erdos_90 C hC N0
  obtain ⟨⟨hbn, hen⟩, h16⟩ := hN0 n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_trans (by norm_num) h16)
  have hll : 0 < Real.log (Real.log (n : ℝ)) := by
    apply Real.log_pos
    have : (16 : ℝ) ≤ n := by exact_mod_cast h16
    have h3 : Real.exp 1 < 16 := by
      have := Real.exp_one_lt_d9; linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := by simp
      _ < Real.log n := Real.log_lt_log (Real.exp_pos 1) (by linarith)
  have hOle : O n ≤ C / Real.log (Real.log (n : ℝ)) := by
    have := hbn
    simp only [Real.norm_eq_abs] at this
    rw [abs_of_pos (one_div_pos.mpr hll)] at this
    calc O n ≤ |O n| := le_abs_self _
      _ ≤ C * (1 / Real.log (Real.log (n : ℝ))) := this
      _ = C / Real.log (Real.log (n : ℝ)) := by ring
  have hmem : unitDistNum P ∈ Erdos90.unitDistanceCounts n := ⟨P, hcard, rfl⟩
  have hle : unitDistNum P ≤ Erdos90.maxUnitDistances n :=
    le_csSup (Erdos90.unitDistanceCounts_BddAbove n) hmem
  have hpow : (n : ℝ) ^ (1 + O n) ≤ (n : ℝ) ^ (1 + C / Real.log (Real.log (n : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hu : (Erdos90b.unitDistancePairs P : ℝ) ≤ (Erdos90.maxUnitDistances n : ℝ) := by
    have := unitDist_le P
    exact_mod_cast this.trans hle
  have : (Erdos90.maxUnitDistances n : ℝ) = (n : ℝ) ^ (1 + O n) := hen
  linarith

end KBridge90

theorem OMA.solution : type_of% @Erdos90.erdos_90 := KBridge90.bridge
