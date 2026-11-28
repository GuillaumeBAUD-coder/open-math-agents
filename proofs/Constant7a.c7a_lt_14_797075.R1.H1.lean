import OMAReductions.R_Constant7a_c7a_lt_14_797075_R1

/-
The proof of θ(x) ~ x (and of the weak prime number theorem it rests on, via the Wiener-Ikehara
tauberian theorem) is ported from the PrimeNumberTheoremAnd project,
  https://github.com/AlexKontorovich/PrimeNumberTheoremAnd , commit 55270df807,
by Alex Kontorovich, Terence Tao and the project's contributors, used under the Apache License 2.0.
Files used, in this order (each in its own section below):
  PrimeNumberTheoremAnd/Mathlib/Algebra/Notation/Support.lean
  PrimeNumberTheoremAnd/Mathlib/Analysis/Asymptotics/Asymptotics.lean
  PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean
  PrimeNumberTheoremAnd/Sobolev.lean
  PrimeNumberTheoremAnd/Fourier.lean
  PrimeNumberTheoremAnd/SmoothExistence.lean
  PrimeNumberTheoremAnd/Wiener.lean (up to and including theorem WeakPNT)
  PrimeNumberTheoremAnd/Consequences.lean (only add_isLittleO'', WeakPNT', WeakPNT'',
    isLittleO_sqrt_mul_log and chebyshev_asymptotic)
Modifications: imports merged into the single import above; blueprint annotations and all
attributes (blueprint, ext, continuity, fun_prop, gcongr, norm_cast) and option settings removed,
with the call sites that relied on them adjusted (an explicit CS.ext lemma, explicit continuity
facts handed to fun_prop, an explicit monotonicity step in place of gcongr); the proofs of
second_fourier and limiting_cor_aux were rewritten so that they compile without the
backward.isDefEq.respectTransparency option; four unproved and unused lemmas of Wiener.lean
(prelim_decay_2, prelim_decay_3, decay_alt and the definition AbsolutelyContinuous) were deleted.
-/
-- Ported from PrimeNumberTheoremAnd: Mathlib/Algebra/Notation/Support.lean, Mathlib/Analysis/Asymptotics/Asymptotics.lean, Mathlib/Analysis/SpecialFunctions/Log/Basic.lean
section PNTX_Base

namespace Function

variable {α : Type*} [Zero α]

theorem support_id : support (id : α → α) = {0}ᶜ := by
  ext; simp

theorem support_id' {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ :=
  support_id

end Function


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


open Filter Real

/-- log^b x / x^a goes to zero at infinity if a is positive. -/
theorem Real.tendsto_pow_log_div_pow_atTop (a : ℝ) (b : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun x ↦ log x ^ b / x^a) Filter.atTop (nhds 0) := by
  apply Asymptotics.isLittleO_iff_tendsto' _|>.mp <| isLittleO_log_rpow_rpow_atTop _ ha
  filter_upwards [eventually_gt_atTop 0] with x hx
  intro h
  rw [rpow_eq_zero hx.le ha.ne.symm] at h
  exfalso
  linarith

end PNTX_Base

-- Ported from PrimeNumberTheoremAnd: Sobolev.lean
section PNTX_Sobolev

open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun

theorem CS.ext {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : CS n E}
    (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; cases h; rfl

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
  refine CS.ext (funext fun x => ?_) ; exact (f.hasDerivAt x |>.const_smul R).deriv

noncomputable def scale (g : CS n E) (R : ℝ) : CS n E := by
  by_cases h : R = 0
  · exact ⟨0, contDiff_const, by simp [HasCompactSupport, tsupport]⟩
  · refine ⟨fun x => funscale g R x, ?_, ?_⟩
    · exact g.h1.comp (contDiff_const_smul R⁻¹)
    · exact g.h2.comp_smul (inv_ne_zero h)

lemma deriv_scale {f : CS (n + 1) E} : (f.scale R).deriv = R⁻¹ • f.deriv.scale R := by
  refine CS.ext (funext fun v => ?_) ; by_cases hR : R = 0
  · simp [hR, scale, deriv]
  · simp only [scale, hR, ↓reduceDIte, smul_apply]
    exact ((f.hasDerivAt (R⁻¹ • v)).scomp v
      (by simpa using! (hasDerivAt_id v).const_smul R⁻¹)).deriv

lemma deriv_scale' {f : CS (n + 1) E} :
    (f.scale R).deriv v = R⁻¹ • f.deriv (R⁻¹ • v) := by
  rw [deriv_scale, smul_apply]
  by_cases hR : R = 0 <;> simp [hR, scale, funscale]

lemma hasDerivAt_scale (f : CS (n + 1) E) (R x : ℝ) :
    HasDerivAt (f.scale R) (R⁻¹ • _root_.deriv f (R⁻¹ • x)) x := by
  convert hasDerivAt (f.scale R) x ; rw [deriv_scale'] ; rfl

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
  | succ n ih => simpa [iteratedDeriv_succ'] using! ih (f := SchwartzMap.derivCLM ℝ ℂ f)

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

theorem W21_approximation (f : W21) (g : trunc) :
    Tendsto (fun R => ‖f - (g.scale R * f : W21)‖) atTop (𝓝 0) := by

  -- Definitions
  let f' := f.deriv
  let f'' := f'.deriv
  let g' := (g : CS 2 ℝ).deriv
  let g'' := g'.deriv
  let h R v := 1 - g.scale R v
  let h' R := - (g.scale R).deriv
  let h'' R := - (g.scale R).deriv.deriv

  -- Properties of h
  have ch {R} : Continuous (fun v => (h R v : ℂ)) :=
    continuous_ofReal.comp <| continuous_const.sub (CS.continuous _)
  have ch' {R} : Continuous (fun v => (h' R v : ℂ)) := continuous_ofReal.comp (CS.continuous _)
  have ch'' {R} : Continuous (fun v => (h'' R v : ℂ)) := continuous_ofReal.comp (CS.continuous _)
  have dh R v : HasDerivAt (h R) (h' R v) v := by
    convert! CS.hasDerivAt_scale (g : CS 2 ℝ) R v |>.const_sub 1 using 1
    simp [h', CS.deriv_scale', show g.deriv.toFun = deriv g.toFun from rfl]
  have dh' R v : HasDerivAt (h' R) (h'' R v) v := ((g.scale R).deriv.hasDerivAt v).neg
  have hh1 R v : |h R v| ≤ 1 := by
    by_cases hR : R = 0 <;>
      simp only [CS.scale, funscale, smul_eq_mul, hR, ↓reduceDIte, Pi.zero_apply, sub_zero,
        abs_one, le_refl, h]
    rw [abs_le] ; constructor <;>
    linarith [g.le_one (R⁻¹ * v), g.nonneg (R⁻¹ * v)]
  have vR v : Tendsto (fun R : ℝ => v * R⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul v

  -- Proof
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
        rw [d1] ; convert! (l5.add l7).deriv using 1 ; ring
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
      have evg' : g' =ᶠ[𝓝 0] 0 := by convert! ← g.zero.deriv ; exact deriv_const' _
      have evg'' : g'' =ᶠ[𝓝 0] 0 := by convert! ← evg'.deriv ; exact deriv_const' _
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
      · simpa [h] using! ((g.tendsto_scale v).const_sub 1).ofReal.mul tendsto_const_nhds
    simpa [F] using tendsto_integral_filter_of_dominated_convergence bound e1 e2 e3 e4

end PNTX_Sobolev

-- Ported from PrimeNumberTheoremAnd: Fourier.lean
section PNTX_Fourier

open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

section lemmas

@[simp]
theorem nnnorm_eq_of_mem_circle (z : Circle) : ‖z.val‖₊ = 1 :=
  NNReal.coe_eq_one.mp (by simp [Circle.norm_coe])

@[simp]
theorem nnnorm_circle_smul (z : Circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]

noncomputable def e (u : ℝ) : ℝ →ᵇ ℂ where
  toFun v := 𝐞 (-v * u)
  map_bounded' :=
    ⟨2, fun x y => (dist_le_norm_add_norm _ _).trans (by simp [Circle.norm_coe, one_add_one_eq_two])⟩

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
  exact congr_fun (VectorFourier.fourierIntegral_const_smul 𝐞 _ _ f c) u

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

end PNTX_Fourier

-- Ported from PrimeNumberTheoremAnd: SmoothExistence.lean
section PNTX_Smooth

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



lemma SmoothExistence :
    ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
    ν.support ⊆ Icc (1 / 2) 2 ∧ ∫ x in Ici 0, ν x / x = 1 := by
  suffices h : ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
      ν.support ⊆ Set.Icc (1 / 2) 2 ∧ 0 < ∫ x in Set.Ici 0, ν x / x by
    obtain ⟨ν, hν, hνnonneg, hνsupp, hνpos⟩ := h
    let c := (∫ x in Ici 0, ν x / x)
    use fun y ↦ ν y / c
    refine ⟨hν.div_const c, fun y ↦ div_nonneg (hνnonneg y) (le_of_lt hνpos), ?_, ?_⟩
    · rw [Function.support_div, Function.support_const (ne_of_lt hνpos).symm, inter_univ]
      convert hνsupp
    · simp only [div_right_comm _ c _, integral_div c, div_self <| ne_of_gt hνpos, c]
  have := smooth_urysohn_support_Ioo (a := 1 / 2) (b := 1) (c := 3 / 2) (d := 2)
    (by linarith) (by linarith)
  obtain ⟨ν, hνContDiff, _, hν0, hν1, hνSupport⟩ := this
  use ν, hνContDiff
  unfold indicator at hν0 hν1
  simp only [mem_Icc, Pi.one_apply, Pi.le_def, mem_Ioo] at hν0 hν1
  simp only [hνSupport, subset_def, mem_Ioo, mem_Icc, and_imp]
  split_ands
  · exact fun x ↦ le_trans (by simp [apply_ite]) (hν0 x)
  · exact fun y hy hy' ↦ ⟨by linarith, by linarith⟩
  · rw [integral_pos_iff_support_of_nonneg]
    · simp only [Function.support_div, measurableSet_Ici, Measure.restrict_apply',
        hνSupport, Function.support_id']
      have : (Ioo (1 / 2 : ℝ) 2 ∩ {0}ᶜ ∩ Ici 0) = Ioo (1 / 2) 2 := by
        ext x
        simp only [one_div, mem_inter_iff, mem_Ioo, mem_compl_iff, mem_singleton_iff, mem_Ici]
        bound
      simp only [this, volume_Ioo, ENNReal.ofReal_pos, sub_pos, gt_iff_lt]
      linarith
    · simp_rw [Pi.le_def, Pi.zero_apply]
      intro y
      by_cases h : y ∈ Function.support ν
      · apply div_nonneg <| le_trans (by simp [apply_ite]) (hν0 y)
        rw [hνSupport, mem_Ioo] at h
        linarith [h.left]
      · simp only [Function.mem_support, ne_eq, not_not] at h
        simp [h]
    · have : (fun x ↦ ν x / x).support ⊆ Icc (1 / 2) 2 := by
        rw [Function.support_div, hνSupport]
        exact (inter_subset_left).trans Ioo_subset_Icc_self
      apply (integrableOn_iff_integrable_of_support_subset this).mp
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      apply hνContDiff.continuous.continuousOn.div continuousOn_id ?_
      simp only [mem_Icc, ne_eq, and_imp, id_eq]
      intros; linarith

end PNTX_Smooth

-- Ported from PrimeNumberTheoremAnd: Wiener.lean (up to and including theorem WeakPNT)
section PNTX_Wiener

-- note: the opening of ArithmeticFunction introduces a notation σ that seems
-- impossible to hide, and hence parameters that are traditionally called σ will
-- have to be called σ' instead in this file.

open Real BigOperators ArithmeticFunction MeasureTheory Filter Set FourierTransform LSeries
  Asymptotics SchwartzMap
open Complex hiding log
open scoped Topology
open scoped ContDiff
open scoped ComplexConjugate

variable {n : ℕ} {A a b c d u x y t σ' : ℝ} {ψ Ψ : ℝ → ℂ} {F G : ℂ → ℂ} {f : ℕ → ℂ} {𝕜 : Type}
  [RCLike 𝕜]



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
    -- `Multiplicative.ofAdd x` is definitionally `x`; unfold it by `change` since `fun_prop`
    -- does not see through it.
    change Measurable (Function.uncurry fun (u : ℝ) (a : ℝ) ↦ ((rexp (-u * (σ' - 1))) : ℂ) •
      (𝐞 (-(a * (u / (2 * π)))) : ℂ) • ψ a)
    simp only [neg_mul, ofReal_exp, ofReal_neg, ofReal_mul, ofReal_sub, ofReal_one, smul_eq_mul]
    fun_prop
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
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  rw [fun (a b d : ℂ) ↦ show a * (b * (ψ t) * d) = (a * b * d) * ψ t by ring]
  simp_rw [← mul_assoc]
  rw [integral_mul_const]
  congr 1
  push_cast
  simp_rw [← Complex.exp_add]
  have (u : ℝ) :
      -↑u * (↑σ' - 1) + 2 * ↑π * -(↑t * (↑u / (2 * ↑π))) * I = (1 - σ' - t * I) * u := calc
    _ = -↑u * (↑σ' - 1) + (2 * ↑π) / (2 * ↑π) * -(↑t * ↑u) * I := by ring
    _ = -↑u * (↑σ' - 1) + 1 * -(↑t * ↑u) * I := by rw [div_self (by norm_num)]
    _ = _ := by ring
  simp_rw [this]
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
    simpa using! (integrable_inv_one_add_sq.comp_div hc).const_mul C
  have l2 : AEStronglyMeasurable (fun u ↦ 𝓕 (ψ : ℝ → ℂ) (u / c)) volume := by
    apply Continuous.aestronglyMeasurable ; have := continuous_FourierIntegral ψ ; fun_prop
  obtain ⟨C, h⟩ := decay_bounds_cor ψ
  apply @Integrable.mono' ℝ ℂ _ volume _ _ (fun u => C / (1 + (u / c) ^ 2)) (l1 C) l2 ?_
  apply Eventually.of_forall (fun x => h _)





lemma continuous_LSeries_aux (hf : Summable (nterm f σ')) :
    Continuous fun x : ℝ => LSeries f (σ' + x * I) := by

  have l1 i : Continuous fun x : ℝ ↦ term f (σ' + x * I) i := by
    by_cases h : i = 0
    · simpa [h] using continuous_const
    · simpa [h] using! continuous_const.div (continuous_const.cpow (by fun_prop) (by simp [h]))
        (fun x => by simp [h])
  have l2 n (x : ℝ) : ‖term f (σ' + x * I) n‖ = nterm f σ' n := by
    by_cases h : n = 0
    · simp [h, nterm]
    · simp [h, nterm, cpow_add _ _ (Nat.cast_ne_zero.mpr h),
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero h)]
  exact continuous_tsum l1 hf (fun n x => le_of_eq (l2 n x))

-- Here compact support is used but perhaps it is not necessary
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

/- `nnabla` is the backward difference `u n - u (n+1)`; kept alongside `nabla`
   for summation-by-parts identities that prefer that orientation. -/
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
@[simp] lemma nabla_mul [Ring E] {u : α → E} {c : E} : nabla (fun n => c * u n) = c • nabla u := by
  ext n ; simp [nabla, mul_sub]

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
  simpa using! summation_by_parts (a := a) (b := b) (A := cumsum a) (by simp)

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
  simp only [BoundedAtFilter, isBigO_iff, norm_eq_abs, Pi.one_apply,
    eventually_atTop]
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
  have r2 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  simpa [r2] using hC (n - 1) r1

lemma dirichlet_test' {a b : ℕ → ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hAb : BoundedAtFilter atTop (shift (cumsum a) * b)) (hbb : ∀ᶠ n in atTop, b (n + 1) ≤ b n)
    (h : Summable (shift (cumsum a) * nnabla b)) : Summable (a * b) := by
  have l1 : ∀ᶠ n in atTop, 0 ≤ (shift (cumsum a) * nnabla b) n := by
    filter_upwards [hbb] with n hb
    exact mul_nonneg (by simpa [shift] using! Finset.sum_nonneg' ha) (sub_nonneg.mpr hb)
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
  convert! (log_mul_add_isBigO_log (b := -b / a) (inv_pos.mpr ha)).comp_tendsto
    (tendsto_mul_add_atTop (b := b) ha) using 1
  ext x
  simp only [Function.comp_apply]
  congr
  field_simp
  simp

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
      (by simpa using! (isLittleO_mul_add_sq 1 0).isBigO.comp_tendsto Real.tendsto_log_atTop)

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

/-- Should this be a gcongr lemma? -/
theorem norm_lt_norm_of_nonneg (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    ‖x‖ ≤ ‖y‖ := by
  simp_rw [Real.norm_eq_abs]
  apply abs_le_abs hxy
  linarith

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
    exact norm_lt_norm_of_nonneg _ _ (inv_nonneg.mpr e2.le) (inv_anti₀ e1 e3)

  have l6 : (fun n => d (n + 1) - d n) =O[atTop] (fun n => (Real.log n) ^ 2) := by
    simpa [d, nabla] using! (nnabla_mul_log_sq ((2 * π) ^ 2) hx)

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
    simpa [a] using! IsBigO.mul l5 (isBigO_refl (fun n : ℕ => 1 / (n : ℝ)) _)
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
    have : 1 ≤ (n : ℝ) := by simpa using! Nat.pos_iff_ne_zero.mpr h
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
  simpa [eventuallyEq_nhdsWithin_iff] using! Eventually.of_forall (limiting_fourier_aux hG' hf ψ hx)




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
    rw [Real.fourier_real_eq_integral_exp_smul]
    congr 1; ext t
    rw [smul_eq_mul, mul_comm (f t)]
    congr 2
    push_cast
    field_simp
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
    convert! l4.pow 2 using 1 ; ring
  have l2 : HasDerivAt (fun t : ℝ => 1 + (a * log t) ^ 2) (2 * a ^ 2 * t⁻¹ * log t) t :=
    l3.const_add _
  have l1 : HasDerivAt (fun t : ℝ => t * (1 + (a * log t) ^ 2))
      (1 + 2 * a ^ 2 * log t + a ^ 2 * log t ^ 2) t := by
    convert! (hasDerivAt_id' t).mul l2 using 1; field_simp; ring
  convert! l1.inv e1 using 1; simp only [hh', pp, hh]; field_simp; ring

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
  · trans 0
    · linarith
    · positivity
  · rw [div_lt_iff₀ (by positivity)]
    convert_to! 1 * 1 < 2 * π
    · simp
    · simp
    apply mul_lt_mul one_lt_two ?_ zero_lt_one zero_le_two
    trans 2
    · exact one_le_two
    · exact two_le_pi

lemma cancel_aux {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i * g i ≤ g (n - 1) * (C * n) + (C * (↑(n - 1 - 1) + 1) * g 0
      - C * (↑(n - 1 - 1) + 1) * g (n - 1) -
    ((n - 1 - 1) • (C * g 0) - ∑ x ∈ Finset.range (n - 1 - 1), C * g (x + 1))) := by

  have l1 (n : ℕ) :
      (g n - g (n + 1)) * ∑ i ∈ Finset.range (n + 1), f i ≤ (g n - g (n + 1)) * (C * (n + 1)) := by
    apply mul_le_mul le_rfl (by simpa using! hf' (n + 1)) (Finset.sum_nonneg' hf) ?_
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
    convert_to! ∑ i ∈ Finset.range (n - 1), (C * (↑i + 1)) • (g i - g (i + 1)) ≤ _
    · congr ; ext i ; simp ; ring
    rw [Finset.sum_range_by_parts]
    simp_rw [Finset.sum_range_sub', l2, smul_sub, smul_eq_mul, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range]
    apply le_of_eq ; ring_nf

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
  | n + 2 => convert! cancel_aux' hf hg hf' hg' (n + 2) using 1 ; simp [cumsum_succ] ; ring

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
    have : (Ioc x₀ (x₀ + 1))ᶜ ∩ Icc x₀ (x₀ + 1) = {x₀} := by simp [← sdiff_eq_compl_inter]
    rw [mem_ae_iff, Measure.restrict_apply measurableSet_Ioc.compl, this]
    simp

  have l2 : AntitoneOn (fun x ↦ f (x₀ + x)) (Icc 1 ↑(n + 1)) := by
    intro u ⟨hu1, _⟩ v ⟨_, hv2⟩ huv ; push_cast at hv2
    refine hf ⟨?_, ?_⟩ ⟨?_, ?_⟩ ?_ <;> linarith

  have l3 := @AntitoneOn.sum_le_integral_Ico 1 (n + 1) (fun x => f (x₀ + x)) (by simp)
    (by simpa using l2)

  simp only [Nat.cast_add, Nat.cast_one, intervalIntegral.integral_comp_add_left] at l3
  convert! _root_.add_le_add l1 l3

  have := @intervalIntegral.integral_comp_mul_add ℝ _ _ 1 (n + 1) 1 f one_ne_zero x₀
  rw [intervalIntegral.integral_add_adjacent_intervals]
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
    have := @HasDerivAt.comp _ _ _ _ _ _ (fun t => t / c) _ _ _  (l3 (x / c) (by positivity)) (l4 x)
    convert! this using 1 ; field_simp
  have l5 (x) (hx : 0 < x) := (l2 x hx).const_mul b
  have l1 (x) (hx : 0 < x) := (l5 x hx).arctan
  have l6 (x) (hx : 0 < x) : HasDerivAt g (g' x) x := by
    convert! (l1 x hx).const_mul (a * c / b) using 1
    simp only [g']
    field_simp
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
  convert_to! ∑ i ∈ Finset.range n, ‖f i‖ * ggg i ≤ _
  · congr ; ext i
    by_cases hi : i = 0
    · simp [hi, hf0]
    · simp only [gg, hi, ↓reduceIte, ggg]
      field_simp

  apply cancel_main' (fun _ => norm_nonneg _) (by simp [hf0]) l1 hf l2 n |>.trans
  gcongr ; simp only [cumsum, gg_of_hh l0, one_div, mul_inv_rev, ggg]

  by_cases hn : n = 0
  · simp only [hn, Finset.range_zero, Finset.sum_empty] ; positivity
  replace hn : 0 < n := by omega
  have : Finset.range n = {0} ∪ Finset.Ico 1 n := by
    ext i ; simp ; by_cases hi : i = 0 <;> simp [hi, hn] ; omega
  simp only [this, Finset.singleton_union, Finset.mem_Ico, nonpos_iff_eq_zero, one_ne_zero,
    false_and, not_false_eq_true, Finset.sum_insert, ↓reduceIte, add_le_add_iff_left, ge_iff_le]
  convert_to! ∑ x_1 ∈ Finset.Ico 1 n, x⁻¹ * hh (π⁻¹ * 2⁻¹) (↑x_1 / x) ≤ _
  · apply Finset.sum_congr rfl (fun i hi => ?_)
    simp at hi
    have : i ≠ 0 := by omega
    simp [this]
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
    simpa using! this.mono_set Ioi_subset_Ici_self

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
  convert! mul_le_mul_of_nonneg_left (decay_bounds_key ψ (1 / (2 * π) * log (i / x)))
    (norm_nonneg (f i / i)) using 1
  · simp
  · change _ = _ * (W21.norm ψ * _)
    simp only [W21.norm, mul_inv_rev, one_div, Complex.norm_div, RCLike.norm_natCast]
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
  simpa only [← Summable.tsum_const_smul _ l5] using!
    Summable.tsum_mono l1 (by simpa using l5.const_smul (W21.norm ψ)) l6

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
    · apply Continuous.aestronglyMeasurable ; have := continuous_FourierIntegral ψ ; fun_prop
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

  -- Shorter notation for clarity
  let S1 x (ψ : ℝ → ℂ) := ∑' (n : ℕ), f n / ↑n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑n / x))
  let S2 x (ψ : ℝ → ℂ) := ↑A * ∫ (u : ℝ) in Ici (-Real.log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))
  let S x ψ := S1 x ψ - S2 x ψ ; change Tendsto (fun x ↦ S x ψ) atTop (𝓝 0)

  -- Build the truncation
  obtain g := exists_trunc
  let Ψ R := g.scale R * ψ
  have key R : Tendsto (fun x ↦ S x (Ψ R)) atTop (𝓝 0) := limiting_cor (Ψ R) hf hcheby hG hG'

  -- Choose the truncation radius
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

  -- Apply the compact support case
  filter_upwards [eventually_ge_atTop 1, key R (ε / 2) (by positivity)] with x hx key

  -- Control the tail term
  have key3 : ‖S x (ψ - Ψ R)‖ < ε / 2 := by
    have : ‖S x _‖ ≤ _ * M := @bound_main f C A x hx (ψ - Ψ R) hcheby
    apply this.trans_lt
    apply (mul_le_mul (d := 1 + M) le_rfl (by simp) (by positivity) W21.norm_nonneg).trans_lt
    have : 0 < 1 + M := by positivity
    convert! (mul_lt_mul_iff_left₀ this).mpr hRψ using 1 ; field_simp

  -- Conclude the proof
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
      simpa using! this

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





-- just the surjectivity is stated here, as this is all that is needed for the current
-- application, but perhaps one should state and prove bijectivity instead

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
    simpa using! (comp_exp_support hsupp hplus).comp_smul this |>.mul_left
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
    have r5 : 1 ≤ volume ((Function.support fun y ↦ ψ y) ∩ Ioi 0) := by convert! volume.mono r4 ; norm_num
    simpa [setIntegral_pos_iff_support_of_nonneg_ae r1 r2] using! zero_lt_one.trans_le r5
  have := div_nonneg l3 l4.le ; field_simp at this ; exact this



lemma WienerIkeharaInterval {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * (indicator (Ico a b) 1 (n / x))) / x) atTop (nhds (A * (b - a))) := by

  -- Take care of the trivial case `a = b`
  by_cases hab : a = b
  · simp [hab]
  replace hb : a < b := lt_of_le_of_ne hb hab ; clear hab

  -- Notation to make the proof more readable
  let S (g : ℝ → ℝ) (x : ℝ) :=  (∑' n, f n * g (n / x)) / x
  have hSnonneg {g : ℝ → ℝ} (hg : 0 ≤ g) : ∀ᶠ x : ℝ in atTop, 0 ≤ S g x := by
    filter_upwards [eventually_ge_atTop 0] with x hx
    refine div_nonneg ?_ hx
    refine tsum_nonneg (fun i => mul_nonneg (hpos _) (hg _))
  have hA : 0 ≤ A := residue_nonneg hpos hf hcheby hG hG'

  -- A few facts about the indicator function of `Icc a b`
  let Iab : ℝ → ℝ := indicator (Ico a b) 1
  change Tendsto (S Iab) atTop (𝓝 (A * (b - a)))
  have hIab : HasCompactSupport Iab := by simpa [Iab, HasCompactSupport, tsupport, hb.ne] using isCompact_Icc
  have Iab_nonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ S Iab x := hSnonneg (indicator_nonneg (by simp))
  have Iab2 : IsBoundedUnder (· ≤ ·) atTop (S Iab) := by
    obtain ⟨C, hC⟩ := hcheby ; exact ⟨C * 2 * b, WI_sum_Iab_le' hpos hC (by linarith)⟩
  have Iab3 : IsBoundedUnder (· ≥ ·) atTop (S Iab) := ⟨0, Iab_nonneg⟩
  have Iab0 : IsCoboundedUnder (· ≥ ·) atTop (S Iab) := Iab2.isCoboundedUnder_ge
  have Iab1 : IsCoboundedUnder (· ≤ ·) atTop (S Iab) := Iab3.isCoboundedUnder_le

  -- Bound from above by a smooth function
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

  -- Bound from below by a smooth function
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

  -- Combine the two bounds
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

-- TODO with `Ico`



/-- A version of the *Wiener-Ikehara Tauberian Theorem*: If `f` is a nonnegative arithmetic
function whose L-series has a simple pole at `s = 1` with residue `A` and otherwise extends
continuously to the closed half-plane `re s ≥ 1`, then `∑ n < N, f n` is asymptotic to `A*N`. -/

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
  have hceilN : ⌈ε * N⌉₊ ≤ N := by
    simp only [Nat.ceil_le]
    exact mul_le_of_le_one_left N.cast_nonneg hε
  have r1 : Finset.range N = Finset.range ⌈ε * N⌉₊ ∪ Finset.Ico ⌈ε * N⌉₊ N := by
    ext n
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
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
  simpa [← S_sub_S h2.2] using! l2.trans_lt h1

theorem WienerIkeharaTheorem' {f : ℕ → ℝ} (hpos : 0 ≤ f)
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun N => cumsum f N / N) atTop (𝓝 A) := by

  convert_to Tendsto (S f 0) atTop (𝓝 A) ; · ext N ; simp [S, cumsum]
  apply (tendsto_S_S_zero hpos hcheby).tendsto_of_eventually_tendsto
  · have L0 : Ioc 0 1 ∈ 𝓝[>] (0 : ℝ) := inter_mem_nhdsWithin _ (Iic_mem_nhds zero_lt_one)
    apply eventually_of_mem L0
    · intro ε hε
      simpa using! WienerIkeharaInterval_discrete' hpos hf hcheby hG hG' hε.1 hε.2
  · have : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    simpa using (this.const_sub 1).const_mul A

theorem vonMangoldt_cheby : cheby Λ := by
  use Real.log 4 + 4
  intro N
  by_cases! h : N = 0
  · simp [h, cumsum]
  simp only [cumsum, norm_real, norm_eq_abs]
  rw [Nat.range_eq_Icc_zero_sub_one _ h, (by simp : N - 1 = ⌊(N : ℝ) - 1⌋₊)]
  simp_rw [abs_of_nonneg vonMangoldt_nonneg]
  rw [← Chebyshev.psi_eq_sum_Icc]
  grw [Chebyshev.psi_le_const_mul_self <| sub_nonneg_of_le <| Nat.one_le_cast_iff_ne_zero.mpr h]
  gcongr
  linarith



-- Proof extracted from the `EulerProducts` project so we can adapt it to the
-- version of the Wiener-Ikehara theorem proved above (with the `cheby`
-- hypothesis)

theorem WeakPNT : Tendsto (fun N ↦ cumsum Λ N / N) atTop (𝓝 1) := by
  let F := vonMangoldt.LFunctionResidueClassAux (q := 1) 1
  have hnv := riemannZeta_ne_zero_of_one_le_re
  have l1 (n : ℕ) : 0 ≤ Λ n := vonMangoldt_nonneg
  have l2 s (hs : 1 < s.re) : F s = LSeries Λ s - 1 / (s - 1) := by
    have := vonMangoldt.eqOn_LFunctionResidueClassAux (q := 1) isUnit_one hs
    simp only [F, this, vonMangoldt.residueClass, Nat.totient_one, Nat.cast_one, inv_one, one_div, sub_left_inj]
    apply LSeries_congr
    intro n _
    simp only [ofReal_inj, indicator_apply_eq_self, mem_setOf_eq]
    exact fun hn ↦ absurd (Subsingleton.eq_one _) hn
  have l3 : ContinuousOn F {s | 1 ≤ s.re} := vonMangoldt.continuousOn_LFunctionResidueClassAux 1
  have l4 : cheby Λ := vonMangoldt_cheby
  have l5 (σ' : ℝ) (hσ' : 1 < σ') : Summable (nterm Λ σ') := by
    simpa only [← nterm_eq_norm_term] using (@ArithmeticFunction.LSeriesSummable_vonMangoldt σ' hσ').norm
  apply WienerIkeharaTheorem' l1 l5 l4 l3 l2

end PNTX_Wiener

-- Ported from PrimeNumberTheoremAnd: Consequences.lean (selected lemmas up to chebyshev_asymptotic)
section PNTX_Conseq

section PNTConseq
open ArithmeticFunction hiding log
open Nat hiding log
open Finset
open BigOperators Filter Real Classical Asymptotics MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius ArithmeticFunction.Omega Chebyshev

/-- If u ~ v and u-w = o(v) then w ~ v. -/
theorem Asymptotics.IsEquivalent.add_isLittleO'' {α : Type*} {β : Type*} [NormedAddCommGroup β]
    {u : α → β} {v : α → β} {w : α → β} {l : Filter α}
    (huv : Asymptotics.IsEquivalent l u v) (hwu : (u - w) =o[l] v) :
    Asymptotics.IsEquivalent l w v := by
  rw [← sub_sub_self u w]
  exact sub_isLittleO huv hwu

theorem WeakPNT' : Tendsto (fun N ↦ (∑ n ∈ Iic N, Λ n) / N) atTop (nhds 1) := by
  have : (fun N ↦ (∑ n ∈ Iic N, Λ n) / N) =
      (fun N ↦ (∑ n ∈ range N, Λ n)/N + Λ N / N) := by
    ext N
    have : N ∈ Iic N := mem_Iic.mpr (le_refl _)
    rw [← Finset.sum_erase_add _ _ this, ← Nat.Iio_eq_range, Iic_erase]
    exact add_div _ _ _

  rw [this, ← add_zero 1]
  apply Tendsto.add WeakPNT
  convert squeeze_zero (f := fun N ↦ Λ N / N) (g := fun N ↦ log N / N) (t₀ := atTop) ?_ ?_ ?_
  · intro N
    exact div_nonneg vonMangoldt_nonneg (cast_nonneg N)
  · intro N
    exact div_le_div_of_nonneg_right vonMangoldt_le_log (cast_nonneg N)
  have := Real.tendsto_pow_log_div_pow_atTop 1 1 Real.zero_lt_one
  simp only [rpow_one] at this
  exact Tendsto.comp this tendsto_natCast_atTop_atTop

/-- An alternate form of the Weak PNT. -/
theorem WeakPNT'' : ψ ~[atTop] (fun x ↦ x) := by
    rw [(by rfl : ψ = (fun x ↦ ψ x))]
    simp_rw [Chebyshev.psi_eq_sum_Icc]
    apply IsEquivalent.trans (v := fun x ↦ (⌊x⌋₊:ℝ))
    · rw [isEquivalent_iff_tendsto_one]
      · convert! Tendsto.comp WeakPNT' tendsto_nat_floor_atTop
        infer_instance
      rw [eventually_iff]
      simp only [ne_eq, cast_eq_zero, floor_eq_zero, not_lt, mem_atTop_sets,
        Set.mem_setOf_eq]
      use 1
      simp only [imp_self, implies_true]
    apply IsLittleO.isEquivalent
    rw [← isLittleO_neg_left]
    apply IsLittleO.of_bound
    intro ε hε
    simp only [Pi.sub_apply, neg_sub, norm_eq_abs, eventually_atTop]
    use ε⁻¹
    intro b hb
    have hb' : 0 ≤ b := le_of_lt (lt_of_lt_of_le (inv_pos_of_pos hε) hb)
    rw [abs_of_nonneg, abs_of_nonneg hb']
    · apply LE.le.trans _ ((inv_le_iff_one_le_mul₀' hε).mp hb)
      linarith [Nat.lt_floor_add_one b]
    rw [sub_nonneg]
    exact floor_le hb'

/-- `√x · log x = o(x)` as `x → ∞`. -/
lemma isLittleO_sqrt_mul_log : (fun x : ℝ ↦ x.sqrt * x.log) =o[atTop] _root_.id := by
  have : (fun x : ℝ ↦ x.sqrt * x.log) =o[atTop] fun x ↦ x := by
    refine (isLittleO_mul_iff_isLittleO_div ?_).mpr ?_
    · filter_upwards [eventually_gt_atTop 0] with x hx; exact (sqrt_ne_zero hx.le).mpr hx.ne'
    · convert! isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2) using 2 with x
      rw [div_sqrt, sqrt_eq_rpow]
  exact this

theorem chebyshev_asymptotic : θ ~[atTop] id := by
  refine WeakPNT''.add_isLittleO'' (IsBigO.trans_isLittleO (g := fun x ↦ 2 * x.sqrt * x.log) ?_ ?_)
  · rw [isBigO_iff']; refine ⟨1, one_pos, ?_⟩
    simp only [one_mul, eventually_atTop]
    exact ⟨2, fun x hx ↦ by
      rw [Pi.sub_apply, norm_eq_abs, norm_eq_abs, abs_of_nonneg (by bound : 0 ≤ 2 * √x * log x)]
      exact (abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x))).symm ▸
        Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith : 1 ≤ x)⟩
  · simpa only [mul_assoc] using! isLittleO_sqrt_mul_log.const_mul_left 2

end PNTConseq

end PNTX_Conseq


namespace RVCore

open Real Finset BigOperators Filter MeasureTheory intervalIntegral Asymptotics
open scoped Nat Topology Chebyshev

/- ### Section 1: The Rhin-Viola Integral and Elementary Moves M1, M2, M3 -/

private noncomputable def rvIntegrand (h i j k l : ℕ) (x y : ℝ) : ℝ :=
  x ^ h * (1 - x) ^ i * y ^ k * (1 - y) ^ j / (1 - x * y) ^ (i + j - l + 1)

private noncomputable def rvInt (h i j k l : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, rvIntegrand h i j k l x y

private lemma rvIntegrand_nonneg (h i j k l : ℕ) {x y : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ rvIntegrand h i j k l x y := by
  unfold rvIntegrand
  have h1x : 0 ≤ 1 - x := sub_nonneg.2 hx1
  have h1y : 0 ≤ 1 - y := sub_nonneg.2 hy1
  have h1xy : 0 ≤ 1 - x * y := by nlinarith
  positivity

private lemma rvIntegrand_le_one (h i j k l : ℕ) (hl : 1 ≤ l) (hlij : l ≤ i + j)
    {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hxy1 : x * y < 1) :
    rvIntegrand h i j k l x y ≤ 1 := by
  unfold rvIntegrand
  have h1xy_pos : 0 < 1 - x * y := sub_pos.2 hxy1
  have h1xy_le1 : 1 - x * y ≤ 1 := by nlinarith
  have h1x_le : 1 - x ≤ 1 - x * y := by nlinarith
  have h1y_le : 1 - y ≤ 1 - x * y := by nlinarith
  have hxh : x ^ h ≤ 1 := pow_le_one₀ hx0 hx1
  have hyk : y ^ k ≤ 1 := pow_le_one₀ hy0 hy1
  have hnum : x ^ h * (1 - x) ^ i * y ^ k * (1 - y) ^ j ≤ (1 - x * y) ^ (i + j) := by
    have h1 : (1 - x) ^ i ≤ (1 - x * y) ^ i := pow_le_pow_left₀ (sub_nonneg.2 hx1) h1x_le i
    have h2 : (1 - y) ^ j ≤ (1 - x * y) ^ j := pow_le_pow_left₀ (sub_nonneg.2 hy1) h1y_le j
    calc x ^ h * (1 - x) ^ i * y ^ k * (1 - y) ^ j
        ≤ 1 * (1 - x * y) ^ i * 1 * (1 - x * y) ^ j := by gcongr
      _ = (1 - x * y) ^ (i + j) := by rw [pow_add]; ring
  rw [div_le_one (pow_pos h1xy_pos _)]
  have hexp : i + j - l + 1 ≤ i + j := by omega
  calc x ^ h * (1 - x) ^ i * y ^ k * (1 - y) ^ j
      ≤ (1 - x * y) ^ (i + j) := hnum
    _ ≤ (1 - x * y) ^ (i + j - l + 1) :=
        pow_le_pow_of_le_one h1xy_pos.le h1xy_le1 hexp

private lemma rvIntegrand_integrable_prod (h i j k l : ℕ) (hl : 1 ≤ l) (hlij : l ≤ i + j) :
    Integrable (Function.uncurry (rvIntegrand h i j k l))
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
  have hμ : volume.restrict (Set.Ioc (0 : ℝ) 1) = volume.restrict (Set.Ioo (0 : ℝ) 1) :=
    Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc.symm
  rw [hμ, Measure.prod_restrict]
  set S : Set (ℝ × ℝ) := Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1
  have hS_meas : MeasurableSet S := measurableSet_Ioo.prod measurableSet_Ioo
  have hcont : ContinuousOn (Function.uncurry (rvIntegrand h i j k l)) S := by
    intro p hp
    have h1xy : 1 - p.1 * p.2 ≠ 0 := by nlinarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
    have hc : ContinuousAt (Function.uncurry (rvIntegrand h i j k l)) p := by
      unfold Function.uncurry rvIntegrand
      refine ContinuousAt.div ?_ ?_ (pow_ne_zero _ h1xy)
      · exact (((continuousAt_fst.pow h).mul ((continuousAt_const.sub continuousAt_fst).pow i)).mul
          (continuousAt_snd.pow k)).mul ((continuousAt_const.sub continuousAt_snd).pow j)
      · exact (continuousAt_const.sub (continuousAt_fst.mul continuousAt_snd)).pow _
    exact hc.continuousWithinAt
  have : IsFiniteMeasure ((volume.prod volume).restrict S) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, Measure.prod_prod, Real.volume_Ioo]
    simp
  refine (integrable_const (1 : ℝ)).mono' (hcont.aestronglyMeasurable hS_meas) ?_
  filter_upwards [ae_restrict_mem hS_meas] with p hp
  dsimp only [Function.uncurry]
  rw [Real.norm_eq_abs, abs_of_nonneg (rvIntegrand_nonneg h i j k l hp.1.1.le hp.1.2.le hp.2.1.le hp.2.2.le)]
  exact rvIntegrand_le_one h i j k l hl hlij hp.1.1.le hp.1.2.le hp.2.1.le hp.2.2.le
    (by nlinarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2])

private lemma rvInt_eq_swap (h i j k l : ℕ) (hl : 1 ≤ l) (hlij : l ≤ i + j) :
    rvInt h i j k l = ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, rvIntegrand h i j k l x y := by
  unfold rvInt
  simp_rw [intervalIntegral.integral_of_le zero_le_one]
  exact MeasureTheory.integral_integral_swap (rvIntegrand_integrable_prod h i j k l hl hlij)

private lemma rvInt_M1 (h i j k l : ℕ) (hl : 1 ≤ l) (hlij : l ≤ i + j) :
    rvInt h i j k l = rvInt k j i h l := by
  rw [rvInt_eq_swap h i j k l hl hlij]
  unfold rvInt
  refine intervalIntegral.integral_congr fun y _ => intervalIntegral.integral_congr fun x _ => ?_
  unfold rvIntegrand
  have hadd : i + j = j + i := add_comm i j
  rw [hadd]
  ring

private noncomputable def rvJ (k j m : ℕ) (x : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..1, y ^ k * (1 - y) ^ j / (1 - x * y) ^ (m + 1)

private lemma rvInt_eq_J (h i j k l : ℕ) :
    rvInt h i j k l = ∫ x in (0 : ℝ)..1, x ^ h * (1 - x) ^ i * rvJ k j (i + j - l) x := by
  unfold rvInt rvJ rvIntegrand
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun y _ => ?_
  ring

private lemma rvJ_pfaff (k j m : ℕ) (hmkj : m ≤ k + j) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    (1 - x) ^ m * rvJ k j m x = (1 - x) ^ j * rvJ j k (k + j - m) x := by
  unfold rvJ
  have h1x_pos : 0 < 1 - x := sub_pos.2 hx1
  let uMap : ℝ → ℝ := fun u => (1 - u) / (1 - x * u)
  let uMap' : ℝ → ℝ := fun u => -(1 - x) / (1 - x * u) ^ 2
  have hden : ∀ u ∈ Set.uIcc (0 : ℝ) 1, 0 < 1 - x * u := by
    intro u hu
    rw [Set.uIcc_of_le zero_le_one] at hu
    nlinarith [hu.1, hu.2]
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt uMap (uMap' u) u := by
    intro u hu
    have hne : 1 - x * u ≠ 0 := (hden u hu).ne'
    have hnum : HasDerivAt (fun t : ℝ => 1 - t) (-1) u := by
      simpa using (hasDerivAt_const u (1 : ℝ)).fun_sub (hasDerivAt_id' u)
    have hden' : HasDerivAt (fun t : ℝ => 1 - x * t) (-x) u := by
      have := (hasDerivAt_id' u).const_mul x
      exact ((hasDerivAt_const u (1 : ℝ)).fun_sub this).congr_deriv (by ring)
    refine (hnum.fun_div hden' hne).congr_deriv ?_
    dsimp only [uMap']
    field_simp [hne]
    ring
  have hφ_cont : ContinuousOn uMap (Set.uIcc (0 : ℝ) 1) :=
    fun u hu => (hderiv u hu).continuousAt.continuousWithinAt
  have hφ'_cont : ContinuousOn uMap' (Set.uIcc (0 : ℝ) 1) := by
    intro u hu
    have hne : 1 - x * u ≠ 0 := (hden u hu).ne'
    have hc : ContinuousAt uMap' u :=
      ContinuousAt.div continuousAt_const
        ((continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).pow 2)
        (pow_ne_zero 2 hne)
    exact hc.continuousWithinAt
  have hφ_mem : ∀ u ∈ Set.uIcc (0 : ℝ) 1, uMap u ∈ Set.Icc (0 : ℝ) 1 := by
    intro u hu
    rw [Set.uIcc_of_le zero_le_one] at hu
    have hp : 0 < 1 - x * u := hden u (by rw [Set.uIcc_of_le zero_le_one]; exact hu)
    refine ⟨div_nonneg (sub_nonneg.2 hu.2) hp.le, (div_le_one hp).2 (by nlinarith [hu.1, hu.2])⟩
  let g : ℝ → ℝ := fun y => y ^ k * (1 - y) ^ j / (1 - x * y) ^ (m + 1)
  have hg_cont : ContinuousOn g (uMap '' Set.uIcc (0 : ℝ) 1) := by
    intro y hy
    rcases hy with ⟨u, hu, rfl⟩
    have hmem := hφ_mem u hu
    have hne : 1 - x * uMap u ≠ 0 := by nlinarith [hmem.1, hmem.2]
    have hc : ContinuousAt g (uMap u) :=
      ContinuousAt.div ((continuousAt_id.pow k).mul ((continuousAt_const.sub continuousAt_id).pow j))
        ((continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).pow (m + 1))
        (pow_ne_zero _ hne)
    exact hc.continuousWithinAt
  have hsub := intervalIntegral.integral_comp_mul_deriv'' hφ_cont
    (fun u hu => (hderiv u (by
      rw [Set.uIcc_of_le zero_le_one]
      rw [min_eq_left zero_le_one, max_eq_right zero_le_one] at hu
      exact Set.Ioo_subset_Icc_self hu)).hasDerivWithinAt)
    hφ'_cont hg_cont
  have hφ0 : uMap 0 = 1 := by simp [uMap]
  have hφ1 : uMap 1 = 0 := by
    dsimp [uMap]
    simp
  have hsym : ∫ y in (1 : ℝ)..0, g y = - ∫ y in (0 : ℝ)..1, g y :=
    intervalIntegral.integral_symm 0 1
  rw [hφ0, hφ1, hsym] at hsub
  simp only [Function.comp_apply] at hsub
  have hneg : ∫ y in (0 : ℝ)..1, g y = ∫ u in (0 : ℝ)..1, -(g (uMap u) * uMap' u) := by
    rw [intervalIntegral.integral_neg]
    linarith
  rw [hneg, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun u hu => ?_
  have hp : 0 < 1 - x * u := hden u hu
  have hne : 1 - x * u ≠ 0 := hp.ne'
  have h1x_ne : 1 - x ≠ 0 := h1x_pos.ne'
  have h1φ : 1 - uMap u = u * (1 - x) / (1 - x * u) := by
    dsimp [uMap]; rw [one_sub_div hne]; ring
  have h1xφ : 1 - x * uMap u = (1 - x) / (1 - x * u) := by
    dsimp [uMap]; field_simp [hne]; ring
  dsimp only [g, uMap']
  rw [h1φ, h1xφ]
  dsimp only [uMap]
  have hp2 : (1 - x * u) ^ (m + 1) * (1 - x * u) ^ (k + j - m + 1) =
      (1 - x * u) ^ k * (1 - x * u) ^ j * (1 - x * u) ^ 2 := by
    rw [← pow_add, ← pow_add, ← pow_add]
    congr 1; omega
  rw [div_pow, div_pow, mul_pow, div_pow]
  field_simp [hne, h1x_ne]
  have hp1 : (1 - x) * (1 - x) ^ m = (1 - x) ^ (m + 1) := (pow_succ' (1 - x) m).symm
  calc (1 - x) * (1 - x) ^ m * (1 - u) ^ k * u ^ j * (1 - x * u) ^ (m + 1) *
        (1 - x * u) ^ (k + j - m + 1)
      = ((1 - x) * (1 - x) ^ m) * (1 - u) ^ k * u ^ j *
          ((1 - x * u) ^ (m + 1) * (1 - x * u) ^ (k + j - m + 1)) := by ring
    _ = (1 - x) ^ (m + 1) * (1 - u) ^ k * u ^ j *
          ((1 - x * u) ^ k * (1 - x * u) ^ j * (1 - x * u) ^ 2) := by rw [hp1, hp2]
    _ = (1 - u) ^ k * (1 - x * u) ^ 2 * (1 - x * u) ^ k * u ^ j *
          (1 - x * u) ^ j * (1 - x) ^ (m + 1) := by ring

private lemma rvInt_M2y (h i j k l : ℕ) (hlij : l ≤ i + j) (hilk : i ≤ l + k) :
    rvInt h i j k l = rvInt h l k j i := by
  rw [rvInt_eq_J, rvInt_eq_J]
  simp_rw [intervalIntegral.integral_of_le zero_le_one]
  have hμ : volume.restrict (Set.Ioc (0 : ℝ) 1) = volume.restrict (Set.Ioo (0 : ℝ) 1) :=
    Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc.symm
  rw [hμ]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  have h1x_pos : 0 < 1 - x := sub_pos.2 hx.2
  have h1x_ne : 1 - x ≠ 0 := h1x_pos.ne'
  have hpf := rvJ_pfaff k j (i + j - l) (by omega) hx.1.le hx.2
  have hexp : k + j - (i + j - l) = l + k - i := by omega
  rw [hexp] at hpf
  have hpow : (1 - x) ^ i * (1 - x) ^ j = (1 - x) ^ l * (1 - x) ^ (i + j - l) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  apply mul_left_cancel₀ (pow_ne_zero (i + j - l) h1x_ne)
  calc (1 - x) ^ (i + j - l) * (x ^ h * (1 - x) ^ i * rvJ k j (i + j - l) x)
      = x ^ h * (1 - x) ^ i * ((1 - x) ^ (i + j - l) * rvJ k j (i + j - l) x) := by ring
    _ = x ^ h * (1 - x) ^ i * ((1 - x) ^ j * rvJ j k (l + k - i) x) := by rw [hpf]
    _ = x ^ h * ((1 - x) ^ i * (1 - x) ^ j) * rvJ j k (l + k - i) x := by ring
    _ = x ^ h * ((1 - x) ^ l * (1 - x) ^ (i + j - l)) * rvJ j k (l + k - i) x := by rw [hpow]
    _ = (1 - x) ^ (i + j - l) * (x ^ h * (1 - x) ^ l * rvJ j k (l + k - i) x) := by ring

private lemma rvInt_M2 (h i j k l : ℕ) (hl : 1 ≤ l) (hj : 1 ≤ j) (hlij : l ≤ i + j)
    (hjhl : j ≤ h + l) :
    rvInt h i j k l = rvInt i h l k j := by
  rw [rvInt_M1 h i j k l hl hlij]
  rw [rvInt_M2y k j i h l (by omega) (by omega)]
  exact rvInt_M1 k l h i j hj (by omega)

private lemma beta_integral (a b : ℕ) :
    ∫ y in (0 : ℝ)..1, y ^ a * (1 - y) ^ b = ((a ! * b ! : ℕ) : ℝ) / (((a + b + 1)! : ℕ) : ℝ) := by
  induction b generalizing a with
  | zero =>
    simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.add_zero]
    rw [integral_pow]
    simp only [one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero, Nat.factorial_succ]
    push_cast
    have ha : (a ! : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero a)
    field_simp [ha]
  | succ b ih =>
    let u : ℝ → ℝ := fun y => (1 - y) ^ (b + 1)
    let u' : ℝ → ℝ := fun y => -((b + 1 : ℕ) : ℝ) * (1 - y) ^ b
    let v : ℝ → ℝ := fun y => y ^ (a + 1) / ((a + 1 : ℕ) : ℝ)
    let v' : ℝ → ℝ := fun y => y ^ a
    have hu : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt u (u' y) y := by
      intro y _
      have h1 : HasDerivAt (fun t : ℝ => 1 - t) (-1) y := by
        simpa using (hasDerivAt_const y (1 : ℝ)).fun_sub (hasDerivAt_id' y)
      exact (h1.fun_pow (b + 1)).congr_deriv (by dsimp [u']; push_cast; ring)
    have hv : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt v (v' y) y := by
      intro y _
      have ha1 : ((a + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      exact ((hasDerivAt_pow (a + 1) y).div_const _).congr_deriv (by
        dsimp [v']; field_simp [ha1])
    have hibp := integral_mul_deriv_eq_deriv_mul hu hv
      ((by fun_prop : Continuous u').intervalIntegrable 0 1)
      ((by fun_prop : Continuous v').intervalIntegrable 0 1)
    have hbnd0 : u 0 * v 0 = 0 := by simp [u, v]
    have hbnd1 : u 1 * v 1 = 0 := by simp [u, v]
    rw [hbnd1, hbnd0, sub_self] at hibp
    have hstep : ∫ y in (0 : ℝ)..1, y ^ a * (1 - y) ^ (b + 1) =
        ((b + 1 : ℕ) : ℝ) / ((a + 1 : ℕ) : ℝ) * ∫ y in (0 : ℝ)..1, y ^ (a + 1) * (1 - y) ^ b := by
      have hl : ∫ y in (0 : ℝ)..1, u y * v' y = ∫ y in (0 : ℝ)..1, y ^ a * (1 - y) ^ (b + 1) := by
        refine intervalIntegral.integral_congr fun y _ => by dsimp [u, v']; ring
      have hr : ∫ y in (0 : ℝ)..1, u' y * v y =
          -(((b + 1 : ℕ) : ℝ) / ((a + 1 : ℕ) : ℝ) *
            ∫ y in (0 : ℝ)..1, y ^ (a + 1) * (1 - y) ^ b) := by
        rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
        refine intervalIntegral.integral_congr fun y _ => by dsimp [u', v]; ring
      linarith
    rw [hstep, ih (a + 1)]
    have hsum : a + 1 + b + 1 = a + (b + 1) + 1 := by omega
    rw [hsum, Nat.factorial_succ a, Nat.factorial_succ b]
    push_cast
    have ha1 : ((a + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hden : (((a + (b + 1) + 1)! : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    field_simp [ha1, hden]

private lemma hasSum_choose_pow (m : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    HasSum (fun r : ℕ => ((r + m).choose m : ℝ) * t ^ r) (1 / (1 - t) ^ (m + 1)) := by
  induction m with
  | zero =>
    simpa [one_div] using hasSum_geometric_of_lt_one ht0 ht1
  | succ m ih =>
    have h1t : 0 < 1 - t := sub_pos.2 ht1
    have hpart : ∀ N : ℕ,
        (1 - t) * ∑ r ∈ range N, ((r + (m + 1)).choose (m + 1) : ℝ) * t ^ r =
          (∑ r ∈ range N, ((r + m).choose m : ℝ) * t ^ r) -
            ((N + m).choose (m + 1) : ℝ) * t ^ N := by
      intro N
      induction N with
      | zero =>
        simp
      | succ N ihN =>
        rw [Finset.sum_range_succ, mul_add, ihN, Finset.sum_range_succ]
        have hch : (N + 1 + m).choose (m + 1) = (N + m).choose m + (N + m).choose (m + 1) := by
          have : N + 1 + m = (N + m) + 1 := by omega
          rw [this, Nat.choose_succ_succ]
        have hch' : (N + (m + 1)).choose (m + 1) = (N + 1 + m).choose (m + 1) := by
          congr 1; omega
        rw [hch', hch]
        push_cast
        rw [pow_succ]
        ring
    have hrem : Tendsto (fun N : ℕ => ((N + m).choose (m + 1) : ℝ) * t ^ N) atTop (𝓝 0) := by
      refine squeeze_zero (g := fun N : ℕ => ((N + m : ℕ) : ℝ) ^ (m + 1) * t ^ N)
        (fun N => by positivity) ?_ ?_
      · intro N
        gcongr
        exact_mod_cast Nat.choose_le_pow (N + m) (m + 1)
      · by_cases ht : t = 0
        · subst ht
          refine tendsto_atTop_of_eventually_const (i₀ := 1) fun N hN => ?_
          simp [show N ≠ 0 by omega]
        · have h1 := (tendsto_pow_const_mul_const_pow_of_lt_one (m + 1) ht0 ht1).comp
            (tendsto_add_atTop_nat m)
          have h2 : (fun N : ℕ => ((N + m : ℕ) : ℝ) ^ (m + 1) * t ^ N) =
              fun N : ℕ => (((N + m : ℕ) : ℝ) ^ (m + 1) * t ^ (N + m)) * (t ^ m)⁻¹ := by
            ext N
            have htm : t ^ (N + m) * (t ^ m)⁻¹ = t ^ N := by
              rw [pow_add, mul_inv_cancel_right₀ (pow_ne_zero m ht)]
            rw [mul_assoc, htm]
          rw [h2]
          simpa using h1.mul_const (t ^ m)⁻¹
    have hih_lim : Tendsto (fun N : ℕ => ∑ r ∈ range N, ((r + m).choose m : ℝ) * t ^ r)
        atTop (𝓝 (1 / (1 - t) ^ (m + 1))) :=
      (hasSum_iff_tendsto_nat_of_nonneg (fun r => by positivity) _).1 ih
    have hlim : Tendsto (fun N : ℕ => ∑ r ∈ range N, ((r + (m + 1)).choose (m + 1) : ℝ) * t ^ r)
        atTop (𝓝 (1 / (1 - t) ^ (m + 2))) := by
      have hdiv : (fun N : ℕ => ∑ r ∈ range N, ((r + (m + 1)).choose (m + 1) : ℝ) * t ^ r) =
          fun N : ℕ => (1 - t)⁻¹ * ((∑ r ∈ range N, ((r + m).choose m : ℝ) * t ^ r) -
            ((N + m).choose (m + 1) : ℝ) * t ^ N) := by
        ext N
        rw [← hpart N, inv_mul_cancel_left₀ h1t.ne']
      rw [hdiv]
      have hlim' := (hih_lim.sub hrem).const_mul (1 - t)⁻¹
      have htarget : (1 - t)⁻¹ * (1 / (1 - t) ^ (m + 1) - 0) = 1 / (1 - t) ^ (m + 2) := by
        rw [sub_zero, one_div, ← mul_inv, ← pow_succ', show m + 1 + 1 = m + 2 by omega, one_div]
      rwa [htarget] at hlim'
    exact (hasSum_iff_tendsto_nat_of_nonneg (fun r => by positivity) _).2 hlim

private lemma hasSum_rvJ (k j m : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum
      (fun r : ℕ => ((r + m).choose m : ℝ) * (((k + r)! * j ! : ℕ) : ℝ) /
        (((k + r + j + 1)! : ℕ) : ℝ) * x ^ r)
      (rvJ k j m x) := by
  unfold rvJ
  have hF : ∀ r : ℕ,
      ∫ y in (0 : ℝ)..1, ((r + m).choose m : ℝ) * x ^ r * (y ^ (k + r) * (1 - y) ^ j) =
        ((r + m).choose m : ℝ) * (((k + r)! * j ! : ℕ) : ℝ) /
          (((k + r + j + 1)! : ℕ) : ℝ) * x ^ r := by
    intro r
    rw [intervalIntegral.integral_const_mul, beta_integral (k + r) j]
    ring
  simp_rw [← hF]
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun r _ => ((r + m).choose m : ℝ) * x ^ r)
    (fun r => (by fun_prop : Continuous fun y : ℝ =>
      ((r + m).choose m : ℝ) * x ^ r * (y ^ (k + r) * (1 - y) ^ j)).aestronglyMeasurable)
    ?_ ?_ ?_ ?_
  · intro r
    filter_upwards with y hy
    rw [Set.uIoc_of_le zero_le_one] at hy
    have hy0 : 0 ≤ y := hy.1.le
    have h1y : 0 ≤ 1 - y := sub_nonneg.2 hy.2
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : y ^ (k + r) ≤ 1 := pow_le_one₀ hy0 hy.2
    have h2 : (1 - y) ^ j ≤ 1 := pow_le_one₀ h1y (by linarith [hy.1])
    calc ((r + m).choose m : ℝ) * x ^ r * (y ^ (k + r) * (1 - y) ^ j)
        ≤ ((r + m).choose m : ℝ) * x ^ r * (1 * 1) := by gcongr
      _ = ((r + m).choose m : ℝ) * x ^ r := by ring
  · filter_upwards with _ _
    exact (hasSum_choose_pow m hx0 hx1).summable
  · exact intervalIntegrable_const
  · filter_upwards with y hy
    rw [Set.uIoc_of_le zero_le_one] at hy
    have hxy0 : 0 ≤ x * y := mul_nonneg hx0 hy.1.le
    have hxy1 : x * y < 1 := by nlinarith [hy.1, hy.2]
    have hsum := (hasSum_choose_pow m hxy0 hxy1).mul_left (y ^ k * (1 - y) ^ j)
    have hfun : (fun r : ℕ => ((r + m).choose m : ℝ) * x ^ r * (y ^ (k + r) * (1 - y) ^ j)) =
        fun r : ℕ => (y ^ k * (1 - y) ^ j) * (((r + m).choose m : ℝ) * (x * y) ^ r) := by
      ext r; rw [mul_pow, pow_add]; ring
    rw [hfun, ← mul_one_div]
    exact hsum

private lemma rvJ_symm (k j m : ℕ) (hmkj : m ≤ k + j) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ((m ! * (k + j - m)! : ℕ) : ℝ) * rvJ k j m x =
      ((k ! * j ! : ℕ) : ℝ) * rvJ m (k + j - m) k x := by
  have h1 := (hasSum_rvJ k j m hx0 hx1).mul_left ((m ! * (k + j - m)! : ℕ) : ℝ)
  have h2 := (hasSum_rvJ m (k + j - m) k hx0 hx1).mul_left ((k ! * j ! : ℕ) : ℝ)
  have hfun :
      (fun r : ℕ => ((m ! * (k + j - m)! : ℕ) : ℝ) *
        (((r + m).choose m : ℝ) * (((k + r)! * j ! : ℕ) : ℝ) /
          (((k + r + j + 1)! : ℕ) : ℝ) * x ^ r)) =
      (fun r : ℕ => ((k ! * j ! : ℕ) : ℝ) *
        (((r + k).choose k : ℝ) * (((m + r)! * (k + j - m)! : ℕ) : ℝ) /
          (((m + r + (k + j - m) + 1)! : ℕ) : ℝ) * x ^ r)) := by
    ext r
    have hden_eq : k + r + j + 1 = m + r + (k + j - m) + 1 := by omega
    rw [hden_eq]
    have hch1 : ((r + m).choose m : ℝ) * (m ! : ℝ) * (r ! : ℝ) = ((r + m)! : ℝ) := by
      have := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left m r)
      rw [Nat.add_sub_cancel] at this
      exact_mod_cast this
    have hch2 : ((r + k).choose k : ℝ) * (k ! : ℝ) * (r ! : ℝ) = ((r + k)! : ℝ) := by
      have := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left k r)
      rw [Nat.add_sub_cancel] at this
      exact_mod_cast this
    have hr : (r ! : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero r)
    have h1' : ((r + m).choose m : ℝ) * (m ! : ℝ) = ((m + r)! : ℝ) / (r ! : ℝ) := by
      rw [add_comm m r, ← hch1, mul_div_cancel_right₀ _ hr]
    have h2' : ((r + k).choose k : ℝ) * (k ! : ℝ) = ((k + r)! : ℝ) / (r ! : ℝ) := by
      rw [add_comm k r, ← hch2, mul_div_cancel_right₀ _ hr]
    push_cast
    calc ((m ! : ℝ) * ((k + j - m)! : ℝ)) *
          (((r + m).choose m : ℝ) * (((k + r)! : ℝ) * (j ! : ℝ)) /
            (((m + r + (k + j - m) + 1)! : ℝ)) * x ^ r)
        = (((r + m).choose m : ℝ) * (m ! : ℝ)) *
            (((k + j - m)! : ℝ) * ((k + r)! : ℝ) * (j ! : ℝ)) /
            (((m + r + (k + j - m) + 1)! : ℝ)) * x ^ r := by ring
      _ = (((m + r)! : ℝ) / (r ! : ℝ)) *
            (((k + j - m)! : ℝ) * ((k + r)! : ℝ) * (j ! : ℝ)) /
            (((m + r + (k + j - m) + 1)! : ℝ)) * x ^ r := by rw [h1']
      _ = (((k + r)! : ℝ) / (r ! : ℝ)) *
            (((m + r)! : ℝ) * ((k + j - m)! : ℝ) * (j ! : ℝ)) /
            (((m + r + (k + j - m) + 1)! : ℝ)) * x ^ r := by ring
      _ = (((r + k).choose k : ℝ) * (k ! : ℝ)) *
            (((m + r)! : ℝ) * ((k + j - m)! : ℝ) * (j ! : ℝ)) /
            (((m + r + (k + j - m) + 1)! : ℝ)) * x ^ r := by rw [← h2']
      _ = ((k ! : ℝ) * (j ! : ℝ)) *
            (((r + k).choose k : ℝ) * (((m + r)! : ℝ) * ((k + j - m)! : ℝ)) /
              (((m + r + (k + j - m) + 1)! : ℝ)) * x ^ r) := by ring
  rw [hfun] at h1
  exact h1.unique h2

private lemma rvInt_M3y (h i j k l : ℕ) (hlij : l ≤ i + j) (hilk : i ≤ k + l) :
    (((i + j - l)! * (k + l - i)! : ℕ) : ℝ) * rvInt h i j k l =
      ((k ! * j ! : ℕ) : ℝ) * rvInt h l (i + j - l) (k + l - i) i := by
  rw [rvInt_eq_J, rvInt_eq_J]
  have hsub : l + (i + j - l) - i = j := by omega
  rw [hsub]
  simp_rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le zero_le_one]
  have hμ : volume.restrict (Set.Ioc (0 : ℝ) 1) = volume.restrict (Set.Ioo (0 : ℝ) 1) :=
    Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc.symm
  rw [hμ]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  have h1x_ne : 1 - x ≠ 0 := (sub_pos.2 hx.2).ne'
  set m := i + j - l
  have hmkj : m ≤ k + j := by omega
  have hk' : k + j - m = k + l - i := by omega
  have hsym := rvJ_symm k j m hmkj hx.1.le hx.2
  have hpf := rvJ_pfaff m (k + j - m) k (by omega) hx.1.le hx.2
  have hpf_exp : m + (k + j - m) - k = j := by omega
  rw [hpf_exp, hk'] at hpf
  rw [hk'] at hsym
  have hpow : (1 - x) ^ i * (1 - x) ^ (k + l - i) = (1 - x) ^ k * (1 - x) ^ l := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  apply mul_left_cancel₀ (pow_ne_zero k h1x_ne)
  calc (1 - x) ^ k * (((m ! * (k + l - i)! : ℕ) : ℝ) * (x ^ h * (1 - x) ^ i * rvJ k j m x))
      = x ^ h * (1 - x) ^ i * (1 - x) ^ k * (((m ! * (k + l - i)! : ℕ) : ℝ) * rvJ k j m x) := by ring
    _ = x ^ h * (1 - x) ^ i * (1 - x) ^ k * (((k ! * j ! : ℕ) : ℝ) * rvJ m (k + l - i) k x) := by rw [hsym]
    _ = x ^ h * (1 - x) ^ i * ((k ! * j ! : ℕ) : ℝ) * ((1 - x) ^ k * rvJ m (k + l - i) k x) := by ring
    _ = x ^ h * (1 - x) ^ i * ((k ! * j ! : ℕ) : ℝ) *
          ((1 - x) ^ (k + l - i) * rvJ (k + l - i) m j x) := by rw [hpf]
    _ = x ^ h * ((k ! * j ! : ℕ) : ℝ) * ((1 - x) ^ i * (1 - x) ^ (k + l - i)) *
          rvJ (k + l - i) m j x := by ring
    _ = x ^ h * ((k ! * j ! : ℕ) : ℝ) * ((1 - x) ^ k * (1 - x) ^ l) *
          rvJ (k + l - i) m j x := by rw [hpow]
    _ = (1 - x) ^ k * (((k ! * j ! : ℕ) : ℝ) * (x ^ h * (1 - x) ^ l * rvJ (k + l - i) m j x)) := by ring

private lemma rvInt_M3 (h i j k l : ℕ) (hl : 1 ≤ l) (hj : 1 ≤ j) (hlij : l ≤ i + j)
    (hjhl : j ≤ h + l) :
    (((h + l - j)! * (i + j - l)! : ℕ) : ℝ) * rvInt h i j k l =
      ((h ! * i ! : ℕ) : ℝ) * rvInt (h + l - j) (i + j - l) l k j := by
  rw [rvInt_M1 h i j k l hl hlij]
  have h1 := rvInt_M3y k j i h l (by omega) (by omega)
  have hmul : (j + i - l)! * (h + l - j)! = (h + l - j)! * (i + j - l)! := by
    rw [mul_comm, add_comm j i]
  have hadd : j + i - l = i + j - l := by omega
  rw [hmul, hadd] at h1
  rw [h1, rvInt_M1 k l (i + j - l) (h + l - j) j hj (by omega)]

/- ### Section 2: General Direct Integration-by-Parts and Linear Form -/

private def rvPoly (h i m : ℕ) (x : ℝ) : ℝ :=
  ∑ a ∈ range (i + 1),
    ((-1 : ℝ) ^ a * (i.choose a : ℝ) * ((h + a).choose m : ℝ)) * x ^ (h + a - m)

private def rvDeriv (h i r : ℕ) (x : ℝ) : ℝ :=
  ∑ a ∈ range (i + 1),
    ((-1 : ℝ) ^ a * (i.choose a : ℝ) * ((h + a).descFactorial r : ℝ)) * x ^ (h + a - r)

private lemma rvDeriv_zero (h i : ℕ) (x : ℝ) :
    rvDeriv h i 0 x = x ^ h * (1 - x) ^ i := by
  unfold rvDeriv
  have hbin : (1 - x) ^ i = ∑ a ∈ range (i + 1), (-1 : ℝ) ^ a * (i.choose a : ℝ) * x ^ a := by
    rw [sub_eq_add_neg, add_comm, add_pow]
    refine sum_congr rfl fun a _ => ?_
    rw [neg_eq_neg_one_mul, mul_pow, one_pow, mul_one]; ring
  rw [hbin, mul_sum]
  refine sum_congr rfl fun a _ => ?_
  simp only [Nat.descFactorial_zero, Nat.cast_one, mul_one, Nat.sub_zero, pow_add]; ring

private lemma rvDeriv_self (h i m : ℕ) (x : ℝ) :
    rvDeriv h i m x = (m ! : ℝ) * rvPoly h i m x := by
  unfold rvDeriv rvPoly
  rw [mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  push_cast; ring

private lemma hasDerivAt_rvDeriv (h i r : ℕ) (_hrh : r < h) (x : ℝ) :
    HasDerivAt (rvDeriv h i r) (rvDeriv h i (r + 1) x) x := by
  unfold rvDeriv
  refine HasDerivAt.fun_sum fun a _ => ?_
  have hpow := (hasDerivAt_pow (h + a - r) x).const_mul
    ((-1 : ℝ) ^ a * (i.choose a : ℝ) * ((h + a).descFactorial r : ℝ))
  refine hpow.congr_deriv ?_
  have hsub : h + a - r - 1 = h + a - (r + 1) := by omega
  have hdesc : (h + a).descFactorial (r + 1) = (h + a - r) * (h + a).descFactorial r :=
    Nat.descFactorial_succ (h + a) r
  rw [hsub, hdesc]; push_cast; ring

private lemma rvDeriv_eval_zero (h i r : ℕ) (hrh : r < h) :
    rvDeriv h i r 0 = 0 := by
  unfold rvDeriv
  refine sum_eq_zero fun a _ => ?_
  rw [zero_pow (by omega : h + a - r ≠ 0), mul_zero]

private lemma rvDeriv_symm (h i r : ℕ) (hrh : r ≤ h) (hri : r ≤ i) (x : ℝ) :
    rvDeriv h i r (1 - x) = (-1 : ℝ) ^ r * rvDeriv i h r x := by
  induction r generalizing x with
  | zero =>
    simp only [pow_zero, one_mul, rvDeriv_zero, sub_sub_cancel]; ring
  | succ r ih =>
    have hfun : (fun t : ℝ => rvDeriv h i r (1 - t)) =
        (fun t : ℝ => (-1 : ℝ) ^ r * rvDeriv i h r t) :=
      funext fun t => ih (by omega) (by omega) t
    have h1 : HasDerivAt (fun t : ℝ => rvDeriv h i r (1 - t))
        (rvDeriv h i (r + 1) (1 - x) * (-1)) x := by
      have hsub : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
        simpa using (hasDerivAt_const x (1 : ℝ)).fun_sub (hasDerivAt_id' x)
      exact (hasDerivAt_rvDeriv h i r (by omega) (1 - x)).comp x hsub
    have h2 : HasDerivAt (fun t : ℝ => (-1 : ℝ) ^ r * rvDeriv i h r t)
        ((-1 : ℝ) ^ r * rvDeriv i h (r + 1) x) x :=
      (hasDerivAt_rvDeriv i h r (by omega) x).const_mul _
    rw [hfun] at h1
    have heq := h1.unique h2
    rw [pow_succ]; linarith

private lemma rvDeriv_eval_one (h i r : ℕ) (hrh : r < h) (hri : r < i) :
    rvDeriv h i r 1 = 0 := by
  have h1 := rvDeriv_symm h i r hrh.le hri.le 0
  simp only [sub_zero, rvDeriv_eval_zero i h r hri, mul_zero] at h1
  exact h1

private lemma continuous_rvDeriv (h i r : ℕ) : Continuous (rvDeriv h i r) := by
  unfold rvDeriv; fun_prop

private lemma rv_ibp (h i m : ℕ) (hmh : m ≤ h) (hmi : m ≤ i) {y : ℝ}
    (hy0 : 0 ≤ y) (hy1 : y < 1) :
    (-1 : ℝ) ^ m * ∫ x in (0 : ℝ)..1, rvPoly h i m x / (1 - x * y) =
      ∫ x in (0 : ℝ)..1, x ^ h * (1 - x) ^ i * y ^ m / (1 - x * y) ^ (m + 1) := by
  have hden : ∀ x ∈ Set.uIcc (0 : ℝ) 1, 1 - x * y ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    nlinarith [hx.1, hx.2]
  have hstep : ∀ t ≤ m,
      ∫ x in (0 : ℝ)..1, rvDeriv h i m x / (1 - x * y) =
        (-1 : ℝ) ^ t * ∫ x in (0 : ℝ)..1,
          rvDeriv h i (m - t) x * ((t ! : ℝ) * y ^ t / (1 - x * y) ^ (t + 1)) := by
    intro t ht
    induction t with
    | zero => simp [div_eq_mul_inv]
    | succ t ih =>
      rw [ih (by omega)]
      set r := m - (t + 1)
      have hr_lt : r < m := by omega
      have hmt : m - t = r + 1 := by omega
      let u : ℝ → ℝ := rvDeriv h i r
      let u' : ℝ → ℝ := rvDeriv h i (r + 1)
      let v : ℝ → ℝ := fun x => (t ! : ℝ) * y ^ t / (1 - x * y) ^ (t + 1)
      let v' : ℝ → ℝ := fun x => ((t + 1)! : ℝ) * y ^ (t + 1) / (1 - x * y) ^ (t + 2)
      have hu : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt u (u' x) x :=
        fun x _ => hasDerivAt_rvDeriv h i r (by omega) x
      have hv : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt v (v' x) x := by
        intro x hx
        have hne : 1 - x * y ≠ 0 := hden x hx
        have hlin : HasDerivAt (fun z : ℝ => 1 - z * y) (-y) x := by
          have := (hasDerivAt_id' x).mul_const y
          exact ((hasDerivAt_const x (1 : ℝ)).fun_sub this).congr_deriv (by ring)
        have hpow : HasDerivAt (fun z : ℝ => (1 - z * y) ^ (t + 1))
            ((t + 1 : ℕ) * (1 - x * y) ^ t * (-y)) x :=
          (hlin.fun_pow (t + 1)).congr_deriv (by simp)
        have hinv := (hpow.fun_inv (pow_ne_zero _ hne)).const_mul ((t ! : ℝ) * y ^ t)
        have hv_eq : v = fun z : ℝ => (t ! : ℝ) * y ^ t * ((1 - z * y) ^ (t + 1))⁻¹ := by
          ext z; simp [v, div_eq_mul_inv]
        rw [hv_eq]
        refine hinv.congr_deriv ?_
        dsimp only [v']
        rw [Nat.factorial_succ]; push_cast
        have hpow1 : ((1 - x * y) ^ (t + 1)) ^ 2 = (1 - x * y) ^ t * (1 - x * y) ^ (t + 2) := by
          rw [← pow_mul, ← pow_add]; congr 1; omega
        rw [hpow1]
        field_simp [hne, pow_ne_zero t hne, pow_ne_zero (t + 2) hne]; ring
      have hv'int : IntervalIntegrable v' volume 0 1 := by
        refine ContinuousOn.intervalIntegrable fun x hx => ?_
        have hne : 1 - x * y ≠ 0 := hden x hx
        exact (ContinuousAt.div continuousAt_const
          ((continuousAt_const.sub (continuousAt_id.mul continuousAt_const)).pow _)
          (pow_ne_zero _ hne)).continuousWithinAt
      have hibp := integral_mul_deriv_eq_deriv_mul hu hv
        ((continuous_rvDeriv h i (r + 1)).intervalIntegrable 0 1) hv'int
      have hu0 : u 0 = 0 := rvDeriv_eval_zero h i r (by omega)
      have hu1 : u 1 = 0 := rvDeriv_eval_one h i r (by omega) (by omega)
      rw [hu0, hu1, zero_mul, zero_mul, sub_self] at hibp
      have hswap : ∫ x in (0 : ℝ)..1, u' x * v x = -(∫ x in (0 : ℝ)..1, u x * v' x) := by linarith
      rw [hmt]
      change (-1 : ℝ) ^ t * ∫ x in (0 : ℝ)..1, u' x * v x =
        (-1 : ℝ) ^ (t + 1) * ∫ x in (0 : ℝ)..1, u x * v' x
      rw [hswap, pow_succ]; ring
  have hfinal := hstep m le_rfl
  rw [Nat.sub_self] at hfinal
  simp_rw [rvDeriv_zero] at hfinal
  simp_rw [rvDeriv_self] at hfinal
  have hfac : (m ! : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)
  have hlhs : ∫ x in (0 : ℝ)..1, (m ! : ℝ) * rvPoly h i m x / (1 - x * y) =
      (m ! : ℝ) * ∫ x in (0 : ℝ)..1, rvPoly h i m x / (1 - x * y) := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; ext x; ring
  have hrhs : ∫ x in (0 : ℝ)..1,
      x ^ h * (1 - x) ^ i * ((m ! : ℝ) * y ^ m / (1 - x * y) ^ (m + 1)) =
      (m ! : ℝ) * ∫ x in (0 : ℝ)..1,
        x ^ h * (1 - x) ^ i * y ^ m / (1 - x * y) ^ (m + 1) := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; ext x; ring
  rw [hlhs, hrhs] at hfinal
  have hcancel : ∫ x in (0 : ℝ)..1, rvPoly h i m x / (1 - x * y) =
      (-1 : ℝ) ^ m * ∫ x in (0 : ℝ)..1,
        x ^ h * (1 - x) ^ i * y ^ m / (1 - x * y) ^ (m + 1) := by
    apply mul_left_cancel₀ hfac; linarith
  have hneg2 : (-1 : ℝ) ^ (2 * m) = 1 := by rw [pow_mul]; norm_num
  rw [hcancel, ← mul_assoc, ← pow_add, ← two_mul, hneg2, one_mul]

private lemma intervalIntegrable_monomial_div (r : ℕ) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    IntervalIntegrable (fun x : ℝ => x ^ r / (1 - x * y)) volume 0 1 := by
  refine ContinuousOn.intervalIntegrable fun x hx => ?_
  rw [Set.uIcc_of_le zero_le_one] at hx
  have hne : 1 - x * y ≠ 0 := by nlinarith [hx.1, hx.2]
  exact (ContinuousAt.div (continuousAt_id.pow r)
    (continuousAt_const.sub (continuousAt_id.mul continuousAt_const)) hne).continuousWithinAt

private lemma continuousOn_integral_monomial (r : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ContinuousOn (fun y : ℝ => ∫ x in (0 : ℝ)..1, x ^ r / (1 - x * y)) (Set.Icc 0 t) := by
  intro y hy
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have h1t : 0 < 1 - t := sub_pos.2 ht1
  have h1t2 : 0 < (1 - t) ^ 2 := sq_pos_of_pos h1t
  set δ := (1 - t) ^ 2 * ε / 2
  refine ⟨δ, by positivity, fun y' hy' hdist => ?_⟩
  rw [Real.dist_eq] at hdist ⊢
  rw [← intervalIntegral.integral_sub
    (intervalIntegrable_monomial_div r hy'.1 (hy'.2.trans_lt ht1))
    (intervalIntegrable_monomial_div r hy.1 (hy.2.trans_lt ht1))]
  have hbd : ∀ x ∈ Set.uIoc (0 : ℝ) 1,
      ‖x ^ r / (1 - x * y') - x ^ r / (1 - x * y)‖ ≤ |y' - y| / (1 - t) ^ 2 := by
    intro x hx
    rw [Set.uIoc_of_le zero_le_one] at hx
    have h1 : 1 - t ≤ 1 - x * y' := by nlinarith [hx.1, hx.2, hy'.1, hy'.2]
    have h2 : 1 - t ≤ 1 - x * y := by nlinarith [hx.1, hx.2, hy.1, hy.2]
    have hp1 : 0 < 1 - x * y' := by linarith
    have hp2 : 0 < 1 - x * y := by linarith
    have hdiff : x ^ r / (1 - x * y') - x ^ r / (1 - x * y) =
        x ^ (r + 1) * (y' - y) / ((1 - x * y') * (1 - x * y)) := by
      field_simp [hp1.ne', hp2.ne']; rw [pow_succ]; ring
    rw [hdiff, Real.norm_eq_abs, abs_div, abs_mul,
        abs_of_nonneg (pow_nonneg hx.1.le _), abs_of_pos (mul_pos hp1 hp2)]
    have hxpow : x ^ (r + 1) ≤ 1 := pow_le_one₀ hx.1.le hx.2
    have hprod : (1 - t) ^ 2 ≤ (1 - x * y') * (1 - x * y) := by
      rw [sq]; exact mul_le_mul h1 h2 h1t.le hp1.le
    calc x ^ (r + 1) * |y' - y| / ((1 - x * y') * (1 - x * y))
        ≤ 1 * |y' - y| / (1 - t) ^ 2 := by gcongr
      _ = |y' - y| / (1 - t) ^ 2 := by ring
  calc |∫ x in (0 : ℝ)..1, (x ^ r / (1 - x * y') - x ^ r / (1 - x * y))|
      ≤ (|y' - y| / (1 - t) ^ 2) * |1 - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hbd
    _ = |y' - y| / (1 - t) ^ 2 := by norm_num
    _ < δ / (1 - t) ^ 2 := by gcongr
    _ = ε / 2 := by dsimp only [δ]; field_simp [h1t2.ne']
    _ < ε := by linarith

private lemma integral_monomial_geom (r : ℕ) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    HasSum (fun m : ℕ => y ^ m / ((m + r + 1 : ℕ) : ℝ))
      (∫ x in (0 : ℝ)..1, x ^ r / (1 - x * y)) := by
  have hF : ∀ m : ℕ, ∫ x in (0 : ℝ)..1, x ^ (m + r) * y ^ m = y ^ m / ((m + r + 1 : ℕ) : ℝ) := by
    intro m; rw [intervalIntegral.integral_mul_const, integral_pow]
    simp [div_eq_mul_inv, mul_comm]
  simp_rw [← hF]
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun m _ => y ^ m)
    (fun m => (by fun_prop : Continuous fun x : ℝ => x ^ (m + r) * y ^ m).aestronglyMeasurable)
    ?_ ?_ ?_ ?_
  · intro m
    filter_upwards with x hx
    rw [Set.uIoc_of_le zero_le_one] at hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hx.1.le _) (pow_nonneg hy0 _))]
    calc x ^ (m + r) * y ^ m ≤ 1 * y ^ m := by gcongr; exact pow_le_one₀ hx.1.le hx.2
      _ = y ^ m := one_mul _
  · filter_upwards with _ _; exact summable_geometric_of_lt_one hy0 hy1
  · exact intervalIntegrable_const
  · filter_upwards with x hx
    rw [Set.uIoc_of_le zero_le_one] at hx
    have hgeom := (hasSum_geometric_of_lt_one (mul_nonneg hx.1.le hy0)
      (by nlinarith [hx.1, hx.2])).mul_left (x ^ r)
    have hfun : (fun m : ℕ => x ^ (m + r) * y ^ m) = fun m : ℕ => x ^ r * (x * y) ^ m := by
      ext m; rw [mul_pow, pow_add]; ring
    rw [hfun, div_eq_mul_inv]; exact hgeom

private lemma double_integral_monomial_geom (r s : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    HasSum (fun m : ℕ => t ^ (m + s + 1) / (((m + r + 1 : ℕ) : ℝ) * ((m + s + 1 : ℕ) : ℝ)))
      (∫ y in (0 : ℝ)..t, (∫ x in (0 : ℝ)..1, x ^ r / (1 - x * y)) * y ^ s) := by
  have hF : ∀ m : ℕ,
      ∫ y in (0 : ℝ)..t, (y ^ m / ((m + r + 1 : ℕ) : ℝ)) * y ^ s =
        t ^ (m + s + 1) / (((m + r + 1 : ℕ) : ℝ) * ((m + s + 1 : ℕ) : ℝ)) := by
    intro m
    have hrew : (fun y : ℝ => (y ^ m / ((m + r + 1 : ℕ) : ℝ)) * y ^ s) =
        fun y : ℝ => ((m + r + 1 : ℕ) : ℝ)⁻¹ * y ^ (m + s) := by
      ext y; rw [pow_add]; ring
    rw [hrew, intervalIntegral.integral_const_mul, integral_pow]
    simp only [zero_pow (Nat.succ_ne_zero _), sub_zero]
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]; push_cast; ring
  simp_rw [← hF]
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun m _ => t ^ m)
    (fun m => (by fun_prop : Continuous fun y : ℝ =>
      (y ^ m / ((m + r + 1 : ℕ) : ℝ)) * y ^ s).aestronglyMeasurable)
    ?_ ?_ ?_ ?_
  · intro m
    filter_upwards with y hy
    rw [Set.uIoc_of_le ht0] at hy
    have hy0 : 0 ≤ y := hy.1.le
    have hden1 : (1 : ℝ) ≤ (m + r + 1 : ℕ) := by exact_mod_cast Nat.succ_pos (m + r)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc (y ^ m / ((m + r + 1 : ℕ) : ℝ)) * y ^ s
        ≤ (y ^ m / 1) * 1 := by gcongr; exact pow_le_one₀ hy0 (hy.2.trans ht1.le)
      _ = y ^ m := by ring
      _ ≤ t ^ m := pow_le_pow_left₀ hy0 hy.2 m
  · filter_upwards with _ _; exact summable_geometric_of_lt_one ht0 ht1
  · exact intervalIntegrable_const
  · filter_upwards with y hy
    rw [Set.uIoc_of_le ht0] at hy
    exact (integral_monomial_geom r hy.1.le (hy.2.trans_lt ht1)).mul_right (y ^ s)

private lemma hasSum_one_div_sq_shift :
    HasSum (fun m : ℕ => (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 2) (π ^ 2 / 6) := by
  have h := hasSum_zeta_two
  rw [← hasSum_nat_add_iff' 1] at h
  simp only [range_one, sum_singleton, Nat.cast_zero, zero_pow (by norm_num : 2 ≠ 0),
    div_zero, sub_zero] at h
  exact h

private lemma hasSum_shifted_diag (r : ℕ) :
    HasSum (fun m : ℕ => (1 : ℝ) / (((m + r + 1 : ℕ) : ℝ) * ((m + r + 1 : ℕ) : ℝ)))
      (π ^ 2 / 6 - ∑ k ∈ Icc 1 r, (1 : ℝ) / (k : ℝ) ^ 2) := by
  have h := hasSum_one_div_sq_shift
  rw [← hasSum_nat_add_iff' r] at h
  have hsum : ∑ i ∈ range r, (1 : ℝ) / ((i + 1 : ℕ) : ℝ) ^ 2 =
      ∑ k ∈ Icc 1 r, (1 : ℝ) / (k : ℝ) ^ 2 := by
    refine sum_bij (fun i _ => i + 1) ?_ ?_ ?_ ?_
    · intro i hi; simp only [mem_range, mem_Icc] at hi ⊢; omega
    · intro a _ b _ hab; omega
    · intro k hk; simp only [mem_Icc, mem_range] at hk ⊢; exact ⟨k - 1, by omega, by omega⟩
    · intro i _; rfl
  rw [hsum] at h
  simpa only [sq] using h

private lemma hasSum_shifted_offdiag {a b : ℕ} (hab : a < b) :
    HasSum (fun m : ℕ => (1 : ℝ) / (((m + a + 1 : ℕ) : ℝ) * ((m + b + 1 : ℕ) : ℝ)))
      ((1 : ℝ) / ((b - a : ℕ) : ℝ) * ∑ k ∈ Icc (a + 1) b, (1 : ℝ) / (k : ℝ)) := by
  set d := b - a
  have hb : b = a + d := by omega
  have hpartial : ∀ N : ℕ,
      ∑ m ∈ range N, (1 : ℝ) / (((m + a + 1 : ℕ) : ℝ) * ((m + b + 1 : ℕ) : ℝ)) =
      (1 : ℝ) / (d : ℝ) *
        ((∑ k ∈ Icc (a + 1) b, (1 : ℝ) / (k : ℝ)) -
          (∑ k ∈ Icc (N + a + 1) (N + b), (1 : ℝ) / (k : ℝ))) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have hterm : (1 : ℝ) / (((N + a + 1 : ℕ) : ℝ) * ((N + b + 1 : ℕ) : ℝ)) =
          (1 : ℝ) / (d : ℝ) * ((1 : ℝ) / ((N + a + 1 : ℕ) : ℝ) -
            (1 : ℝ) / ((N + b + 1 : ℕ) : ℝ)) := by
        have h1 : ((N + a + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        have h2 : ((N + b + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        have h3 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
        have hdiff : ((N + b + 1 : ℕ) : ℝ) - ((N + a + 1 : ℕ) : ℝ) = (d : ℝ) := by
          rw [hb]; push_cast; ring
        field_simp [h1, h2, h3]; linarith
      have hshift :
          ∑ k ∈ Icc (N + 1 + a + 1) (N + 1 + b), (1 : ℝ) / (k : ℝ) =
          (∑ k ∈ Icc (N + a + 1) (N + b), (1 : ℝ) / (k : ℝ)) -
            (1 : ℝ) / ((N + a + 1 : ℕ) : ℝ) + (1 : ℝ) / ((N + b + 1 : ℕ) : ℝ) := by
        have hleft : Icc (N + a + 1) (N + b + 1) =
            insert (N + a + 1) (Icc (N + 1 + a + 1) (N + 1 + b)) := by
          ext k; simp only [mem_Icc, mem_insert]; omega
        have hright : Icc (N + a + 1) (N + b + 1) =
            insert (N + b + 1) (Icc (N + a + 1) (N + b)) := by
          ext k; simp only [mem_Icc, mem_insert]; omega
        have h1 := congrArg (fun S : Finset ℕ => ∑ k ∈ S, (1 : ℝ) / (k : ℝ)) hleft
        have h2 := congrArg (fun S : Finset ℕ => ∑ k ∈ S, (1 : ℝ) / (k : ℝ)) hright
        rw [sum_insert (by simp only [mem_Icc]; omega)] at h1
        rw [sum_insert (by simp only [mem_Icc]; omega)] at h2
        linarith
      rw [hterm, hshift]; ring
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun m => by positivity)]
  simp_rw [hpartial]
  have htail : Tendsto (fun N : ℕ => ∑ k ∈ Icc (N + a + 1) (N + b), (1 : ℝ) / (k : ℝ))
      atTop (𝓝 0) := by
    refine squeeze_zero (g := fun N : ℕ => (d : ℝ) / ((N + 1 : ℕ) : ℝ))
      (fun N => sum_nonneg fun k _ => by positivity) ?_ ?_
    · intro N
      calc ∑ k ∈ Icc (N + a + 1) (N + b), (1 : ℝ) / (k : ℝ)
          ≤ ∑ _k ∈ Icc (N + a + 1) (N + b), (1 : ℝ) / ((N + 1 : ℕ) : ℝ) := by
            refine sum_le_sum fun k hk => ?_
            have hk1 : (N + 1 : ℕ) ≤ k := by simp only [mem_Icc] at hk; omega
            gcongr
        _ = (d : ℝ) / ((N + 1 : ℕ) : ℝ) := by
            rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
            rw [show N + b + 1 - (N + a + 1) = d by omega, mul_one_div]
    · simpa [div_eq_mul_inv] using
        (tendsto_const_nhds (x := (d : ℝ))).mul
          ((tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).inv_tendsto_atTop)
  simpa [sub_zero] using
    ((tendsto_const_nhds (x := ∑ k ∈ Icc (a + 1) b, (1 : ℝ) / (k : ℝ))).sub htail).const_mul
      ((1 : ℝ) / (d : ℝ))

private noncomputable def beukersTerm (r s : ℕ) : ℝ :=
  if r = s then π ^ 2 / 6 - ∑ k ∈ Icc 1 r, (1 : ℝ) / (k : ℝ) ^ 2
  else (1 : ℝ) / ((max r s - min r s : ℕ) : ℝ) *
    ∑ k ∈ Icc (min r s + 1) (max r s), (1 : ℝ) / (k : ℝ)

private lemma hasSum_beukersTerm (r s : ℕ) :
    HasSum (fun m : ℕ => (1 : ℝ) / (((m + r + 1 : ℕ) : ℝ) * ((m + s + 1 : ℕ) : ℝ)))
      (beukersTerm r s) := by
  unfold beukersTerm
  rcases lt_trichotomy r s with hlt | rfl | hgt
  · rw [if_neg hlt.ne, max_eq_right hlt.le, min_eq_left hlt.le]; exact hasSum_shifted_offdiag hlt
  · rw [if_pos rfl]; exact hasSum_shifted_diag r
  · rw [if_neg hgt.ne', max_eq_left hgt.le, min_eq_right hgt.le]
    simpa [mul_comm] using hasSum_shifted_offdiag hgt

private lemma tendsto_double_integral_monomial (r s : ℕ) :
    Tendsto
      (fun t : ℝ => ∫ y in (0 : ℝ)..t, (∫ x in (0 : ℝ)..1, x ^ r / (1 - x * y)) * y ^ s)
      (𝓝[<] 1) (𝓝 (beukersTerm r s)) := by
  have hev : ∀ᶠ t : ℝ in 𝓝[<] 1,
      ∫ y in (0 : ℝ)..t, (∫ x in (0 : ℝ)..1, x ^ r / (1 - x * y)) * y ^ s =
        ∑' m : ℕ, t ^ (m + s + 1) / (((m + r + 1 : ℕ) : ℝ) * ((m + s + 1 : ℕ) : ℝ)) := by
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with t ht
    exact (double_integral_monomial_geom r s ht.1.le ht.2).tsum_eq.symm
  rw [tendsto_congr' hev, ← (hasSum_beukersTerm r s).tsum_eq]
  refine tendsto_tsum_of_dominated_convergence (bound := fun m : ℕ => (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 2)
    hasSum_one_div_sq_shift.summable ?_ ?_
  · intro m
    have hpow : Tendsto (fun t : ℝ => t ^ (m + s + 1)) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) := by
      have hid : Tendsto (fun t : ℝ => t) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using hid.pow (m + s + 1)
    simpa using hpow.div_const (((m + r + 1 : ℕ) : ℝ) * ((m + s + 1 : ℕ) : ℝ))
  · filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with t ht m
    have ht0 : 0 ≤ t := ht.1.le
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hnum : t ^ (m + s + 1) ≤ 1 := pow_le_one₀ ht.1.le ht.2.le
    have hden1 : ((m + 1 : ℕ) : ℝ) ≤ (m + r + 1 : ℕ) := by exact_mod_cast (by omega : m + 1 ≤ m + r + 1)
    have hden2 : ((m + 1 : ℕ) : ℝ) ≤ (m + s + 1 : ℕ) := by exact_mod_cast (by omega : m + 1 ≤ m + s + 1)
    rw [sq]; gcongr

private def rvRatTerm (r s : ℕ) : ℚ :=
  if r = s then -(∑ k ∈ Icc 1 r, (1 : ℚ) / (k : ℚ) ^ 2)
  else (1 : ℚ) / ((max r s - min r s : ℕ) : ℚ) *
    ∑ k ∈ Icc (min r s + 1) (max r s), (1 : ℚ) / (k : ℚ)

private def rvQ (h i j k l : ℕ) : ℤ :=
  let m := i + j - l
  (-1 : ℤ) ^ m *
    ∑ a ∈ range (i + 1), ∑ b ∈ range (j + 1),
      if h + a - m = k - m + b then
        ((-1 : ℤ) ^ a * (i.choose a : ℤ) * ((h + a).choose m : ℤ)) *
        ((-1 : ℤ) ^ b * (j.choose b : ℤ))
      else 0

private def rvP (h i j k l : ℕ) : ℚ :=
  let m := i + j - l
  (-1 : ℚ) ^ m *
    ∑ a ∈ range (i + 1), ∑ b ∈ range (j + 1),
      ((-1 : ℚ) ^ a * (i.choose a : ℚ) * ((h + a).choose m : ℚ)) *
      ((-1 : ℚ) ^ b * (j.choose b : ℚ)) *
      rvRatTerm (h + a - m) (k - m + b)

private lemma rvInt_eq_linear_form (h i j k l : ℕ) (hl : 1 ≤ l) (hlij : l ≤ i + j)
    (hmh : i + j - l ≤ h) (hmi : i + j - l ≤ i) (hmk : i + j - l ≤ k) :
    rvInt h i j k l = (rvP h i j k l : ℝ) + (rvQ h i j k l : ℝ) * (π ^ 2 / 6) := by
  set m := i + j - l
  let g : ℝ → ℝ := fun y => ∫ x in (0 : ℝ)..1, rvIntegrand h i j k l x y
  have hF_lim : Tendsto (fun t : ℝ => ∫ y in (0 : ℝ)..t, g y) (𝓝[<] 1) (𝓝 (rvInt h i j k l)) := by
    rw [rvInt_eq_swap h i j k l hl hlij]
    have hg_int : IntervalIntegrable g volume 0 1 := by
      have hint := rvIntegrand_integrable_prod h i j k l hl hlij
      have h1 : Integrable g (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
        have h2 := hint.swap.integral_prod_left
        refine h2.congr ?_
        filter_upwards with y
        dsimp [g, Function.uncurry]
        exact (intervalIntegral.integral_of_le zero_le_one).symm
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 h1
    have hcont : ContinuousOn (fun t : ℝ => ∫ y in (0 : ℝ)..t, g y) (Set.Icc 0 1) := by
      have h1 := intervalIntegral.continuousOn_primitive_interval' hg_int Set.left_mem_uIcc
      simpa [Set.uIcc_of_le zero_le_one] using h1
    have hlim_Icc : Tendsto (fun t : ℝ => ∫ y in (0 : ℝ)..t, g y) (𝓝[Set.Icc 0 1] 1)
        (𝓝 (∫ y in (0 : ℝ)..1, g y)) :=
      hcont 1 (Set.right_mem_Icc.2 zero_le_one)
    exact hlim_Icc.mono_left (nhdsWithin_le_iff.2
      (Filter.mem_of_superset (Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1))
        fun t ht => ⟨ht.1.le, ht.2.le⟩))
  have hF_expand : ∀ t : ℝ, 0 ≤ t → t < 1 →
      ∫ y in (0 : ℝ)..t, g y =
        (-1 : ℝ) ^ m *
          ∑ a ∈ range (i + 1), ∑ b ∈ range (j + 1),
            ((-1 : ℝ) ^ a * (i.choose a : ℝ) * ((h + a).choose m : ℝ)) *
            ((-1 : ℝ) ^ b * (j.choose b : ℝ)) *
            (∫ y in (0 : ℝ)..t,
              (∫ x in (0 : ℝ)..1, x ^ (h + a - m) / (1 - x * y)) * y ^ (k - m + b)) := by
    intro t ht0 ht1
    have hpt : ∀ y ∈ Set.uIcc (0 : ℝ) t,
        g y = (-1 : ℝ) ^ m *
          ∑ a ∈ range (i + 1), ∑ b ∈ range (j + 1),
            ((-1 : ℝ) ^ a * (i.choose a : ℝ) * ((h + a).choose m : ℝ)) *
            ((-1 : ℝ) ^ b * (j.choose b : ℝ)) *
            ((∫ x in (0 : ℝ)..1, x ^ (h + a - m) / (1 - x * y)) * y ^ (k - m + b)) := by
      intro y hy
      rw [Set.uIcc_of_le ht0] at hy
      have hy0 : 0 ≤ y := hy.1
      have hy1 : y < 1 := hy.2.trans_lt ht1
      have hgy : g y =
          (∫ x in (0 : ℝ)..1, x ^ h * (1 - x) ^ i * y ^ m / (1 - x * y) ^ (m + 1)) *
            (y ^ (k - m) * (1 - y) ^ j) := by
        dsimp only [g]
        rw [← intervalIntegral.integral_mul_const]
        refine intervalIntegral.integral_congr fun x _ => ?_
        unfold rvIntegrand
        have hkm : m + (k - m) = k := by omega
        have hyk : y ^ m * y ^ (k - m) = y ^ k := by rw [← pow_add, hkm]
        calc x ^ h * (1 - x) ^ i * y ^ k * (1 - y) ^ j / (1 - x * y) ^ (m + 1)
            = x ^ h * (1 - x) ^ i * (y ^ m * y ^ (k - m)) * (1 - y) ^ j / (1 - x * y) ^ (m + 1) := by
              rw [hyk]
          _ = x ^ h * (1 - x) ^ i * y ^ m / (1 - x * y) ^ (m + 1) * (y ^ (k - m) * (1 - y) ^ j) := by
              ring
      rw [hgy, ← rv_ibp h i m hmh hmi hy0 hy1]
      have hpoly_int : ∫ x in (0 : ℝ)..1, rvPoly h i m x / (1 - x * y) =
          ∑ a ∈ range (i + 1),
            ((-1 : ℝ) ^ a * (i.choose a : ℝ) * ((h + a).choose m : ℝ)) *
            (∫ x in (0 : ℝ)..1, x ^ (h + a - m) / (1 - x * y)) := by
        unfold rvPoly
        simp_rw [sum_div]
        rw [intervalIntegral.integral_finsetSum]
        · refine sum_congr rfl fun a _ => ?_
          rw [← intervalIntegral.integral_const_mul]
          congr 1; ext x; ring
        · intro a _
          have hint := intervalIntegrable_monomial_div (h + a - m) hy0 hy1
          have heq : (fun x : ℝ => ((-1 : ℝ) ^ a * (i.choose a : ℝ) * ((h + a).choose m : ℝ)) *
              x ^ (h + a - m) / (1 - x * y)) =
              fun x : ℝ => ((-1 : ℝ) ^ a * (i.choose a : ℝ) * ((h + a).choose m : ℝ)) *
                (x ^ (h + a - m) / (1 - x * y)) := by ext x; ring
          rw [heq]; exact hint.const_mul _
      have hybin : y ^ (k - m) * (1 - y) ^ j =
          ∑ b ∈ range (j + 1), ((-1 : ℝ) ^ b * (j.choose b : ℝ)) * y ^ (k - m + b) := by
        have hbin : (1 - y) ^ j = ∑ b ∈ range (j + 1), (-1 : ℝ) ^ b * (j.choose b : ℝ) * y ^ b := by
          rw [sub_eq_add_neg, add_comm, add_pow]
          refine sum_congr rfl fun b _ => ?_
          rw [neg_eq_neg_one_mul, mul_pow, one_pow, mul_one]; ring
        rw [hbin, mul_sum]
        refine sum_congr rfl fun b _ => ?_
        rw [pow_add]; ring
      rw [hpoly_int, hybin, mul_assoc]
      congr 1
      rw [sum_mul]
      refine sum_congr rfl fun a _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun b _ => ?_
      ring
    rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul]
    congr 1
    have hint_term : ∀ a ∈ range (i + 1), ∀ b ∈ range (j + 1),
        IntervalIntegrable
          (fun y : ℝ =>
            ((-1 : ℝ) ^ a * (i.choose a : ℝ) * ((h + a).choose m : ℝ)) *
            ((-1 : ℝ) ^ b * (j.choose b : ℝ)) *
            ((∫ x in (0 : ℝ)..1, x ^ (h + a - m) / (1 - x * y)) * y ^ (k - m + b)))
          volume 0 t := by
      intro a _ b _
      have hc : ContinuousOn
          (fun y : ℝ =>
            ((-1 : ℝ) ^ a * (i.choose a : ℝ) * ((h + a).choose m : ℝ)) *
            ((-1 : ℝ) ^ b * (j.choose b : ℝ)) *
            ((∫ x in (0 : ℝ)..1, x ^ (h + a - m) / (1 - x * y)) * y ^ (k - m + b)))
          (Set.Icc 0 t) :=
        continuousOn_const.mul ((continuousOn_integral_monomial (h + a - m) ht0 ht1).mul
          (continuous_pow (k - m + b)).continuousOn)
      exact hc.intervalIntegrable_of_Icc ht0
    rw [intervalIntegral.integral_finsetSum]
    · refine sum_congr rfl fun a ha => ?_
      rw [intervalIntegral.integral_finsetSum (fun b hb => hint_term a ha b hb)]
      refine sum_congr rfl fun b _ => ?_
      rw [intervalIntegral.integral_const_mul]
    · intro a _
      have hc : ContinuousOn
          (fun y : ℝ => ∑ b ∈ range (j + 1),
            ((-1 : ℝ) ^ a * (i.choose a : ℝ) * ((h + a).choose m : ℝ)) *
            ((-1 : ℝ) ^ b * (j.choose b : ℝ)) *
            ((∫ x in (0 : ℝ)..1, x ^ (h + a - m) / (1 - x * y)) * y ^ (k - m + b)))
          (Set.Icc 0 t) :=
        continuousOn_finsetSum _ fun b _ =>
          continuousOn_const.mul ((continuousOn_integral_monomial (h + a - m) ht0 ht1).mul
            (continuous_pow (k - m + b)).continuousOn)
      exact hc.intervalIntegrable_of_Icc ht0
  have hF_lim2 : Tendsto (fun t : ℝ => ∫ y in (0 : ℝ)..t, g y) (𝓝[<] 1)
      (𝓝 ((-1 : ℝ) ^ m *
        ∑ a ∈ range (i + 1), ∑ b ∈ range (j + 1),
          ((-1 : ℝ) ^ a * (i.choose a : ℝ) * ((h + a).choose m : ℝ)) *
          ((-1 : ℝ) ^ b * (j.choose b : ℝ)) *
          beukersTerm (h + a - m) (k - m + b))) := by
    have hev : ∀ᶠ t : ℝ in 𝓝[<] 1,
        ∫ y in (0 : ℝ)..t, g y =
          (-1 : ℝ) ^ m *
            ∑ a ∈ range (i + 1), ∑ b ∈ range (j + 1),
              ((-1 : ℝ) ^ a * (i.choose a : ℝ) * ((h + a).choose m : ℝ)) *
              ((-1 : ℝ) ^ b * (j.choose b : ℝ)) *
              (∫ y in (0 : ℝ)..t,
                (∫ x in (0 : ℝ)..1, x ^ (h + a - m) / (1 - x * y)) * y ^ (k - m + b)) := by
      filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with t ht
      exact hF_expand t ht.1.le ht.2
    rw [tendsto_congr' hev]
    refine (tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun b _ =>
      (tendsto_double_integral_monomial (h + a - m) (k - m + b)).const_mul _).const_mul _
  have heq := tendsto_nhds_unique hF_lim hF_lim2
  rw [heq]
  unfold rvP rvQ beukersTerm rvRatTerm
  push_cast
  have hsplit : ∀ r s : ℕ,
      (if r = s then π ^ 2 / 6 - ∑ t ∈ Icc 1 r, (1 : ℝ) / (t : ℝ) ^ 2
       else (1 : ℝ) / ((max r s - min r s : ℕ) : ℝ) *
         ∑ t ∈ Icc (min r s + 1) (max r s), (1 : ℝ) / (t : ℝ)) =
      (if r = s then -(∑ t ∈ Icc 1 r, (1 : ℝ) / (t : ℝ) ^ 2)
       else (1 : ℝ) / ((max r s - min r s : ℕ) : ℝ) *
         ∑ t ∈ Icc (min r s + 1) (max r s), (1 : ℝ) / (t : ℝ)) +
      (if r = s then π ^ 2 / 6 else 0) := by
    intro r s; split_ifs <;> ring
  simp_rw [hsplit, mul_add, sum_add_distrib, mul_add]
  congr 1
  · congr 1
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    split_ifs <;> push_cast <;> rfl
  · rw [mul_assoc]
    congr 1
    rw [sum_mul]
    refine sum_congr rfl fun a _ => ?_
    rw [sum_mul]
    refine sum_congr rfl fun b _ => ?_
    split_ifs <;> ring

private lemma rvP_denom_int (h i j k l M1 M2 : ℕ)
    (hdiag1 : min (h + i - (i + j - l)) (k + j - (i + j - l)) ≤ M1)
    (hdiag2 : min (h + i - (i + j - l)) (k + j - (i + j - l)) ≤ M2)
    (hmax : max (h + i - (i + j - l)) (k + j - (i + j - l)) ≤ M1)
    (hdiff1 : (h + i - (i + j - l)) - (k - (i + j - l)) ≤ M2)
    (hdiff2 : (k + j - (i + j - l)) - (h - (i + j - l)) ≤ M2)
    (hmh : i + j - l ≤ h) (hmk : i + j - l ≤ k) :
    ∃ P : ℤ, (P : ℝ) =
      ((Nat.lcmUpto M1 * Nat.lcmUpto M2 : ℕ) : ℝ) * (rvP h i j k l : ℝ) := by
  set m := i + j - l
  have hdvd1 (t : ℕ) (ht1 : 1 ≤ t) (htM : t ≤ M1) : t ∣ Nat.lcmUpto M1 :=
    Finset.dvd_lcm (mem_Icc.2 ⟨ht1, htM⟩)
  have hdvd2 (t : ℕ) (ht1 : 1 ≤ t) (htM : t ≤ M2) : t ∣ Nat.lcmUpto M2 :=
    Finset.dvd_lcm (mem_Icc.2 ⟨ht1, htM⟩)
  have hterm_int : ∀ a ∈ range (i + 1), ∀ b ∈ range (j + 1),
      ∃ z : ℤ, (z : ℚ) =
        ((Nat.lcmUpto M1 * Nat.lcmUpto M2 : ℕ) : ℚ) * rvRatTerm (h + a - m) (k - m + b) := by
    intro a ha b hb
    have hai : a ≤ i := Nat.lt_succ_iff.1 (mem_range.1 ha)
    have hbj : b ≤ j := Nat.lt_succ_iff.1 (mem_range.1 hb)
    set r := h + a - m
    set s := k - m + b
    have hr_lo : h - m ≤ r := by omega
    have hr_hi : r ≤ h + i - m := by omega
    have hs_lo : k - m ≤ s := by omega
    have hs_hi : s ≤ k + j - m := by omega
    unfold rvRatTerm
    split_ifs with hrs
    · have hrM1 : r ≤ M1 := le_trans (le_min hr_hi (hrs ▸ hs_hi)) hdiag1
      have hrM2 : r ≤ M2 := le_trans (le_min hr_hi (hrs ▸ hs_hi)) hdiag2
      refine ⟨-(∑ t ∈ Icc 1 r,
          ((Nat.lcmUpto M1 / t : ℕ) : ℤ) * ((Nat.lcmUpto M2 / t : ℕ) : ℤ)), ?_⟩
      rw [mul_neg, mul_sum, Int.cast_neg, Int.cast_sum]
      congr 1
      refine sum_congr rfl fun t ht => ?_
      simp only [mem_Icc] at ht
      have ht0 : (t : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      have h1 : ((Nat.lcmUpto M1 / t : ℕ) : ℚ) = (Nat.lcmUpto M1 : ℚ) / (t : ℚ) :=
        Nat.cast_div (hdvd1 t ht.1 (ht.2.trans hrM1)) ht0
      have h2 : ((Nat.lcmUpto M2 / t : ℕ) : ℚ) = (Nat.lcmUpto M2 : ℚ) / (t : ℚ) :=
        Nat.cast_div (hdvd2 t ht.1 (ht.2.trans hrM2)) ht0
      rw [Int.cast_mul, Int.cast_natCast, Int.cast_natCast, h1, h2, Nat.cast_mul]
      ring
    · set hi := max r s
      set lo := min r s
      have hhiM1 : hi ≤ M1 := (max_le_max hr_hi hs_hi).trans hmax
      have hdiff1' : 1 ≤ hi - lo := by omega
      have hdiffM2 : hi - lo ≤ M2 := by
        dsimp only [hi, lo]
        rcases le_total r s with hle | hle
        · rw [max_eq_right hle, min_eq_left hle]; omega
        · rw [max_eq_left hle, min_eq_right hle]; omega
      refine ⟨((Nat.lcmUpto M2 / (hi - lo) : ℕ) : ℤ) *
          ∑ t ∈ Icc (lo + 1) hi, ((Nat.lcmUpto M1 / t : ℕ) : ℤ), ?_⟩
      have hd0 : ((hi - lo : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      have hdiv2 : ((Nat.lcmUpto M2 / (hi - lo) : ℕ) : ℚ) =
          (Nat.lcmUpto M2 : ℚ) / ((hi - lo : ℕ) : ℚ) :=
        Nat.cast_div (hdvd2 (hi - lo) hdiff1' hdiffM2) hd0
      rw [Int.cast_mul, Int.cast_natCast, Int.cast_sum, hdiv2, mul_sum, mul_sum, mul_sum]
      refine sum_congr rfl fun t ht => ?_
      simp only [mem_Icc] at ht
      have ht0 : (t : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      have hdiv1 : ((Nat.lcmUpto M1 / t : ℕ) : ℚ) = (Nat.lcmUpto M1 : ℚ) / (t : ℚ) :=
        Nat.cast_div (hdvd1 t (by omega) (ht.2.trans hhiM1)) ht0
      rw [Int.cast_natCast, hdiv1, Nat.cast_mul]
      ring
  choose f hf using hterm_int
  refine ⟨(-1 : ℤ) ^ m * ∑ a ∈ range (i + 1), ∑ b ∈ range (j + 1),
      ((-1 : ℤ) ^ a * (i.choose a : ℤ) * ((h + a).choose m : ℤ)) *
      ((-1 : ℤ) ^ b * (j.choose b : ℤ)) *
      (if hab : a ∈ range (i + 1) ∧ b ∈ range (j + 1) then f a hab.1 b hab.2 else 0), ?_⟩
  suffices hq : ((((-1 : ℤ) ^ m * ∑ a ∈ range (i + 1), ∑ b ∈ range (j + 1),
      ((-1 : ℤ) ^ a * (i.choose a : ℤ) * ((h + a).choose m : ℤ)) *
      ((-1 : ℤ) ^ b * (j.choose b : ℤ)) *
      (if hab : a ∈ range (i + 1) ∧ b ∈ range (j + 1) then f a hab.1 b hab.2 else 0) : ℤ) : ℚ)) =
      ((Nat.lcmUpto M1 * Nat.lcmUpto M2 : ℕ) : ℚ) * rvP h i j k l by
    have := congrArg (fun q : ℚ => (q : ℝ)) hq
    simpa using this
  unfold rvP
  rw [mul_left_comm]
  push_cast
  congr 1
  rw [mul_sum]
  refine sum_congr rfl fun a ha => ?_
  rw [mul_sum]
  refine sum_congr rfl fun b hb => ?_
  rw [dif_pos ⟨ha, hb⟩, hf a ha b hb]
  push_cast
  ring

private lemma rvInt_denom (h i j k l M1 M2 : ℕ) (hl : 1 ≤ l) (hlij : l ≤ i + j)
    (hmh : i + j - l ≤ h) (hmi : i + j - l ≤ i) (hmk : i + j - l ≤ k)
    (hdiag1 : min (h + i - (i + j - l)) (k + j - (i + j - l)) ≤ M1)
    (hdiag2 : min (h + i - (i + j - l)) (k + j - (i + j - l)) ≤ M2)
    (hmax : max (h + i - (i + j - l)) (k + j - (i + j - l)) ≤ M1)
    (hdiff1 : (h + i - (i + j - l)) - (k - (i + j - l)) ≤ M2)
    (hdiff2 : (k + j - (i + j - l)) - (h - (i + j - l)) ≤ M2) :
    ∃ P : ℤ, ((Nat.lcmUpto M1 * Nat.lcmUpto M2 : ℕ) : ℝ) * rvInt h i j k l =
      (P : ℝ) + ((((Nat.lcmUpto M1 * Nat.lcmUpto M2 : ℕ) : ℤ) * rvQ h i j k l : ℤ) : ℝ) *
        (π ^ 2 / 6) := by
  obtain ⟨P, hP⟩ := rvP_denom_int h i j k l M1 M2 hdiag1 hdiag2 hmax hdiff1 hdiff2 hmh hmk
  refine ⟨P, ?_⟩
  rw [rvInt_eq_linear_form h i j k l hl hlij hmh hmi hmk, mul_add, ← hP]
  push_cast
  ring

/- ### Section 3: Irrationality of π^2 / 6 from Beukers's Diagonal Integral + PNT -/

private lemma beukers_kernel_le {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y < 1) :
    x * (1 - x) * y * (1 - y) / (1 - x * y) ≤ 451 / 5000 := by
  have hden : 0 < 1 - x * y := by nlinarith
  rw [div_le_iff₀ hden]
  set t := Real.sqrt (x * y)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht_sq : t ^ 2 = x * y := Real.sq_sqrt (mul_nonneg hx0 hy0)
  have ht1 : t ≤ 1 := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by nlinarith)
  have hamgm : 2 * t ≤ x + y := by
    have hsq : 0 ≤ (Real.sqrt x - Real.sqrt y) ^ 2 := sq_nonneg _
    rw [sub_sq, Real.sq_sqrt hx0, Real.sq_sqrt hy0] at hsq
    have hmul : Real.sqrt x * Real.sqrt y = t := (Real.sqrt_mul hx0 y).symm
    linarith
  have hstep1 : x * (1 - x) * y * (1 - y) ≤ t ^ 2 * (1 - t) ^ 2 := by
    have h1 : x * (1 - x) * y * (1 - y) = t ^ 2 * (1 - (x + y) + t ^ 2) := by
      nlinarith [ht_sq]
    rw [h1]; nlinarith [sq_nonneg t]
  have hstep2 : t ^ 2 * (1 - t) ^ 2 ≤ (451 / 5000 : ℝ) * (1 - t ^ 2) := by
    have hpoly : (451 / 5000 : ℝ) * (1 + t) - t ^ 2 * (1 - t) =
        (t - 309 / 500) ^ 2 * (t + 59 / 250) + (7 / 250000 : ℝ) * (1 - t) +
          (18968 / 500000000 : ℝ) := by ring
    have hge : 0 ≤ (451 / 5000 : ℝ) * (1 + t) - t ^ 2 * (1 - t) := by
      rw [hpoly]
      have h1 : 0 ≤ (t - 309 / 500) ^ 2 * (t + 59 / 250) :=
        mul_nonneg (sq_nonneg _) (by linarith)
      have h2 : 0 ≤ (7 / 250000 : ℝ) * (1 - t) := by linarith
      linarith
    nlinarith
  linarith [ht_sq]

private lemma rvInt_diag_pos_and_le (n : ℕ) (hn : 1 ≤ n) :
    0 < rvInt n n n n n ∧ rvInt n n n n n ≤ (451 / 5000 : ℝ) ^ (n - 1) := by
  have hsub : n + n - n = n := by omega
  have hbound : ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      rvIntegrand n n n n n x y ≤ (451 / 5000 : ℝ) ^ (n - 1) := by
    intro x hx y hy
    unfold rvIntegrand
    rw [hsub]
    have hx0 : 0 ≤ x := hx.1.le
    have hx1 : x ≤ 1 := hx.2.le
    have hy0 : 0 ≤ y := hy.1.le
    have hy1 : y ≤ 1 := hy.2.le
    have h1x0 : 0 ≤ 1 - x := sub_nonneg.2 hx1
    have h1y0 : 0 ≤ 1 - y := sub_nonneg.2 hy1
    have h1xy_pos : 0 < 1 - x * y := by nlinarith [hx.1, hx.2, hy.1, hy.2]
    have hker := beukers_kernel_le hx0 hx1 hy0 hy.2
    have hker0 : 0 ≤ x * (1 - x) * y * (1 - y) / (1 - x * y) := by positivity
    have h1 : x * (1 - x) * y * (1 - y) / (1 - x * y) ^ 2 ≤ 1 := by
      have h1x : 1 - x ≤ 1 - x * y := by nlinarith [hx.1, hx.2, hy.1, hy.2]
      have h1y : 1 - y ≤ 1 - x * y := by nlinarith [hx.1, hx.2, hy.1, hy.2]
      rw [div_le_one (sq_pos_of_pos h1xy_pos), sq]
      calc x * (1 - x) * y * (1 - y) ≤ 1 * (1 - x * y) * 1 * (1 - x * y) := by gcongr
        _ = (1 - x * y) * (1 - x * y) := by ring
    have hrew : x ^ n * (1 - x) ^ n * y ^ n * (1 - y) ^ n / (1 - x * y) ^ (n + 1) =
        (x * (1 - x) * y * (1 - y) / (1 - x * y)) ^ (n - 1) *
          (x * (1 - x) * y * (1 - y) / (1 - x * y) ^ 2) := by
      have hn1 : (n - 1) + 1 = n := by omega
      have hn2 : (n - 1) + 2 = n + 1 := by omega
      rw [div_pow, mul_pow, mul_pow, mul_pow, ← mul_div_mul_comm]
      have hnum : (x ^ (n - 1) * (1 - x) ^ (n - 1) * y ^ (n - 1) * (1 - y) ^ (n - 1)) *
          (x * (1 - x) * y * (1 - y)) =
          x ^ n * (1 - x) ^ n * y ^ n * (1 - y) ^ n := by
        calc (x ^ (n - 1) * (1 - x) ^ (n - 1) * y ^ (n - 1) * (1 - y) ^ (n - 1)) *
              (x * (1 - x) * y * (1 - y))
            = (x ^ (n - 1) * x) * ((1 - x) ^ (n - 1) * (1 - x)) *
                (y ^ (n - 1) * y) * ((1 - y) ^ (n - 1) * (1 - y)) := by ring
          _ = x ^ ((n - 1) + 1) * (1 - x) ^ ((n - 1) + 1) *
                y ^ ((n - 1) + 1) * (1 - y) ^ ((n - 1) + 1) := by
              simp only [pow_succ]
          _ = x ^ n * (1 - x) ^ n * y ^ n * (1 - y) ^ n := by rw [hn1]
      rw [hnum, ← pow_add, hn2]
    rw [hrew]
    calc (x * (1 - x) * y * (1 - y) / (1 - x * y)) ^ (n - 1) *
          (x * (1 - x) * y * (1 - y) / (1 - x * y) ^ 2)
        ≤ (451 / 5000 : ℝ) ^ (n - 1) * 1 := by
          gcongr
      _ = (451 / 5000 : ℝ) ^ (n - 1) := mul_one _
  constructor
  · -- Strictly positive via lower bound on [1/4, 3/4]^2
    have hinner_ge : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        (if x ∈ Set.Icc (1 / 4 : ℝ) (3 / 4) then (1 / 2 : ℝ) * (1 / 256 : ℝ) ^ n else 0) ≤
          ∫ y in (0 : ℝ)..1, rvIntegrand n n n n n x y := by
      intro x hx
      have hint_y : IntervalIntegrable (fun y => rvIntegrand n n n n n x y) volume 0 1 := by
        have hI : Integrable (fun y => rvIntegrand n n n n n x y) (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
          by_cases hx1 : x = 1
          · subst hx1
            have hzero : ∀ y ∈ Set.Ioo (0 : ℝ) 1, rvIntegrand n n n n n 1 y = 0 := by
              intro y _; unfold rvIntegrand; rw [sub_self, zero_pow (by omega)]; ring
            exact (integrable_const (0 : ℝ)).congr (by
              filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
              exact (hzero y hy).symm)
          · have hxlt : x < 1 := lt_of_le_of_ne hx.2 hx1
            have hc : ContinuousOn (fun y => rvIntegrand n n n n n x y) (Set.Icc 0 1) := by
              intro y hy
              have hne : 1 - x * y ≠ 0 := by nlinarith [hx.1, hy.1, hy.2]
              unfold rvIntegrand
              exact (ContinuousAt.div
                (((continuousAt_const.mul continuousAt_const).mul (continuousAt_id.pow n)).mul
                  ((continuousAt_const.sub continuousAt_id).pow n))
                ((continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).pow _)
                (pow_ne_zero _ hne)).continuousWithinAt
            exact (hc.intervalIntegrable_of_Icc zero_le_one).1.mono_set Set.Ioo_subset_Ioc_self
        have hμ : volume.restrict (Set.Ioc (0 : ℝ) 1) = volume.restrict (Set.Ioo (0 : ℝ) 1) :=
          Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc.symm
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
        rwa [MeasureTheory.IntegrableOn, hμ]
      split_ifs with hxmid
      · have hsplit1 : ∫ y in (0 : ℝ)..1, rvIntegrand n n n n n x y =
            (∫ y in (0 : ℝ)..(1 / 4 : ℝ), rvIntegrand n n n n n x y) +
            (∫ y in (1 / 4 : ℝ)..(3 / 4 : ℝ), rvIntegrand n n n n n x y) +
            (∫ y in (3 / 4 : ℝ)..1, rvIntegrand n n n n n x y) := by
          have hi01 : IntervalIntegrable (fun y => rvIntegrand n n n n n x y) volume 0 (1 / 4) :=
            hint_y.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc (by simp [Set.uIcc_of_le]; norm_num))
          have hi13 : IntervalIntegrable (fun y => rvIntegrand n n n n n x y) volume (1 / 4) (3 / 4) :=
            hint_y.mono_set (Set.uIcc_subset_uIcc (by simp [Set.uIcc_of_le]; norm_num) (by simp [Set.uIcc_of_le]; norm_num))
          have hi03 : IntervalIntegrable (fun y => rvIntegrand n n n n n x y) volume 0 (3 / 4) :=
            hint_y.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc (by simp [Set.uIcc_of_le]; norm_num))
          have hi31 : IntervalIntegrable (fun y => rvIntegrand n n n n n x y) volume (3 / 4) 1 :=
            hint_y.mono_set (Set.uIcc_subset_uIcc (by simp [Set.uIcc_of_le]; norm_num) Set.right_mem_uIcc)
          have h12 := intervalIntegral.integral_add_adjacent_intervals hi01 hi13
          have h23 := intervalIntegral.integral_add_adjacent_intervals hi03 hi31
          linarith
        have ha : 0 ≤ ∫ y in (0 : ℝ)..(1 / 4 : ℝ), rvIntegrand n n n n n x y :=
          intervalIntegral.integral_nonneg (by norm_num) fun y hy =>
            rvIntegrand_nonneg n n n n n hx.1 hx.2 hy.1 (by linarith [hy.2])
        have hc : 0 ≤ ∫ y in (3 / 4 : ℝ)..1, rvIntegrand n n n n n x y :=
          intervalIntegral.integral_nonneg (by norm_num) fun y hy =>
            rvIntegrand_nonneg n n n n n hx.1 hx.2 (by linarith [hy.1]) hy.2
        have hb : (1 / 2 : ℝ) * (1 / 256 : ℝ) ^ n ≤
            ∫ y in (1 / 4 : ℝ)..(3 / 4 : ℝ), rvIntegrand n n n n n x y := by
          have hconst : (1 / 2 : ℝ) * (1 / 256 : ℝ) ^ n =
              ∫ _ in (1 / 4 : ℝ)..(3 / 4 : ℝ), (1 / 256 : ℝ) ^ n := by
            rw [intervalIntegral.integral_const, smul_eq_mul]; norm_num
          rw [hconst]
          refine intervalIntegral.integral_mono_on (by norm_num) intervalIntegrable_const
            (hint_y.mono_set (Set.uIcc_subset_uIcc (by simp [Set.uIcc_of_le]; norm_num) (by simp [Set.uIcc_of_le]; norm_num)))
            fun y hy => ?_
          unfold rvIntegrand
          have h1xy_le1 : 1 - x * y ≤ 1 := by nlinarith [hxmid.1, hy.1]
          have h1xy_pos : 0 < 1 - x * y := by nlinarith [hxmid.1, hxmid.2, hy.1, hy.2]
          have hden : (1 - x * y) ^ (n + n - n + 1) ≤ 1 := pow_le_one₀ h1xy_pos.le h1xy_le1
          have hprod : (1 / 256 : ℝ) ^ n ≤ x ^ n * (1 - x) ^ n * y ^ n * (1 - y) ^ n := by
            have hbase : (1 / 256 : ℝ) ≤ x * (1 - x) * y * (1 - y) := by
              have hx1 : (1 / 4 : ℝ) ≤ x := hxmid.1
              have hx2 : (1 / 4 : ℝ) ≤ 1 - x := by linarith [hxmid.2]
              have hy1 : (1 / 4 : ℝ) ≤ y := hy.1
              have hy2 : (1 / 4 : ℝ) ≤ 1 - y := by linarith [hy.2]
              calc (1 / 256 : ℝ) = (1 / 4) * (1 / 4) * (1 / 4) * (1 / 4) := by norm_num
                _ ≤ x * (1 - x) * y * (1 - y) := by gcongr
            calc (1 / 256 : ℝ) ^ n ≤ (x * (1 - x) * y * (1 - y)) ^ n :=
                  pow_le_pow_left₀ (by norm_num) hbase n
              _ = x ^ n * (1 - x) ^ n * y ^ n * (1 - y) ^ n := by simp only [mul_pow]
          have hnum_nn : 0 ≤ x ^ n * (1 - x) ^ n * y ^ n * (1 - y) ^ n := by
            have hx0 : 0 ≤ x := by linarith [hxmid.1]
            have h1x : 0 ≤ 1 - x := by linarith [hxmid.2]
            have hy0 : 0 ≤ y := by linarith [hy.1]
            have h1y : 0 ≤ 1 - y := by linarith [hy.2]
            positivity
          calc (1 / 256 : ℝ) ^ n = (1 / 256 : ℝ) ^ n / 1 := (div_one _).symm
            _ ≤ x ^ n * (1 - x) ^ n * y ^ n * (1 - y) ^ n / (1 - x * y) ^ (n + n - n + 1) := by
                exact div_le_div₀ hnum_nn hprod (pow_pos h1xy_pos _) hden
        linarith
      · exact intervalIntegral.integral_nonneg zero_le_one fun y hy =>
          rvIntegrand_nonneg n n n n n hx.1 hx.2 hy.1 hy.2
    have hout_int : IntervalIntegrable (fun x => ∫ y in (0 : ℝ)..1, rvIntegrand n n n n n x y) volume 0 1 := by
      have hint := rvIntegrand_integrable_prod n n n n n hn (by omega)
      have h1 := hint.integral_prod_left
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
      refine h1.congr ?_
      filter_upwards with x
      exact (intervalIntegral.integral_of_le zero_le_one).symm
    have hind_int : IntervalIntegrable
        (fun x : ℝ => if x ∈ Set.Icc (1 / 4 : ℝ) (3 / 4) then (1 / 2 : ℝ) * (1 / 256 : ℝ) ^ n else 0)
        volume 0 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
      have hc : Integrable (fun _ : ℝ => (1 / 2 : ℝ) * (1 / 256 : ℝ) ^ n)
          (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
        integrableOn_const (hs := by simp)
      exact (hc.indicator (s := Set.Icc (1 / 4 : ℝ) (3 / 4)) measurableSet_Icc).congr
        (by filter_upwards with x; simp [Set.indicator])
    have hind_val : ∫ x in (0 : ℝ)..1,
        (if x ∈ Set.Icc (1 / 4 : ℝ) (3 / 4) then (1 / 2 : ℝ) * (1 / 256 : ℝ) ^ n else 0) =
        (1 / 4 : ℝ) * (1 / 256 : ℝ) ^ n := by
      rw [intervalIntegral.integral_of_le zero_le_one]
      have hfun : (fun x : ℝ => if x ∈ Set.Icc (1 / 4 : ℝ) (3 / 4) then (1 / 2 : ℝ) * (1 / 256 : ℝ) ^ n else 0) =
          (Set.Icc (1 / 4 : ℝ) (3 / 4)).indicator (fun _ => (1 / 2 : ℝ) * (1 / 256 : ℝ) ^ n) := by
        ext x; simp [Set.indicator]
      have hsubI : Set.Icc (1 / 4 : ℝ) (3 / 4) ⊆ Set.Ioc (0 : ℝ) 1 :=
        fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
      rw [hfun, setIntegral_indicator measurableSet_Icc, Set.inter_eq_right.2 hsubI,
          setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Icc]
      norm_num
      ring
    have hpos : (0 : ℝ) < (1 / 4 : ℝ) * (1 / 256 : ℝ) ^ n := by positivity
    have hle := intervalIntegral.integral_mono_on zero_le_one hind_int hout_int hinner_ge
    unfold rvInt
    linarith
  · -- Upper bound ≤ (451/5000)^(n - 1)
    unfold rvInt
    have hconst : (451 / 5000 : ℝ) ^ (n - 1) = ∫ _ in (0 : ℝ)..1, (451 / 5000 : ℝ) ^ (n - 1) := by
      simp
    rw [hconst]
    simp_rw [intervalIntegral.integral_of_le zero_le_one]
    have hμ : volume.restrict (Set.Ioc (0 : ℝ) 1) = volume.restrict (Set.Ioo (0 : ℝ) 1) :=
      Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc.symm
    rw [hμ]
    have hout_int : Integrable (fun x => ∫ y in Set.Ioo (0 : ℝ) 1, rvIntegrand n n n n n x y)
        (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
      have hint := rvIntegrand_integrable_prod n n n n n hn (by omega)
      rw [hμ] at hint
      exact hint.integral_prod_left
    refine integral_mono_ae hout_int (integrable_const _) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hin_int : Integrable (fun y => rvIntegrand n n n n n x y) (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
      have hc : ContinuousOn (fun y => rvIntegrand n n n n n x y) (Set.Icc 0 1) := by
        intro y hy
        have hne : 1 - x * y ≠ 0 := by nlinarith [hx.1, hx.2, hy.1, hy.2]
        unfold rvIntegrand
        exact (ContinuousAt.div
          (((continuousAt_const.mul continuousAt_const).mul (continuousAt_id.pow n)).mul
            ((continuousAt_const.sub continuousAt_id).pow n))
          ((continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).pow _)
          (pow_ne_zero _ hne)).continuousWithinAt
      exact (hc.intervalIntegrable_of_Icc zero_le_one).1.mono_set Set.Ioo_subset_Ioc_self
    calc ∫ y in Set.Ioo (0 : ℝ) 1, rvIntegrand n n n n n x y
        ≤ ∫ _ in Set.Ioo (0 : ℝ) 1, (451 / 5000 : ℝ) ^ (n - 1) := by
          refine integral_mono_ae hin_int (integrable_const _) ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
          exact hbound x hx y hy
      _ = (451 / 5000 : ℝ) ^ (n - 1) := by
          rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioo]; norm_num

private lemma irrational_pi_sq_div_six_of_psi
    (hpsi : Chebyshev.psi ~[atTop] (fun x : ℝ => x)) :
    Irrational (π ^ 2 / 6) := by
  rintro ⟨r, hr⟩
  have hpsi_ev : ∀ᶠ n : ℕ in atTop, Chebyshev.psi (n : ℝ) ≤ (11 / 10 : ℝ) * (n : ℝ) := by
    have hdiv : Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) :=
      (Asymptotics.isEquivalent_iff_tendsto_one
        (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx; exact hx.ne')).1 hpsi
    have h1 := hdiv.comp tendsto_natCast_atTop_atTop
    have h2 : ∀ᶠ n : ℕ in atTop, Chebyshev.psi (n : ℝ) / (n : ℝ) < (11 / 10 : ℝ) :=
      h1.eventually (gt_mem_nhds (by norm_num))
    filter_upwards [h2, eventually_ge_atTop 1] with n hn hn1
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 hn1
    exact ((div_lt_iff₀ hnpos).1 hn).le
  have hdecay : Tendsto (fun n : ℕ => ((r.den : ℝ) * (5000 / 451 : ℝ)) *
      (Real.exp (22 / 10 : ℝ) * (451 / 5000 : ℝ)) ^ n) atTop (𝓝 0) := by
    have hbase_lt : Real.exp (22 / 10 : ℝ) * (451 / 5000 : ℝ) < 1 := by
      have hexp : Real.exp (22 / 10 : ℝ) < 10 := by
        have hlog10 : (22 / 10 : ℝ) < Real.log 10 := by
          have h10 : (10 : ℝ) = 2 * 2 * 2 * (5 / 4) := by norm_num
          have hl2 : (0.6931 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
          have h54 : (1 / 5 : ℝ) ≤ Real.log (5 / 4 : ℝ) := by
            have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (4 / 5 : ℝ) by norm_num)
            rw [show (4 / 5 : ℝ) = ((5 / 4 : ℝ))⁻¹ by norm_num, Real.log_inv] at this
            linarith
          have hl10 : Real.log 10 = Real.log 2 + Real.log 2 + Real.log 2 + Real.log (5 / 4) := by
            rw [h10, Real.log_mul (by norm_num) (by norm_num),
                Real.log_mul (by norm_num) (by norm_num),
                Real.log_mul (by norm_num) (by norm_num)]
          linarith
        exact (Real.lt_log_iff_exp_lt (by norm_num)).1 hlog10
      nlinarith
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hbase_lt).const_mul _
  have hsmall : ∀ᶠ n : ℕ in atTop,
      ((r.den : ℝ) * (5000 / 451 : ℝ)) * (Real.exp (22 / 10 : ℝ) * (451 / 5000 : ℝ)) ^ n < 1 :=
    hdecay.eventually (gt_mem_nhds zero_lt_one)
  obtain ⟨n, ⟨hn1, hpsin⟩, hsm⟩ := (((eventually_ge_atTop 1).and hpsi_ev).and hsmall).exists
  obtain ⟨P, hP⟩ := rvInt_denom n n n n n n n hn1 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨hpos, hle⟩ := rvInt_diag_pos_and_le n hn1
  have hlcm_le : ((Nat.lcmUpto n : ℝ)) ^ 2 ≤ Real.exp (22 / 10 : ℝ) ^ n := by
    have hlog := Chebyshev.psi_eq_log_lcmUpto n
    have hlpos : (0 : ℝ) < Nat.lcmUpto n := Nat.cast_pos.2 (Nat.lcmUpto_pos n)
    have h1 : (Nat.lcmUpto n : ℝ) ≤ Real.exp ((11 / 10 : ℝ) * n) := by
      rw [← Real.log_le_iff_le_exp hlpos, ← hlog]; exact hpsin
    calc (Nat.lcmUpto n : ℝ) ^ 2 ≤ (Real.exp ((11 / 10 : ℝ) * n)) ^ 2 := by gcongr
      _ = Real.exp (2 * ((11 / 10 : ℝ) * n)) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
      _ = Real.exp ((n : ℝ) * (22 / 10 : ℝ)) := by congr 1; ring
      _ = Real.exp (22 / 10 : ℝ) ^ n := by rw [Real.exp_nat_mul]
  let Z : ℤ := (r.den : ℤ) * P + r.num * (((Nat.lcmUpto n * Nat.lcmUpto n : ℕ) : ℤ) * rvQ n n n n n)
  have hZ_eq : (Z : ℝ) = (r.den : ℝ) * (((Nat.lcmUpto n * Nat.lcmUpto n : ℕ) : ℝ) * rvInt n n n n n) := by
    have hr_cast : (π ^ 2 / 6 : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by
      rw [← hr, Rat.cast_def]
    have hrden : (r.den : ℝ) ≠ 0 := Nat.cast_ne_zero.2 r.den_nz
    dsimp only [Z]
    rw [hP, hr_cast]
    push_cast
    field_simp [hrden]
  have hZ_pos : (0 : ℝ) < (Z : ℝ) := by
    rw [hZ_eq]
    have hlpos : (0 : ℝ) < (Nat.lcmUpto n * Nat.lcmUpto n : ℕ) := by
      exact_mod_cast Nat.mul_pos (Nat.lcmUpto_pos n) (Nat.lcmUpto_pos n)
    have hrpos : (0 : ℝ) < r.den := Nat.cast_pos.2 r.pos
    positivity
  have hZ_lt : (Z : ℝ) < 1 := by
    rw [hZ_eq]
    have hpow_sub : (451 / 5000 : ℝ) ^ (n - 1) = (5000 / 451 : ℝ) * (451 / 5000 : ℝ) ^ n := by
      have hn' : n = (n - 1) + 1 := by omega
      conv_rhs => rw [hn', pow_succ]
      ring
    have hcast : ((Nat.lcmUpto n * Nat.lcmUpto n : ℕ) : ℝ) = (Nat.lcmUpto n : ℝ) ^ 2 := by
      push_cast; rw [sq]
    rw [hcast]
    calc (r.den : ℝ) * ((Nat.lcmUpto n : ℝ) ^ 2 * rvInt n n n n n)
        ≤ (r.den : ℝ) * (Real.exp (22 / 10 : ℝ) ^ n * (451 / 5000 : ℝ) ^ (n - 1)) := by
          gcongr
      _ = ((r.den : ℝ) * (5000 / 451 : ℝ)) * (Real.exp (22 / 10 : ℝ) * (451 / 5000 : ℝ)) ^ n := by
          rw [hpow_sub, mul_pow]; ring
      _ < 1 := hsm
  have hZ_pos' : (0 : ℤ) < Z := by exact_mod_cast hZ_pos
  have hZ_lt' : Z < (1 : ℤ) := by exact_mod_cast hZ_lt
  omega

private lemma linear_form_unique_of_irrational (hirr : Irrational (π ^ 2 / 6))
    {P1 Q1 P2 Q2 : ℤ}
    (h : (P1 : ℝ) + (Q1 : ℝ) * (π ^ 2 / 6) = (P2 : ℝ) + (Q2 : ℝ) * (π ^ 2 / 6)) :
    P1 = P2 ∧ Q1 = Q2 := by
  have hQ : Q1 = Q2 := by
    by_contra hne
    have hdiff : (Q1 : ℝ) - (Q2 : ℝ) ≠ 0 := sub_ne_zero.2 (Int.cast_injective.ne hne)
    refine hirr ⟨((P2 - P1 : ℤ) : ℚ) / ((Q1 - Q2 : ℤ) : ℚ), ?_⟩
    push_cast
    rw [div_eq_iff hdiff]
    linarith
  subst hQ
  have hP : (P1 : ℝ) = (P2 : ℝ) := by linarith
  exact ⟨by exact_mod_cast hP, rfl⟩

/- ### Section 4: The 7 Direct-IBP Orbit States and Exact Factorial Relations -/

private noncomputable def targetI (n : ℕ) : ℝ :=
  rvInt (12 * n) (12 * n) (14 * n) (14 * n) (13 * n)

private lemma targetI_eq_H1_integral (n : ℕ) :
    targetI n =
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        ((x ^ 12 * (1 - x) ^ 12 * y ^ 14 * (1 - y) ^ 14) / (1 - x * y) ^ 13) ^ n / (1 - x * y) := by
  unfold targetI rvInt rvIntegrand
  refine intervalIntegral.integral_congr fun x _ => intervalIntegral.integral_congr fun y _ => ?_
  have hexp : 12 * n + 14 * n - 13 * n + 1 = 13 * n + 1 := by omega
  rw [hexp, div_pow, div_div, ← pow_mul, ← pow_succ]
  congr 1
  simp only [mul_pow, ← pow_mul]

private structure StateSpec where
  M1 : ℕ
  M2 : ℕ
  pos : List ℕ
  neg : List ℕ

private def stateSpec : Fin 7 → StateSpec
  | ⟨0, _⟩ => ⟨16, 15, [], []⟩
  | ⟨1, _⟩ => ⟨15, 13, [12, 12, 13], [10, 11, 16]⟩
  | ⟨2, _⟩ => ⟨16, 14, [14, 14], [13, 15]⟩
  | ⟨3, _⟩ => ⟨15, 14, [13, 14], [11, 16]⟩
  | ⟨4, _⟩ => ⟨16, 15, [12, 12], [11, 13]⟩
  | ⟨5, _⟩ => ⟨16, 13, [12, 13], [10, 15]⟩
  | ⟨6, _⟩ => ⟨15, 14, [12, 14, 14], [11, 13, 16]⟩

private def factProd (n : ℕ) (cs : List ℕ) : ℕ :=
  (cs.map (fun c => (c * n)!)).prod

private lemma factProd_pos (n : ℕ) (cs : List ℕ) : 0 < factProd n cs := by
  unfold factProd
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.map_cons, List.prod_cons]
    exact Nat.mul_pos (Nat.factorial_pos _) ih

private lemma orbit_st0 (n : ℕ) (hn : 1 ≤ n) :
    targetI n = rvInt (12 * n) (12 * n) (13 * n) (14 * n) (14 * n) := by
  unfold targetI
  exact rvInt_M2 (12 * n) (12 * n) (14 * n) (14 * n) (13 * n)
    (by omega) (by omega) (by omega) (by omega)

private lemma orbit_st4 (n : ℕ) (hn : 1 ≤ n) :
    (((11 * n)! * (13 * n)! : ℕ) : ℝ) * targetI n =
      (((12 * n)! * (12 * n)! : ℕ) : ℝ) * rvInt (14 * n) (14 * n) (11 * n) (13 * n) (13 * n) := by
  rw [orbit_st0 n hn]
  have h1 := rvInt_M3 (12 * n) (12 * n) (13 * n) (14 * n) (14 * n)
    (by omega) (by omega) (by omega) (by omega)
  have hs1 : 12 * n + 14 * n - 13 * n = 13 * n := by omega
  have hs2 : 12 * n + 13 * n - 14 * n = 11 * n := by omega
  rw [hs1, hs2] at h1
  rw [show (11 * n)! * (13 * n)! = (13 * n)! * (11 * n)! by ring]
  rw [h1, rvInt_M1 (13 * n) (11 * n) (14 * n) (14 * n) (13 * n) (by omega) (by omega)]

private lemma orbit_st1 (n : ℕ) (hn : 1 ≤ n) :
    (((10 * n)! * (11 * n)! * (16 * n)! : ℕ) : ℝ) * targetI n =
      (((12 * n)! * (12 * n)! * (13 * n)! : ℕ) : ℝ) *
        rvInt (14 * n) (14 * n) (10 * n) (16 * n) (11 * n) := by
  have h4 := orbit_st4 n hn
  have h5 : rvInt (14 * n) (14 * n) (11 * n) (13 * n) (13 * n) =
      rvInt (14 * n) (14 * n) (13 * n) (13 * n) (11 * n) :=
    rvInt_M2 (14 * n) (14 * n) (11 * n) (13 * n) (13 * n)
      (by omega) (by omega) (by omega) (by omega)
  have h6 : rvInt (14 * n) (14 * n) (13 * n) (13 * n) (11 * n) =
      rvInt (13 * n) (13 * n) (14 * n) (14 * n) (11 * n) :=
    rvInt_M1 (14 * n) (14 * n) (13 * n) (13 * n) (11 * n) (by omega) (by omega)
  have h7 : rvInt (13 * n) (13 * n) (14 * n) (14 * n) (11 * n) =
      rvInt (13 * n) (13 * n) (11 * n) (14 * n) (14 * n) :=
    rvInt_M2 (13 * n) (13 * n) (14 * n) (14 * n) (11 * n)
      (by omega) (by omega) (by omega) (by omega)
  have h8 := rvInt_M3 (13 * n) (13 * n) (11 * n) (14 * n) (14 * n)
    (by omega) (by omega) (by omega) (by omega)
  have hs1 : 13 * n + 14 * n - 11 * n = 16 * n := by omega
  have hs2 : 13 * n + 11 * n - 14 * n = 10 * n := by omega
  rw [hs1, hs2] at h8
  have h9 := rvInt_M1 (16 * n) (10 * n) (14 * n) (14 * n) (11 * n) (by omega) (by omega)
  rw [h9] at h8
  rw [h5, h6, h7] at h4
  have h13ne : ((13 * n)! : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  apply mul_left_cancel₀ h13ne
  push_cast at h4 h8 ⊢
  calc ((13 * n)! : ℝ) * (((10 * n)! : ℝ) * ((11 * n)! : ℝ) * ((16 * n)! : ℝ) * targetI n)
      = ((16 * n)! : ℝ) * ((10 * n)! : ℝ) * (((11 * n)! : ℝ) * ((13 * n)! : ℝ) * targetI n) := by ring
    _ = ((16 * n)! : ℝ) * ((10 * n)! : ℝ) *
          (((12 * n)! : ℝ) * ((12 * n)! : ℝ) * rvInt (13 * n) (13 * n) (11 * n) (14 * n) (14 * n)) := by
        rw [h4]
    _ = ((12 * n)! : ℝ) * ((12 * n)! : ℝ) *
          (((16 * n)! : ℝ) * ((10 * n)! : ℝ) * rvInt (13 * n) (13 * n) (11 * n) (14 * n) (14 * n)) := by ring
    _ = ((12 * n)! : ℝ) * ((12 * n)! : ℝ) *
          (((13 * n)! : ℝ) * ((13 * n)! : ℝ) * rvInt (14 * n) (14 * n) (10 * n) (16 * n) (11 * n)) := by
        rw [h8]
    _ = ((13 * n)! : ℝ) * (((12 * n)! : ℝ) * ((12 * n)! : ℝ) * ((13 * n)! : ℝ) *
          rvInt (14 * n) (14 * n) (10 * n) (16 * n) (11 * n)) := by ring

private lemma orbit_st2 (n : ℕ) (hn : 1 ≤ n) :
    (((13 * n)! * (15 * n)! : ℕ) : ℝ) * targetI n =
      (((14 * n)! * (14 * n)! : ℕ) : ℝ) * rvInt (13 * n) (12 * n) (12 * n) (15 * n) (13 * n) := by
  have h1 : targetI n = rvInt (14 * n) (14 * n) (12 * n) (12 * n) (13 * n) :=
    rvInt_M1 (12 * n) (12 * n) (14 * n) (14 * n) (13 * n) (by omega) (by omega)
  have h2 := rvInt_M3 (14 * n) (14 * n) (12 * n) (12 * n) (13 * n)
    (by omega) (by omega) (by omega) (by omega)
  have hs1 : 14 * n + 13 * n - 12 * n = 15 * n := by omega
  have hs2 : 14 * n + 12 * n - 13 * n = 13 * n := by omega
  rw [hs1, hs2] at h2
  have h3 := rvInt_M1 (15 * n) (13 * n) (13 * n) (12 * n) (12 * n) (by omega) (by omega)
  have h4 := rvInt_M2 (12 * n) (13 * n) (13 * n) (15 * n) (12 * n)
    (by omega) (by omega) (by omega) (by omega)
  rw [h1, show (13 * n)! * (15 * n)! = (15 * n)! * (13 * n)! by ring, h2, h3, h4]

private lemma orbit_st3 (n : ℕ) (hn : 1 ≤ n) :
    (((11 * n)! * (16 * n)! : ℕ) : ℝ) * targetI n =
      (((13 * n)! * (14 * n)! : ℕ) : ℝ) * rvInt (12 * n) (12 * n) (14 * n) (11 * n) (16 * n) := by
  have h1 := orbit_st0 n hn
  have h2 : rvInt (12 * n) (12 * n) (13 * n) (14 * n) (14 * n) =
      rvInt (14 * n) (13 * n) (12 * n) (12 * n) (14 * n) :=
    rvInt_M1 (12 * n) (12 * n) (13 * n) (14 * n) (14 * n) (by omega) (by omega)
  have h3 : rvInt (14 * n) (13 * n) (12 * n) (12 * n) (14 * n) =
      rvInt (13 * n) (14 * n) (14 * n) (12 * n) (12 * n) :=
    rvInt_M2 (14 * n) (13 * n) (12 * n) (12 * n) (14 * n)
      (by omega) (by omega) (by omega) (by omega)
  have h4 := rvInt_M3 (13 * n) (14 * n) (14 * n) (12 * n) (12 * n)
    (by omega) (by omega) (by omega) (by omega)
  have hs1 : 13 * n + 12 * n - 14 * n = 11 * n := by omega
  have hs2 : 14 * n + 14 * n - 12 * n = 16 * n := by omega
  rw [hs1, hs2] at h4
  have h5 := rvInt_M1 (11 * n) (16 * n) (12 * n) (12 * n) (14 * n) (by omega) (by omega)
  have h6 := rvInt_M2 (12 * n) (12 * n) (16 * n) (11 * n) (14 * n)
    (by omega) (by omega) (by omega) (by omega)
  rw [h1, h2, h3, h4, h5, h6]

private lemma orbit_st5 (n : ℕ) (hn : 1 ≤ n) :
    (((10 * n)! * (15 * n)! : ℕ) : ℝ) * targetI n =
      (((12 * n)! * (13 * n)! : ℕ) : ℝ) * rvInt (14 * n) (14 * n) (10 * n) (15 * n) (12 * n) := by
  have h1 : targetI n = rvInt (14 * n) (14 * n) (12 * n) (12 * n) (13 * n) :=
    rvInt_M1 (12 * n) (12 * n) (14 * n) (14 * n) (13 * n) (by omega) (by omega)
  have h2 : rvInt (14 * n) (14 * n) (12 * n) (12 * n) (13 * n) =
      rvInt (14 * n) (14 * n) (13 * n) (12 * n) (12 * n) :=
    rvInt_M2 (14 * n) (14 * n) (12 * n) (12 * n) (13 * n)
      (by omega) (by omega) (by omega) (by omega)
  have h3 : rvInt (14 * n) (14 * n) (13 * n) (12 * n) (12 * n) =
      rvInt (12 * n) (13 * n) (14 * n) (14 * n) (12 * n) :=
    rvInt_M1 (14 * n) (14 * n) (13 * n) (12 * n) (12 * n) (by omega) (by omega)
  have h4 : rvInt (12 * n) (13 * n) (14 * n) (14 * n) (12 * n) =
      rvInt (13 * n) (12 * n) (12 * n) (14 * n) (14 * n) :=
    rvInt_M2 (12 * n) (13 * n) (14 * n) (14 * n) (12 * n)
      (by omega) (by omega) (by omega) (by omega)
  have h5 := rvInt_M3 (13 * n) (12 * n) (12 * n) (14 * n) (14 * n)
    (by omega) (by omega) (by omega) (by omega)
  have hs1 : 13 * n + 14 * n - 12 * n = 15 * n := by omega
  have hs2 : 12 * n + 12 * n - 14 * n = 10 * n := by omega
  rw [hs1, hs2] at h5
  have h6 := rvInt_M1 (15 * n) (10 * n) (14 * n) (14 * n) (12 * n) (by omega) (by omega)
  rw [h1, h2, h3, h4, show (10 * n)! * (15 * n)! = (15 * n)! * (10 * n)! by ring,
      show (12 * n)! * (13 * n)! = (13 * n)! * (12 * n)! by ring, h5, h6]

private lemma orbit_st6 (n : ℕ) (hn : 1 ≤ n) :
    (((11 * n)! * (13 * n)! * (16 * n)! : ℕ) : ℝ) * targetI n =
      (((12 * n)! * (14 * n)! * (14 * n)! : ℕ) : ℝ) *
        rvInt (13 * n) (13 * n) (11 * n) (16 * n) (12 * n) := by
  have h1 := orbit_st0 n hn
  have h2 : rvInt (12 * n) (12 * n) (13 * n) (14 * n) (14 * n) =
      rvInt (14 * n) (13 * n) (12 * n) (12 * n) (14 * n) :=
    rvInt_M1 (12 * n) (12 * n) (13 * n) (14 * n) (14 * n) (by omega) (by omega)
  have h3 := rvInt_M3 (14 * n) (13 * n) (12 * n) (12 * n) (14 * n)
    (by omega) (by omega) (by omega) (by omega)
  have hs1 : 14 * n + 14 * n - 12 * n = 16 * n := by omega
  have hs2 : 13 * n + 12 * n - 14 * n = 11 * n := by omega
  rw [hs1, hs2] at h3
  have h4 := rvInt_M1 (16 * n) (11 * n) (14 * n) (12 * n) (12 * n) (by omega) (by omega)
  have h5 := rvInt_M2 (12 * n) (14 * n) (11 * n) (16 * n) (12 * n)
    (by omega) (by omega) (by omega) (by omega)
  have h6 := rvInt_M3 (14 * n) (12 * n) (12 * n) (16 * n) (11 * n)
    (by omega) (by omega) (by omega) (by omega)
  have hs3 : 14 * n + 11 * n - 12 * n = 13 * n := by omega
  have hs4 : 12 * n + 12 * n - 11 * n = 13 * n := by omega
  rw [hs3, hs4] at h6
  rw [h4, h5] at h3
  rw [h1, h2]
  have h13ne : ((13 * n)! : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  apply mul_left_cancel₀ h13ne
  push_cast at h3 h6 ⊢
  calc ((13 * n)! : ℝ) * (((11 * n)! : ℝ) * ((13 * n)! : ℝ) * ((16 * n)! : ℝ) *
        rvInt (14 * n) (13 * n) (12 * n) (12 * n) (14 * n))
      = ((13 * n)! : ℝ) * ((13 * n)! : ℝ) *
          (((16 * n)! : ℝ) * ((11 * n)! : ℝ) * rvInt (14 * n) (13 * n) (12 * n) (12 * n) (14 * n)) := by ring
    _ = ((13 * n)! : ℝ) * ((13 * n)! : ℝ) *
          (((14 * n)! : ℝ) * ((13 * n)! : ℝ) * rvInt (14 * n) (12 * n) (12 * n) (16 * n) (11 * n)) := by
        rw [h3]
    _ = ((14 * n)! : ℝ) * ((13 * n)! : ℝ) *
          (((13 * n)! : ℝ) * ((13 * n)! : ℝ) * rvInt (14 * n) (12 * n) (12 * n) (16 * n) (11 * n)) := by ring
    _ = ((14 * n)! : ℝ) * ((13 * n)! : ℝ) *
          (((14 * n)! : ℝ) * ((12 * n)! : ℝ) * rvInt (13 * n) (13 * n) (11 * n) (16 * n) (12 * n)) := by
        rw [h6]
    _ = ((13 * n)! : ℝ) * (((12 * n)! : ℝ) * ((14 * n)! : ℝ) * ((14 * n)! : ℝ) *
          rvInt (13 * n) (13 * n) (11 * n) (16 * n) (12 * n)) := by ring

private def stateMult (n : ℕ) (s : StateSpec) : ℕ :=
  let X := factProd n s.neg * (Nat.lcmUpto (s.M1 * n) * Nat.lcmUpto (s.M2 * n))
  let Y := factProd n s.pos
  X / Nat.gcd X Y

private lemma stateMult_pos (n : ℕ) (s : StateSpec) : 0 < stateMult n s := by
  unfold stateMult
  set X := factProd n s.neg * (Nat.lcmUpto (s.M1 * n) * Nat.lcmUpto (s.M2 * n))
  set Y := factProd n s.pos
  have hX : 0 < X := Nat.mul_pos (factProd_pos n s.neg)
    (Nat.mul_pos (Nat.lcmUpto_pos _) (Nat.lcmUpto_pos _))
  have hg : Nat.gcd X Y ≤ X := Nat.le_of_dvd hX (Nat.gcd_dvd_left X Y)
  have hg_pos : 0 < Nat.gcd X Y := Nat.gcd_pos_of_pos_left Y hX
  exact Nat.div_pos hg hg_pos

private lemma stateMult_linear_form (n : ℕ) (hn : 1 ≤ n) (idx : Fin 7) :
    ∃ P Q : ℤ, (stateMult n (stateSpec idx) : ℝ) * targetI n =
      (P : ℝ) + (Q : ℝ) * (π ^ 2 / 6) := by
  have aux : ∀ (s : StateSpec) (h i j k l : ℕ),
      (factProd n s.neg : ℝ) * targetI n = (factProd n s.pos : ℝ) * rvInt h i j k l →
      (∃ P' Q' : ℤ, ((Nat.lcmUpto (s.M1 * n) * Nat.lcmUpto (s.M2 * n) : ℕ) : ℝ) * rvInt h i j k l =
        (P' : ℝ) + (Q' : ℝ) * (π ^ 2 / 6)) →
      ∃ P Q : ℤ, (stateMult n s : ℝ) * targetI n = (P : ℝ) + (Q : ℝ) * (π ^ 2 / 6) := by
    intro s h i j k l horb ⟨P', Q', hlin⟩
    set L := Nat.lcmUpto (s.M1 * n) * Nat.lcmUpto (s.M2 * n)
    set X := factProd n s.neg * L
    set Y := factProd n s.pos
    set g := Nat.gcd X Y
    have hgX : g ∣ X := Nat.gcd_dvd_left X Y
    have hgY : g ∣ Y := Nat.gcd_dvd_right X Y
    have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right X (factProd_pos n s.pos)
    have hg_ne : (g : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hg_pos.ne'
    refine ⟨((Y / g : ℕ) : ℤ) * P', ((Y / g : ℕ) : ℤ) * Q', ?_⟩
    have hXeq : (X : ℝ) = (g : ℝ) * (stateMult n s : ℝ) := by
      unfold stateMult
      exact_mod_cast (Nat.mul_div_cancel' hgX).symm
    have hYeq : (Y : ℝ) = (g : ℝ) * ((Y / g : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_div_cancel' hgY).symm
    apply mul_left_cancel₀ hg_ne
    calc (g : ℝ) * ((stateMult n s : ℝ) * targetI n)
        = (X : ℝ) * targetI n := by rw [← mul_assoc, ← hXeq]
      _ = (L : ℝ) * ((factProd n s.neg : ℝ) * targetI n) := by
          dsimp only [X]; push_cast; ring
      _ = (L : ℝ) * ((Y : ℝ) * rvInt h i j k l) := by rw [horb]
      _ = (Y : ℝ) * ((L : ℝ) * rvInt h i j k l) := by ring
      _ = (Y : ℝ) * ((P' : ℝ) + (Q' : ℝ) * (π ^ 2 / 6)) := by rw [hlin]
      _ = (g : ℝ) * (((((Y / g : ℕ) : ℤ) * P' : ℤ) : ℝ) +
            ((((Y / g : ℕ) : ℤ) * Q' : ℤ) : ℝ) * (π ^ 2 / 6)) := by
          rw [Int.cast_mul, Int.cast_mul, Int.cast_natCast, hYeq]
          ring
  fin_cases idx
  · refine aux (stateSpec 0) (12 * n) (12 * n) (13 * n) (14 * n) (14 * n) ?_ ?_
    · simp only [stateSpec, factProd, List.map_nil, List.prod_nil, Nat.cast_one, one_mul]
      exact orbit_st0 n hn
    · obtain ⟨P', hP'⟩ := rvInt_denom (12 * n) (12 * n) (13 * n) (14 * n) (14 * n)
        (16 * n) (15 * n) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)
      exact ⟨P', _, hP'⟩
  · refine aux (stateSpec 1) (14 * n) (14 * n) (10 * n) (16 * n) (11 * n) ?_ ?_
    · simp only [stateSpec, factProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one]
      simpa [Nat.cast_mul, mul_assoc] using orbit_st1 n hn
    · obtain ⟨P', hP'⟩ := rvInt_denom (14 * n) (14 * n) (10 * n) (16 * n) (11 * n)
        (15 * n) (13 * n) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)
      exact ⟨P', _, hP'⟩
  · refine aux (stateSpec 2) (13 * n) (12 * n) (12 * n) (15 * n) (13 * n) ?_ ?_
    · simp only [stateSpec, factProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one]
      simpa [Nat.cast_mul, mul_assoc] using orbit_st2 n hn
    · obtain ⟨P', hP'⟩ := rvInt_denom (13 * n) (12 * n) (12 * n) (15 * n) (13 * n)
        (16 * n) (14 * n) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)
      exact ⟨P', _, hP'⟩
  · refine aux (stateSpec 3) (12 * n) (12 * n) (14 * n) (11 * n) (16 * n) ?_ ?_
    · simp only [stateSpec, factProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one]
      simpa [Nat.cast_mul, mul_assoc] using orbit_st3 n hn
    · obtain ⟨P', hP'⟩ := rvInt_denom (12 * n) (12 * n) (14 * n) (11 * n) (16 * n)
        (15 * n) (14 * n) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)
      exact ⟨P', _, hP'⟩
  · refine aux (stateSpec 4) (14 * n) (14 * n) (11 * n) (13 * n) (13 * n) ?_ ?_
    · simp only [stateSpec, factProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one]
      simpa [Nat.cast_mul, mul_assoc] using orbit_st4 n hn
    · obtain ⟨P', hP'⟩ := rvInt_denom (14 * n) (14 * n) (11 * n) (13 * n) (13 * n)
        (16 * n) (15 * n) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)
      exact ⟨P', _, hP'⟩
  · refine aux (stateSpec 5) (14 * n) (14 * n) (10 * n) (15 * n) (12 * n) ?_ ?_
    · simp only [stateSpec, factProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one]
      simpa [Nat.cast_mul, mul_assoc] using orbit_st5 n hn
    · obtain ⟨P', hP'⟩ := rvInt_denom (14 * n) (14 * n) (10 * n) (15 * n) (12 * n)
        (16 * n) (13 * n) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)
      exact ⟨P', _, hP'⟩
  · refine aux (stateSpec 6) (13 * n) (13 * n) (11 * n) (16 * n) (12 * n) ?_ ?_
    · simp only [stateSpec, factProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one]
      simpa [Nat.cast_mul, mul_assoc] using orbit_st6 n hn
    · obtain ⟨P', hP'⟩ := rvInt_denom (13 * n) (13 * n) (11 * n) (16 * n) (12 * n)
        (15 * n) (14 * n) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)
      exact ⟨P', _, hP'⟩

private def D_n (n : ℕ) : ℕ :=
  ((List.finRange 7).map (fun i => stateMult n (stateSpec i))).foldr Nat.gcd
    (stateMult n (stateSpec 0))

private lemma D_n_dvd (n : ℕ) (i : Fin 7) : D_n n ∣ stateMult n (stateSpec i) := by
  unfold D_n
  have hmem : stateMult n (stateSpec i) ∈
      (List.finRange 7).map (fun j => stateMult n (stateSpec j)) :=
    List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩
  suffices h : ∀ (l : List ℕ) (b x : ℕ), x ∈ l → l.foldr Nat.gcd b ∣ x from
    h _ _ _ hmem
  intro l b x hx
  induction l with
  | nil => cases hx
  | cons a t ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 hx with rfl | hxt
    · exact Nat.gcd_dvd_left x _
    · exact dvd_trans (Nat.gcd_dvd_right a _) (ih hxt)

private lemma D_n_pos (n : ℕ) : 0 < D_n n := by
  unfold D_n
  suffices h : ∀ (l : List ℕ) (b : ℕ), 0 < b → 0 < l.foldr Nat.gcd b from
    h _ _ (stateMult_pos n (stateSpec 0))
  intro l b hb
  induction l with
  | nil => exact hb
  | cons a t ih =>
    simp only [List.foldr_cons]
    exact Nat.gcd_pos_of_pos_right a ih

private def targetQ (n : ℕ) : ℤ :=
  rvQ (12 * n) (12 * n) (13 * n) (14 * n) (14 * n)

private lemma D_n_linear_form (hirr : Irrational (π ^ 2 / 6)) (n : ℕ) (hn : 1 ≤ n) :
    ∃ P : ℤ, (D_n n : ℝ) * targetI n =
      (P : ℝ) + (((D_n n : ℤ) * targetQ n : ℤ) : ℝ) * (π ^ 2 / 6) := by
  have hcomb : ∀ (a b : ℕ),
      (∃ P1 Q1 : ℤ, (a : ℝ) * targetI n = (P1 : ℝ) + (Q1 : ℝ) * (π ^ 2 / 6)) →
      (∃ P2 Q2 : ℤ, (b : ℝ) * targetI n = (P2 : ℝ) + (Q2 : ℝ) * (π ^ 2 / 6)) →
      ∃ P Q : ℤ, (Nat.gcd a b : ℝ) * targetI n = (P : ℝ) + (Q : ℝ) * (π ^ 2 / 6) := by
    rintro a b ⟨P1, Q1, h1⟩ ⟨P2, Q2, h2⟩
    refine ⟨Int.gcdA (a : ℤ) (b : ℤ) * P1 + Int.gcdB (a : ℤ) (b : ℤ) * P2,
      Int.gcdA (a : ℤ) (b : ℤ) * Q1 + Int.gcdB (a : ℤ) (b : ℤ) * Q2, ?_⟩
    have hbez : ((Nat.gcd a b : ℤ) : ℝ) =
        (a : ℝ) * (Int.gcdA (a : ℤ) (b : ℤ) : ℝ) + (b : ℝ) * (Int.gcdB (a : ℤ) (b : ℤ) : ℝ) := by
      have := Int.gcd_eq_gcd_ab (a : ℤ) (b : ℤ)
      have hcast : ((Int.gcd (a : ℤ) (b : ℤ) : ℕ) : ℤ) = (Nat.gcd a b : ℤ) := by
        simp [Int.gcd_natCast_natCast]
      rw [hcast] at this
      exact_mod_cast this
    push_cast at hbez ⊢
    calc (Nat.gcd a b : ℝ) * targetI n
        = ((a : ℝ) * (Int.gcdA (a : ℤ) (b : ℤ) : ℝ) +
            (b : ℝ) * (Int.gcdB (a : ℤ) (b : ℤ) : ℝ)) * targetI n := by rw [hbez]
      _ = (Int.gcdA (a : ℤ) (b : ℤ) : ℝ) * ((a : ℝ) * targetI n) +
            (Int.gcdB (a : ℤ) (b : ℤ) : ℝ) * ((b : ℝ) * targetI n) := by ring
      _ = (Int.gcdA (a : ℤ) (b : ℤ) : ℝ) * ((P1 : ℝ) + (Q1 : ℝ) * (π ^ 2 / 6)) +
            (Int.gcdB (a : ℤ) (b : ℤ) : ℝ) * ((P2 : ℝ) + (Q2 : ℝ) * (π ^ 2 / 6)) := by rw [h1, h2]
      _ = ((Int.gcdA (a : ℤ) (b : ℤ) : ℝ) * (P1 : ℝ) + (Int.gcdB (a : ℤ) (b : ℤ) : ℝ) * (P2 : ℝ)) +
            ((Int.gcdA (a : ℤ) (b : ℤ) : ℝ) * (Q1 : ℝ) + (Int.gcdB (a : ℤ) (b : ℤ) : ℝ) * (Q2 : ℝ)) *
              (π ^ 2 / 6) := by ring
  have hfold : ∀ (l : List ℕ) (b : ℕ),
      (∀ x ∈ l, ∃ P Q : ℤ, (x : ℝ) * targetI n = (P : ℝ) + (Q : ℝ) * (π ^ 2 / 6)) →
      (∃ P Q : ℤ, (b : ℝ) * targetI n = (P : ℝ) + (Q : ℝ) * (π ^ 2 / 6)) →
      ∃ P Q : ℤ, ((l.foldr Nat.gcd b : ℕ) : ℝ) * targetI n = (P : ℝ) + (Q : ℝ) * (π ^ 2 / 6) := by
    intro l b hl hb
    induction l with
    | nil => exact hb
    | cons a t ih =>
      simp only [List.foldr_cons]
      exact hcomb a (t.foldr Nat.gcd b) (hl a List.mem_cons_self)
        (ih fun x hx => hl x (List.mem_cons_of_mem a hx))
  obtain ⟨P, Q, hPQ⟩ := hfold ((List.finRange 7).map (fun i => stateMult n (stateSpec i)))
    (stateMult n (stateSpec 0))
    (fun x hx => by
      rcases List.mem_map.1 hx with ⟨i, _, rfl⟩
      exact stateMult_linear_form n hn i)
    (stateMult_linear_form n hn 0)
  change (D_n n : ℝ) * targetI n = (P : ℝ) + (Q : ℝ) * (π ^ 2 / 6) at hPQ
  obtain ⟨P0, hP0⟩ := rvInt_denom (12 * n) (12 * n) (13 * n) (14 * n) (14 * n)
    (16 * n) (15 * n) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [← orbit_st0 n hn] at hP0
  set L0 : ℕ := Nat.lcmUpto (16 * n) * Nat.lcmUpto (15 * n)
  have hL0_pos : 0 < L0 := Nat.mul_pos (Nat.lcmUpto_pos _) (Nat.lcmUpto_pos _)
  have hcmp : (((L0 : ℤ) * P : ℤ) : ℝ) + (((L0 : ℤ) * Q : ℤ) : ℝ) * (π ^ 2 / 6) =
      (((D_n n : ℤ) * P0 : ℤ) : ℝ) +
        (((D_n n : ℤ) * ((L0 : ℤ) * targetQ n) : ℤ) : ℝ) * (π ^ 2 / 6) := by
    have h1 : (L0 : ℝ) * ((D_n n : ℝ) * targetI n) = (D_n n : ℝ) * ((L0 : ℝ) * targetI n) := by ring
    rw [hPQ, hP0] at h1
    unfold targetQ
    push_cast at h1 ⊢
    linarith
  have hQeq : (L0 : ℤ) * Q = (D_n n : ℤ) * ((L0 : ℤ) * targetQ n) :=
    (linear_form_unique_of_irrational hirr hcmp).2
  have hQ : Q = (D_n n : ℤ) * targetQ n := by
    have hL0z : (L0 : ℤ) ≠ 0 := Int.natCast_ne_zero.2 hL0_pos.ne'
    apply mul_left_cancel₀ hL0z
    linarith
  exact ⟨P, hQ ▸ hPQ⟩

/- ### Section 5: Bound on |targetQ n| -/

private lemma targetQ_abs_le (n : ℕ) :
    |(targetQ n : ℝ)| ≤ ((12 * n + 1 : ℕ) : ℝ) * ((3 ^ 12 * 2 ^ 25 : ℕ) : ℝ) ^ n := by
  unfold targetQ rvQ
  have hm : 12 * n + 13 * n - 14 * n = 11 * n := by omega
  simp only [hm]
  have hcast_lhs :
      (((((-1 : ℤ) ^ (11 * n) *
        ∑ a ∈ range (12 * n + 1), ∑ b ∈ range (13 * n + 1),
          if 12 * n + a - 11 * n = 14 * n - 11 * n + b then
            ((-1 : ℤ) ^ a * ((12 * n).choose a : ℤ) * ((12 * n + a).choose (11 * n) : ℤ)) *
            ((-1 : ℤ) ^ b * ((13 * n).choose b : ℤ))
          else 0) : ℤ) : ℝ)) =
      (-1 : ℝ) ^ (11 * n) *
        ∑ a ∈ range (12 * n + 1), ∑ b ∈ range (13 * n + 1),
          if 12 * n + a - 11 * n = 14 * n - 11 * n + b then
            ((-1 : ℝ) ^ a * ((12 * n).choose a : ℝ) * ((12 * n + a).choose (11 * n) : ℝ)) *
            ((-1 : ℝ) ^ b * ((13 * n).choose b : ℝ))
          else 0 := by
    push_cast
    refine congrArg _ (sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_)
    split_ifs <;> rfl
  rw [hcast_lhs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  calc |∑ a ∈ range (12 * n + 1), ∑ b ∈ range (13 * n + 1),
          if 12 * n + a - 11 * n = 14 * n - 11 * n + b then
            ((-1 : ℝ) ^ a * ((12 * n).choose a : ℝ) * ((12 * n + a).choose (11 * n) : ℝ)) *
            ((-1 : ℝ) ^ b * ((13 * n).choose b : ℝ))
          else 0|
      ≤ ∑ a ∈ range (12 * n + 1), |∑ b ∈ range (13 * n + 1),
          if 12 * n + a - 11 * n = 14 * n - 11 * n + b then
            ((-1 : ℝ) ^ a * ((12 * n).choose a : ℝ) * ((12 * n + a).choose (11 * n) : ℝ)) *
            ((-1 : ℝ) ^ b * ((13 * n).choose b : ℝ))
          else 0| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ range (12 * n + 1), ((3 ^ 12 * 2 ^ 25 : ℕ) : ℝ) ^ n := by
        refine sum_le_sum fun a ha => ?_
        have ha_le : a ≤ 12 * n := Nat.lt_succ_iff.1 (mem_range.1 ha)
        by_cases hge : 2 * n ≤ a
        · have huniq : ∑ b ∈ range (13 * n + 1),
              (if 12 * n + a - 11 * n = 14 * n - 11 * n + b then
                ((-1 : ℝ) ^ a * ((12 * n).choose a : ℝ) * ((12 * n + a).choose (11 * n) : ℝ)) *
                ((-1 : ℝ) ^ b * ((13 * n).choose b : ℝ))
              else 0) =
              ((-1 : ℝ) ^ a * ((12 * n).choose a : ℝ) * ((12 * n + a).choose (11 * n) : ℝ)) *
              ((-1 : ℝ) ^ (a - 2 * n) * ((13 * n).choose (a - 2 * n) : ℝ)) := by
            rw [Finset.sum_eq_single (a - 2 * n)]
            · rw [if_pos (by omega)]
            · intro b _ hbne
              rw [if_neg (by omega)]
            · intro hnot
              exfalso; apply hnot; rw [mem_range]; omega
          rw [huniq]
          rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_pow, abs_pow, abs_neg, abs_one,
              one_pow, one_pow, one_mul, one_mul,
              abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _),
              abs_of_nonneg (Nat.cast_nonneg _)]
          have hch1 : ((12 * n + a).choose (11 * n) : ℝ) ≤ (2 : ℝ) ^ (12 * n + a) := by
            exact_mod_cast Nat.choose_le_two_pow (12 * n + a) (11 * n)
          have hch2 : ((13 * n).choose (a - 2 * n) : ℝ) ≤ (2 : ℝ) ^ (13 * n) := by
            exact_mod_cast Nat.choose_le_two_pow (13 * n) (a - 2 * n)
          have hch0 : ((12 * n).choose a : ℝ) * (2 : ℝ) ^ a ≤ (3 : ℝ) ^ (12 * n) := by
            have hbin : (3 : ℝ) ^ (12 * n) =
                ∑ k ∈ range (12 * n + 1), ((12 * n).choose k : ℝ) * (2 : ℝ) ^ k := by
              rw [show (3 : ℝ) = 2 + 1 by norm_num, add_pow]
              refine sum_congr rfl fun k _ => by rw [one_pow, mul_one]; ring
            rw [hbin]
            exact Finset.single_le_sum
              (f := fun k : ℕ => ((12 * n).choose k : ℝ) * (2 : ℝ) ^ k)
              (fun k _ => by positivity) (mem_range.2 (by omega))
          calc ((12 * n).choose a : ℝ) * ((12 * n + a).choose (11 * n) : ℝ) *
                ((13 * n).choose (a - 2 * n) : ℝ)
              ≤ ((12 * n).choose a : ℝ) * (2 : ℝ) ^ (12 * n + a) * (2 : ℝ) ^ (13 * n) := by
                gcongr
            _ = (((12 * n).choose a : ℝ) * (2 : ℝ) ^ a) * (2 : ℝ) ^ (25 * n) := by
                rw [pow_add, show 25 * n = 12 * n + 13 * n by omega, pow_add]; ring
            _ ≤ (3 : ℝ) ^ (12 * n) * (2 : ℝ) ^ (25 * n) := by gcongr
            _ = ((3 ^ 12 * 2 ^ 25 : ℕ) : ℝ) ^ n := by
                rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_ofNat,
                    mul_pow, ← pow_mul, ← pow_mul]
        · have hzero : ∑ b ∈ range (13 * n + 1),
              (if 12 * n + a - 11 * n = 14 * n - 11 * n + b then
                ((-1 : ℝ) ^ a * ((12 * n).choose a : ℝ) * ((12 * n + a).choose (11 * n) : ℝ)) *
                ((-1 : ℝ) ^ b * ((13 * n).choose b : ℝ))
              else 0) = 0 := by
            refine sum_eq_zero fun b _ => if_neg (by omega)
          rw [hzero, abs_zero]
          positivity
    _ = ((12 * n + 1 : ℕ) : ℝ) * ((3 ^ 12 * 2 ^ 25 : ℕ) : ℝ) ^ n := by
        rw [sum_const, card_range, nsmul_eq_mul]

private lemma targetQ_eventually_le :
    ∀ᶠ n : ℕ in atTop, |(targetQ n : ℝ)| ≤ (32768 : ℝ) ^ (3 * n) := by
  have hratio : ((3 ^ 12 * 2 ^ 25 : ℕ) : ℝ) / (32768 : ℝ) ^ 3 < 3 / 5 := by norm_num
  have htend : Tendsto (fun n : ℕ => ((12 * n + 1 : ℕ) : ℝ) * ((3 / 5 : ℝ) ^ n)) atTop (𝓝 0) := by
    have h1 := (tendsto_self_mul_const_pow_of_lt_one (show (0 : ℝ) ≤ 3 / 5 by norm_num)
      (show (3 / 5 : ℝ) < 1 by norm_num)).const_mul (12 : ℝ)
    have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one (show (0 : ℝ) ≤ 3 / 5 by norm_num)
      (show (3 / 5 : ℝ) < 1 by norm_num)
    have hsum := h1.add h2
    simp only [mul_zero, add_zero] at hsum
    refine hsum.congr fun n => ?_
    push_cast; ring
  filter_upwards [htend.eventually (gt_mem_nhds zero_lt_one)] with n hn
  have h1 := targetQ_abs_le n
  have hpos : (0 : ℝ) < (32768 : ℝ) ^ (3 * n) := by positivity
  rw [← div_le_one hpos]
  calc |(targetQ n : ℝ)| / (32768 : ℝ) ^ (3 * n)
      ≤ ((12 * n + 1 : ℕ) : ℝ) * ((3 ^ 12 * 2 ^ 25 : ℕ) : ℝ) ^ n / (32768 : ℝ) ^ (3 * n) := by
        gcongr
    _ = ((12 * n + 1 : ℕ) : ℝ) * (((3 ^ 12 * 2 ^ 25 : ℕ) : ℝ) / (32768 : ℝ) ^ 3) ^ n := by
        rw [div_pow, ← pow_mul]; ring
    _ ≤ ((12 * n + 1 : ℕ) : ℝ) * (3 / 5 : ℝ) ^ n := by
        gcongr
    _ ≤ 1 := hn.le

/- ### Section 6: Prime Valuations, Decidable Interval Checker, and PNT Bound on D_n -/

private lemma padicValNat_gcd {p a b : ℕ} [Fact p.Prime] (ha : a ≠ 0) (hb : b ≠ 0) :
    padicValNat p (Nat.gcd a b) = min (padicValNat p a) (padicValNat p b) := by
  have hg : Nat.gcd a b ≠ 0 := (Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha)).ne'
  refine le_antisymm ?_ ?_
  · rw [le_min_iff]
    exact ⟨((padicValNat_dvd_iff _ a).1 (dvd_trans pow_padicValNat_dvd (Nat.gcd_dvd_left a b))).resolve_left ha,
      ((padicValNat_dvd_iff _ b).1 (dvd_trans pow_padicValNat_dvd (Nat.gcd_dvd_right a b))).resolve_left hb⟩
  · have h1 : p ^ min (padicValNat p a) (padicValNat p b) ∣ a :=
      (padicValNat_dvd_iff _ a).2 (Or.inr (min_le_left _ _))
    have h2 : p ^ min (padicValNat p a) (padicValNat p b) ∣ b :=
      (padicValNat_dvd_iff _ b).2 (Or.inr (min_le_right _ _))
    exact ((padicValNat_dvd_iff _ (Nat.gcd a b)).1 (Nat.dvd_gcd h1 h2)).resolve_left hg

private lemma padicValNat_div_gcd {p a b : ℕ} [Fact p.Prime] (ha : a ≠ 0) (hb : b ≠ 0) :
    padicValNat p (a / Nat.gcd a b) = padicValNat p a - padicValNat p b := by
  rw [padicValNat.div_of_dvd (Nat.gcd_dvd_left a b), padicValNat_gcd ha hb]
  omega

private lemma padicValNat_lcm_finset_dvd {p e : ℕ} [hp : Fact p.Prime] {s : Finset ℕ}
    (hs : ∀ x ∈ s, x ≠ 0) (he : 1 ≤ e) (hdvd : p ^ e ∣ s.lcm id) :
    ∃ x ∈ s, p ^ e ∣ x := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.lcm_empty] at hdvd
    have h1 : p ^ e ≤ 1 := Nat.le_of_dvd zero_lt_one hdvd
    have h2 : 2 ≤ p ^ e := le_trans hp.out.two_le (Nat.le_self_pow (by omega) p)
    omega
  | insert a t hat ih =>
    have ha0 : a ≠ 0 := hs a (mem_insert_self a t)
    have ht0 : ∀ x ∈ t, x ≠ 0 := fun x hx => hs x (mem_insert_of_mem hx)
    have htlcm0 : t.lcm id ≠ 0 := by
      intro h0
      rcases Finset.lcm_eq_zero_iff.1 h0 with ⟨x, hx, hx0⟩
      exact ht0 x hx hx0
    rw [Finset.lcm_insert] at hdvd
    have hle : e ≤ (Nat.lcm a (t.lcm id)).factorization p := by
      rw [Nat.factorization_def _ hp.out]
      exact ((padicValNat_dvd_iff e _).1 hdvd).resolve_left (Nat.lcm_ne_zero ha0 htlcm0)
    rw [Nat.factorization_lcm ha0 htlcm0, Finsupp.sup_apply] at hle
    rcases le_sup_iff.1 hle with h1 | h2
    · refine ⟨a, mem_insert_self a t, ?_⟩
      rw [Nat.factorization_def _ hp.out] at h1
      exact (padicValNat_dvd_iff e a).2 (Or.inr h1)
    · rw [Nat.factorization_def _ hp.out] at h2
      have hd2 : p ^ e ∣ t.lcm id := (padicValNat_dvd_iff e _).2 (Or.inr h2)
      obtain ⟨x, hxt, hxd⟩ := ih ht0 hd2
      exact ⟨x, mem_insert_of_mem hxt, hxd⟩

private lemma padicValNat_lcmUpto_le_one {p M : ℕ} [hp : Fact p.Prime] (hsq : M < p ^ 2) :
    padicValNat p (Nat.lcmUpto M) ≤ 1 := by
  by_contra h
  push Not at h
  have hdvd : p ^ 2 ∣ Nat.lcmUpto M := (padicValNat_dvd_iff 2 _).2 (Or.inr h)
  obtain ⟨k, hk, hkd⟩ := padicValNat_lcm_finset_dvd
    (fun x hx => by simp only [mem_Icc] at hx; omega) (by omega) hdvd
  simp only [mem_Icc] at hk
  have hle : p ^ 2 ≤ k := Nat.le_of_dvd (by omega) hkd
  omega

private lemma padicValNat_lcmUpto_eq_one {p M : ℕ} [hp : Fact p.Prime]
    (hpM : p ≤ M) (hsq : M < p ^ 2) :
    padicValNat p (Nat.lcmUpto M) = 1 := by
  have hle := padicValNat_lcmUpto_le_one (p := p) hsq
  have hdvd : p ^ 1 ∣ Nat.lcmUpto M := by
    rw [pow_one]
    exact Finset.dvd_lcm (mem_Icc.2 ⟨hp.out.one_le, hpM⟩)
  have hge : 1 ≤ padicValNat p (Nat.lcmUpto M) :=
    ((padicValNat_dvd_iff 1 _).1 hdvd).resolve_left (Nat.lcmUpto_pos M).ne'
  omega

private lemma padicValNat_lcmUpto_eq_zero {p M : ℕ} [hp : Fact p.Prime] (hMp : M < p) :
    padicValNat p (Nat.lcmUpto M) = 0 := by
  by_contra h
  have hge : 1 ≤ padicValNat p (Nat.lcmUpto M) := Nat.one_le_iff_ne_zero.2 h
  have hdvd : p ^ 1 ∣ Nat.lcmUpto M := (padicValNat_dvd_iff 1 _).2 (Or.inr hge)
  obtain ⟨k, hk, hkd⟩ := padicValNat_lcm_finset_dvd
    (fun x hx => by simp only [mem_Icc] at hx; omega) le_rfl hdvd
  simp only [mem_Icc] at hk
  rw [pow_one] at hkd
  have hle : p ≤ k := Nat.le_of_dvd (by omega) hkd
  omega

private lemma padicValNat_factorial_of_sq_gt {p M : ℕ} [hp : Fact p.Prime] (hsq : M < p ^ 2) :
    padicValNat p M ! = M / p := by
  have hlog : Nat.log p M < 2 := by
    by_cases hM : M = 0
    · subst hM; simp
    · exact (Nat.log_lt_iff_lt_pow hp.out.one_lt hM).2 hsq
  rw [padicValNat_factorial hlog]
  have hico : Finset.Ico 1 2 = {1} := by decide
  rw [hico, Finset.sum_singleton, pow_one]

private lemma padicValNat_factProd {p n : ℕ} [Fact p.Prime] (cs : List ℕ) :
    padicValNat p (factProd n cs) = (cs.map (fun c => padicValNat p (c * n)!)).sum := by
  induction cs with
  | nil => simp [factProd]
  | cons c t ih =>
    have hcons : factProd n (c :: t) = (c * n)! * factProd n t := by
      simp [factProd]
    rw [hcons, List.map_cons, List.sum_cons,
        padicValNat.mul (Nat.factorial_ne_zero _) (factProd_pos n t).ne', ih]

private lemma log_eq_sum_padicValNat {N M : ℕ} (hN : 0 < N)
    (hpf : ∀ p ∈ N.primeFactors, p ≤ M) :
    Real.log (N : ℝ) =
      ∑ p ∈ (Icc 1 M).filter Nat.Prime, (padicValNat p N : ℝ) * Real.log (p : ℝ) := by
  have hprod : (N : ℝ) = ∏ p ∈ N.primeFactors, (p : ℝ) ^ (padicValNat p N) := by
    have h1 := Nat.prod_factorization_pow_eq_self hN.ne'
    rw [Finsupp.prod, Nat.support_factorization] at h1
    have h2 : ∏ p ∈ N.primeFactors, p ^ (N.factorization p) =
        ∏ p ∈ N.primeFactors, p ^ (padicValNat p N) := by
      refine prod_congr rfl fun p hp => ?_
      rw [Nat.factorization_def N (Nat.prime_of_mem_primeFactors hp)]
    rw [h2] at h1
    exact_mod_cast h1.symm
  rw [hprod, Real.log_prod (fun p hp => by
    have hpos : 0 < p := (Nat.prime_of_mem_primeFactors hp).pos
    positivity)]
  simp_rw [Real.log_pow]
  refine sum_subset ?_ ?_
  · intro p hp
    simp only [mem_filter, mem_Icc]
    have hpr := Nat.prime_of_mem_primeFactors hp
    exact ⟨⟨hpr.one_le, hpf p hp⟩, hpr⟩
  · intro p hp hnot
    simp only [mem_filter, mem_Icc] at hp
    have : Fact p.Prime := ⟨hp.2⟩
    have hndvd : ¬ p ∣ N := fun hd => hnot (Nat.mem_primeFactors.2 ⟨hp.2, hd, hN.ne'⟩)
    rw [padicValNat.eq_zero_of_not_dvd hndvd, Nat.cast_zero, zero_mul]

private structure IvSpec where
  aNum : ℕ
  aDen : ℕ
  bNum : ℕ
  bDen : ℕ
  sav : ℕ
  sid : Fin 7

private def checkIv (iv : IvSpec) : Bool :=
  let s := stateSpec iv.sid
  (0 < iv.aNum) && (0 < iv.aDen) && (0 < iv.bNum) && (0 < iv.bDen) &&
  (iv.aNum * iv.bDen < iv.bNum * iv.aDen) &&
  (iv.bNum ≤ 2 * iv.bDen) &&
  (iv.aDen ≤ 16 * iv.aNum) &&
  (s.M1 ≤ 16) && (s.M2 ≤ 16) &&
  ((s.pos ++ s.neg).all (fun c => c ≤ 16 && c * iv.bNum ≤ ((c * iv.aNum) / iv.aDen + 1) * iv.bDen)) &&
  (let baseLo := (if iv.aDen ≤ 16 * iv.aNum then 1 else 0) +
                 (if iv.aDen ≤ 15 * iv.aNum then 1 else 0)
   let mHi := (if s.M1 * iv.bNum ≤ iv.bDen then 0 else 1) +
              (if s.M2 * iv.bNum ≤ iv.bDen then 0 else 1)
   let posSum := (s.pos.map (fun c => (c * iv.aNum) / iv.aDen)).sum
   let negSum := (s.neg.map (fun c => (c * iv.aNum) / iv.aDen)).sum
   decide (iv.sav + ((mHi + negSum) - posSum) ≤ baseLo))

private def checkDisjoint : List IvSpec → Bool
  | [] => true
  | [_] => true
  | iv1 :: iv2 :: rest =>
      decide (iv1.bNum * iv2.aDen ≤ iv2.aNum * iv1.bDen) && checkDisjoint (iv2 :: rest)

private def chosenIvs : List IvSpec :=
  [ ⟨1, 14, 1, 13, 1, 2⟩,
    ⟨1, 13, 1, 12, 1, 3⟩,
    ⟨1, 12, 1, 11, 2, 1⟩,
    ⟨1, 11, 1, 10, 1, 1⟩,
    ⟨1, 7, 2, 13, 1, 2⟩,
    ⟨2, 13, 1, 6, 1, 3⟩,
    ⟨1, 6, 2, 11, 2, 1⟩,
    ⟨2, 11, 3, 16, 1, 1⟩,
    ⟨3, 16, 1, 5, 1, 5⟩,
    ⟨3, 14, 3, 13, 1, 2⟩,
    ⟨3, 13, 1, 4, 1, 3⟩,
    ⟨1, 4, 3, 11, 1, 1⟩,
    ⟨2, 7, 4, 13, 1, 2⟩,
    ⟨4, 13, 5, 16, 1, 3⟩,
    ⟨1, 3, 5, 14, 1, 1⟩,
    ⟨5, 14, 4, 11, 2, 6⟩,
    ⟨4, 11, 5, 13, 1, 2⟩,
    ⟨5, 13, 2, 5, 1, 5⟩,
    ⟨5, 12, 3, 7, 1, 1⟩,
    ⟨3, 7, 7, 16, 2, 6⟩,
    ⟨7, 16, 6, 13, 1, 2⟩,
    ⟨6, 13, 7, 15, 1, 5⟩,
    ⟨1, 2, 8, 15, 1, 2⟩,
    ⟨8, 15, 7, 13, 1, 4⟩,
    ⟨7, 13, 6, 11, 1, 1⟩,
    ⟨4, 7, 7, 12, 1, 2⟩,
    ⟨7, 12, 3, 5, 1, 1⟩,
    ⟨3, 5, 8, 13, 1, 4⟩,
    ⟨8, 13, 5, 8, 1, 1⟩,
    ⟨9, 14, 2, 3, 1, 2⟩,
    ⟨2, 3, 11, 16, 1, 1⟩,
    ⟨9, 13, 7, 10, 1, 1⟩,
    ⟨5, 7, 11, 15, 1, 2⟩,
    ⟨3, 4, 10, 13, 1, 4⟩,
    ⟨10, 13, 4, 5, 1, 1⟩,
    ⟨4, 5, 13, 16, 1, 3⟩,
    ⟨5, 6, 11, 13, 1, 4⟩,
    ⟨11, 13, 7, 8, 1, 1⟩,
    ⟨12, 13, 15, 16, 1, 1⟩,
    ⟨13, 12, 12, 11, 2, 1⟩,
    ⟨7, 6, 13, 11, 2, 1⟩,
    ⟨16, 13, 5, 4, 1, 3⟩,
    ⟨5, 4, 14, 11, 1, 1⟩,
    ⟨9, 7, 17, 13, 1, 2⟩,
    ⟨4, 3, 19, 14, 1, 1⟩,
    ⟨3, 2, 23, 15, 1, 2⟩ ]

private lemma chosenIvs_valid : chosenIvs.all checkIv = true := by decide

private lemma chosenIvs_disjoint : checkDisjoint chosenIvs = true := by decide

private def totalSavingRat : ℚ :=
  (chosenIvs.map (fun iv =>
    (iv.sav : ℚ) * ((iv.aDen : ℚ) / (iv.aNum : ℚ) - (iv.bDen : ℚ) / (iv.bNum : ℚ)))).sum

private def savingCommonDen : ℕ := 5354228880

private def totalSavingNat : ℕ :=
  (chosenIvs.map (fun iv =>
    iv.sav * (iv.aDen * (savingCommonDen / iv.aNum) - iv.bDen * (savingCommonDen / iv.bNum)))).sum

private lemma chosenIvs_dvd_commonDen :
    chosenIvs.all (fun iv =>
      decide (iv.aNum ∣ savingCommonDen ∧ iv.bNum ∣ savingCommonDen ∧
        iv.bDen * (savingCommonDen / iv.bNum) ≤ iv.aDen * (savingCommonDen / iv.aNum))) = true := by
  decide

private lemma totalSavingNat_gt : 104 * (savingCommonDen / 10) < totalSavingNat := by decide

private lemma totalSavingRat_gt : (104 : ℚ) / 10 < totalSavingRat := by
  have heq : (totalSavingNat : ℚ) = (savingCommonDen : ℚ) * totalSavingRat := by
    unfold totalSavingNat totalSavingRat
    suffices h : ∀ (l : List IvSpec),
        l.all checkIv = true →
        l.all (fun iv =>
          decide (iv.aNum ∣ savingCommonDen ∧ iv.bNum ∣ savingCommonDen ∧
            iv.bDen * (savingCommonDen / iv.bNum) ≤ iv.aDen * (savingCommonDen / iv.aNum))) = true →
        ((l.map (fun iv =>
          iv.sav * (iv.aDen * (savingCommonDen / iv.aNum) - iv.bDen * (savingCommonDen / iv.bNum)))).sum : ℚ) =
        (savingCommonDen : ℚ) * (l.map (fun iv =>
          (iv.sav : ℚ) * ((iv.aDen : ℚ) / (iv.aNum : ℚ) - (iv.bDen : ℚ) / (iv.bNum : ℚ)))).sum from
      h chosenIvs chosenIvs_valid chosenIvs_dvd_commonDen
    intro l
    induction l with
    | nil => intro _ _; simp
    | cons iv t ih =>
      intro hv hd
      rw [List.all_cons, Bool.and_eq_true] at hv hd
      simp only [List.map_cons, List.sum_cons, Nat.cast_add, mul_add]
      rw [ih hv.2 hd.2]
      congr 1
      have hvc := hv.1
      unfold checkIv at hvc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hvc
      have hdc := hd.1
      simp only [decide_eq_true_eq] at hdc
      obtain ⟨hd1, hd2, hsub⟩ := hdc
      have haN0 : (iv.aNum : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hvc.1.1.1.1.1.1.1.1.1.1.ne'
      have hbN0 : (iv.bNum : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hvc.1.1.1.1.1.1.1.1.2.ne'
      have hdiv1 : ((savingCommonDen / iv.aNum : ℕ) : ℚ) = (savingCommonDen : ℚ) / (iv.aNum : ℚ) :=
        Nat.cast_div hd1 haN0
      have hdiv2 : ((savingCommonDen / iv.bNum : ℕ) : ℚ) = (savingCommonDen : ℚ) / (iv.bNum : ℚ) :=
        Nat.cast_div hd2 hbN0
      rw [Nat.cast_mul, Nat.cast_sub hsub, Nat.cast_mul, Nat.cast_mul, hdiv1, hdiv2]
      ring
  have hgt_q : ((104 * (savingCommonDen / 10) : ℕ) : ℚ) < (totalSavingNat : ℚ) := by
    exact_mod_cast totalSavingNat_gt
  have h10 : ((104 * (savingCommonDen / 10) : ℕ) : ℚ) = (savingCommonDen : ℚ) * ((104 : ℚ) / 10) := by
    norm_num [savingCommonDen]
  rw [h10, heq] at hgt_q
  exact lt_of_mul_lt_mul_left hgt_q (by norm_num [savingCommonDen])

private lemma checkIv_sound {iv : IvSpec} (hc : checkIv iv = true) {n p : ℕ}
    [hp : Fact p.Prime] (hn : 65 ≤ n)
    (hlo : iv.bDen * n < iv.bNum * p) (hhi : iv.aNum * p ≤ iv.aDen * n) :
    padicValNat p (D_n n) + iv.sav ≤ padicValNat p (stateMult n (stateSpec 0)) := by
  unfold checkIv at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨haN, haD⟩, hbN⟩, hbD⟩, hab⟩, hb2⟩, ha16⟩, hM1⟩, hM2⟩, hcs⟩, hsav⟩ := hc
  set s := stateSpec iv.sid
  have hsq16 : 16 * n < p ^ 2 := by
    have h2p : n < 2 * p := by
      have : iv.bDen * n < 2 * iv.bDen * p := by
        calc iv.bDen * n < iv.bNum * p := hlo
          _ ≤ (2 * iv.bDen) * p := Nat.mul_le_mul_right p hb2
          _ = 2 * iv.bDen * p := by ring
      have : iv.bDen * n < iv.bDen * (2 * p) := by linarith
      exact Nat.lt_of_mul_lt_mul_left this
    nlinarith
  have hdvd0 : padicValNat p (D_n n) ≤ padicValNat p (stateMult n s) := by
    have h := D_n_dvd n iv.sid
    exact ((padicValNat_dvd_iff _ _).1
      (dvd_trans pow_padicValNat_dvd h)).resolve_left (stateMult_pos n s).ne'
  have hbase_le : (if iv.aDen ≤ 16 * iv.aNum then 1 else 0) +
      (if iv.aDen ≤ 15 * iv.aNum then 1 else 0) ≤
      padicValNat p (stateMult n (stateSpec 0)) := by
    have hst0 : stateMult n (stateSpec 0) = Nat.lcmUpto (16 * n) * Nat.lcmUpto (15 * n) := by
      simp [stateMult, stateSpec, factProd]
    rw [hst0, padicValNat.mul (Nat.lcmUpto_pos _).ne' (Nat.lcmUpto_pos _).ne']
    have h16 : (if iv.aDen ≤ 16 * iv.aNum then 1 else 0) ≤ padicValNat p (Nat.lcmUpto (16 * n)) := by
      rw [if_pos ha16]
      have hp16 : p ≤ 16 * n := by
        have : iv.aNum * p ≤ iv.aNum * (16 * n) := by
          calc iv.aNum * p ≤ iv.aDen * n := hhi
            _ ≤ (16 * iv.aNum) * n := Nat.mul_le_mul_right n ha16
            _ = iv.aNum * (16 * n) := by ring
        exact Nat.le_of_mul_le_mul_left this haN
      rw [padicValNat_lcmUpto_eq_one hp16 hsq16]
    have h15 : (if iv.aDen ≤ 15 * iv.aNum then 1 else 0) ≤ padicValNat p (Nat.lcmUpto (15 * n)) := by
      split_ifs with h15'
      · have hp15 : p ≤ 15 * n := by
          have : iv.aNum * p ≤ iv.aNum * (15 * n) := by
            calc iv.aNum * p ≤ iv.aDen * n := hhi
              _ ≤ (15 * iv.aNum) * n := Nat.mul_le_mul_right n h15'
              _ = iv.aNum * (15 * n) := by ring
          exact Nat.le_of_mul_le_mul_left this haN
        rw [padicValNat_lcmUpto_eq_one hp15 (by omega)]
      · exact Nat.zero_le _
    omega
  have hdiv_eq : ∀ c ∈ s.pos ++ s.neg, padicValNat p (c * n)! = (c * iv.aNum) / iv.aDen := by
    intro c hc_mem
    have hc_info := hcs c hc_mem
    obtain ⟨hc16, hcb⟩ := hc_info
    have hcsq : c * n < p ^ 2 := by
      have : c * n ≤ 16 * n := Nat.mul_le_mul_right n hc16
      omega
    rw [padicValNat_factorial_of_sq_gt hcsq]
    set k := (c * iv.aNum) / iv.aDen
    have hge : k * p ≤ c * n := by
      have hk1 : k * iv.aDen ≤ c * iv.aNum := Nat.div_mul_le_self (c * iv.aNum) iv.aDen
      have : iv.aDen * (k * p) ≤ iv.aDen * (c * n) := by
        calc iv.aDen * (k * p) = (k * iv.aDen) * p := by ring
          _ ≤ (c * iv.aNum) * p := Nat.mul_le_mul_right p hk1
          _ = c * (iv.aNum * p) := by ring
          _ ≤ c * (iv.aDen * n) := Nat.mul_le_mul_left c hhi
          _ = iv.aDen * (c * n) := by ring
      exact Nat.le_of_mul_le_mul_left this haD
    have hlt : c * n < (k + 1) * p := by
      rcases eq_or_ne c 0 with rfl | hc0
      · have := hp.out.pos; nlinarith
      · have : iv.bDen * (c * n) < iv.bDen * ((k + 1) * p) := by
          calc iv.bDen * (c * n) = c * (iv.bDen * n) := by ring
            _ < c * (iv.bNum * p) := Nat.mul_lt_mul_of_pos_left hlo (Nat.pos_of_ne_zero hc0)
            _ = (c * iv.bNum) * p := by ring
            _ ≤ ((k + 1) * iv.bDen) * p := Nat.mul_le_mul_right p hcb
            _ = iv.bDen * ((k + 1) * p) := by ring
        exact Nat.lt_of_mul_lt_mul_left this
    have h1 : k ≤ c * n / p := (Nat.le_div_iff_mul_le hp.out.pos).2 hge
    have h2 : c * n / p < k + 1 := (Nat.div_lt_iff_lt_mul hp.out.pos).2 hlt
    omega
  have hpos_eq : padicValNat p (factProd n s.pos) =
      (s.pos.map (fun c => (c * iv.aNum) / iv.aDen)).sum := by
    rw [padicValNat_factProd]
    congr 1
    exact List.map_congr_left fun c hc => hdiv_eq c (List.mem_append_left s.neg hc)
  have hneg_eq : padicValNat p (factProd n s.neg) =
      (s.neg.map (fun c => (c * iv.aNum) / iv.aDen)).sum := by
    rw [padicValNat_factProd]
    congr 1
    exact List.map_congr_left fun c hc => hdiv_eq c (List.mem_append_right s.pos hc)
  have hM_le : ∀ M : ℕ, M ≤ 16 →
      padicValNat p (Nat.lcmUpto (M * n)) ≤ if M * iv.bNum ≤ iv.bDen then 0 else 1 := by
    intro M hM
    have hMsq : M * n < p ^ 2 := by
      have : M * n ≤ 16 * n := Nat.mul_le_mul_right n hM
      omega
    split_ifs with hMb
    · rcases eq_or_ne M 0 with rfl | hM0
      · simp [Nat.lcmUpto]
      · have hMlt : M * n < p := by
          have : iv.bDen * (M * n) < iv.bDen * p := by
            calc iv.bDen * (M * n) = M * (iv.bDen * n) := by ring
              _ < M * (iv.bNum * p) := Nat.mul_lt_mul_of_pos_left hlo (Nat.pos_of_ne_zero hM0)
              _ = (M * iv.bNum) * p := by ring
              _ ≤ iv.bDen * p := Nat.mul_le_mul_right p hMb
          exact Nat.lt_of_mul_lt_mul_left this
        rw [padicValNat_lcmUpto_eq_zero hMlt]
    · exact padicValNat_lcmUpto_le_one hMsq
  have hs_val : padicValNat p (stateMult n s) ≤
      ((if s.M1 * iv.bNum ≤ iv.bDen then 0 else 1) +
       (if s.M2 * iv.bNum ≤ iv.bDen then 0 else 1) +
       (s.neg.map (fun c => (c * iv.aNum) / iv.aDen)).sum) -
       (s.pos.map (fun c => (c * iv.aNum) / iv.aDen)).sum := by
    unfold stateMult
    have hX0 : factProd n s.neg * (Nat.lcmUpto (s.M1 * n) * Nat.lcmUpto (s.M2 * n)) ≠ 0 :=
      (Nat.mul_pos (factProd_pos _ _) (Nat.mul_pos (Nat.lcmUpto_pos _) (Nat.lcmUpto_pos _))).ne'
    rw [padicValNat_div_gcd hX0 (factProd_pos n s.pos).ne',
        padicValNat.mul (factProd_pos _ _).ne' (Nat.mul_pos (Nat.lcmUpto_pos _) (Nat.lcmUpto_pos _)).ne',
        padicValNat.mul (Nat.lcmUpto_pos _).ne' (Nat.lcmUpto_pos _).ne',
        hpos_eq, hneg_eq]
    have hm1 := hM_le s.M1 hM1
    have hm2 := hM_le s.M2 hM2
    omega
  omega

private lemma sum_log_primes_interval (n aNum aDen bNum bDen : ℕ)
    (haN : 0 < aNum) (haD : 0 < aDen) (hbN : 0 < bNum) (hbD : 0 < bDen)
    (hle : aNum * bDen ≤ bNum * aDen) (hmax : aDen ≤ 16 * aNum) :
    ∑ p ∈ ((Icc 1 (16 * n)).filter Nat.Prime).filter
        (fun p => bDen * n < bNum * p ∧ aNum * p ≤ aDen * n), Real.log (p : ℝ) =
      Chebyshev.theta ((n : ℝ) * (aDen : ℝ) / (aNum : ℝ)) -
      Chebyshev.theta ((n : ℝ) * (bDen : ℝ) / (bNum : ℝ)) := by
  rw [Chebyshev.theta_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc]
  set x1 : ℝ := (n : ℝ) * (bDen : ℝ) / (bNum : ℝ)
  set x2 : ℝ := (n : ℝ) * (aDen : ℝ) / (aNum : ℝ)
  have hx1_nn : 0 ≤ x1 := by positivity
  have hx2_nn : 0 ≤ x2 := by positivity
  have hx12 : x1 ≤ x2 := by
    dsimp only [x1, x2]
    rw [div_le_div_iff₀ (Nat.cast_pos.2 hbN) (Nat.cast_pos.2 haN)]
    have hle' : (aNum : ℝ) * (bDen : ℝ) ≤ (bNum : ℝ) * (aDen : ℝ) := by exact_mod_cast hle
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hsub : (Icc 0 ⌊x1⌋₊).filter Nat.Prime ⊆ (Icc 0 ⌊x2⌋₊).filter Nat.Prime := by
    intro p hp
    simp only [mem_filter, mem_Icc] at hp ⊢
    exact ⟨⟨Nat.zero_le _, hp.1.2.trans (Nat.floor_mono hx12)⟩, hp.2⟩
  rw [← Finset.sum_sdiff hsub, add_sub_cancel_right]
  refine sum_congr (Finset.ext fun p => ?_) fun _ _ => rfl
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨⟨_, _⟩, hpr⟩, hlo, hhi⟩
    have hp_le : p ≤ ⌊x2⌋₊ := by
      rw [Nat.le_floor_iff hx2_nn]
      dsimp only [x2]
      rw [le_div_iff₀ (Nat.cast_pos.2 haN)]
      exact_mod_cast (by linarith : p * aNum ≤ n * aDen)
    have hp_gt : ¬ (p ≤ ⌊x1⌋₊) := by
      rw [Nat.le_floor_iff hx1_nn, not_le]
      dsimp only [x1]
      rw [div_lt_iff₀ (Nat.cast_pos.2 hbN)]
      exact_mod_cast (by linarith : n * bDen < p * bNum)
    exact ⟨⟨⟨Nat.zero_le _, hp_le⟩, hpr⟩, fun h => hp_gt h.1.2⟩
  · rintro ⟨⟨⟨_, hp_le⟩, hpr⟩, hnot⟩
    have hp_gt : ¬ (p ≤ ⌊x1⌋₊) := fun h => hnot ⟨⟨Nat.zero_le _, h⟩, hpr⟩
    rw [Nat.le_floor_iff hx2_nn] at hp_le
    rw [Nat.le_floor_iff hx1_nn, not_le] at hp_gt
    dsimp only [x2] at hp_le
    dsimp only [x1] at hp_gt
    rw [le_div_iff₀ (Nat.cast_pos.2 haN)] at hp_le
    rw [div_lt_iff₀ (Nat.cast_pos.2 hbN)] at hp_gt
    have hhi : aNum * p ≤ aDen * n := by
      exact_mod_cast (by linarith : (aNum : ℝ) * (p : ℝ) ≤ (aDen : ℝ) * (n : ℝ))
    have hlo : bDen * n < bNum * p := by
      exact_mod_cast (by linarith : (bDen : ℝ) * (n : ℝ) < (bNum : ℝ) * (p : ℝ))
    have hp16 : p ≤ 16 * n := by
      have : aNum * p ≤ aNum * (16 * n) := by
        calc aNum * p ≤ aDen * n := hhi
          _ ≤ (16 * aNum) * n := Nat.mul_le_mul_right n hmax
          _ = aNum * (16 * n) := by ring
      exact Nat.le_of_mul_le_mul_left this haN
    exact ⟨⟨⟨hpr.one_le, hp16⟩, hpr⟩, hlo, hhi⟩

private lemma disjoint_list_le {l : List IvSpec} (hd : checkDisjoint l = true)
    (hv : l.all checkIv = true) :
    l.Pairwise (fun iv1 iv2 => iv1.bNum * iv2.aDen ≤ iv2.aNum * iv1.bDen) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons iv1 t ih =>
    cases t with
    | nil => exact List.pairwise_singleton _ _
    | cons iv2 rest =>
      simp only [checkDisjoint, Bool.and_eq_true, decide_eq_true_eq] at hd
      rw [List.all_cons, Bool.and_eq_true] at hv
      have htail := ih hd.2 hv.2
      rw [List.pairwise_cons]
      refine ⟨?_, htail⟩
      intro iv3 hiv3
      rcases List.mem_cons.1 hiv3 with rfl | hmem
      · exact hd.1
      · have h23 : iv2.bNum * iv3.aDen ≤ iv3.aNum * iv2.bDen :=
          (List.pairwise_cons.1 htail).1 iv3 hmem
        have hv2 : checkIv iv2 = true := by
          have := hv.2
          rw [List.all_cons, Bool.and_eq_true] at this
          exact this.1
        unfold checkIv at hv2
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hv2
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨haN2, haD2⟩, hbN2⟩, hbD2⟩, hab2⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hv2
        have h1 : iv1.bNum * iv2.aDen * iv2.bNum * iv3.aDen ≤
            iv2.aNum * iv1.bDen * iv2.bNum * iv3.aDen := by
          have := Nat.mul_le_mul_right (iv2.bNum * iv3.aDen) hd.1
          linarith
        have h2 : iv2.aNum * iv1.bDen * iv2.bNum * iv3.aDen ≤
            iv2.aNum * iv1.bDen * (iv3.aNum * iv2.bDen) := by
          have := Nat.mul_le_mul_left (iv2.aNum * iv1.bDen) h23
          linarith
        have h3 : iv2.aNum * iv2.bDen ≤ iv2.bNum * iv2.aDen := hab2.le
        have hmul : (iv2.aDen * iv2.bNum) * (iv1.bNum * iv3.aDen) ≤
            (iv2.aDen * iv2.bNum) * (iv3.aNum * iv1.bDen) := by
          calc (iv2.aDen * iv2.bNum) * (iv1.bNum * iv3.aDen)
              = iv1.bNum * iv2.aDen * iv2.bNum * iv3.aDen := by ring
            _ ≤ iv2.aNum * iv1.bDen * (iv3.aNum * iv2.bDen) := le_trans h1 h2
            _ = (iv2.aNum * iv2.bDen) * (iv3.aNum * iv1.bDen) := by ring
            _ ≤ (iv2.bNum * iv2.aDen) * (iv3.aNum * iv1.bDen) :=
                Nat.mul_le_mul_right _ h3
            _ = (iv2.aDen * iv2.bNum) * (iv3.aNum * iv1.bDen) := by ring
        exact Nat.le_of_mul_le_mul_left hmul (Nat.mul_pos haD2 hbN2)

private lemma log_D_n_le (n : ℕ) (hn : 65 ≤ n) :
    Real.log (D_n n : ℝ) ≤
      Chebyshev.psi ((16 * n : ℕ) : ℝ) + Chebyshev.psi ((15 * n : ℕ) : ℝ) -
        (chosenIvs.map (fun iv =>
          (iv.sav : ℝ) *
            (Chebyshev.theta ((n : ℝ) * (iv.aDen : ℝ) / (iv.aNum : ℝ)) -
             Chebyshev.theta ((n : ℝ) * (iv.bDen : ℝ) / (iv.bNum : ℝ))))).sum := by
  set Pset := (Icc 1 (16 * n)).filter Nat.Prime
  have hst0 : stateMult n (stateSpec 0) = Nat.lcmUpto (16 * n) * Nat.lcmUpto (15 * n) := by
    simp [stateMult, stateSpec, factProd]
  have hpf0 : ∀ p ∈ (stateMult n (stateSpec 0)).primeFactors, p ≤ 16 * n := by
    intro p hp
    have hpr := Nat.prime_of_mem_primeFactors hp
    have hdvd := Nat.dvd_of_mem_primeFactors hp
    rw [hst0] at hdvd
    have : Fact p.Prime := ⟨hpr⟩
    rcases hpr.dvd_mul.1 hdvd with h1 | h2
    · by_contra hgt; push Not at hgt
      have hz := padicValNat_lcmUpto_eq_zero (p := p) hgt
      have hge : 1 ≤ padicValNat p (Nat.lcmUpto (16 * n)) :=
        ((padicValNat_dvd_iff 1 _).1 (by rwa [pow_one])).resolve_left (Nat.lcmUpto_pos _).ne'
      omega
    · by_contra hgt; push Not at hgt
      have hz := padicValNat_lcmUpto_eq_zero (p := p) (by omega : 15 * n < p)
      have hge : 1 ≤ padicValNat p (Nat.lcmUpto (15 * n)) :=
        ((padicValNat_dvd_iff 1 _).1 (by rwa [pow_one])).resolve_left (Nat.lcmUpto_pos _).ne'
      omega
  have hpfD : ∀ p ∈ (D_n n).primeFactors, p ≤ 16 * n := by
    intro p hp
    have hpr := Nat.prime_of_mem_primeFactors hp
    have hdvd := dvd_trans (Nat.dvd_of_mem_primeFactors hp) (D_n_dvd n 0)
    exact hpf0 p (Nat.mem_primeFactors.2 ⟨hpr, hdvd, (stateMult_pos n (stateSpec 0)).ne'⟩)
  have hlogD := log_eq_sum_padicValNat (D_n_pos n) hpfD
  have hlog0 := log_eq_sum_padicValNat (stateMult_pos n (stateSpec 0)) hpf0
  have hpsi0 : Real.log (stateMult n (stateSpec 0) : ℝ) =
      Chebyshev.psi ((16 * n : ℕ) : ℝ) + Chebyshev.psi ((15 * n : ℕ) : ℝ) := by
    rw [hst0, Nat.cast_mul, Real.log_mul (Nat.cast_pos.2 (Nat.lcmUpto_pos _)).ne'
      (Nat.cast_pos.2 (Nat.lcmUpto_pos _)).ne',
      Chebyshev.psi_eq_log_lcmUpto, Chebyshev.psi_eq_log_lcmUpto]
  let hit (iv : IvSpec) (p : ℕ) : Prop := iv.bDen * n < iv.bNum * p ∧ iv.aNum * p ≤ iv.aDen * n
  have hpw := disjoint_list_le chosenIvs_disjoint chosenIvs_valid
  have hpt : ∀ p ∈ Pset,
      padicValNat p (D_n n) +
        (chosenIvs.map (fun iv => if hit iv p then iv.sav else 0)).sum ≤
        padicValNat p (stateMult n (stateSpec 0)) := by
    intro p hp
    have hpr : Nat.Prime p := (mem_filter.1 hp).2
    have : Fact p.Prime := ⟨hpr⟩
    have hsum_le : ∀ (l : List IvSpec),
        l.all checkIv = true →
        l.Pairwise (fun iv1 iv2 => iv1.bNum * iv2.aDen ≤ iv2.aNum * iv1.bDen) →
        padicValNat p (D_n n) + (l.map (fun iv => if hit iv p then iv.sav else 0)).sum ≤
          padicValNat p (stateMult n (stateSpec 0)) := by
      intro l
      induction l with
      | nil =>
        intro _ _
        simp only [List.map_nil, List.sum_nil, add_zero]
        exact ((padicValNat_dvd_iff _ _).1
          (dvd_trans pow_padicValNat_dvd (D_n_dvd n 0))).resolve_left (stateMult_pos n _).ne'
      | cons iv t ih =>
        intro hv hpw_l
        simp only [List.all_cons, Bool.and_eq_true] at hv
        rw [List.pairwise_cons] at hpw_l
        simp only [List.map_cons, List.sum_cons]
        by_cases hhit : hit iv p
        · rw [if_pos hhit]
          have hrest_zero : (t.map (fun iv' => if hit iv' p then iv'.sav else 0)).sum = 0 := by
            refine List.sum_eq_zero fun x hx => ?_
            rcases List.mem_map.1 hx with ⟨iv', hiv', rfl⟩
            rw [if_neg]
            rintro ⟨hlo', hhi'⟩
            have hdisj := hpw_l.1 iv' hiv'
            have h1 : iv.bDen * n * iv'.aDen < iv.bNum * p * iv'.aDen := by
              have hv' := List.all_eq_true.1 hv.2 iv' hiv'
              unfold checkIv at hv'
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hv'
              exact Nat.mul_lt_mul_of_pos_right hhit.1 hv'.1.1.1.1.1.1.1.1.1.2
            have h2 : iv.bNum * p * iv'.aDen ≤ iv'.aNum * p * iv.bDen := by
              have := Nat.mul_le_mul_right p hdisj
              linarith
            have h3 : iv'.aNum * p * iv.bDen ≤ iv'.aDen * n * iv.bDen := by
              have := Nat.mul_le_mul_right iv.bDen hhi'
              linarith
            linarith
          rw [hrest_zero, add_zero]
          exact checkIv_sound hv.1 hn hhit.1 hhit.2
        · rw [if_neg hhit, zero_add]
          exact ih hv.2 hpw_l.2
    exact hsum_le chosenIvs chosenIvs_valid hpw
  have hsum_ineq :
      (∑ p ∈ Pset, (padicValNat p (D_n n) : ℝ) * Real.log (p : ℝ)) +
      (∑ p ∈ Pset, ((chosenIvs.map (fun iv => if hit iv p then iv.sav else 0)).sum : ℝ) *
        Real.log (p : ℝ)) ≤
      ∑ p ∈ Pset, (padicValNat p (stateMult n (stateSpec 0)) : ℝ) * Real.log (p : ℝ) := by
    rw [← Finset.sum_add_distrib]
    refine sum_le_sum fun p hp => ?_
    rw [← add_mul]
    have hlog_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by
      have := (mem_filter.1 hp).2.one_le; exact_mod_cast this)
    have hle_r : (padicValNat p (D_n n) : ℝ) +
        ((chosenIvs.map (fun iv => if hit iv p then iv.sav else 0)).sum : ℝ) ≤
        (padicValNat p (stateMult n (stateSpec 0)) : ℝ) := by
      exact_mod_cast hpt p hp
    exact mul_le_mul_of_nonneg_right hle_r hlog_nn
  have hswap_list :
      ∑ p ∈ Pset, ((chosenIvs.map (fun iv => if hit iv p then iv.sav else 0)).sum : ℝ) *
        Real.log (p : ℝ) =
      (chosenIvs.map (fun iv =>
        (iv.sav : ℝ) *
          (Chebyshev.theta ((n : ℝ) * (iv.aDen : ℝ) / (iv.aNum : ℝ)) -
           Chebyshev.theta ((n : ℝ) * (iv.bDen : ℝ) / (iv.bNum : ℝ))))).sum := by
    suffices h : ∀ (l : List IvSpec), l.all checkIv = true →
        ∑ p ∈ Pset, ((l.map (fun iv => if hit iv p then iv.sav else 0)).sum : ℝ) *
          Real.log (p : ℝ) =
        (l.map (fun iv =>
          (iv.sav : ℝ) *
            (Chebyshev.theta ((n : ℝ) * (iv.aDen : ℝ) / (iv.aNum : ℝ)) -
             Chebyshev.theta ((n : ℝ) * (iv.bDen : ℝ) / (iv.bNum : ℝ))))).sum from
      h chosenIvs chosenIvs_valid
    intro l
    induction l with
    | nil => intro _; simp
    | cons iv t ih =>
      intro hv
      simp only [List.all_cons, Bool.and_eq_true] at hv
      simp only [List.map_cons, List.sum_cons, Nat.cast_add, add_mul, Finset.sum_add_distrib]
      rw [ih hv.2]
      congr 1
      have hterm : ∑ p ∈ Pset, ((if hit iv p then iv.sav else 0 : ℕ) : ℝ) * Real.log (p : ℝ) =
          (iv.sav : ℝ) * ∑ p ∈ Pset.filter (fun p => hit iv p), Real.log (p : ℝ) := by
        rw [Finset.mul_sum]
        conv_rhs => rw [Finset.sum_filter]
        refine sum_congr rfl fun p _ => ?_
        split_ifs <;> simp
      rw [hterm]
      congr 1
      have hvc := hv.1
      unfold checkIv at hvc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hvc
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨haN, haD⟩, hbN⟩, hbD⟩, hab⟩, _⟩, ha16⟩, _⟩, _⟩, _⟩, _⟩ := hvc
      exact sum_log_primes_interval n iv.aNum iv.aDen iv.bNum iv.bDen
        haN haD hbN hbD hab.le ha16
  linarith [hlogD, hlog0, hpsi0, hsum_ineq, hswap_list]

private lemma tendsto_psi_mul_div (hpsi : Chebyshev.psi ~[atTop] (fun x : ℝ => x))
    (c : ℕ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => Chebyshev.psi ((c * n : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 (c : ℝ)) := by
  have h1 : Tendsto (fun n : ℕ => ((c * n : ℕ) : ℝ)) atTop atTop := by
    have hmul : (fun n : ℕ => ((c * n : ℕ) : ℝ)) = fun n : ℕ => (c : ℝ) * (n : ℝ) := by
      ext n; push_cast; rfl
    rw [hmul]
    exact Tendsto.const_mul_atTop (Nat.cast_pos.2 hc) tendsto_natCast_atTop_atTop
  have hdiv : Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one
      (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx; exact hx.ne')).1 hpsi
  have h2 := (hdiv.comp h1).const_mul (c : ℝ)
  rw [mul_one] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hcpos : (c : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  simp only [Function.comp_apply, Nat.cast_mul]
  field_simp [hnpos, hcpos]

private lemma tendsto_theta_rat_div (htheta : Chebyshev.theta ~[atTop] id)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun n : ℕ => Chebyshev.theta ((n : ℝ) * (a : ℝ) / (b : ℝ)) / (n : ℝ))
      atTop (𝓝 ((a : ℝ) / (b : ℝ))) := by
  have hrate : (0 : ℝ) < (a : ℝ) / (b : ℝ) := div_pos (Nat.cast_pos.2 ha) (Nat.cast_pos.2 hb)
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) * (a : ℝ) / (b : ℝ)) atTop atTop := by
    have hrew : (fun n : ℕ => (n : ℝ) * (a : ℝ) / (b : ℝ)) =
        fun n : ℕ => ((a : ℝ) / (b : ℝ)) * (n : ℝ) := by ext n; ring
    rw [hrew]
    exact Tendsto.const_mul_atTop hrate tendsto_natCast_atTop_atTop
  have hdiv : Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one
      (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx; exact hx.ne')).1 htheta
  have h2 := (hdiv.comp h1).const_mul ((a : ℝ) / (b : ℝ))
  rw [mul_one] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  simp only [Function.comp_apply]
  field_simp [hnpos, (Nat.cast_pos.2 ha).ne', (Nat.cast_pos.2 hb).ne']

private lemma D_n_eventually_le
    (hpsi : Chebyshev.psi ~[atTop] (fun x : ℝ => x))
    (htheta : Chebyshev.theta ~[atTop] id) :
    ∀ᶠ n : ℕ in atTop, (D_n n : ℝ) ≤ (32768 : ℝ) ^ (2 * n) := by
  have hlist_tendsto :
      Tendsto (fun n : ℕ =>
        (chosenIvs.map (fun iv =>
          (iv.sav : ℝ) *
            ((Chebyshev.theta ((n : ℝ) * (iv.aDen : ℝ) / (iv.aNum : ℝ)) -
              Chebyshev.theta ((n : ℝ) * (iv.bDen : ℝ) / (iv.bNum : ℝ))) / (n : ℝ)))).sum)
        atTop (𝓝 (totalSavingRat : ℝ)) := by
    suffices h : ∀ (l : List IvSpec), l.all checkIv = true →
        Tendsto (fun n : ℕ =>
          (l.map (fun iv =>
            (iv.sav : ℝ) *
              ((Chebyshev.theta ((n : ℝ) * (iv.aDen : ℝ) / (iv.aNum : ℝ)) -
                Chebyshev.theta ((n : ℝ) * (iv.bDen : ℝ) / (iv.bNum : ℝ))) / (n : ℝ)))).sum)
          atTop
          (𝓝 (((l.map (fun iv =>
            (iv.sav : ℚ) * ((iv.aDen : ℚ) / (iv.aNum : ℚ) - (iv.bDen : ℚ) / (iv.bNum : ℚ)))).sum : ℚ) : ℝ)) from
      h chosenIvs chosenIvs_valid
    intro l
    induction l with
    | nil => intro _; simp
    | cons iv t ih =>
      intro hv
      simp only [List.all_cons, Bool.and_eq_true] at hv
      have hvc := hv.1
      unfold checkIv at hvc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hvc
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨haN, haD⟩, hbN⟩, hbD⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hvc
      have h1 := tendsto_theta_rat_div htheta iv.aDen iv.aNum haD haN
      have h2 := tendsto_theta_rat_div htheta iv.bDen iv.bNum hbD hbN
      have hdiff : Tendsto (fun n : ℕ =>
          (iv.sav : ℝ) *
            ((Chebyshev.theta ((n : ℝ) * (iv.aDen : ℝ) / (iv.aNum : ℝ)) -
              Chebyshev.theta ((n : ℝ) * (iv.bDen : ℝ) / (iv.bNum : ℝ))) / (n : ℝ)))
          atTop (𝓝 ((iv.sav : ℝ) * ((iv.aDen : ℝ) / (iv.aNum : ℝ) - (iv.bDen : ℝ) / (iv.bNum : ℝ)))) := by
        simpa [sub_div] using (h1.sub h2).const_mul (iv.sav : ℝ)
      have hsum := hdiff.add (ih hv.2)
      simp only [List.map_cons, List.sum_cons, Rat.cast_add, Rat.cast_mul, Rat.cast_sub,
        Rat.cast_div, Rat.cast_natCast] at hsum ⊢
      exact hsum
  have hfull : Tendsto (fun n : ℕ =>
      (Chebyshev.psi ((16 * n : ℕ) : ℝ) + Chebyshev.psi ((15 * n : ℕ) : ℝ) -
        (chosenIvs.map (fun iv =>
          (iv.sav : ℝ) *
            (Chebyshev.theta ((n : ℝ) * (iv.aDen : ℝ) / (iv.aNum : ℝ)) -
             Chebyshev.theta ((n : ℝ) * (iv.bDen : ℝ) / (iv.bNum : ℝ))))).sum) / (n : ℝ))
      atTop (𝓝 (31 - (totalSavingRat : ℝ))) := by
    have h1 := ((tendsto_psi_mul_div hpsi 16 (by omega)).add
      (tendsto_psi_mul_div hpsi 15 (by omega))).sub hlist_tendsto
    have h31 : ((16 : ℕ) : ℝ) + ((15 : ℕ) : ℝ) - (totalSavingRat : ℝ) = 31 - (totalSavingRat : ℝ) := by
      norm_num
    rw [h31] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n _
    have hdiv_list : ∀ (l : List IvSpec),
        (l.map (fun iv =>
          (iv.sav : ℝ) *
            (Chebyshev.theta ((n : ℝ) * (iv.aDen : ℝ) / (iv.aNum : ℝ)) -
             Chebyshev.theta ((n : ℝ) * (iv.bDen : ℝ) / (iv.bNum : ℝ))))).sum / (n : ℝ) =
        (l.map (fun iv =>
          (iv.sav : ℝ) *
            ((Chebyshev.theta ((n : ℝ) * (iv.aDen : ℝ) / (iv.aNum : ℝ)) -
              Chebyshev.theta ((n : ℝ) * (iv.bDen : ℝ) / (iv.bNum : ℝ))) / (n : ℝ)))).sum := by
      intro l
      induction l with
      | nil => simp
      | cons iv t ih =>
        simp only [List.map_cons, List.sum_cons, add_div]
        rw [ih, mul_div_assoc]
    rw [sub_div, add_div, hdiv_list]
  have hlimit_lt : 31 - (totalSavingRat : ℝ) < 30 * Real.log 2 := by
    have hrat : (104 / 10 : ℝ) < (totalSavingRat : ℝ) := by
      have := Rat.cast_lt (K := ℝ).2 totalSavingRat_gt
      simpa using this
    have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    linarith
  have hev := hfull.eventually (gt_mem_nhds hlimit_lt)
  filter_upwards [eventually_ge_atTop 65, hev] with n hn hlt
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have hDpos : (0 : ℝ) < D_n n := Nat.cast_pos.2 (D_n_pos n)
  have hlog_le : Real.log (D_n n : ℝ) ≤ (30 * Real.log 2) * (n : ℝ) := by
    have h1 := log_D_n_le n hn
    have h2 := ((div_lt_iff₀ hnpos).1 hlt).le
    linarith
  have h32768 : Real.log ((32768 : ℝ) ^ (2 * n)) = (30 * Real.log 2) * (n : ℝ) := by
    rw [Real.log_pow, show (32768 : ℝ) = (2 : ℝ) ^ (15 : ℕ) by norm_num, Real.log_pow]
    push_cast; ring
  rw [← h32768] at hlog_le
  exact (Real.log_le_log_iff hDpos (by positivity)).1 hlog_le

/- ### Section 7: Final Assembly of H1 -/

private lemma tendsto_natLog_atTop (B : ℕ) (hB : 1 < B) :
    Tendsto (fun b : ℕ => Nat.log B b) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro N
  refine ⟨B ^ N, fun b hb => ?_⟩
  have h := Nat.log_mono_right (b := B) hb
  rwa [Nat.log_pow hB] at h

theorem main_H1_of_PNT
    (hpsi : Chebyshev.psi ~[atTop] (fun x : ℝ => x))
    (htheta : Chebyshev.theta ~[atTop] id) :
    ∀ᶠ b : ℕ in atTop,
      let I : ℝ := ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
          ((x ^ 12 * (1 - x) ^ 12 * y ^ 14 * (1 - y) ^ 14) / (1 - x * y) ^ 13) ^
            (Nat.log 32768 b) / (1 - x * y)
      ∃ d p q : ℤ, (b : ℝ) ^ 2 ≤ 2 * d ∧ (d : ℝ) ≤ (b : ℝ) ^ 2 ∧
        |(q : ℝ)| ≤ (b : ℝ) ^ 5 ∧ (d : ℝ) * I = p + q * (π ^ 2 / 6) := by
  have hirr := irrational_pi_sq_div_six_of_psi hpsi
  have hlog_top := tendsto_natLog_atTop 32768 (by norm_num)
  have hev_n : ∀ᶠ n : ℕ in atTop,
      1 ≤ n ∧ (D_n n : ℝ) ≤ (32768 : ℝ) ^ (2 * n) ∧ |(targetQ n : ℝ)| ≤ (32768 : ℝ) ^ (3 * n) :=
    ((eventually_ge_atTop 1).and (D_n_eventually_le hpsi htheta)).and targetQ_eventually_le
      |>.mono fun n h => ⟨h.1.1, h.1.2, h.2⟩
  filter_upwards [eventually_ge_atTop 1, hlog_top.eventually hev_n] with b hb1 ⟨hn1, hDn_le, hQ_le⟩
  dsimp only
  set n := Nat.log 32768 b
  rw [← targetI_eq_H1_integral n]
  obtain ⟨P, hP⟩ := D_n_linear_form hirr n hn1
  have hpow_le : (32768 : ℝ) ^ n ≤ (b : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 32768 (by omega : b ≠ 0)
  have hDn_b2 : D_n n ≤ b ^ 2 := by
    have h1 : (D_n n : ℝ) ≤ (b : ℝ) ^ 2 := by
      calc (D_n n : ℝ) ≤ (32768 : ℝ) ^ (2 * n) := hDn_le
        _ = ((32768 : ℝ) ^ n) ^ 2 := by rw [← pow_mul, mul_comm]
        _ ≤ (b : ℝ) ^ 2 := by gcongr
    exact_mod_cast h1
  set k : ℕ := b ^ 2 / D_n n
  have hDpos : 0 < D_n n := D_n_pos n
  have hk_pos : 1 ≤ k := Nat.div_pos hDn_b2 hDpos
  refine ⟨((k * D_n n : ℕ) : ℤ), (k : ℤ) * P, (k : ℤ) * ((D_n n : ℤ) * targetQ n), ?_, ?_, ?_, ?_⟩
  · have hmod : b ^ 2 < (k + 1) * D_n n := by
      have h1 := Nat.lt_div_mul_add (a := b ^ 2) hDpos
      have h2 : (k + 1) * D_n n = b ^ 2 / D_n n * D_n n + D_n n := by
        dsimp only [k]; ring
      linarith
    have h2 : b ^ 2 ≤ 2 * (k * D_n n) := by nlinarith
    exact_mod_cast h2
  · have hle : k * D_n n ≤ b ^ 2 := Nat.div_mul_le_self (b ^ 2) (D_n n)
    exact_mod_cast hle
  · have hQ_b3 : |(targetQ n : ℝ)| ≤ (b : ℝ) ^ 3 := by
      calc |(targetQ n : ℝ)| ≤ (32768 : ℝ) ^ (3 * n) := hQ_le
        _ = ((32768 : ℝ) ^ n) ^ 3 := by rw [← pow_mul, mul_comm]
        _ ≤ (b : ℝ) ^ 3 := by gcongr
    have hd_le : ((k * D_n n : ℕ) : ℝ) ≤ (b : ℝ) ^ 2 := by
      exact_mod_cast Nat.div_mul_le_self (b ^ 2) (D_n n)
    push_cast
    rw [show (k : ℝ) * ((D_n n : ℝ) * (targetQ n : ℝ)) =
        ((k * D_n n : ℕ) : ℝ) * (targetQ n : ℝ) by push_cast; ring,
        abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    calc ((k * D_n n : ℕ) : ℝ) * |(targetQ n : ℝ)|
        ≤ (b : ℝ) ^ 2 * (b : ℝ) ^ 3 := by gcongr
      _ = (b : ℝ) ^ 5 := by ring
  · push_cast
    calc ((k : ℝ) * (D_n n : ℝ)) * targetI n
        = (k : ℝ) * ((D_n n : ℝ) * targetI n) := by ring
      _ = (k : ℝ) * ((P : ℝ) + ((D_n n : ℝ) * (targetQ n : ℝ)) * (π ^ 2 / 6)) := by
          rw [hP]; push_cast; ring
      _ = (k : ℝ) * (P : ℝ) + (k : ℝ) * ((D_n n : ℝ) * (targetQ n : ℝ)) * (π ^ 2 / 6) := by ring

end RVCore

theorem OMA.solution : OMA.R_Constant7a_c7a_lt_14_797075_R1.H1 :=
  RVCore.main_H1_of_PNT WeakPNT'' chebyshev_asymptotic
