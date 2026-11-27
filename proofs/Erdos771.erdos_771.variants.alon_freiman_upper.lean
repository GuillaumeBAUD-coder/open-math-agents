import FormalConjectures.ErdosProblems.«771»

-- Problem: Erdős Problem 771 — Alon-Freiman upper bound
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/771.lean (declaration Erdos771.erdos_771.variants.alon_freiman_upper)

/-
Erdős Problem 771, upper bound of Alon and Freiman (1988): for every ε > 0 and every large n,
f(n) ≤ (1/2 + ε) n / log n.

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
The proof of OMA.PNT.h1 from chebyshev_asymptotic (OMA.PNT.exists_prime_of_theta_lt, OMA.PNT.h1)
and the argument in namespace OMA.O14b are new.
-/

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


theorem isLittleO_const_id_cocompact [ProperSpace F'']
    (c : E'') : (fun _x : F'' => c) =o[cocompact F''] id :=
  isLittleO_const_left.2 <| Or.inr tendsto_norm_cocompact_atTop

-- to replace existing `isLittleO_const_id_atTop`
theorem isLittleO_const_id_atTop2 [LinearOrder F''] [NoMaxOrder F''] [ClosedIciTopology F'']
    [ProperSpace F''] (c : E'') : (fun _x : F'' => c) =o[atTop] id :=
 (isLittleO_const_id_cocompact c).mono atTop_le_cocompact

-- to replace existing `isLittleO_const_id_atBot`
theorem isLittleO_const_id_atBot2 [LinearOrder F''] [NoMinOrder F''] [ClosedIicTopology F'']
    [ProperSpace F''] (c : E'') : (fun _x : F'' => c) =o[atBot] id :=
  (isLittleO_const_id_cocompact c).mono atBot_le_cocompact

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

lemma deriv_apply {f : CS (n + 1) E} {x : ℝ} : f.deriv x = _root_.deriv f x := rfl

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

theorem hasDerivAt_e {u x : ℝ} : HasDerivAt (e u) (-2 * π * u * I * e u x) x := by
  have l2 : HasDerivAt (fun v => -v * u) (-u) x := by
    simpa only [neg_mul_comm] using hasDerivAt_mul_const (-u)
  convert! (hasDerivAt_fourierChar (-x * u)).scomp x l2 using 1
  change _ = ((-u : ℝ) : ℂ) * _ -- `scomp` introduces ℝ-smul on ℂ, which we undo
  simp ; ring

lemma fourierIntegral_deriv_aux2 (e : ℝ →ᵇ ℂ) {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (⇑e * f) :=
  hf.bdd_mul e.continuous.aestronglyMeasurable (ae_of_all _ e.norm_coe_le_norm)

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

/-- If, eventually in `T`, the integrand `f T` is bounded on `uIoc lo hi` by `B T`
and `B T * |hi - lo| → 0`, then the interval integral `∫ x in lo..hi, f T x → 0`. -/
lemma tendsto_intervalIntegral_zero_of_uniform_norm_bound
    {f : ℝ → ℝ → ℂ} {lo hi : ℝ} {B : ℝ → ℝ}
    (hB : Filter.Tendsto (fun T : ℝ => B T * |hi - lo|) Filter.atTop (nhds 0))
    (hf : ∀ᶠ T in Filter.atTop, ∀ x ∈ Set.uIoc lo hi, ‖f T x‖ ≤ B T) :
    Filter.Tendsto (fun T : ℝ => ∫ x in lo..hi, f T x) Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ hB
  filter_upwards [hf] with T hT
  exact intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => hT x hx)

/-- The decay `K * (log (T + 2) / (T + 2)) → 0` as `T → ∞`, for any constant `K`. -/
lemma tendsto_const_mul_log_add_two_div_add_two_atTop (K : ℝ) :
    Filter.Tendsto (fun T : ℝ => K * (Real.log (T + 2) / (T + 2)))
      Filter.atTop (nhds 0) := by
  have h0 : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
    simpa using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num : (1 : ℝ) ≠ 0))
  have hshift : Filter.Tendsto (fun T : ℝ => Real.log (T + 2) / (T + 2))
      Filter.atTop (nhds 0) := by
    have := h0.comp (tendsto_atTop_add_const_right Filter.atTop 2 tendsto_id)
    simpa [Function.comp_def] using this
  simpa using hshift.const_mul K

/-- Fourier-transform decay from an integrable derivative: for integrable,
differentiable `g` with integrable derivative, `‖𝓕 g w‖ ≤ (∫ ‖deriv g x‖) / (2π·|w|)`. -/
lemma norm_fourier_le_integral_deriv_div
    (g : ℝ → ℂ) (hg : Integrable g) (hdiff : Differentiable ℝ g)
    (hg' : Integrable (deriv g)) {w : ℝ} (hw : w ≠ 0) :
    ‖𝓕 g w‖ ≤ (∫ x, ‖deriv g x‖ ∂volume) / ((2 * Real.pi) * |w|) := by
  have hmul :
      𝓕 (deriv g) w = (2 * Real.pi * Complex.I * (w : ℂ)) * 𝓕 g w := by
    have h := congrFun (Real.fourier_deriv hg hdiff hg') w
    simpa [smul_eq_mul, mul_assoc] using h
  have h_fourier :
      ‖𝓕 (deriv g) w‖ ≤ ∫ x, ‖deriv g x‖ ∂volume := by
    exact VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (innerₗ ℝ)
      (deriv g) w
  have hleft :
      ((2 * Real.pi) * |w|) * ‖𝓕 g w‖ =
        ‖(2 * Real.pi * Complex.I * (w : ℂ)) * 𝓕 g w‖ := by
    have htwopi : ‖(2 * ↑Real.pi : ℂ)‖ = 2 * Real.pi := by
      rw [norm_mul, Complex.norm_two, Complex.norm_of_nonneg Real.pi_pos.le]
    have hwc : ‖(w : ℂ)‖ = |w| := by rw [norm_real, Real.norm_eq_abs]
    rw [norm_mul, norm_mul, norm_mul, htwopi, norm_I, hwc]
    ring
  have hmain : ((2 * Real.pi) * |w|) * ‖𝓕 g w‖ ≤ ∫ x, ‖deriv g x‖ ∂volume := by
    rw [hleft, ← hmul]
    exact h_fourier
  have hpos : 0 < (2 * Real.pi) * |w| := by
    positivity
  exact (le_div_iff₀ hpos).mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmain)

/-- The oscillatory-integral form of the decay bound: for `0 < T`,
`‖∫ g y · exp(T·i·y)‖ ≤ (∫ ‖deriv g x‖) / T`. -/
lemma norm_oscillatory_integral_le_integral_deriv_div
    (g : ℝ → ℂ) (hg : Integrable g) (hdiff : Differentiable ℝ g)
    (hg' : Integrable (deriv g)) {T : ℝ} (hT : 0 < T) :
    ‖∫ y, g y * exp ((T : ℂ) * Complex.I * (y : ℂ)) ∂volume‖ ≤
      (∫ x, ‖deriv g x‖ ∂volume) / T := by
  have hw : -T / (2 * Real.pi) ≠ 0 := by
    exact div_ne_zero (neg_ne_zero.mpr hT.ne') (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  have hfourier := norm_fourier_le_integral_deriv_div g hg hdiff hg' hw
  have heq :
      (∫ y, g y * exp ((T : ℂ) * Complex.I * (y : ℂ)) ∂volume) =
        𝓕 g (-T / (2 * Real.pi)) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with y
    rw [smul_eq_mul]
    rw [mul_comm (g y)]
    congr 1
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [heq]
  refine hfourier.trans_eq ?_
  congr 1
  have hden : (2 * Real.pi) * |-T / (2 * Real.pi)| = T := by
    have htwopi_pos : 0 < 2 * Real.pi := by positivity
    have hneg : -T / (2 * Real.pi) < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hT) htwopi_pos
    rw [abs_of_neg hneg]
    field_simp [Real.pi_ne_zero]
  rw [hden]

/-- The `|T|` variant of the oscillatory-integral decay bound: for `T ≠ 0`,
`‖∫ g y · exp(T·i·y)‖ ≤ (∫ ‖deriv g x‖) / |T|`. -/
lemma norm_oscillatory_integral_le_integral_deriv_div_abs
    (g : ℝ → ℂ) (hg : Integrable g) (hdiff : Differentiable ℝ g)
    (hg' : Integrable (deriv g)) {T : ℝ} (hT : T ≠ 0) :
    ‖∫ y, g y * exp ((T : ℂ) * Complex.I * (y : ℂ)) ∂volume‖ ≤
      (∫ x, ‖deriv g x‖ ∂volume) / |T| := by
  have hw : -T / (2 * Real.pi) ≠ 0 := by
    exact div_ne_zero (neg_ne_zero.mpr hT) (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  have hfourier := norm_fourier_le_integral_deriv_div g hg hdiff hg' hw
  have heq :
      (∫ y, g y * exp ((T : ℂ) * Complex.I * (y : ℂ)) ∂volume) =
        𝓕 g (-T / (2 * Real.pi)) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with y
    rw [smul_eq_mul]
    rw [mul_comm (g y)]
    congr 1
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [heq]
  refine hfourier.trans_eq ?_
  congr 1
  have hden : (2 * Real.pi) * |-T / (2 * Real.pi)| = |T| := by
    have htwopi_pos : 0 < 2 * Real.pi := by positivity
    rw [abs_div, abs_neg, abs_of_pos htwopi_pos]
    field_simp [Real.pi_ne_zero]
  rw [hden]

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



lemma continuous_multiplicative_ofAdd : Continuous (⇑Multiplicative.ofAdd : ℝ → ℝ) := ⟨fun _ ↦ id⟩


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

theorem prelim_decay (ψ : ℝ → ℂ) (u : ℝ) : ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ ∫ t, ‖ψ t‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm ..

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

lemma decay_bounds_aux {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    (h : ∀ t, ‖f t‖ ≤ A * (1 + t ^ 2)⁻¹) :
    ∫ t, ‖f t‖ ≤ π * A := by
  have l1 : Integrable (fun x ↦ A * (1 + x ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul A
  simp_rw [← integral_univ_inv_one_add_sq, mul_comm, ← integral_const_mul]
  exact integral_mono (l1.mono' hf (Eventually.of_forall h)).norm l1 h

theorem decay_bounds_W21 (f : W21) (hA : ∀ t, ‖f t‖ ≤ A / (1 + t ^ 2))
    (hA' : ∀ t, ‖deriv (deriv f) t‖ ≤ A / (1 + t ^ 2)) (u) :
    ‖𝓕 (f : ℝ → ℂ) u‖ ≤ (π + 1 / (4 * π)) * A / (1 + u ^ 2) := by
  have l0 : 1 * (4 * π)⁻¹ * A = (4 * π ^ 2)⁻¹ * (π * A) := by field_simp
  have l1 : ∫ (v : ℝ), ‖f v‖ ≤ π * A := by
    apply decay_bounds_aux f.continuous.aestronglyMeasurable
    simp_rw [← div_eq_mul_inv] ; exact hA
  have l2 : ∫ (v : ℝ), ‖deriv (deriv f) v‖ ≤ π * A := by
    apply decay_bounds_aux f.deriv.deriv.continuous.aestronglyMeasurable
    simp_rw [← div_eq_mul_inv] ; exact hA'
  apply decay_bounds_key f u |>.trans
  change W21.norm _ * _ ≤ _
  simp_rw [W21.norm, div_eq_mul_inv, add_mul, l0] ; gcongr

lemma decay_bounds (ψ : CS 2 ℂ) (hA : ∀ t, ‖ψ t‖ ≤ A / (1 + t ^ 2))
    (hA' : ∀ t, ‖deriv^[2] ψ t‖ ≤ A / (1 + t ^ 2)) :
    ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ (π + 1 / (4 * π)) * A / (1 + u ^ 2) := by
  exact decay_bounds_W21 ψ hA hA' u

lemma decay_bounds_cor_aux (ψ : CS 2 ℂ) : ∃ C : ℝ, ∀ u, ‖ψ u‖ ≤ C / (1 + u ^ 2) := by
  have l1 : HasCompactSupport (fun u : ℝ => ((1 + u ^ 2) : ℝ) * ψ u) := by exact ψ.h2.mul_left
  have := ψ.h1.continuous
  obtain ⟨C, hC⟩ := l1.exists_bound_of_continuous (by fun_prop)
  refine ⟨C, fun u => ?_⟩
  specialize hC u
  simp only [norm_mul, Complex.norm_real, norm_of_nonneg (one_add_sq_pos u).le] at hC
  rwa [le_div_iff₀' (one_add_sq_pos _)]

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

lemma nnabla_cast (u : ℝ → E) [Sub E] : nnabla u ∘ ((↑) : ℕ → ℝ) = nnabla (u ∘ (↑)) := by
  ext n ; simp [nnabla]

end nabla

lemma Finset.sum_shift_front {E : Type*} [Ring E] {u : ℕ → E} {n : ℕ} :
    cumsum u (n + 1) = u 0 + cumsum (shift u) n := by
  simp_rw [add_comm n, cumsum, sum_range_add, sum_range_one, add_comm 1] ; rfl

lemma Finset.sum_shift_front' {E : Type*} [Ring E] {u : ℕ → E} :
    shift (cumsum u) = (fun _ => u 0) + cumsum (shift u) := by
  ext n ; apply Finset.sum_shift_front

lemma Finset.sum_shift_back {E : Type*} [Ring E] {u : ℕ → E} {n : ℕ} :
    cumsum u (n + 1) = cumsum u n + u n := by
  simp [cumsum, Finset.range_add_one, add_comm]

lemma Finset.sum_shift_back' {E : Type*} [Ring E] {u : ℕ → E} :
    shift (cumsum u) = cumsum u + u := by
  ext n ; apply Finset.sum_shift_back

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

lemma isBigO_pow_pow_of_le {m n : ℕ} (h : m ≤ n) :
    (fun x : ℝ => x ^ m) =O[atTop] (fun x : ℝ => x ^ n) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop 1] with x l1
  simpa [abs_eq_self.mpr (zero_le_one.trans l1)] using pow_le_pow_right₀ l1 h

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

lemma one_div_sub_one (n : ℕ) : 1 / (↑(n - 1) : ℝ) ≤ 2 / n := by
  match n with
  | 0 => simp
  | 1 => simp
  | n + 2 => { norm_cast ; rw [div_le_div_iff₀] <;> simp [mul_add] <;> linarith }

lemma quadratic_pos (a b c x : ℝ) (ha : 0 < a) (hΔ : discrim a b c < 0) :
    0 < a * x ^ 2 + b * x + c := by
  have l1 : a * x ^ 2 + b * x + c = a * (x + b / (2 * a)) ^ 2 - discrim a b c / (4 * a) := by
    simp only [discrim]; field_simp; ring
  have l2 : 0 < - discrim a b c := by linarith
  rw [l1, sub_eq_add_neg, ← neg_div] ; positivity

noncomputable def pp (a x : ℝ) : ℝ := a ^ 2 * (x + 1) ^ 2 + (1 - a) * (1 + a)

noncomputable def pp' (a x : ℝ) : ℝ := a ^ 2 * (2 * (x + 1))

lemma pp_pos {a : ℝ} (ha : a ∈ Ioo (-1) 1) (x : ℝ) : 0 < pp a x := by
  simp only [pp]
  have : 0 < 1 - a := by linarith [ha.2]
  have : 0 < 1 + a := by linarith [ha.1]
  positivity

lemma pp_deriv (a x : ℝ) : HasDerivAt (pp a) (pp' a x) x := by
  unfold pp pp'
  simpa using hasDerivAt_id x |>.add_const 1 |>.pow 2 |>.const_mul _

lemma pp_deriv_eq (a : ℝ) : deriv (pp a) = pp' a := by
  ext x ; exact pp_deriv a x |>.deriv

lemma pp'_deriv (a x : ℝ) : HasDerivAt (pp' a) (a ^ 2 * 2) x := by
  simpa using! hasDerivAt_id x |>.add_const 1 |>.const_mul 2 |>.const_mul (a ^ 2)

lemma pp'_deriv_eq (a : ℝ) : deriv (pp' a) = fun _ => a ^ 2 * 2 := by
  ext x ; exact pp'_deriv a x |>.deriv

noncomputable def hh (a t : ℝ) : ℝ := (t * (1 + (a * log t) ^ 2))⁻¹

noncomputable def hh' (a t : ℝ) : ℝ := - pp a (log t) * hh a t ^ 2

lemma hh_nonneg (a : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ hh a t := by dsimp only [hh] ; positivity

lemma hh_le (a t : ℝ) (ht : 0 ≤ t) : |hh a t| ≤ t⁻¹ := by
  by_cases h0 : t = 0
  · simp [hh, h0]
  replace ht : 0 < t := lt_of_le_of_ne ht (by tauto)
  unfold hh
  rw [abs_inv, inv_le_inv₀ (by positivity) ht, abs_mul, abs_eq_self.mpr ht.le]
  convert_to! t * 1 ≤ _
  · simp
  apply mul_le_mul le_rfl ?_ zero_le_one ht.le
  rw [abs_eq_self.mpr (by positivity)]
  simp only [le_add_iff_nonneg_right]
  positivity

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

lemma gg_l1 {x : ℝ} (hx : 0 < x) (n : ℕ) : |gg x n| ≤ 1 / n := by
  simp only [gg_of_hh hx.ne.symm, one_div, mul_inv_rev, abs_mul]
  apply mul_le_mul le_rfl (hh_le _ _ (by positivity)) (by positivity) (by positivity) |>.trans
    (le_of_eq ?_)
  simp [abs_inv, abs_eq_self.mpr hx.le] ; field_simp

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

lemma sum_telescopic (a : ℕ → ℝ) (n : ℕ) : ∑ i ∈ Finset.range n, (a (i + 1) - a i) = a n - a 0 := by
  apply Finset.sum_range_sub

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

lemma cancel_main {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) (hn : 2 ≤ n) :
    cumsum (f * g) n ≤ C * cumsum g n := by
  convert! cancel_aux' hf hg hf' hg' n using 1
  match n with
  | n + 2 => simp only [cumsum_succ] ; push_cast ; ring

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

theorem set_integral_ofReal {f : ℝ → ℝ} {s : Set ℝ} : ∫ x in s, (f x : ℂ) = ∫ x in s, f x :=
  integral_ofReal

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



lemma le_floor_mul_iff (hb : 0 ≤ b) (hx : 0 < x) : n ≤ ⌊b * x⌋₊ ↔ n / x ≤ b := by
  rw [div_le_iff₀ hx, Nat.le_floor_iff] ; positivity

lemma lt_ceil_mul_iff (hx : 0 < x) : n < ⌈b * x⌉₊ ↔ n / x < b := by
  rw [div_lt_iff₀ hx, Nat.lt_ceil]

lemma ceil_mul_le_iff (hx : 0 < x) : ⌈a * x⌉₊ ≤ n ↔ a ≤ n / x := by
  rw [le_div_iff₀ hx, Nat.ceil_le]

lemma mem_Icc_iff_div (hb : 0 ≤ b) (hx : 0 < x) : n ∈ Finset.Icc ⌈a * x⌉₊ ⌊b * x⌋₊ ↔ n / x ∈ Icc a b := by
  rw [Finset.mem_Icc, mem_Icc, ceil_mul_le_iff hx, le_floor_mul_iff hb hx]

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

-- Ported from PrimeNumberTheoremAnd: Consequences.lean (selected lemmas up to chebyshev_asymptotic), followed by the new proof of H1
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

section OMA_AlonFreiman

open Filter Finset Real Complex MeasureTheory intervalIntegral Classical
open scoped Chebyshev BigOperators

namespace OMA.AlonFreiman

lemma lcm_Icc_pos (s : ℕ) : 0 < (Finset.Icc 1 s).lcm (id : ℕ → ℕ) := by
  rw [Nat.pos_iff_ne_zero]
  intro h
  rw [Finset.lcm_eq_zero_iff] at h
  obtain ⟨x, hx, hx0⟩ := h
  simp only [Finset.mem_Icc] at hx
  simp only [id_eq] at hx0
  omega

lemma pow_dvd_lcm_iff {T : Finset ℕ} (hT : ∀ x ∈ T, x ≠ 0) {p e : ℕ} (hp : p.Prime) :
    p ^ e ∣ T.lcm (id : ℕ → ℕ) ↔ (e = 0 ∨ ∃ x ∈ T, p ^ e ∣ x) := by
  induction T using Finset.induction_on with
  | empty =>
    simp only [Finset.lcm_empty, Nat.dvd_one, pow_eq_one_iff, Finset.notMem_empty, false_and,
      exists_false, or_false]
    constructor
    · rintro (rfl | rfl)
      · exact absurd rfl hp.ne_one
      · rfl
    · intro he; right; exact he
  | @insert a T ha ih =>
    have ha0 : a ≠ 0 := hT a (Finset.mem_insert_self a T)
    have hT0 : ∀ x ∈ T, x ≠ 0 := fun x hx => hT x (Finset.mem_insert_of_mem hx)
    have hlcm0 : T.lcm (id : ℕ → ℕ) ≠ 0 := by
      intro hz
      rw [Finset.lcm_eq_zero_iff] at hz
      obtain ⟨x, hx, hx0⟩ := hz
      exact hT0 x hx hx0
    rw [Finset.lcm_insert]
    constructor
    · intro hdvd
      by_cases he : e = 0
      · exact Or.inl he
      · right
        have hle := (hp.pow_dvd_iff_le_factorization (Nat.lcm_ne_zero ha0 hlcm0)).1 hdvd
        rw [Nat.factorization_lcm ha0 hlcm0, Finsupp.sup_apply] at hle
        rcases le_sup_iff.1 hle with h1 | h2
        · exact ⟨a, Finset.mem_insert_self a T,
            (hp.pow_dvd_iff_le_factorization ha0).2 h1⟩
        · have hd2 : p ^ e ∣ T.lcm (id : ℕ → ℕ) := (hp.pow_dvd_iff_le_factorization hlcm0).2 h2
          rcases (ih hT0).1 hd2 with rfl | ⟨x, hx, hpx⟩
          · exact absurd rfl he
          · exact ⟨x, Finset.mem_insert_of_mem hx, hpx⟩
    · rintro (rfl | ⟨x, hx, hpx⟩)
      · simp
      · rcases Finset.mem_insert.1 hx with rfl | hxT
        · exact dvd_trans hpx (Nat.dvd_lcm_left _ _)
        · exact dvd_trans ((ih hT0).2 (Or.inr ⟨x, hxT, hpx⟩)) (Nat.dvd_lcm_right _ _)

lemma factorization_lcm_Icc_eq (s p : ℕ) (hp : p.Prime) :
    ((Finset.Icc 1 s).lcm (id : ℕ → ℕ)).factorization p =
      ((Finset.Icc 1 s).filter (fun k => ∃ r : ℕ, 1 ≤ r ∧ k = p ^ r)).card := by
  set m := (Finset.Icc 1 s).lcm (id : ℕ → ℕ)
  have hm0 : m ≠ 0 := (lcm_Icc_pos s).ne'
  have hIcc0 : ∀ x ∈ Finset.Icc 1 s, x ≠ 0 := fun x hx => by
    rw [Finset.mem_Icc] at hx; omega
  set F := (Finset.Icc 1 s).filter (fun k => ∃ r : ℕ, 1 ≤ r ∧ k = p ^ r)
  have hfac_le : ∀ r : ℕ, r ≤ m.factorization p ↔ (r = 0 ∨ p ^ r ≤ s) := by
    intro r
    rw [← hp.pow_dvd_iff_le_factorization hm0, pow_dvd_lcm_iff hIcc0 hp]
    constructor
    · rintro (rfl | ⟨x, hx, hpx⟩)
      · exact Or.inl rfl
      · right
        rw [Finset.mem_Icc] at hx
        exact le_trans (Nat.le_of_dvd hx.1 hpx) hx.2
    · rintro (rfl | hle)
      · exact Or.inl rfl
      · right
        by_cases hr0 : r = 0
        · subst hr0
          exact ⟨1, Finset.mem_Icc.2 ⟨le_rfl, by simpa using hle⟩, by simp⟩
        · exact ⟨p ^ r, Finset.mem_Icc.2 ⟨Nat.one_le_pow r p hp.pos, hle⟩, dvd_rfl⟩
  have hbij : F = (Finset.Icc 1 (m.factorization p)).image (fun r => p ^ r) := by
    ext k
    simp only [F, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨_, hks⟩, ⟨r, hr1, rfl⟩⟩
      exact ⟨r, ⟨hr1, (hfac_le r).2 (Or.inr hks)⟩, rfl⟩
    · rintro ⟨r, ⟨hr1, hrf⟩, rfl⟩
      rcases (hfac_le r).1 hrf with rfl | hle
      · omega
      · exact ⟨⟨Nat.one_le_pow r p hp.pos, hle⟩, ⟨r, hr1, rfl⟩⟩
  rw [hbij, Finset.card_image_of_injective _ (fun a b hab => Nat.pow_right_injective hp.two_le hab),
    Nat.card_Icc, Nat.add_sub_cancel]

lemma log_lcm_Icc_eq_psi (s : ℕ) :
    Real.log (((Finset.Icc 1 s).lcm (id : ℕ → ℕ) : ℕ) : ℝ) = Chebyshev.psi (s : ℝ) := by
  set m := (Finset.Icc 1 s).lcm (id : ℕ → ℕ)
  have hm0 : m ≠ 0 := (lcm_Icc_pos s).ne'
  have hlog : Real.log (m : ℝ) =
      ∑ p ∈ m.primeFactors, (m.factorization p : ℝ) * Real.log (p : ℝ) := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hm0]
    rw [Finsupp.prod, Nat.cast_prod, Real.log_prod]
    · refine Finset.sum_congr rfl fun p hp => ?_
      rw [Nat.cast_pow, Real.log_pow]
    · intro p hp
      have hp0 : p ≠ 0 := (Nat.prime_of_mem_primeFactors hp).ne_zero
      exact (Nat.cast_ne_zero (R := ℝ)).2 (pow_ne_zero _ hp0)
  rw [hlog, Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
  have hsum_Icc : ∑ k ∈ Finset.Icc 0 s, ArithmeticFunction.vonMangoldt k =
      ∑ k ∈ Finset.Icc 1 s, ArithmeticFunction.vonMangoldt k := by
    have h0 : Finset.Icc 0 s = insert 0 (Finset.Icc 1 s) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [h0, Finset.sum_insert (by simp), ArithmeticFunction.map_zero, zero_add]
  rw [hsum_Icc]
  have hprime_mem : ∀ k ∈ Finset.Icc 1 s, IsPrimePow k → k.minFac ∈ m.primeFactors := by
    intro k hk hpk
    have hpr : k.minFac.Prime := Nat.minFac_prime hpk.ne_one
    rw [Nat.mem_primeFactors]
    exact ⟨hpr, dvd_trans (Nat.minFac_dvd k) (Finset.dvd_lcm hk), hm0⟩
  have hgroup : ∑ k ∈ Finset.Icc 1 s, ArithmeticFunction.vonMangoldt k =
      ∑ p ∈ m.primeFactors,
        ∑ k ∈ (Finset.Icc 1 s).filter (fun k => ∃ r : ℕ, 1 ≤ r ∧ k = p ^ r), Real.log p := by
    rw [← Finset.sum_filter_of_ne (p := IsPrimePow) (fun k _ hne => by
      by_contra hnp
      rw [ArithmeticFunction.vonMangoldt_apply, if_neg hnp] at hne
      exact hne rfl)]
    have hfib := Finset.sum_fiberwise_of_maps_to
      (s := (Finset.Icc 1 s).filter IsPrimePow) (t := m.primeFactors)
      (g := Nat.minFac) (f := fun k => ArithmeticFunction.vonMangoldt k)
      (fun k hk => hprime_mem k (Finset.mem_filter.1 hk).1 (Finset.mem_filter.1 hk).2)
    rw [← hfib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpr : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hfilt : ((Finset.Icc 1 s).filter IsPrimePow).filter (fun k => k.minFac = p) =
        (Finset.Icc 1 s).filter (fun k => ∃ r : ℕ, 1 ≤ r ∧ k = p ^ r) := by
      ext k
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hk, hpk⟩, hmin⟩
        obtain ⟨q, r, hqp, hr, rfl⟩ := hpk
        have hq : (q ^ r).minFac = q := by
          rw [Nat.Prime.pow_minFac hqp.nat_prime (by omega)]
        rw [hq] at hmin
        subst hmin
        exact ⟨hk, r, hr, rfl⟩
      · rintro ⟨hk, r, hr, rfl⟩
        refine ⟨⟨hk, hpr.isPrimePow.pow (by omega)⟩, ?_⟩
        exact hpr.pow_minFac (by omega)
    rw [hfilt]
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨_, r, hr, rfl⟩ := Finset.mem_filter.1 hk
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega), ArithmeticFunction.vonMangoldt_apply_prime hpr]
  rw [hgroup]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.sum_const, nsmul_eq_mul, factorization_lcm_Icc_eq s p (Nat.prime_of_mem_primeFactors hp)]

/- ### Part 2: Iterative Divisor Extraction -/

lemma divisor_extract_aux (n s : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 n)
    (T : ℝ) (hT : 0 < T) (hS_card : ((Nat.log 2 n + 1 : ℕ) : ℝ) * T < S.card)
    (hB_lb : (n : ℝ) / (s + 1 : ℝ) < (S.card : ℝ) - (Nat.log 2 n : ℝ) * T) :
    ∀ (k d : ℕ) (B : Finset ℕ),
      1 ≤ d → d ≤ n → 2 ^ k ≤ d →
      B ⊆ Finset.Icc 1 (n / d) →
      (∀ b ∈ B, d * b ∈ S) →
      (S.card : ℝ) - (k : ℝ) * T ≤ B.card →
      ∃ d' : ℕ, ∃ B' : Finset ℕ,
        1 ≤ d' ∧ d' ≤ s ∧
        B' ⊆ Finset.Icc 1 (n / d') ∧
        (∀ b ∈ B', d' * b ∈ S) ∧
        (S.card : ℝ) - (Nat.log 2 n : ℝ) * T ≤ B'.card ∧
        ∀ q : ℕ, 2 ≤ q → T < ((B'.filter (fun b => ¬ q ∣ b)).card : ℝ) := by
  intro k d B hd1 hdn h2k hB hBS hBcard
  have hk_log : k ≤ Nat.log 2 n := by
    by_cases hn0 : n = 0
    · subst hn0; omega
    · exact (Nat.le_log_iff_pow_le (by omega) hn0).2 (le_trans h2k hdn)
  by_cases hstop : ∀ q : ℕ, 2 ≤ q → T < ((B.filter (fun b => ¬ q ∣ b)).card : ℝ)
  · have hB_le : B.card ≤ n / d := by
      simpa [Nat.card_Icc] using Finset.card_le_card hB
    have hk_le : (k : ℝ) ≤ Nat.log 2 n := by exact_mod_cast hk_log
    have hB_ge : (S.card : ℝ) - (Nat.log 2 n : ℝ) * T ≤ B.card := by nlinarith
    have hnd_gt : (n : ℝ) / (s + 1 : ℝ) < (n : ℝ) / (d : ℝ) := by
      have h1 : (B.card : ℝ) ≤ (n / d : ℕ) := by exact_mod_cast hB_le
      have h2 : ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / (d : ℝ) := Nat.cast_div_le
      linarith
    have hd_pos : (0 : ℝ) < d := by exact_mod_cast hd1
    have hs_pos : (0 : ℝ) < (s + 1 : ℝ) := by positivity
    have hd_lt : (d : ℝ) < (s + 1 : ℝ) := by
      rw [div_lt_div_iff₀ hs_pos hd_pos] at hnd_gt
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le hd1 hdn
      nlinarith
    have hds : d ≤ s := by
      have : d < s + 1 := by exact_mod_cast hd_lt
      omega
    exact ⟨d, B, hd1, hds, hB, hBS, hB_ge, hstop⟩
  · push Not at hstop
    obtain ⟨q, hq2, hqle⟩ := hstop
    let B' : Finset ℕ := (B.filter (fun b => q ∣ b)).image (fun b => b / q)
    let d' : ℕ := d * q
    have hq_pos : 0 < q := by omega
    have hB'_sub : B' ⊆ Finset.Icc 1 (n / d') := by
      intro x hx
      simp only [B', Finset.mem_image, Finset.mem_filter] at hx
      obtain ⟨b, ⟨hbB, hqb⟩, rfl⟩ := hx
      have hb_mem := Finset.mem_Icc.1 (hB hbB)
      obtain ⟨y, rfl⟩ := hqb
      have hy_pos : 1 ≤ y := by
        by_contra h0
        have hy0 : y = 0 := by omega
        subst hy0
        omega
      rw [Nat.mul_div_cancel_left y hq_pos, Finset.mem_Icc]
      refine ⟨hy_pos, ?_⟩
      rw [Nat.le_div_iff_mul_le (Nat.mul_pos hd1 hq_pos)]
      calc y * (d * q) = d * (q * y) := by ring
        _ ≤ d * (n / d) := Nat.mul_le_mul_left d hb_mem.2
        _ ≤ n := Nat.mul_div_le n d
    have hB'S : ∀ x ∈ B', d' * x ∈ S := by
      intro x hx
      simp only [B', Finset.mem_image, Finset.mem_filter] at hx
      obtain ⟨b, ⟨hbB, hqb⟩, rfl⟩ := hx
      have : d' * (b / q) = d * b := by
        dsimp [d']
        rw [mul_assoc, Nat.mul_div_cancel' hqb]
      rw [this]
      exact hBS b hbB
    have hB'_card_eq : B'.card = (B.filter (fun b => q ∣ b)).card := by
      apply Finset.card_image_of_injOn
      intro x hx y hy hxy
      simp only [Finset.mem_coe, Finset.mem_filter] at hx hy
      dsimp only at hxy
      have hx' := Nat.mul_div_cancel' hx.2
      have hy' := Nat.mul_div_cancel' hy.2
      rw [← hx', ← hy', hxy]
    have hpart : (B.filter (fun b => q ∣ b)).card + (B.filter (fun b => ¬ q ∣ b)).card = B.card := by
      rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.2 (fun _ _ h1 h2 => h2 h1))]
      congr 1
      ext x
      simp only [Finset.mem_union, Finset.mem_filter]
      tauto
    have hB'_card : (S.card : ℝ) - ((k + 1 : ℕ) : ℝ) * T ≤ B'.card := by
      have h1 : (B'.card : ℝ) + ((B.filter (fun b => ¬ q ∣ b)).card : ℝ) = B.card := by
        exact_mod_cast (by rw [hB'_card_eq, hpart])
      push_cast
      linarith
    have hB'_ne : B'.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      have h0 : (B'.card : ℝ) = 0 := by simp [hempty]
      have hk1 : ((k + 1 : ℕ) : ℝ) ≤ ((Nat.log 2 n + 1 : ℕ) : ℝ) := by
        exact_mod_cast (Nat.succ_le_succ hk_log)
      have : ((k + 1 : ℕ) : ℝ) * T ≤ ((Nat.log 2 n + 1 : ℕ) : ℝ) * T :=
        mul_le_mul_of_nonneg_right hk1 hT.le
      linarith
    have hd'_le : d' ≤ n := by
      obtain ⟨x, hx⟩ := hB'_ne
      have hx_mem := Finset.mem_Icc.1 (hB'_sub hx)
      calc d' = d' * 1 := (mul_one d').symm
        _ ≤ d' * x := Nat.mul_le_mul_left d' hx_mem.1
        _ ≤ d' * (n / d') := Nat.mul_le_mul_left d' hx_mem.2
        _ ≤ n := Nat.mul_div_le n d'
    have h2k' : 2 ^ (k + 1) ≤ d' := by
      rw [pow_succ]
      exact Nat.mul_le_mul h2k hq2
    have hlt : n - d' < n - d := by
      have : d < d' := lt_mul_of_one_lt_right hd1 (by omega)
      omega
    exact divisor_extract_aux n s S hS T hT hS_card hB_lb (k + 1) d' B'
      (Nat.mul_pos hd1 hq_pos) hd'_le h2k' hB'_sub hB'S hB'_card
termination_by _ d _ => n - d

/- ### Part 3a: Fourier Identity & `d1` / `cos` Bounds -/

lemma integral_exp_int (k : ℤ) :
    ∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ), Complex.exp (2 * Real.pi * Complex.I * k * t) =
      if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk
    simp; norm_num
  · have hne : (2 : ℂ) * Real.pi * Complex.I * k ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero, hk]
    let F : ℝ → ℂ := fun t => Complex.exp (2 * Real.pi * Complex.I * k * t) /
        (2 * Real.pi * Complex.I * k)
    have hderiv : ∀ t ∈ Set.uIcc (-1 / 2 : ℝ) (1 / 2 : ℝ),
        HasDerivAt F (Complex.exp (2 * Real.pi * Complex.I * k * t)) t := by
      intro t _
      have h1 : HasDerivAt (fun x : ℝ => (2 : ℂ) * Real.pi * Complex.I * k * x)
          (2 * Real.pi * Complex.I * k) t := by
        have hc := (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul ((2 : ℂ) * Real.pi * Complex.I * k)
        simpa using hc
      have h2 := (Complex.hasDerivAt_exp _).comp t h1
      simpa [F, mul_div_cancel_right₀ _ hne] using h2.div_const (2 * Real.pi * Complex.I * k)
    have hcont : Continuous (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * k * t)) := by
      continuity
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable (-1 / 2) (1 / 2))]
    have harg1 : (2 : ℂ) * Real.pi * Complex.I * k * ((1 / 2 : ℝ) : ℂ) =
        (k : ℂ) * (Real.pi * Complex.I) := by
      push_cast; ring
    have harg2 : (2 : ℂ) * Real.pi * Complex.I * k * ((-1 / 2 : ℝ) : ℂ) =
        ((-k : ℤ) : ℂ) * (Real.pi * Complex.I) := by
      push_cast; ring
    dsimp [F]
    rw [harg1, harg2, Complex.exp_int_mul, Complex.exp_int_mul, Complex.exp_pi_mul_I,
      zpow_neg, ← inv_zpow, inv_neg, inv_one, sub_self]

lemma subset_sum_count_eq_integral (C : Finset ℕ) (T : ℕ) :
    ((C.powerset.filter (fun A => ∑ b ∈ A, b = T)).card : ℝ) =
      (2 : ℝ) ^ C.card * ∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        Real.cos (2 * Real.pi * ((1 / 2 : ℝ) * ∑ b ∈ C, (b : ℝ) - T) * t) *
          ∏ b ∈ C, Real.cos (Real.pi * b * t) := by
  let f : ℝ → ℂ := fun t =>
    Complex.exp (-2 * Real.pi * Complex.I * T * t) *
      ∏ b ∈ C, (1 + Complex.exp (2 * Real.pi * Complex.I * b * t))
  have hf_expand : ∀ t : ℝ, f t =
      ∑ A ∈ C.powerset, Complex.exp (2 * Real.pi * Complex.I * (((∑ b ∈ A, b : ℕ) : ℤ) - T : ℤ) * t) := by
    intro t
    dsimp [f]
    rw [Finset.prod_one_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [← Complex.exp_sum, ← Complex.exp_add]
    congr 1
    have hsum : ∑ x ∈ A, (2 : ℂ) * Real.pi * Complex.I * (x : ℂ) * t =
        (2 : ℂ) * Real.pi * Complex.I * (∑ x ∈ A, (x : ℂ)) * t := by
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul]
    rw [hsum]
    push_cast
    ring
  have hf_int1 : ∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ), f t =
      ((C.powerset.filter (fun A => ∑ b ∈ A, b = T)).card : ℂ) := by
    simp_rw [hf_expand]
    rw [intervalIntegral.integral_finsetSum]
    · simp_rw [integral_exp_int]
      have hiff : ∀ A : Finset ℕ, (((∑ b ∈ A, b : ℕ) : ℤ) - (T : ℤ) = 0) ↔ ∑ b ∈ A, b = T := by
        intro A; omega
      simp_rw [hiff, Finset.sum_boole]
    · intro A _
      exact (Continuous.intervalIntegrable (by continuity) _ _)
  have hf_cos : ∀ t : ℝ, f t =
      (2 : ℂ) ^ C.card *
        Complex.exp (2 * Real.pi * Complex.I * ((1 / 2 : ℝ) * ∑ b ∈ C, (b : ℝ) - T) * t) *
        ∏ b ∈ C, (Real.cos (Real.pi * b * t) : ℂ) := by
    intro t
    dsimp [f]
    have hterm : ∀ b : ℕ, 1 + Complex.exp (2 * Real.pi * Complex.I * b * t) =
        2 * Complex.exp (Real.pi * Complex.I * b * t) * (Real.cos (Real.pi * b * t) : ℂ) := by
      intro b
      rw [Complex.ofReal_cos, Complex.cos]
      have h1 : Complex.exp (↑(Real.pi * b * t) * Complex.I) = Complex.exp (Real.pi * Complex.I * b * t) := by
        congr 1; push_cast; ring
      have h2 : Complex.exp (-↑(Real.pi * b * t) * Complex.I) = Complex.exp (-(Real.pi * Complex.I * b * t)) := by
        congr 1; push_cast; ring
      rw [h1, h2]
      have hmul : Complex.exp (Real.pi * Complex.I * b * t) * Complex.exp (Real.pi * Complex.I * b * t) =
          Complex.exp (2 * Real.pi * Complex.I * b * t) := by
        rw [← Complex.exp_add]; congr 1; ring
      have hinv : Complex.exp (Real.pi * Complex.I * b * t) * Complex.exp (-(Real.pi * Complex.I * b * t)) = 1 := by
        rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
      calc 1 + Complex.exp (2 * Real.pi * Complex.I * b * t)
          = Complex.exp (Real.pi * Complex.I * b * t) * Complex.exp (-(Real.pi * Complex.I * b * t)) +
            Complex.exp (Real.pi * Complex.I * b * t) * Complex.exp (Real.pi * Complex.I * b * t) := by
              rw [hinv, hmul]
        _ = 2 * Complex.exp (Real.pi * Complex.I * b * t) *
              ((Complex.exp (Real.pi * Complex.I * b * t) + Complex.exp (-(Real.pi * Complex.I * b * t))) / 2) := by
              ring
    simp_rw [hterm, Finset.prod_mul_distrib, Finset.prod_const, ← Complex.exp_sum]
    rw [← mul_assoc, ← mul_assoc]
    congr 1
    rw [mul_comm (Complex.exp (-2 * Real.pi * Complex.I * T * t)) ((2 : ℂ) ^ C.card)]
    rw [mul_assoc ((2 : ℂ) ^ C.card), ← Complex.exp_add]
    congr 2
    have hsum : ∑ x ∈ C, (Real.pi : ℂ) * Complex.I * (x : ℂ) * t =
        (Real.pi : ℂ) * Complex.I * (∑ x ∈ C, (x : ℂ)) * t := by
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul]
    rw [hsum]
    push_cast
    ring
  have hf_int_re : (∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ), f t).re =
      (2 : ℝ) ^ C.card * ∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        Real.cos (2 * Real.pi * ((1 / 2 : ℝ) * ∑ b ∈ C, (b : ℝ) - T) * t) *
          ∏ b ∈ C, Real.cos (Real.pi * b * t) := by
    have hcont : Continuous f := by dsimp [f]; continuity
    rw [← Complex.reCLM_apply, ← Complex.reCLM.intervalIntegral_comp_comm (hcont.intervalIntegrable (-1 / 2) (1 / 2))]
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [Complex.reCLM_apply, hf_cos t]
    have hprod : ∏ b ∈ C, (Real.cos (Real.pi * b * t) : ℂ) =
        ((∏ b ∈ C, Real.cos (Real.pi * b * t) : ℝ) : ℂ) := by
      push_cast; rfl
    rw [hprod]
    have h2pow : ((2 : ℂ) ^ C.card) = (((2 : ℝ) ^ C.card : ℝ) : ℂ) := by push_cast; rfl
    rw [h2pow]
    set arg_theta : ℝ := 2 * Real.pi * ((1 / 2 : ℝ) * ∑ b ∈ C, (b : ℝ) - T) * t
    have hexp : Complex.exp (2 * Real.pi * Complex.I * ((1 / 2 : ℝ) * ∑ b ∈ C, (b : ℝ) - T) * t) =
        Complex.exp ((arg_theta : ℂ) * Complex.I) := by
      congr 1; dsimp [arg_theta]; push_cast; ring
    rw [hexp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, zero_mul, add_zero]
    ring
  rw [← hf_int_re, hf_int1]
  simp

noncomputable def d1 (x : ℝ) : ℝ := |x - (round x : ℝ)|

lemma d1_nonneg (x : ℝ) : 0 ≤ d1 x := abs_nonneg _

lemma d1_le_half (x : ℝ) : d1 x ≤ 1 / 2 := abs_sub_round x

lemma d1_le_abs_sub_int (x : ℝ) (k : ℤ) : d1 x ≤ |x - (k : ℝ)| := by
  dsimp [d1]
  by_cases h : |x - (k : ℝ)| < 1 / 2
  · have hk : round x = k := by
      have h1 : |(round x : ℝ) - k| < 1 := by
        calc |(round x : ℝ) - k| = |(round x - x) + (x - k)| := by ring_nf
          _ ≤ |round x - x| + |x - k| := abs_add_le _ _
          _ = |x - round x| + |x - k| := by rw [abs_sub_comm]
          _ < 1 / 2 + 1 / 2 := add_lt_add_of_le_of_lt (abs_sub_round x) h
          _ = 1 := by norm_num
      have h2 : |round x - k| < 1 := by exact_mod_cast h1
      rw [Int.abs_lt_one_iff] at h2
      omega
    rw [hk]
  · push Not at h
    exact le_trans (abs_sub_round x) h

lemma d1_add_le (x y : ℝ) : d1 (x + y) ≤ d1 x + |y| := by
  calc d1 (x + y) ≤ |x + y - (round x : ℝ)| := d1_le_abs_sub_int _ (round x)
    _ = |(x - round x) + y| := by congr 1; ring
    _ ≤ |x - round x| + |y| := abs_add_le _ _

lemma d1_div_ge (a : ℤ) (q : ℕ) (hq : 0 < q) (hndvd : ¬ (q : ℤ) ∣ a) :
    1 / (q : ℝ) ≤ d1 ((a : ℝ) / q) := by
  dsimp [d1]
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hne : a - (q : ℤ) * round ((a : ℝ) / q) ≠ 0 := by
    intro h0
    apply hndvd
    exact ⟨round ((a : ℝ) / q), by omega⟩
  have habs1 : (1 : ℝ) ≤ |((a - (q : ℤ) * round ((a : ℝ) / q) : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hne
  have heq : |(a : ℝ) / q - (round ((a : ℝ) / q) : ℝ)| =
      |((a - (q : ℤ) * round ((a : ℝ) / q) : ℤ) : ℝ)| / (q : ℝ) := by
    rw [← abs_of_pos hq0, ← abs_div]
    congr 1
    rw [abs_of_pos hq0]
    push_cast
    field_simp
  rw [heq]
  exact div_le_div_of_nonneg_right habs1 hq0.le

lemma cos_le_one_sub_two_div_pi_sq {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ Real.pi / 2) :
    Real.cos y ≤ 1 - 2 * (y / Real.pi) ^ 2 := by
  let g : ℝ → ℝ := fun t => 1 - 2 * (t / Real.pi) ^ 2 - Real.cos t
  have hmono : MonotoneOn g (Set.Icc 0 (Real.pi / 2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (Real.pi / 2))
    · exact Continuous.continuousOn (by continuity)
    · exact Differentiable.differentiableOn (by fun_prop)
    · intro t ht
      rw [interior_Icc] at ht
      have hderiv : deriv g t = Real.sin t - 4 * t / Real.pi ^ 2 := by
        have hd : HasDerivAt g (Real.sin t - 4 * t / Real.pi ^ 2) t := by
          have hd1 : HasDerivAt (fun x : ℝ => 1 - 2 * (x / Real.pi) ^ 2)
              (0 - 2 * (2 * (t / Real.pi) ^ (2 - 1) * (1 / Real.pi))) t :=
            (hasDerivAt_const t (1 : ℝ)).sub ((((hasDerivAt_id t).div_const Real.pi).pow 2).const_mul 2)
          refine (hd1.sub (Real.hasDerivAt_cos t)).congr_deriv ?_
          simp; ring
        exact hd.deriv
      rw [hderiv]
      have hsin := Real.mul_le_sin ht.1.le ht.2.le
      have hpi2 : (2 : ℝ) ≤ Real.pi := Real.two_le_pi
      have h4 : 4 * t / Real.pi ^ 2 ≤ 2 / Real.pi * t := by
        have hpi0 : 0 < Real.pi := Real.pi_pos
        rw [div_le_iff₀ (by positivity)]
        have : 2 / Real.pi * t * Real.pi ^ 2 = 2 * Real.pi * t := by field_simp
        rw [this]
        nlinarith [ht.1]
      linarith
  have hg0 : g 0 = 0 := by simp [g]
  have hge := hmono (Set.left_mem_Icc.2 (by positivity)) ⟨hy0, hy1⟩ hy0
  rw [hg0] at hge
  dsimp [g] at hge
  linarith

lemma abs_cos_pi_le_exp (x : ℝ) : |Real.cos (Real.pi * x)| ≤ Real.exp (-2 * (d1 x) ^ 2) := by
  let k : ℤ := round x
  have hcos : |Real.cos (Real.pi * x)| = Real.cos (Real.pi * d1 x) := by
    have hpi : Real.pi * x = Real.pi * (x - k) + k * Real.pi := by ring
    rw [hpi, Real.cos_add_int_mul_pi, abs_mul, abs_neg_one_zpow, one_mul]
    dsimp [d1]
    rw [← Real.cos_abs (Real.pi * (x - k)), abs_mul, abs_of_pos Real.pi_pos]
    exact abs_of_nonneg (Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [mul_nonneg Real.pi_pos.le (abs_nonneg (x - k)), Real.pi_pos],
       by nlinarith [Real.pi_pos, abs_sub_round x]⟩)
  rw [hcos]
  have hd0 : 0 ≤ Real.pi * d1 x := mul_nonneg Real.pi_pos.le (d1_nonneg x)
  have hd1 : Real.pi * d1 x ≤ Real.pi / 2 := by nlinarith [Real.pi_pos, d1_le_half x]
  have h1 := cos_le_one_sub_two_div_pi_sq hd0 hd1
  have hpi_div : Real.pi * d1 x / Real.pi = d1 x := by field_simp [Real.pi_ne_zero]
  rw [hpi_div] at h1
  have h2 : 1 - 2 * (d1 x) ^ 2 ≤ Real.exp (-2 * (d1 x) ^ 2) := by
    linarith [Real.add_one_le_exp (-2 * (d1 x) ^ 2)]
  exact le_trans h1 h2

/- ### Dirichlet Approximation via Pigeonhole -/

lemma dirichlet_approx (t : ℝ) (Q : ℕ) (hQ : 1 ≤ Q) :
    ∃ (a : ℤ) (q : ℕ), 1 ≤ q ∧ q ≤ Q ∧ Nat.Coprime a.natAbs q ∧
      |t - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * Q) := by
  let bucket : ℕ → ℕ := fun k => ⌊(Q : ℝ) * Int.fract ((k : ℝ) * t)⌋₊
  have hmaps : ∀ k ∈ Finset.range (Q + 1), bucket k ∈ Finset.range Q := by
    intro k _
    rw [Finset.mem_range]
    apply Nat.floor_lt' (by omega) |>.2
    have hfr := Int.fract_lt_one ((k : ℝ) * t)
    have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ
    nlinarith
  have hcard : (Finset.range Q).card < (Finset.range (Q + 1)).card := by
    simp
  obtain ⟨k₁, hk₁, k₂, hk₂, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  rw [Finset.mem_range] at hk₁ hk₂
  wlog hlt : k₁ < k₂ generalizing k₁ k₂
  · exact this k₂ hk₂ k₁ hk₁ hne.symm heq.symm (by omega)
  let q₀ : ℕ := k₂ - k₁
  let a₀ : ℤ := ⌊(k₂ : ℝ) * t⌋ - ⌊(k₁ : ℝ) * t⌋
  have hq₀_pos : 1 ≤ q₀ := by omega
  have hq₀_le : q₀ ≤ Q := by omega
  have hdiff : |(q₀ : ℝ) * t - (a₀ : ℝ)| ≤ 1 / (Q : ℝ) := by
    have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ
    have h1 : (bucket k₁ : ℝ) ≤ (Q : ℝ) * Int.fract ((k₁ : ℝ) * t) :=
      Nat.floor_le (mul_nonneg hQpos.le (Int.fract_nonneg _))
    have h2 : (Q : ℝ) * Int.fract ((k₁ : ℝ) * t) < (bucket k₁ : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have h3 : (bucket k₂ : ℝ) ≤ (Q : ℝ) * Int.fract ((k₂ : ℝ) * t) :=
      Nat.floor_le (mul_nonneg hQpos.le (Int.fract_nonneg _))
    have h4 : (Q : ℝ) * Int.fract ((k₂ : ℝ) * t) < (bucket k₂ : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    rw [heq] at h1 h2
    have hfr_abs : |Int.fract ((k₂ : ℝ) * t) - Int.fract ((k₁ : ℝ) * t)| ≤ 1 / (Q : ℝ) := by
      rw [abs_le]
      constructor <;> nlinarith [one_div_mul_cancel hQpos.ne']
    have heq_fr : (q₀ : ℝ) * t - (a₀ : ℝ) = Int.fract ((k₂ : ℝ) * t) - Int.fract ((k₁ : ℝ) * t) := by
      have hk : (q₀ : ℝ) = (k₂ : ℝ) - (k₁ : ℝ) := by
        have : k₁ + q₀ = k₂ := by omega
        have : (k₁ : ℝ) + q₀ = k₂ := by exact_mod_cast this
        linarith
      rw [hk]
      dsimp [a₀]
      rw [Int.fract, Int.fract]
      push_cast
      ring
    rwa [heq_fr]
  let g : ℕ := Nat.gcd a₀.natAbs q₀
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right _ hq₀_pos
  have hg_dvd_a : (g : ℤ) ∣ a₀ := Int.natCast_dvd.2 (Nat.gcd_dvd_left _ _)
  have hg_dvd_q : g ∣ q₀ := Nat.gcd_dvd_right _ _
  let q : ℕ := q₀ / g
  let a : ℤ := a₀ / (g : ℤ)
  have hq_pos : 1 ≤ q := Nat.div_pos (Nat.le_of_dvd hq₀_pos hg_dvd_q) hg_pos
  have hq_le : q ≤ Q := le_trans (Nat.div_le_self _ _) hq₀_le
  have hcop : Nat.Coprime a.natAbs q := by
    have ha_abs : a.natAbs = a₀.natAbs / g := by
      have := Int.natAbs_ediv a₀ g
      rw [if_pos (Or.inr (Or.inr hg_dvd_a)), add_zero] at this
      exact this
    rw [ha_abs]
    exact Nat.coprime_div_gcd_div_gcd hg_pos
  refine ⟨a, q, hq_pos, hq_le, hcop, ?_⟩
  have hq₀_eq : (q₀ : ℝ) = (q : ℝ) * g := by
    exact_mod_cast (Nat.div_mul_cancel hg_dvd_q).symm
  have ha₀_eq : (a₀ : ℝ) = (a : ℝ) * g := by
    exact_mod_cast (Int.ediv_mul_cancel hg_dvd_a).symm
  have hq₀pos : (0 : ℝ) < q₀ := by exact_mod_cast hq₀_pos
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq_pos
  have hgpos : (0 : ℝ) < g := by exact_mod_cast hg_pos
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ
  calc |t - (a : ℝ) / q| = |(q₀ : ℝ) * t - (a₀ : ℝ)| / (q₀ : ℝ) := by
        rw [← abs_of_pos hq₀pos, ← abs_div]
        congr 1
        rw [abs_of_pos hq₀pos, hq₀_eq, ha₀_eq]
        field_simp
    _ ≤ (1 / (Q : ℝ)) / (q₀ : ℝ) := div_le_div_of_nonneg_right hdiff hq₀pos.le
    _ = 1 / ((q₀ : ℝ) * Q) := by ring
    _ ≤ 1 / ((q : ℝ) * Q) := by
        apply one_div_le_one_div_of_le (mul_pos hqpos hQpos)
        have hqle0 : q ≤ q₀ := Nat.div_le_self _ _
        have : (q : ℝ) ≤ q₀ := by exact_mod_cast hqle0
        nlinarith

/- ### Large-q Bad Count on `[1, M]` -/

lemma d1_bad_count_large_q (M q : ℕ) (a : ℤ) (hq : 2 ≤ q) (hcop : Nat.Coprime a.natAbs q)
    (δ₀ : ℝ) (_hδ : 0 ≤ δ₀) :
    ((Finset.Icc 1 M).filter (fun b : ℕ => d1 ((b : ℝ) * a / q) ≤ δ₀)).card ≤
      (M / q + 1) * (2 * ⌊δ₀ * q⌋₊ + 2) := by
  let S : Finset ℕ := (Finset.Icc 1 M).filter (fun b => d1 ((b : ℝ) * a / q) ≤ δ₀)
  let R : Finset ℕ := (Finset.range (⌊δ₀ * q⌋₊ + 1)) ∪ ((Finset.range (⌊δ₀ * q⌋₊ + 1)).image (fun u => q - u))
  have hR_card : R.card ≤ 2 * ⌊δ₀ * q⌋₊ + 2 := by
    have hcard1 : (Finset.range (⌊δ₀ * q⌋₊ + 1)).card = ⌊δ₀ * q⌋₊ + 1 := Finset.card_range _
    have hcard2 : ((Finset.range (⌊δ₀ * q⌋₊ + 1)).image (fun u => q - u)).card ≤ ⌊δ₀ * q⌋₊ + 1 :=
      Finset.card_image_le.trans_eq hcard1
    have hcardu := Finset.card_union_le (Finset.range (⌊δ₀ * q⌋₊ + 1))
      ((Finset.range (⌊δ₀ * q⌋₊ + 1)).image (fun u => q - u))
    dsimp [R]
    omega
  let block : ℕ → Finset ℕ := fun k => (Finset.Icc (k * q + 1) (k * q + q)).filter
    (fun b => d1 ((b : ℝ) * a / q) ≤ δ₀)
  have hcover : S ⊆ (Finset.range (M / q + 1)).biUnion block := by
    intro b hb
    simp only [S, Finset.mem_filter, Finset.mem_Icc] at hb
    rw [Finset.mem_biUnion]
    refine ⟨(b - 1) / q, Finset.mem_range.2 ?_, ?_⟩
    · have : (b - 1) / q ≤ M / q := Nat.div_le_div_right (by omega)
      omega
    · simp only [block, Finset.mem_filter, Finset.mem_Icc]
      have hqpos : 0 < q := by omega
      have h1 := Nat.div_mul_le_self (b - 1) q
      have h2 := Nat.lt_div_mul_add (a := b - 1) hqpos
      refine ⟨⟨by omega, by omega⟩, hb.2⟩
  have hblock_card : ∀ k : ℕ, (block k).card ≤ R.card := by
    intro k
    let f : ℕ → ℕ := fun b => (((b : ℤ) * a) % q).toNat
    apply Finset.card_le_card_of_injOn f
    · intro b hb
      simp only [block, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hb
      have hqpos : 0 < q := by omega
      have hq_z : (0 : ℤ) < q := by exact_mod_cast hqpos
      set r : ℕ := f b
      have hr_lt : r < q := by
        have h1 : 0 ≤ ((b : ℤ) * a) % q := Int.emod_nonneg _ hq_z.ne'
        have h2 : ((b : ℤ) * a) % q < q := Int.emod_lt_of_pos _ hq_z
        dsimp [r, f]
        omega
      have hr_eq : (r : ℤ) = ((b : ℤ) * a) % q := by
        dsimp [r, f]
        exact Int.toNat_of_nonneg (Int.emod_nonneg _ hq_z.ne')
      have hd1_eq : d1 ((r : ℝ) / q) = d1 ((b : ℝ) * a / q) := by
        let d : ℤ := ((b : ℤ) * a) / q
        have hdiv : (b : ℤ) * a = d * q + r := by
          rw [hr_eq, Int.emod_def]
          dsimp [d]
          ring
        have hreal : (b : ℝ) * a / q = (r : ℝ) / q + (d : ℝ) := by
          have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hqpos.ne'
          have hdivR : (b : ℝ) * a = (d : ℝ) * q + r := by exact_mod_cast hdiv
          rw [hdivR]
          field_simp
          ring
        dsimp [d1]
        rw [hreal]
        have hround : round ((r : ℝ) / q + (d : ℝ)) = round ((r : ℝ) / q) + d :=
          round_add_intCast ((r : ℝ) / q) d
        rw [hround]
        push_cast
        congr 1
        ring
      have hd1_r : d1 ((r : ℝ) / q) ≤ δ₀ := hd1_eq ▸ hb.2
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hqpos
      have hr0 : 0 ≤ (r : ℝ) / q := by positivity
      have hr1 : (r : ℝ) / q < 1 := by
        rw [div_lt_one hq0]
        exact_mod_cast hr_lt
      have hround_cases : round ((r : ℝ) / q) = 0 ∨ round ((r : ℝ) / q) = 1 := by
        have hbd := abs_sub_round ((r : ℝ) / q)
        rw [abs_le] at hbd
        have hgt : (-1 : ℝ) < round ((r : ℝ) / q) := by linarith
        have hlt2 : (round ((r : ℝ) / q) : ℝ) < 2 := by linarith
        have h1' : (-1 : ℤ) < round ((r : ℝ) / q) := by exact_mod_cast hgt
        have h2' : round ((r : ℝ) / q) < 2 := by exact_mod_cast hlt2
        omega
      simp only [R, Finset.mem_coe, Finset.mem_union, Finset.mem_range, Finset.mem_image]
      rcases hround_cases with h0 | h1
      · left
        have hle : (r : ℝ) / q ≤ δ₀ := by
          have := hd1_r
          dsimp [d1] at this
          rw [h0, Int.cast_zero, sub_zero, abs_of_nonneg hr0] at this
          exact this
        have : (r : ℝ) ≤ δ₀ * q := (div_le_iff₀ hq0).1 hle
        have : r ≤ ⌊δ₀ * q⌋₊ := Nat.le_floor this
        omega
      · right
        have hle : 1 - (r : ℝ) / q ≤ δ₀ := by
          have := hd1_r
          dsimp [d1] at this
          rw [h1, Int.cast_one, abs_sub_comm, abs_of_nonneg (by linarith)] at this
          exact this
        have : ((q - r : ℕ) : ℝ) ≤ δ₀ * q := by
          rw [Nat.cast_sub hr_lt.le]
          have hsub : ((q : ℝ) - r) / q ≤ δ₀ := by
            have hqq : ((q : ℝ) - r) / q = 1 - (r : ℝ) / q := by field_simp
            linarith
          exact (div_le_iff₀ hq0).1 hsub
        have hqmr : q - r ≤ ⌊δ₀ * q⌋₊ := Nat.le_floor this
        exact ⟨q - r, by omega, by omega⟩
    · intro b₁ hb₁ b₂ hb₂ hfeq
      simp only [block, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hb₁ hb₂
      have hqpos : 0 < q := by omega
      have hq_z : (0 : ℤ) < q := by exact_mod_cast hqpos
      have heq_mod : ((b₁ : ℤ) * a) % q = ((b₂ : ℤ) * a) % q := by
        have h1 := Int.toNat_of_nonneg (Int.emod_nonneg ((b₁ : ℤ) * a) hq_z.ne')
        have h2 := Int.toNat_of_nonneg (Int.emod_nonneg ((b₂ : ℤ) * a) hq_z.ne')
        dsimp [f] at hfeq
        rw [← h1, ← h2, hfeq]
      have hdvd_a : (q : ℤ) ∣ ((b₁ : ℤ) - b₂) * a := by
        rw [sub_mul, Int.dvd_iff_emod_eq_zero, Int.sub_emod, heq_mod, sub_self, Int.zero_emod]
      have hcop_z : IsCoprime a (q : ℤ) := Int.isCoprime_iff_nat_coprime.2 (by simpa using hcop)
      have hdvd : (q : ℤ) ∣ (b₁ : ℤ) - b₂ := hcop_z.symm.dvd_of_dvd_mul_right hdvd_a
      obtain ⟨m, hm⟩ := hdvd
      have hlt_abs : ((b₁ : ℤ) - b₂).natAbs < q := by omega
      by_cases hm0 : m = 0
      · subst hm0; simp at hm; omega
      · have hm1 : 1 ≤ m.natAbs := Int.natAbs_pos.2 hm0
        have hgap : q ≤ ((b₁ : ℤ) - b₂).natAbs := by
          rw [hm, Int.natAbs_mul, Int.natAbs_natCast]
          exact Nat.le_mul_of_pos_right _ hm1
        omega
  change S.card ≤ _
  calc S.card ≤ ((Finset.range (M / q + 1)).biUnion block).card := Finset.card_le_card hcover
    _ ≤ ∑ k ∈ Finset.range (M / q + 1), (block k).card := Finset.card_biUnion_le
    _ ≤ ∑ _k ∈ Finset.range (M / q + 1), R.card := Finset.sum_le_sum fun k _ => hblock_card k
    _ = (M / q + 1) * R.card := by simp
    _ ≤ (M / q + 1) * (2 * ⌊δ₀ * q⌋₊ + 2) := Nat.mul_le_mul_left _ hR_card

/- ### Finite `Finset.powerset` Expectation & Variance & Exponential Moment -/

noncomputable def wPow (B : Finset ℕ) (p : ℝ) (C : Finset ℕ) : ℝ :=
  p ^ C.card * (1 - p) ^ (B.card - C.card)

lemma wPow_nonneg {B : Finset ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (C : Finset ℕ) :
    0 ≤ wPow B p C := by
  dsimp [wPow]
  exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (sub_nonneg.2 hp1) _)

lemma sum_powerset_wPow_insert {x : ℕ} {B : Finset ℕ} (hx : x ∉ B) (p : ℝ) (F : Finset ℕ → ℝ) :
    ∑ C ∈ (insert x B).powerset, wPow (insert x B) p C * F C =
      (1 - p) * ∑ C ∈ B.powerset, wPow B p C * F C +
        p * ∑ C ∈ B.powerset, wPow B p C * F (insert x C) := by
  rw [Finset.powerset_insert, Finset.sum_union]
  · have h1 : ∑ C ∈ B.powerset, wPow (insert x B) p C * F C =
        (1 - p) * ∑ C ∈ B.powerset, wPow B p C * F C := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun C hCB => ?_
      have hC_sub : C ⊆ B := Finset.mem_powerset.1 hCB
      have hcard : C.card ≤ B.card := Finset.card_le_card hC_sub
      dsimp [wPow]
      rw [Finset.card_insert_of_notMem hx, show B.card + 1 - C.card = (B.card - C.card) + 1 by omega,
        pow_succ]
      ring
    have h2 : ∑ C ∈ B.powerset.image (insert x), wPow (insert x B) p C * F C =
        p * ∑ C ∈ B.powerset, wPow B p C * F (insert x C) := by
      rw [Finset.sum_image, Finset.mul_sum]
      · refine Finset.sum_congr rfl fun C hCB => ?_
        have hC_sub : C ⊆ B := Finset.mem_powerset.1 hCB
        have hxC : x ∉ C := fun h => hx (hC_sub h)
        dsimp [wPow]
        rw [Finset.card_insert_of_notMem hx, Finset.card_insert_of_notMem hxC,
          show B.card + 1 - (C.card + 1) = B.card - C.card by omega, pow_succ]
        ring
      · intro C₁ hC₁ C₂ hC₂ heq
        have hx1 : x ∉ C₁ := fun h => hx (Finset.mem_powerset.1 hC₁ h)
        have hx2 : x ∉ C₂ := fun h => hx (Finset.mem_powerset.1 hC₂ h)
        have h1 : C₁ = (insert x C₁).erase x := (Finset.erase_insert hx1).symm
        rw [h1, heq, Finset.erase_insert hx2]
    rw [h1, h2]
  · rw [Finset.disjoint_left]
    intro C hC1 hC2
    simp only [Finset.mem_image, Finset.mem_powerset] at hC1 hC2
    obtain ⟨C', _, rfl⟩ := hC2
    exact hx (hC1 (Finset.mem_insert_self x C'))

/- ### Part 4: Weighted Powerset Moments, Net & Adjustment, Major/Minor Arcs -/

lemma sum_powerset_wPow_one (B : Finset ℕ) (p : ℝ) :
    ∑ C ∈ B.powerset, wPow B p C = 1 := by
  induction B using Finset.induction with
  | empty => simp [wPow]
  | @insert x B hx ih =>
    have h := sum_powerset_wPow_insert hx p (fun _ => (1 : ℝ))
    simp only [mul_one] at h
    rw [h, ih]
    ring

lemma sum_powerset_wPow_sum (B : Finset ℕ) (p : ℝ) (f : ℕ → ℝ) :
    ∑ C ∈ B.powerset, wPow B p C * (∑ b ∈ C, f b) = p * ∑ b ∈ B, f b := by
  induction B using Finset.induction with
  | empty => simp
  | @insert x B hx ih =>
    rw [sum_powerset_wPow_insert hx p (fun C => ∑ b ∈ C, f b)]
    have h2 : ∑ C ∈ B.powerset, wPow B p C * (∑ b ∈ insert x C, f b) =
        f x * ∑ C ∈ B.powerset, wPow B p C +
          ∑ C ∈ B.powerset, wPow B p C * (∑ b ∈ C, f b) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun C hCB => ?_
      have hxC : x ∉ C := fun h => hx (Finset.mem_powerset.1 hCB h)
      rw [Finset.sum_insert hxC]
      ring
    rw [h2, sum_powerset_wPow_one, ih, Finset.sum_insert hx]
    ring

lemma sum_powerset_wPow_var (B : Finset ℕ) (p : ℝ) (f : ℕ → ℝ) :
    ∑ C ∈ B.powerset, wPow B p C * (∑ b ∈ C, f b - p * ∑ b ∈ B, f b) ^ 2 =
      p * (1 - p) * ∑ b ∈ B, (f b) ^ 2 := by
  induction B using Finset.induction with
  | empty => simp
  | @insert x B hx ih =>
    rw [sum_powerset_wPow_insert hx p (fun C => (∑ b ∈ C, f b - p * ∑ b ∈ insert x B, f b) ^ 2)]
    set S : ℝ := ∑ b ∈ B, f b
    have hzero : ∑ C ∈ B.powerset, wPow B p C * (∑ b ∈ C, f b - p * S) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib, sum_powerset_wPow_sum,
        ← Finset.sum_mul, sum_powerset_wPow_one]
      ring
    have h1 : ∑ C ∈ B.powerset, wPow B p C * (∑ b ∈ C, f b - p * ∑ b ∈ insert x B, f b) ^ 2 =
        ∑ C ∈ B.powerset, wPow B p C * (∑ b ∈ C, f b - p * S) ^ 2 -
          2 * p * f x * ∑ C ∈ B.powerset, wPow B p C * (∑ b ∈ C, f b - p * S) +
          p ^ 2 * (f x) ^ 2 * ∑ C ∈ B.powerset, wPow B p C := by
      have hterm : ∀ C ∈ B.powerset,
          wPow B p C * (∑ b ∈ C, f b - p * ∑ b ∈ insert x B, f b) ^ 2 =
            wPow B p C * (∑ b ∈ C, f b - p * S) ^ 2 -
              2 * p * f x * (wPow B p C * (∑ b ∈ C, f b - p * S)) +
              p ^ 2 * (f x) ^ 2 * wPow B p C := by
        intro C _
        rw [Finset.sum_insert hx]
        dsimp [S]
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]
    have h2 : ∑ C ∈ B.powerset, wPow B p C * (∑ b ∈ insert x C, f b - p * ∑ b ∈ insert x B, f b) ^ 2 =
        ∑ C ∈ B.powerset, wPow B p C * (∑ b ∈ C, f b - p * S) ^ 2 +
          2 * (1 - p) * f x * ∑ C ∈ B.powerset, wPow B p C * (∑ b ∈ C, f b - p * S) +
          (1 - p) ^ 2 * (f x) ^ 2 * ∑ C ∈ B.powerset, wPow B p C := by
      have hterm : ∀ C ∈ B.powerset,
          wPow B p C * (∑ b ∈ insert x C, f b - p * ∑ b ∈ insert x B, f b) ^ 2 =
            wPow B p C * (∑ b ∈ C, f b - p * S) ^ 2 +
              2 * (1 - p) * f x * (wPow B p C * (∑ b ∈ C, f b - p * S)) +
              (1 - p) ^ 2 * (f x) ^ 2 * wPow B p C := by
        intro C hCB
        have hxC : x ∉ C := fun h => hx (Finset.mem_powerset.1 hCB h)
        rw [Finset.sum_insert hx, Finset.sum_insert hxC]
        dsimp [S]
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]
    rw [h1, h2, hzero, sum_powerset_wPow_one, ih, Finset.sum_insert hx]
    ring

lemma exp_neg_le_linear {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.exp (-t) ≤ 1 - (1 - Real.exp (-1)) * t := by
  by_cases ht_eq0 : t = 0
  · subst ht_eq0; simp
  by_cases ht_eq1 : t = 1
  · subst ht_eq1; simp
  have ht_pos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht_eq0)
  have ht_lt1 : t < 1 := lt_of_le_of_ne ht1 ht_eq1
  let g : ℝ → ℝ := fun u => Real.exp (-u) - (1 - (1 - Real.exp (-1)) * u)
  let g' : ℝ → ℝ := fun u => -Real.exp (-u) + (1 - Real.exp (-1))
  have hg_cont : Continuous g := by continuity
  have hg_deriv : ∀ u : ℝ, HasDerivAt g (g' u) u := by
    intro u
    have h1 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (Real.exp (-u) * (-1)) u :=
      (Real.hasDerivAt_exp (-u)).comp u ((hasDerivAt_id u).neg)
    have h2 : HasDerivAt (fun x : ℝ => 1 - (1 - Real.exp (-1)) * x) (0 - (1 - Real.exp (-1)) * 1) u :=
      (hasDerivAt_const u (1 : ℝ)).sub ((hasDerivAt_id u).const_mul (1 - Real.exp (-1)))
    refine (h1.sub h2).congr_deriv ?_
    dsimp [g']
    ring
  by_contra hgt
  push Not at hgt
  obtain ⟨c₁, hc₁, hslope1⟩ := exists_hasDerivAt_eq_slope g g' ht_pos hg_cont.continuousOn
    (fun u _ => hg_deriv u)
  obtain ⟨c₂, hc₂, hslope2⟩ := exists_hasDerivAt_eq_slope g g' ht_lt1 hg_cont.continuousOn
    (fun u _ => hg_deriv u)
  have hg0 : g 0 = 0 := by simp [g]
  have hg1 : g 1 = 0 := by simp [g]
  have h1pos : 0 < -Real.exp (-c₁) + (1 - Real.exp (-1)) := by
    dsimp [g'] at hslope1
    rw [hslope1, hg0, sub_zero]
    exact div_pos (by linarith) (sub_pos.2 ht_pos)
  have h2neg : -Real.exp (-c₂) + (1 - Real.exp (-1)) < 0 := by
    dsimp [g'] at hslope2
    rw [hslope2, hg1, zero_sub]
    exact div_neg_of_neg_of_pos (by linarith) (sub_pos.2 ht_lt1)
  have hc12 : -c₂ < -c₁ := by linarith [hc₁.2, hc₂.1]
  have hexp : Real.exp (-c₂) < Real.exp (-c₁) := Real.exp_strictMono hc12
  linarith

lemma sum_powerset_wPow_exp_le (B : Finset ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (g : ℕ → ℝ) (hg0 : ∀ b ∈ B, 0 ≤ g b) (hg1 : ∀ b ∈ B, g b ≤ 1) :
    ∑ C ∈ B.powerset, wPow B p C * Real.exp (- ∑ b ∈ C, g b) ≤
      Real.exp (- (1 - Real.exp (-1)) * p * ∑ b ∈ B, g b) := by
  induction B using Finset.induction with
  | empty => simp [wPow]
  | @insert x B hx ih =>
    have hg0' : ∀ b ∈ B, 0 ≤ g b := fun b hb => hg0 b (Finset.mem_insert_of_mem hb)
    have hg1' : ∀ b ∈ B, g b ≤ 1 := fun b hb => hg1 b (Finset.mem_insert_of_mem hb)
    have ih' := ih hg0' hg1'
    rw [sum_powerset_wPow_insert hx p (fun C => Real.exp (- ∑ b ∈ C, g b))]
    have h2 : ∑ C ∈ B.powerset, wPow B p C * Real.exp (- ∑ b ∈ insert x C, g b) =
        Real.exp (- g x) * ∑ C ∈ B.powerset, wPow B p C * Real.exp (- ∑ b ∈ C, g b) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun C hCB => ?_
      have hxC : x ∉ C := fun h => hx (Finset.mem_powerset.1 hCB h)
      rw [Finset.sum_insert hxC, neg_add, Real.exp_add]
      ring
    rw [h2]
    set S_lhs : ℝ := ∑ C ∈ B.powerset, wPow B p C * Real.exp (- ∑ b ∈ C, g b)
    have hS_nn : 0 ≤ S_lhs :=
      Finset.sum_nonneg fun C _ => mul_nonneg (wPow_nonneg hp0 hp1 C) (Real.exp_pos _).le
    have hx0 : 0 ≤ g x := hg0 x (Finset.mem_insert_self x B)
    have hx1 : g x ≤ 1 := hg1 x (Finset.mem_insert_self x B)
    have hfactor : (1 - p) + p * Real.exp (- g x) ≤
        Real.exp (- (1 - Real.exp (-1)) * p * g x) := by
      have hlin := exp_neg_le_linear hx0 hx1
      have hle1 : (1 - p) + p * Real.exp (- g x) ≤ 1 - (1 - Real.exp (-1)) * p * g x := by
        nlinarith
      have hle2 : 1 - (1 - Real.exp (-1)) * p * g x ≤ Real.exp (- (1 - Real.exp (-1)) * p * g x) := by
        linarith [Real.add_one_le_exp (- (1 - Real.exp (-1)) * p * g x)]
      exact le_trans hle1 hle2
    have hfactor_nn : 0 ≤ (1 - p) + p * Real.exp (- g x) := by
      have : 0 ≤ 1 - p := sub_nonneg.2 hp1
      positivity
    calc (1 - p) * S_lhs + p * (Real.exp (- g x) * S_lhs)
        = ((1 - p) + p * Real.exp (- g x)) * S_lhs := by ring
      _ ≤ Real.exp (- (1 - Real.exp (-1)) * p * g x) *
            Real.exp (- (1 - Real.exp (-1)) * p * ∑ b ∈ B, g b) :=
          mul_le_mul hfactor ih' hS_nn (Real.exp_pos _).le
      _ = Real.exp (- (1 - Real.exp (-1)) * p * ∑ b ∈ insert x B, g b) := by
          rw [← Real.exp_add, Finset.sum_insert hx]
          congr 1
          ring

lemma weighted_sum_filter_le {α : Type*} (s : Finset α) (w f : α → ℝ)
    (hw : ∀ x ∈ s, 0 ≤ w x) (hf : ∀ x ∈ s, 0 ≤ f x) {c : ℝ} (hc : 0 < c) :
    ∑ x ∈ s.filter (fun x => c ≤ f x), w x ≤ (∑ x ∈ s, w x * f x) / c := by
  rw [le_div_iff₀ hc, mul_comm, Finset.mul_sum]
  calc ∑ x ∈ s.filter (fun x => c ≤ f x), c * w x
      = ∑ x ∈ s.filter (fun x => c ≤ f x), w x * c := by
        refine Finset.sum_congr rfl fun x _ => mul_comm _ _
    _ ≤ ∑ x ∈ s.filter (fun x => c ≤ f x), w x * f x := by
        refine Finset.sum_le_sum fun x hx => ?_
        rw [Finset.mem_filter] at hx
        exact mul_le_mul_of_nonneg_left hx.2 (hw x hx.1)
    _ ≤ ∑ x ∈ s, w x * f x := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun x hx _ => ?_
        exact mul_nonneg (hw x hx) (hf x hx)

/- ### Part 4b: Minor-Arc Exponential Sum Lower Bound on `B` -/

lemma d1_neg (x : ℝ) : d1 (-x) = d1 x := by
  have h1 : ∀ y : ℝ, d1 (-y) ≤ d1 y := fun y => by
    calc d1 (-y) ≤ |-y - ((-round y : ℤ) : ℝ)| := d1_le_abs_sub_int (-y) (-round y)
      _ = |-(y - (round y : ℝ))| := by push_cast; ring_nf
      _ = d1 y := by rw [abs_neg]; rfl
  exact le_antisymm (h1 x) (by simpa using h1 (-x))

lemma minor_arc_sum_d1_sq_ge {B : Finset ℕ} {M : ℕ} {L T : ℝ}
    (hM : 1 ≤ M) (hL : 10 ≤ L) (hB_sub : B ⊆ Finset.Icc 1 M)
    (hB_lb : (M : ℝ) / (2 * L) ≤ (B.card : ℝ))
    (hT_pos : 0 < T) (hT_le : T ≤ (2 / 5 : ℝ) * (B.card : ℝ))
    (hB_nondiv : ∀ q : ℕ, 2 ≤ q → T ≤ ((B.filter (fun b => ¬ q ∣ b)).card : ℝ))
    {t : ℝ} (ht_lo : 1 / (3 * (M : ℝ)) ≤ |t|) (ht_hi : |t| ≤ 1 / 2) :
    T * (3 / (400 * L)) ^ 2 ≤ ∑ b ∈ B, (d1 ((b : ℝ) * t)) ^ 2 := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hLpos : 0 < L := by linarith
  obtain ⟨a, q, hq1, hq_le, hcop, hdir⟩ := dirichlet_approx t (4 * M) (by omega)
  have hq2 : 2 ≤ q := by
    by_contra hq_lt
    have hq_eq : q = 1 := by omega
    subst hq_eq
    have ha0 : a = 0 := by
      by_contra ha_ne
      have ha1 : (1 : ℝ) ≤ |(a : ℝ)| := by
        have : (1 : ℤ) ≤ |a| := Int.one_le_abs ha_ne
        exact_mod_cast this
      have htri : |t - (a : ℝ) / 1| ≥ |(a : ℝ)| - |t| := by
        have := abs_sub_abs_le_abs_sub (a : ℝ) t
        rw [abs_sub_comm] at this
        simpa using this
      have h14 : 1 / ((1 : ℝ) * ((4 * M : ℕ) : ℝ)) < 1 / 2 := by
        rw [one_div_lt_one_div (by positivity) (by positivity)]
        push_cast
        linarith
      simp only [Nat.cast_one, div_one] at hdir htri
      linarith
    subst ha0
    simp only [Int.cast_zero, zero_div, sub_zero, Nat.cast_one, one_mul] at hdir
    have h14 : 1 / ((4 * M : ℕ) : ℝ) < 1 / (3 * (M : ℝ)) := by
      rw [one_div_lt_one_div (by positivity) (by positivity)]
      push_cast
      linarith
    linarith
  have hqpos : (0 : ℝ) < q := by positivity
  have hshift : ∀ b ∈ B, d1 ((b : ℝ) * a / q) ≤ d1 ((b : ℝ) * t) + 1 / (4 * (q : ℝ)) := by
    intro b hb
    have hb_le : b ≤ M := (Finset.mem_Icc.1 (hB_sub hb)).2
    have hb_leR : (b : ℝ) ≤ M := by exact_mod_cast hb_le
    have hb_nn : (0 : ℝ) ≤ b := by positivity
    have htri := d1_add_le ((b : ℝ) * t) ((b : ℝ) * ((a : ℝ) / q - t))
    have harg : (b : ℝ) * t + (b : ℝ) * ((a : ℝ) / q - t) = (b : ℝ) * a / q := by ring
    rw [harg] at htri
    have htail : |(b : ℝ) * ((a : ℝ) / q - t)| ≤ 1 / (4 * (q : ℝ)) := by
      rw [abs_mul, abs_of_nonneg hb_nn, abs_sub_comm]
      have hdir' : |t - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * (4 * (M : ℝ))) := by
        simpa [Nat.cast_mul, Nat.cast_ofNat] using hdir
      have hmul := mul_le_mul_of_nonneg_left hdir' hb_nn
      have hbd : (b : ℝ) * (1 / ((q : ℝ) * (4 * (M : ℝ)))) ≤ 1 / (4 * (q : ℝ)) := by
        calc (b : ℝ) * (1 / ((q : ℝ) * (4 * (M : ℝ))))
            ≤ (M : ℝ) * (1 / ((q : ℝ) * (4 * (M : ℝ)))) := by gcongr
          _ = 1 / (4 * (q : ℝ)) := by field_simp
      linarith
    linarith
  by_cases hq_small : (q : ℝ) ≤ 100 * L
  · have hgood : ∀ b ∈ B.filter (fun b => ¬ q ∣ b),
        3 / (400 * L) ≤ d1 ((b : ℝ) * t) := by
      intro b hb
      rw [Finset.mem_filter] at hb
      have hcop_z : IsCoprime a (q : ℤ) := Int.isCoprime_iff_nat_coprime.2 (by simpa using hcop)
      have hndvd : ¬ (q : ℤ) ∣ (b : ℤ) * a := fun hd =>
        hb.2 (Int.natCast_dvd_natCast.1 (hcop_z.symm.dvd_of_dvd_mul_right hd))
      have hd_ge := d1_div_ge ((b : ℤ) * a) q (by positivity) hndvd
      have hcast : (((b : ℤ) * a : ℤ) : ℝ) / q = (b : ℝ) * a / q := by push_cast; ring
      rw [hcast] at hd_ge
      have hsh := hshift b hb.1
      have h34 : 3 / (400 * L) ≤ 1 / (q : ℝ) - 1 / (4 * (q : ℝ)) := by
        have hdiff : 1 / (q : ℝ) - 1 / (4 * (q : ℝ)) = 3 / (4 * (q : ℝ)) := by field_simp; ring
        rw [hdiff]
        exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
      linarith
    have hsum : ∑ b ∈ B.filter (fun b => ¬ q ∣ b), (3 / (400 * L)) ^ 2 ≤
        ∑ b ∈ B, (d1 ((b : ℝ) * t)) ^ 2 := by
      calc ∑ b ∈ B.filter (fun b => ¬ q ∣ b), (3 / (400 * L)) ^ 2
          ≤ ∑ b ∈ B.filter (fun b => ¬ q ∣ b), (d1 ((b : ℝ) * t)) ^ 2 := by
            refine Finset.sum_le_sum fun b hb => ?_
            have h1 := hgood b hb
            exact pow_le_pow_left₀ (by positivity) h1 2
        _ ≤ ∑ b ∈ B, (d1 ((b : ℝ) * t)) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              fun _ _ _ => sq_nonneg _
    rw [Finset.sum_const, nsmul_eq_mul] at hsum
    have hcnt := hB_nondiv q hq2
    have : T * (3 / (400 * L)) ^ 2 ≤
        ((B.filter (fun b => ¬ q ∣ b)).card : ℝ) * (3 / (400 * L)) ^ 2 :=
      mul_le_mul_of_nonneg_right hcnt (sq_nonneg _)
    linarith
  · push Not at hq_small
    set δ₀ : ℝ := 1 / (50 * L)
    have hδ0 : 0 ≤ δ₀ := by positivity
    have hbad := d1_bad_count_large_q M q a hq2 hcop δ₀ hδ0
    set S_bad := (Finset.Icc 1 M).filter (fun b : ℕ => d1 ((b : ℝ) * a / q) ≤ δ₀)
    have hbad_R : (S_bad.card : ℝ) ≤ (3 / 5 : ℝ) * (B.card : ℝ) := by
      have hbad' : (S_bad.card : ℝ) ≤ ((M / q + 1 : ℕ) : ℝ) * ((2 * ⌊δ₀ * q⌋₊ + 2 : ℕ) : ℝ) := by
        exact_mod_cast hbad
      have h1 : ((M / q + 1 : ℕ) : ℝ) ≤ 5 * (M : ℝ) / (q : ℝ) := by
        push_cast
        have hdiv : ((M / q : ℕ) : ℝ) ≤ (M : ℝ) / (q : ℝ) := by
          rw [le_div_iff₀ hqpos]
          exact_mod_cast Nat.div_mul_le_self M q
        have h1le : (1 : ℝ) ≤ 4 * (M : ℝ) / (q : ℝ) := by
          rw [le_div_iff₀ hqpos]
          have : (q : ℝ) ≤ 4 * (M : ℝ) := by exact_mod_cast hq_le
          linarith
        have h5 : (M : ℝ) / (q : ℝ) + 4 * (M : ℝ) / (q : ℝ) = 5 * (M : ℝ) / (q : ℝ) := by ring
        linarith
      have h2 : ((2 * ⌊δ₀ * q⌋₊ + 2 : ℕ) : ℝ) ≤ 3 * δ₀ * (q : ℝ) := by
        push_cast
        have hfl : (⌊δ₀ * q⌋₊ : ℝ) ≤ δ₀ * (q : ℝ) := Nat.floor_le (by positivity)
        have h2lt : (2 : ℝ) ≤ δ₀ * (q : ℝ) := by
          dsimp [δ₀]
          rw [one_div_mul_eq_div, le_div_iff₀ (by positivity)]
          linarith
        linarith
      have hprod : (S_bad.card : ℝ) ≤ (5 * (M : ℝ) / (q : ℝ)) * (3 * δ₀ * (q : ℝ)) :=
        hbad'.trans (mul_le_mul h1 h2 (by positivity) (by positivity))
      have hsimp : (5 * (M : ℝ) / (q : ℝ)) * (3 * δ₀ * (q : ℝ)) = (3 / 10 : ℝ) * ((M : ℝ) / L) := by
        dsimp [δ₀]
        field_simp
        ring
      rw [hsimp] at hprod
      have hML : (M : ℝ) / L ≤ 2 * (B.card : ℝ) := by
        have := hB_lb
        rw [div_le_iff₀ (by positivity)] at this
        rw [div_le_iff₀ hLpos]
        linarith
      linarith
    set G : Finset ℕ := B.filter (fun b : ℕ => δ₀ < d1 ((b : ℝ) * a / q))
    have hB_split : B.card ≤ G.card + (B ∩ S_bad).card := by
      have hsub : B ⊆ G ∪ (B ∩ S_bad) := by
        intro b hb
        by_cases hlt : δ₀ < d1 ((b : ℝ) * a / q)
        · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hb, hlt⟩)
        · push Not at hlt
          exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hb, Finset.mem_filter.2 ⟨hB_sub hb, hlt⟩⟩)
      exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hG_card : (2 / 5 : ℝ) * (B.card : ℝ) ≤ (G.card : ℝ) := by
      have h1 : ((B ∩ S_bad).card : ℝ) ≤ (S_bad.card : ℝ) := by
        exact_mod_cast Finset.card_le_card Finset.inter_subset_right
      have h2 : (B.card : ℝ) ≤ (G.card : ℝ) + ((B ∩ S_bad).card : ℝ) := by exact_mod_cast hB_split
      linarith
    have hgood : ∀ b ∈ G, 3 / (400 * L) ≤ d1 ((b : ℝ) * t) := by
      intro b hb
      rw [Finset.mem_filter] at hb
      have hsh := hshift b hb.1
      have htail : 1 / (4 * (q : ℝ)) ≤ 1 / (400 * L) := by
        rw [one_div_le_one_div (by positivity) (by positivity)]
        linarith
      have : 3 / (400 * L) ≤ δ₀ - 1 / (400 * L) := by
        dsimp [δ₀]
        have : 1 / (50 * L) - 1 / (400 * L) = 7 / (400 * L) := by field_simp; ring
        rw [this]
        gcongr
        norm_num
      linarith [hb.2]
    have hsum : ∑ b ∈ G, (3 / (400 * L)) ^ 2 ≤ ∑ b ∈ B, (d1 ((b : ℝ) * t)) ^ 2 := by
      calc ∑ b ∈ G, (3 / (400 * L)) ^ 2
          ≤ ∑ b ∈ G, (d1 ((b : ℝ) * t)) ^ 2 := by
            refine Finset.sum_le_sum fun b hb => pow_le_pow_left₀ (by positivity) (hgood b hb) 2
        _ ≤ ∑ b ∈ B, (d1 ((b : ℝ) * t)) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              fun _ _ _ => sq_nonneg _
    rw [Finset.sum_const, nsmul_eq_mul] at hsum
    have : T * (3 / (400 * L)) ^ 2 ≤ (G.card : ℝ) * (3 / (400 * L)) ^ 2 :=
      mul_le_mul_of_nonneg_right (hT_le.trans hG_card) (sq_nonneg _)
    linarith

/- ### Part 4c: Net Covering & Deterministic Subset Adjustment -/

noncomputable def arcNet (M : ℕ) (L : ℝ) : Finset ℝ :=
  (Finset.range (⌊(M : ℝ) * L ^ 4⌋₊ + 1)).image
    (fun j : ℕ => min (1 / 2 : ℝ) (1 / (3 * (M : ℝ)) + (j : ℝ) / ((M : ℝ) * L ^ 4)))

lemma arcNet_card_le (M : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    ((arcNet M L).card : ℝ) ≤ (M : ℝ) * L ^ 4 + 1 := by
  have h1 : (arcNet M L).card ≤ ⌊(M : ℝ) * L ^ 4⌋₊ + 1 :=
    (Finset.card_image_le).trans_eq (Finset.card_range _)
  have h2 : ((arcNet M L).card : ℝ) ≤ (⌊(M : ℝ) * L ^ 4⌋₊ : ℝ) + 1 := by exact_mod_cast h1
  have h3 : (⌊(M : ℝ) * L ^ 4⌋₊ : ℝ) ≤ (M : ℝ) * L ^ 4 := Nat.floor_le (by positivity)
  linarith

lemma arcNet_mem_Icc {M : ℕ} (hM : 1 ≤ M) {L : ℝ} {t : ℝ} (ht : t ∈ arcNet M L) :
    1 / (3 * (M : ℝ)) ≤ t ∧ t ≤ 1 / 2 := by
  simp only [arcNet, Finset.mem_image, Finset.mem_range] at ht
  obtain ⟨j, _, rfl⟩ := ht
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have h3M : 1 / (3 * (M : ℝ)) ≤ 1 / 2 := by
    rw [one_div_le_one_div (by positivity) (by positivity)]
    linarith
  refine ⟨le_min h3M ?_, min_le_left _ _⟩
  exact le_add_of_nonneg_right (by positivity)

lemma arcNet_cover {M : ℕ} (hM : 1 ≤ M) (_hL : 1 ≤ L) {t : ℝ}
    (ht_lo : 1 / (3 * (M : ℝ)) ≤ t) (ht_hi : t ≤ 1 / 2) :
    ∃ t' ∈ arcNet M L, |t - t'| ≤ 1 / ((M : ℝ) * L ^ 4) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hMLpos : 0 < (M : ℝ) * L ^ 4 := by positivity
  set u : ℝ := (t - 1 / (3 * (M : ℝ))) * ((M : ℝ) * L ^ 4)
  have hu0 : 0 ≤ u := mul_nonneg (sub_nonneg.2 ht_lo) hMLpos.le
  have hu_hi : u ≤ (M : ℝ) * L ^ 4 / 2 := by
    have : t - 1 / (3 * (M : ℝ)) ≤ 1 / 2 := by linarith [show (0 : ℝ) < 1 / (3 * (M : ℝ)) by positivity]
    have := mul_le_mul_of_nonneg_right this hMLpos.le
    linarith
  set j : ℕ := ⌊u⌋₊
  have hj_lt : j < ⌊(M : ℝ) * L ^ 4⌋₊ + 1 := by
    have hj_le : (j : ℝ) ≤ u := Nat.floor_le hu0
    have hu_lt : u < (⌊(M : ℝ) * L ^ 4⌋₊ : ℝ) + 1 := by
      have := Nat.lt_floor_add_one ((M : ℝ) * L ^ 4)
      linarith
    exact_mod_cast lt_of_le_of_lt hj_le hu_lt
  set tj : ℝ := 1 / (3 * (M : ℝ)) + (j : ℝ) / ((M : ℝ) * L ^ 4)
  have htj_le : tj ≤ t := by
    have hj_le : (j : ℝ) ≤ u := Nat.floor_le hu0
    have hdiv : (j : ℝ) / ((M : ℝ) * L ^ 4) ≤ t - 1 / (3 * (M : ℝ)) := by
      rw [div_le_iff₀ hMLpos]
      exact hj_le
    linarith
  have htj_min : min (1 / 2 : ℝ) tj = tj := min_eq_right (htj_le.trans ht_hi)
  refine ⟨min (1 / 2 : ℝ) tj, Finset.mem_image.2 ⟨j, Finset.mem_range.2 hj_lt, rfl⟩, ?_⟩
  rw [htj_min, abs_of_nonneg (sub_nonneg.2 htj_le)]
  have hu_lt : u < (j : ℝ) + 1 := Nat.lt_floor_add_one u
  have hdiv2 : t - 1 / (3 * (M : ℝ)) < ((j : ℝ) + 1) / ((M : ℝ) * L ^ 4) := by
    rw [lt_div_iff₀ hMLpos]
    exact hu_lt
  have : ((j : ℝ) + 1) / ((M : ℝ) * L ^ 4) =
      (j : ℝ) / ((M : ℝ) * L ^ 4) + 1 / ((M : ℝ) * L ^ 4) := by ring
  linarith

lemma shrink_exists (B_hi C : Finset ℕ) (target M : ℕ)
    (hB_hi : ∀ b ∈ B_hi, b ≤ M) (hlt : target < ∑ b ∈ C, b)
    (hlow : ∑ b ∈ C \ B_hi, b ≤ target) :
    ∃ C' ⊆ C, target ≤ ∑ b ∈ C', b ∧ ∑ b ∈ C', b ≤ target + M ∧ (C \ C') ⊆ B_hi := by
  induction hn : C.card using Nat.strong_induction_on generalizing C with
  | h k ih =>
    by_cases hdone : ∑ b ∈ C, b ≤ target + M
    · exact ⟨C, Subset.rfl, hlt.le, hdone, by simp⟩
    · push Not at hdone
      have hne : (C ∩ B_hi).Nonempty := by
        by_contra hempty
        rw [Finset.not_nonempty_iff_eq_empty] at hempty
        have hdiff : C \ B_hi = C := by
          rw [Finset.sdiff_eq_self_iff_disjoint, Finset.disjoint_iff_inter_eq_empty]
          exact hempty
        rw [hdiff] at hlow
        omega
      obtain ⟨x, hx⟩ := hne
      rw [Finset.mem_inter] at hx
      set C1 := C.erase x
      have hxC : x ∈ C := hx.1
      have hC1_card : C1.card < k := by
        rw [← hn]
        exact Finset.card_erase_lt_of_mem hxC
      have hx_le : x ≤ M := hB_hi x hx.2
      have hsum1 : ∑ b ∈ C1, b + x = ∑ b ∈ C, b := Finset.sum_erase_add C _ hxC
      have hlt1 : target < ∑ b ∈ C1, b := by omega
      have hlow1 : ∑ b ∈ C1 \ B_hi, b ≤ target := by
        calc ∑ b ∈ C1 \ B_hi, b
            ≤ ∑ b ∈ C \ B_hi, b :=
              Finset.sum_le_sum_of_subset (Finset.sdiff_subset_sdiff (Finset.erase_subset _ _) Subset.rfl)
          _ ≤ target := hlow
      obtain ⟨C', hC1, hge', hle', hdiff'⟩ := ih C1.card hC1_card C1 hlt1 hlow1 rfl
      refine ⟨C', hC1.trans (Finset.erase_subset _ _), hge', hle', ?_⟩
      intro y hy
      rw [Finset.mem_sdiff] at hy
      by_cases hyx : y = x
      · exact hyx ▸ hx.2
      · exact hdiff' (Finset.mem_sdiff.2 ⟨Finset.mem_erase.2 ⟨hyx, hy.1⟩, hy.2⟩)

lemma grow_exists (B B_hi C : Finset ℕ) (target M : ℕ)
    (hCB : C ⊆ B) (hB_hi : ∀ b ∈ B_hi, b ≤ M) (hlt : ∑ b ∈ C, b < target)
    (hhi : target ≤ ∑ b ∈ C ∪ (B ∩ B_hi), b) :
    ∃ C', C ⊆ C' ∧ C' ⊆ B ∧ target ≤ ∑ b ∈ C', b + M ∧ ∑ b ∈ C', b ≤ target ∧ (C' \ C) ⊆ B_hi := by
  set D := B \ C
  induction hn : D.card using Nat.strong_induction_on generalizing C D with
  | h k ih =>
    by_cases hdone : target ≤ ∑ b ∈ C, b + M
    · exact ⟨C, Subset.rfl, hCB, hdone, hlt.le, by simp⟩
    · push Not at hdone
      have hne : (D ∩ B_hi).Nonempty := by
        by_contra hempty
        rw [Finset.not_nonempty_iff_eq_empty] at hempty
        have hsub : C ∪ (B ∩ B_hi) ⊆ C := by
          intro y hy
          rcases Finset.mem_union.1 hy with hyC | hyB
          · exact hyC
          · by_contra hyC'
            have : y ∈ D ∩ B_hi :=
              Finset.mem_inter.2 ⟨Finset.mem_sdiff.2 ⟨(Finset.mem_inter.1 hyB).1, hyC'⟩,
                (Finset.mem_inter.1 hyB).2⟩
            rw [hempty] at this
            simp at this
        have hsum_le : ∑ b ∈ C ∪ (B ∩ B_hi), b ≤ ∑ b ∈ C, b :=
          Finset.sum_le_sum_of_subset hsub
        omega
      obtain ⟨x, hx⟩ := hne
      rw [Finset.mem_inter, Finset.mem_sdiff] at hx
      set C1 := insert x C
      have hxC : x ∉ C := hx.1.2
      have hC1B : C1 ⊆ B := Finset.insert_subset_iff.2 ⟨hx.1.1, hCB⟩
      have hD1_eq : B \ C1 = D.erase x := by
        ext y
        simp only [D, C1, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
        tauto
      have hD1_card : (B \ C1).card < k := by
        rw [hD1_eq, ← hn]
        exact Finset.card_erase_lt_of_mem (Finset.mem_sdiff.2 hx.1)
      have hx_le : x ≤ M := hB_hi x hx.2
      have hsum1 : ∑ b ∈ C1, b = x + ∑ b ∈ C, b := Finset.sum_insert hxC
      have hlt1 : ∑ b ∈ C1, b < target := by omega
      have hhi1 : target ≤ ∑ b ∈ C1 ∪ (B ∩ B_hi), b := by
        calc target ≤ ∑ b ∈ C ∪ (B ∩ B_hi), b := hhi
          _ ≤ ∑ b ∈ C1 ∪ (B ∩ B_hi), b :=
            Finset.sum_le_sum_of_subset (Finset.union_subset_union_left (Finset.subset_insert _ _))
      obtain ⟨C', hC1', hC'B, hge', hle', hdiff'⟩ :=
        ih (B \ C1).card hD1_card C1 hC1B hlt1 hhi1 rfl
      refine ⟨C', (Finset.subset_insert _ _).trans hC1', hC'B, hge', hle', ?_⟩
      intro y hy
      rw [Finset.mem_sdiff] at hy
      by_cases hyx : y = x
      · exact hyx ▸ hx.2
      · exact hdiff' (Finset.mem_sdiff.2 ⟨hy.1, fun h => hy.2 (Finset.mem_of_mem_insert_of_ne h hyx)⟩)

/- ### Part 4d: Major/Minor Arc Integration & Subset-Sum Existence -/

lemma one_sub_le_cos (y : ℝ) : 1 - y ^ 2 / 2 ≤ Real.cos y := by
  have hnonneg : ∀ t : ℝ, 0 ≤ t → 1 - t ^ 2 / 2 ≤ Real.cos t := by
    intro t ht0
    let f : ℝ → ℝ := fun u => Real.cos u - (1 - u ^ 2 / 2)
    have hmono : MonotoneOn f (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      · exact Continuous.continuousOn (by continuity)
      · exact Differentiable.differentiableOn (by fun_prop)
      · intro u hu
        rw [interior_Ici] at hu
        have hd : HasDerivAt f (-Real.sin u + u) u := by
          have h1 : HasDerivAt (fun x : ℝ => 1 - x ^ 2 / 2) (-u) u := by
            have := ((hasDerivAt_id u).pow 2).div_const 2
            refine ((hasDerivAt_const u (1 : ℝ)).sub this).congr_deriv ?_
            simp [id]
          refine ((Real.hasDerivAt_cos u).sub h1).congr_deriv ?_
          ring
        rw [hd.deriv]
        linarith [Real.sin_le hu.le]
    have hge := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht0) ht0
    dsimp [f] at hge
    simp only [Real.cos_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
      sub_zero] at hge
    linarith
  by_cases hy : 0 ≤ y
  · exact hnonneg y hy
  · have := hnonneg (-y) (by linarith)
    simpa [Real.cos_neg, neg_sq] using this

lemma one_sub_sum_le_prod_one_sub {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx0 : ∀ i ∈ s, 0 ≤ x i) (hx1 : ∀ i ∈ s, x i ≤ 1) :
    1 - ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 - x i) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    have hx0' : ∀ i ∈ s, 0 ≤ x i := fun i hi => hx0 i (Finset.mem_insert_of_mem hi)
    have hx1' : ∀ i ∈ s, x i ≤ 1 := fun i hi => hx1 i (Finset.mem_insert_of_mem hi)
    have ih' := ih hx0' hx1'
    have ha0 : 0 ≤ x a := hx0 a (Finset.mem_insert_self a s)
    have ha1 : x a ≤ 1 := hx1 a (Finset.mem_insert_self a s)
    have hprod_nn : 0 ≤ ∏ i ∈ s, (1 - x i) :=
      Finset.prod_nonneg fun i hi => sub_nonneg.2 (hx1' i hi)
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have h1 : (1 - x a) * (1 - ∑ i ∈ s, x i) ≤ (1 - x a) * ∏ i ∈ s, (1 - x i) :=
      mul_le_mul_of_nonneg_left ih' (sub_nonneg.2 ha1)
    have h2 : 1 - (x a + ∑ i ∈ s, x i) ≤ (1 - x a) * (1 - ∑ i ∈ s, x i) := by
      have hs0 : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg hx0'
      nlinarith
    exact le_trans h2 h1

lemma integral_cos_pos_of_arc_bounds (g : ℝ → ℝ) (a r c_min V : ℝ)
    (ha_pos : 0 < a) (hr_pos : 0 < r) (hra : r ≤ a) (ha_half : a ≤ 1 / 2)
    (hr_val : r = 1 / (4 * Real.sqrt V)) (hVpos : 0 < V)
    (hg_int : ∀ x y : ℝ, IntervalIntegrable g MeasureTheory.volume x y)
    (hg_nonneg_mid : ∀ t ∈ Set.Icc (-a) a, 0 ≤ g t)
    (hg_maj : ∀ t ∈ Set.Icc (-r) r, (1 / 4 : ℝ) ≤ g t)
    (hg_minor : ∀ t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2), a ≤ |t| → |g t| ≤ Real.exp (-2 * c_min))
    (hc_win : Real.exp (-2 * c_min) < 1 / (8 * Real.sqrt V)) :
    0 < ∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ), g t := by
  have hint_mid_ge : 1 / (8 * Real.sqrt V) ≤ ∫ t in (-a)..a, g t := by
    have hsplit1 := (intervalIntegral.integral_add_adjacent_intervals
      (hg_int (-a) (-r)) (hg_int (-r) a)).symm
    have hsplit2 := (intervalIntegral.integral_add_adjacent_intervals
      (hg_int (-r) r) (hg_int r a)).symm
    have hleft_nn : 0 ≤ ∫ t in (-a)..(-r), g t := by
      apply intervalIntegral.integral_nonneg (by linarith)
      intro t ht
      exact hg_nonneg_mid t ⟨ht.1, ht.2.trans (by linarith)⟩
    have hright_nn : 0 ≤ ∫ t in r..a, g t := by
      apply intervalIntegral.integral_nonneg hra
      intro t ht
      exact hg_nonneg_mid t ⟨(by linarith : -a ≤ r).trans ht.1, ht.2⟩
    have hr_int : 1 / (8 * Real.sqrt V) ≤ ∫ t in (-r)..r, g t := by
      have hconst : (1 / (8 * Real.sqrt V) : ℝ) = ∫ _t in (-r)..r, (1 / 4 : ℝ) := by
        rw [intervalIntegral.integral_const, smul_eq_mul, hr_val]
        field_simp
        ring
      rw [hconst]
      exact intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const (hg_int (-r) r) hg_maj
    linarith
  have hint_left_bd : |∫ t in (-1 / 2 : ℝ)..(-a), g t| ≤ (1 / 2 : ℝ) * Real.exp (-2 * c_min) := by
    have hbound : ∀ t ∈ Set.uIoc (-1 / 2 : ℝ) (-a), ‖g t‖ ≤ Real.exp (-2 * c_min) := by
      intro t ht
      rw [Set.uIoc_of_le (by linarith)] at ht
      rw [Real.norm_eq_abs]
      refine hg_minor t ⟨ht.1.le, ht.2.trans (by linarith)⟩ ?_
      rw [abs_of_nonpos (ht.2.trans (by linarith))]
      linarith [ht.2]
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ -a - (-1 / 2 : ℝ))] at hnorm
    have hlen : -a - (-1 / 2 : ℝ) ≤ 1 / 2 := by linarith
    exact hnorm.trans ((mul_le_mul_of_nonneg_left hlen (Real.exp_pos _).le).trans_eq (mul_comm _ _))
  have hint_right_bd : |∫ t in a..(1 / 2 : ℝ), g t| ≤ (1 / 2 : ℝ) * Real.exp (-2 * c_min) := by
    have hbound : ∀ t ∈ Set.uIoc a (1 / 2 : ℝ), ‖g t‖ ≤ Real.exp (-2 * c_min) := by
      intro t ht
      rw [Set.uIoc_of_le ha_half] at ht
      rw [Real.norm_eq_abs]
      refine hg_minor t ⟨(by linarith : (-1 / 2 : ℝ) ≤ a).trans ht.1.le, ht.2⟩ ?_
      rw [abs_of_nonneg ((by linarith : 0 ≤ a).trans ht.1.le)]
      exact ht.1.le
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ (1 / 2 : ℝ) - a)] at hnorm
    have hlen : (1 / 2 : ℝ) - a ≤ 1 / 2 := by linarith
    exact hnorm.trans ((mul_le_mul_of_nonneg_left hlen (Real.exp_pos _).le).trans_eq (mul_comm _ _))
  have hsplit1 := (intervalIntegral.integral_add_adjacent_intervals
    (hg_int (-1 / 2) (-a)) (hg_int (-a) (1 / 2))).symm
  have hsplit2 := (intervalIntegral.integral_add_adjacent_intervals
    (hg_int (-a) a) (hg_int a (1 / 2))).symm
  have h1 := (abs_le.1 hint_left_bd).1
  have h2 := (abs_le.1 hint_right_bd).1
  linarith

lemma exists_subset_sum_eq_of_arc_bounds (C : Finset ℕ) (M M' : ℕ) {c_min : ℝ}
    (hM : 1 ≤ M) (hC_sub : C ⊆ Finset.Icc 1 M)
    (hsum : |(1 / 2 : ℝ) * ∑ b ∈ C, (b : ℝ) - M'| ≤ (M : ℝ) / 2)
    (hV : (9 : ℝ) * (M : ℝ) ^ 2 ≤ 16 * ∑ b ∈ C, (b : ℝ) ^ 2)
    (hminor : ∀ t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2),
      1 / (3 * (M : ℝ)) ≤ |t| → c_min ≤ ∑ b ∈ C, (d1 ((b : ℝ) * t)) ^ 2)
    (hc_win : Real.exp (-2 * c_min) < 1 / (8 * Real.sqrt (∑ b ∈ C, (b : ℝ) ^ 2))) :
    ∃ A ⊆ C, ∑ b ∈ A, b = M' := by
  set V : ℝ := ∑ b ∈ C, (b : ℝ) ^ 2
  set Δ : ℝ := (1 / 2 : ℝ) * ∑ b ∈ C, (b : ℝ) - M'
  set g : ℝ → ℝ := fun t => Real.cos (2 * Real.pi * Δ * t) * ∏ b ∈ C, Real.cos (Real.pi * b * t)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hVpos : 0 < V := by
    have : 0 < (9 : ℝ) * (M : ℝ) ^ 2 := by positivity
    linarith
  set a : ℝ := 1 / (3 * (M : ℝ))
  set r : ℝ := 1 / (4 * Real.sqrt V)
  have ha_pos : 0 < a := by positivity
  have hr_pos : 0 < r := by positivity
  have hra : r ≤ a := by
    dsimp [r, a]
    rw [one_div_le_one_div (by positivity) (by positivity)]
    have hsq : (3 * (M : ℝ)) ^ 2 ≤ (4 * Real.sqrt V) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hVpos.le]
      linarith
    exact le_of_sq_le_sq hsq (by positivity)
  have ha_half : a ≤ 1 / 2 := by
    dsimp [a]
    rw [one_div_le_one_div (by positivity) (by positivity)]
    linarith
  have hg_cont : Continuous g := by continuity
  have hg_int : ∀ x y : ℝ, IntervalIntegrable g MeasureTheory.volume x y :=
    fun x y => hg_cont.intervalIntegrable x y
  have hg_nonneg_mid : ∀ t ∈ Set.Icc (-a) a, 0 ≤ g t := by
    intro t ht
    have ht_abs : |t| ≤ a := abs_le.2 ht
    have hcos1 : 0 ≤ Real.cos (2 * Real.pi * Δ * t) := by
      apply Real.cos_nonneg_of_mem_Icc
      have hbd : |2 * Real.pi * Δ * t| ≤ Real.pi / 2 := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2),
          abs_of_pos Real.pi_pos]
        calc 2 * Real.pi * |Δ| * |t|
            ≤ 2 * Real.pi * ((M : ℝ) / 2) * a := by gcongr
          _ = Real.pi / 3 := by dsimp [a]; field_simp
          _ ≤ Real.pi / 2 := by linarith [Real.pi_pos]
      exact abs_le.1 hbd
    have hcos2 : 0 ≤ ∏ b ∈ C, Real.cos (Real.pi * b * t) := by
      refine Finset.prod_nonneg fun b hb => ?_
      apply Real.cos_nonneg_of_mem_Icc
      have hb_le : (b : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.1 (hC_sub hb)).2
      have hbd : |Real.pi * b * t| ≤ Real.pi / 2 := by
        rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_nonneg (by positivity)]
        calc Real.pi * b * |t|
            ≤ Real.pi * M * a := by gcongr
          _ = Real.pi / 3 := by dsimp [a]; field_simp
          _ ≤ Real.pi / 2 := by linarith [Real.pi_pos]
      exact abs_le.1 hbd
    exact mul_nonneg hcos1 hcos2
  have hg_maj : ∀ t ∈ Set.Icc (-r) r, (1 / 4 : ℝ) ≤ g t := by
    intro t ht
    have ht_abs : |t| ≤ r := abs_le.2 ht
    have hta : |t| ≤ a := ht_abs.trans hra
    have hcos1 : (1 / 2 : ℝ) ≤ Real.cos (2 * Real.pi * Δ * t) := by
      have hbd : |2 * Real.pi * Δ * t| ≤ Real.pi / 3 := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2),
          abs_of_pos Real.pi_pos]
        calc 2 * Real.pi * |Δ| * |t|
            ≤ 2 * Real.pi * ((M : ℝ) / 2) * a := by gcongr
          _ = Real.pi / 3 := by dsimp [a]; field_simp
      have hanti := Real.strictAntiOn_cos.antitoneOn
      have hmem1 : |2 * Real.pi * Δ * t| ∈ Set.Icc 0 Real.pi :=
        ⟨abs_nonneg _, hbd.trans (by linarith [Real.pi_pos])⟩
      have hmem2 : Real.pi / 3 ∈ Set.Icc 0 Real.pi := ⟨by positivity, by linarith [Real.pi_pos]⟩
      have hle := hanti hmem1 hmem2 hbd
      rw [Real.cos_pi_div_three, Real.cos_abs] at hle
      exact hle
    have hprod_ge : (1 / 2 : ℝ) ≤ ∏ b ∈ C, Real.cos (Real.pi * b * t) := by
      have hterm : ∀ b ∈ C, 1 - (Real.pi * b * t) ^ 2 / 2 ≤ Real.cos (Real.pi * b * t) :=
        fun b _ => one_sub_le_cos _
      have hx0 : ∀ b ∈ C, 0 ≤ (Real.pi * b * t) ^ 2 / 2 := fun b _ => by positivity
      have hx1 : ∀ b ∈ C, (Real.pi * b * t) ^ 2 / 2 ≤ 1 := by
        intro b hb
        have hb_le : (b : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.1 (hC_sub hb)).2
        have habs : |Real.pi * b * t| ≤ Real.pi / 3 := by
          rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_nonneg (by positivity)]
          calc Real.pi * b * |t|
              ≤ Real.pi * M * a := by gcongr
            _ = Real.pi / 3 := by dsimp [a]; field_simp
        have hsq : (Real.pi * b * t) ^ 2 ≤ (Real.pi / 3) ^ 2 := by
          calc (Real.pi * b * t) ^ 2 = |Real.pi * b * t| ^ 2 := (sq_abs _).symm
            _ ≤ (Real.pi / 3) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
        have hpi4 : Real.pi < 4 := Real.pi_lt_four
        have hpi9 : (Real.pi / 3) ^ 2 / 2 ≤ 1 := by nlinarith [Real.pi_pos]
        linarith
      have h1 : ∏ b ∈ C, (1 - (Real.pi * b * t) ^ 2 / 2) ≤ ∏ b ∈ C, Real.cos (Real.pi * b * t) := by
        refine Finset.prod_le_prod (fun b hb => sub_nonneg.2 (hx1 b hb)) hterm
      have h2 := one_sub_sum_le_prod_one_sub C (fun b => (Real.pi * b * t) ^ 2 / 2) hx0 hx1
      have hsum_le : ∑ b ∈ C, (Real.pi * b * t) ^ 2 / 2 ≤ 1 / 2 := by
        have hfact : ∑ b ∈ C, (Real.pi * b * t) ^ 2 / 2 = (Real.pi ^ 2 * t ^ 2 / 2) * V := by
          dsimp [V]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          ring
        rw [hfact]
        have ht2 : t ^ 2 ≤ r ^ 2 := by
          rw [← sq_abs t, ← sq_abs r, abs_of_pos hr_pos]
          exact pow_le_pow_left₀ (abs_nonneg t) ht_abs 2
        have hr2 : r ^ 2 * V = 1 / 16 := by
          dsimp [r]
          rw [div_pow, one_pow, mul_pow, Real.sq_sqrt hVpos.le]
          field_simp
          ring
        have hpi4 : Real.pi < 4 := Real.pi_lt_four
        calc (Real.pi ^ 2 * t ^ 2 / 2) * V
            ≤ (Real.pi ^ 2 * r ^ 2 / 2) * V := by gcongr
          _ = Real.pi ^ 2 / 2 * (r ^ 2 * V) := by ring
          _ = Real.pi ^ 2 / 32 := by rw [hr2]; ring
          _ ≤ 1 / 2 := by nlinarith [Real.pi_pos]
      linarith
    have hmul := mul_le_mul hcos1 hprod_ge (by positivity) (by linarith)
    linarith
  have hg_minor : ∀ t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2), a ≤ |t| →
      |g t| ≤ Real.exp (-2 * c_min) := by
    intro t ht hta
    have hcos_le1 : |Real.cos (2 * Real.pi * Δ * t)| ≤ 1 := Real.abs_cos_le_one _
    have hprod_le : |∏ b ∈ C, Real.cos (Real.pi * b * t)| ≤
        Real.exp (-2 * ∑ b ∈ C, (d1 ((b : ℝ) * t)) ^ 2) := by
      rw [Finset.abs_prod]
      have hterm_le : ∀ b ∈ C, |Real.cos (Real.pi * (b : ℝ) * t)| ≤
          Real.exp (-2 * (d1 ((b : ℝ) * t)) ^ 2) := by
        intro b _
        rw [mul_assoc]
        exact abs_cos_pi_le_exp ((b : ℝ) * t)
      calc ∏ b ∈ C, |Real.cos (Real.pi * (b : ℝ) * t)|
          ≤ ∏ b ∈ C, Real.exp (-2 * (d1 ((b : ℝ) * t)) ^ 2) :=
            Finset.prod_le_prod (fun b _ => abs_nonneg _) hterm_le
        _ = Real.exp (∑ b ∈ C, -2 * (d1 ((b : ℝ) * t)) ^ 2) := (Real.exp_sum _ _).symm
        _ = Real.exp (-2 * ∑ b ∈ C, (d1 ((b : ℝ) * t)) ^ 2) := by
            rw [← Finset.mul_sum]
    have hexp_le : Real.exp (-2 * ∑ b ∈ C, (d1 ((b : ℝ) * t)) ^ 2) ≤ Real.exp (-2 * c_min) := by
      apply Real.exp_le_exp.2
      have := hminor t ht hta
      linarith
    have hgt_abs : |g t| = |Real.cos (2 * Real.pi * Δ * t)| * |∏ b ∈ C, Real.cos (Real.pi * b * t)| := by
      dsimp [g]
      exact abs_mul _ _
    calc |g t|
        = |Real.cos (2 * Real.pi * Δ * t)| * |∏ b ∈ C, Real.cos (Real.pi * b * t)| := hgt_abs
      _ ≤ 1 * |∏ b ∈ C, Real.cos (Real.pi * b * t)| :=
          mul_le_mul_of_nonneg_right hcos_le1 (abs_nonneg _)
      _ ≤ Real.exp (-2 * c_min) := by linarith
  have hint_pos : 0 < ∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ), g t :=
    integral_cos_pos_of_arc_bounds g a r c_min V ha_pos hr_pos hra ha_half rfl hVpos
      hg_int hg_nonneg_mid hg_maj hg_minor hc_win
  have hcnt := subset_sum_count_eq_integral C M'
  have hcnt_pos : (0 : ℝ) < ((C.powerset.filter (fun A => ∑ b ∈ A, b = M')).card : ℝ) := by
    rw [hcnt]
    exact mul_pos (by positivity) hint_pos
  have hcard_pos : 0 < (C.powerset.filter (fun A => ∑ b ∈ A, b = M')).card := by
    exact_mod_cast hcnt_pos
  obtain ⟨A, hA⟩ := Finset.card_pos.1 hcard_pos
  rw [Finset.mem_filter, Finset.mem_powerset] at hA
  exact ⟨A, hA.1, hA.2⟩

/- ### Part 4e: Probabilistic Choice of `C₀` & Adjustment to `C` -/

lemma sum_ge_card_sq_div_two (B : Finset ℕ) (hB : ∀ b ∈ B, 1 ≤ b) :
    B.card * (B.card + 1) ≤ 2 * ∑ b ∈ B, b := by
  induction hn : B.card using Nat.strong_induction_on generalizing B with
  | h k ih =>
    cases k with
    | zero => simp
    | succ m =>
      have hne : B.Nonempty := Finset.card_pos.1 (by omega)
      set x := B.max' hne
      have hxB : x ∈ B := Finset.max'_mem B hne
      have hB_le : B ⊆ Finset.Icc 1 x := fun b hb =>
        Finset.mem_Icc.2 ⟨hB b hb, Finset.le_max' B b hb⟩
      have hx_ge : m + 1 ≤ x := by
        have := Finset.card_le_card hB_le
        simpa [Nat.card_Icc, hn] using this
      set B' := B.erase x
      have hB'_card : B'.card = m := by
        rw [Finset.card_erase_of_mem hxB, hn]
        simp
      have hB'_pos : ∀ b ∈ B', 1 ≤ b := fun b hb => hB b (Finset.erase_subset _ _ hb)
      have ih' := ih m (by omega) B' hB'_pos hB'_card
      have hsum : ∑ b ∈ B', b + x = ∑ b ∈ B, b := Finset.sum_erase_add B _ hxB
      nlinarith

lemma sum_sq_ge_card_cube_div_eight (B : Finset ℕ) (hB : ∀ b ∈ B, 1 ≤ b) :
    ((B.card : ℝ) ^ 3) / 8 ≤ ∑ b ∈ B, (b : ℝ) ^ 2 := by
  let B_hi := B.filter (fun b => (B.card + 1) / 2 ≤ b)
  let B_lo := B.filter (fun b => ¬ ((B.card + 1) / 2 ≤ b))
  have hpart : B_hi.card + B_lo.card = B.card := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.2 (fun _ _ h1 h2 => h2 h1))]
    congr 1
    ext x
    rw [Finset.mem_union]
    rw [Finset.mem_filter, Finset.mem_filter]
    tauto
  have hlo_sub : B_lo ⊆ Finset.Icc 1 (B.card / 2) := by
    intro b hb
    rw [Finset.mem_filter] at hb
    exact Finset.mem_Icc.2 ⟨hB b hb.1, by omega⟩
  have hlo_card : B_lo.card ≤ B.card / 2 := by
    simpa [Nat.card_Icc] using Finset.card_le_card hlo_sub
  have hhi_card : (B.card : ℝ) / 2 ≤ (B_hi.card : ℝ) := by
    have h1 : B.card ≤ 2 * B_hi.card := by omega
    have h2 : (B.card : ℝ) ≤ 2 * (B_hi.card : ℝ) := by exact_mod_cast h1
    linarith
  have hsum : ∑ b ∈ B_hi, ((B.card : ℝ) / 2) ^ 2 ≤ ∑ b ∈ B, (b : ℝ) ^ 2 := by
    calc ∑ b ∈ B_hi, ((B.card : ℝ) / 2) ^ 2
        ≤ ∑ b ∈ B_hi, (b : ℝ) ^ 2 := by
          refine Finset.sum_le_sum fun b hb => ?_
          rw [Finset.mem_filter] at hb
          have h1 : B.card ≤ 2 * b := by omega
          have h2 : (B.card : ℝ) / 2 ≤ (b : ℝ) := by
            have : (B.card : ℝ) ≤ 2 * (b : ℝ) := by exact_mod_cast h1
            linarith
          exact pow_le_pow_left₀ (by positivity) h2 2
      _ ≤ ∑ b ∈ B, (b : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => sq_nonneg _
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  have hbound : ((B.card : ℝ) ^ 3) / 8 ≤ (B_hi.card : ℝ) * ((B.card : ℝ) / 2) ^ 2 := by
    have h1 : (B.card : ℝ) / 2 * ((B.card : ℝ) / 2) ^ 2 = ((B.card : ℝ) ^ 3) / 8 := by ring
    rw [← h1]
    exact mul_le_mul_of_nonneg_right hhi_card (by positivity)
  linarith

lemma sum_union_le_of_nonneg {α : Type*} [DecidableEq α] (s t : Finset α) (f : α → ℝ)
    (hf : ∀ x ∈ s ∪ t, 0 ≤ f x) :
    ∑ x ∈ s ∪ t, f x ≤ ∑ x ∈ s, f x + ∑ x ∈ t, f x := by
  have h := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := f)
  have hinter : 0 ≤ ∑ x ∈ s ∩ t, f x :=
    Finset.sum_nonneg fun x hx => hf x (Finset.mem_union_left _ (Finset.mem_inter.1 hx).1)
  linarith

lemma sum_biUnion_le_of_nonneg {α β : Type*} [DecidableEq β] (u : Finset α) (g : α → Finset β)
    (f : β → ℝ) (hf : ∀ i ∈ u, ∀ x ∈ g i, 0 ≤ f x) :
    ∑ x ∈ u.biUnion g, f x ≤ ∑ i ∈ u, ∑ x ∈ g i, f x := by
  induction u using Finset.induction with
  | empty => simp
  | @insert a u ha ih =>
    have hf' : ∀ i ∈ u, ∀ x ∈ g i, 0 ≤ f x := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have ih' := ih hf'
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have huni : ∑ x ∈ g a ∪ u.biUnion g, f x ≤ ∑ x ∈ g a, f x + ∑ x ∈ u.biUnion g, f x := by
      apply sum_union_le_of_nonneg
      intro x hx
      rcases Finset.mem_union.1 hx with hxa | hxu
      · exact hf a (Finset.mem_insert_self a u) x hxa
      · obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.1 hxu
        exact hf' i hi x hxi
    linarith

lemma exists_good_C0_of_reduced (B : Finset ℕ) (M M' : ℕ) {L T : ℝ}
    (hM : 1 ≤ M) (hM' : 1 ≤ M') (hL : 10 ≤ L) (hB_sub : B ⊆ Finset.Icc 1 M)
    (hB_lb : (M : ℝ) / (2 * L) ≤ (B.card : ℝ))
    (hT_pos : 0 < T) (hT_le : T ≤ (2 / 5 : ℝ) * (B.card : ℝ))
    (hB_nondiv : ∀ q : ℕ, 2 ≤ q → T ≤ ((B.filter (fun b => ¬ q ∣ b)).card : ℝ))
    (hM'_lt : 2 * (M' : ℝ) < ∑ b ∈ B, (b : ℝ))
    (hmu2_big : 64 * (M : ℝ) ^ 2 < (2 * (M' : ℝ) / ∑ b ∈ B, (b : ℝ)) * ∑ b ∈ B, (b : ℝ) ^ 2)
    (hnet_small : ((M : ℝ) * L ^ 4 + 1) *
      Real.exp (-((1 / 2 : ℝ) * (1 - Real.exp (-1)) *
        (2 * (M' : ℝ) / ∑ b ∈ B, (b : ℝ)) * (T * (3 / (400 * L)) ^ 2))) < 1 / 4) :
    ∃ C₀ ⊆ B,
      |∑ b ∈ C₀, (b : ℝ) - 2 * (M' : ℝ)| < 4 * Real.sqrt (2 * (M' : ℝ) * M) ∧
      ((2 * (M' : ℝ) / ∑ b ∈ B, (b : ℝ)) * ∑ b ∈ B, (b : ℝ) ^ 2) / 2 < ∑ b ∈ C₀, (b : ℝ) ^ 2 ∧
      ∀ t ∈ arcNet M L,
        (1 / 2 : ℝ) * (1 - Real.exp (-1)) * (2 * (M' : ℝ) / ∑ b ∈ B, (b : ℝ)) *
          (T * (3 / (400 * L)) ^ 2) < ∑ b ∈ C₀, (d1 ((b : ℝ) * t)) ^ 2 := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hM'pos : (0 : ℝ) < M' := by exact_mod_cast hM'
  have hLpos : 0 < L := by linarith
  set S_B : ℝ := ∑ b ∈ B, (b : ℝ)
  set p : ℝ := 2 * (M' : ℝ) / S_B
  have hS_B_pos : 0 < S_B := by linarith
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by
    dsimp [p]
    rw [div_le_one hS_B_pos]
    linarith
  set μ₂ : ℝ := p * ∑ b ∈ B, (b : ℝ) ^ 2
  have hμ₂_pos : 0 < μ₂ := lt_of_lt_of_le (by positivity) hmu2_big.le
  set E_min : ℝ := T * (3 / (400 * L)) ^ 2
  set α : ℝ := (1 / 2 : ℝ) * (1 - Real.exp (-1)) * p * E_min
  set S_bad1 : Finset (Finset ℕ) :=
    B.powerset.filter (fun C => 32 * (M' : ℝ) * M ≤ (∑ b ∈ C, (b : ℝ) - 2 * (M' : ℝ)) ^ 2)
  set S_bad2 : Finset (Finset ℕ) :=
    B.powerset.filter (fun C => (μ₂ / 2) ^ 2 ≤ (∑ b ∈ C, (b : ℝ) ^ 2 - μ₂) ^ 2)
  set S_bad3 : ℝ → Finset (Finset ℕ) := fun t =>
    B.powerset.filter (fun C => Real.exp (-α) ≤ Real.exp (- ∑ b ∈ C, (d1 ((b : ℝ) * t)) ^ 2))
  set S_bad : Finset (Finset ℕ) := S_bad1 ∪ S_bad2 ∪ (arcNet M L).biUnion S_bad3
  have hw_nn : ∀ C ∈ B.powerset, 0 ≤ wPow B p C := fun C _ => wPow_nonneg hp0 hp1 C
  have hbad1_bd : ∑ C ∈ S_bad1, wPow B p C ≤ 1 / 16 := by
    have hmark := weighted_sum_filter_le B.powerset (wPow B p)
      (fun C => (∑ b ∈ C, (b : ℝ) - 2 * (M' : ℝ)) ^ 2) hw_nn (fun _ _ => sq_nonneg _)
      (by positivity : 0 < 32 * (M' : ℝ) * M)
    have hvar : ∑ C ∈ B.powerset, wPow B p C * (∑ b ∈ C, (b : ℝ) - 2 * (M' : ℝ)) ^ 2 ≤
        2 * (M' : ℝ) * M := by
      have hpS : p * ∑ b ∈ B, (b : ℝ) = 2 * (M' : ℝ) :=
        div_mul_cancel₀ _ hS_B_pos.ne'
      have hvar_eq := sum_powerset_wPow_var B p (fun b : ℕ => (b : ℝ))
      rw [hpS] at hvar_eq
      rw [hvar_eq]
      have hsq_le : ∑ b ∈ B, (b : ℝ) ^ 2 ≤ (M : ℝ) * S_B := by
        dsimp [S_B]
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun b hb => ?_
        have hbM : (b : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.1 (hB_sub hb)).2
        calc (b : ℝ) ^ 2 = (b : ℝ) * (b : ℝ) := sq _
          _ ≤ (M : ℝ) * (b : ℝ) := mul_le_mul_of_nonneg_right hbM (by positivity)
      have h1mp : 1 - p ≤ 1 := by linarith
      have hpm : p * (1 - p) ≤ p * 1 := mul_le_mul_of_nonneg_left h1mp hp0
      have hmul := mul_le_mul hpm hsq_le (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
      calc p * (1 - p) * ∑ b ∈ B, (b : ℝ) ^ 2
          ≤ p * 1 * ((M : ℝ) * S_B) := hmul
        _ = (p * ∑ b ∈ B, (b : ℝ)) * (M : ℝ) := by dsimp [S_B]; ring
        _ = 2 * (M' : ℝ) * M := by rw [hpS]
    calc ∑ C ∈ S_bad1, wPow B p C
        ≤ (∑ C ∈ B.powerset, wPow B p C * (∑ b ∈ C, (b : ℝ) - 2 * (M' : ℝ)) ^ 2) /
            (32 * (M' : ℝ) * M) := hmark
      _ ≤ (2 * (M' : ℝ) * M) / (32 * (M' : ℝ) * M) :=
          div_le_div_of_nonneg_right hvar (by positivity)
      _ = 1 / 16 := by field_simp; ring
  have hbad2_bd : ∑ C ∈ S_bad2, wPow B p C < 1 / 16 := by
    have hmark := weighted_sum_filter_le B.powerset (wPow B p)
      (fun C => (∑ b ∈ C, (b : ℝ) ^ 2 - μ₂) ^ 2) hw_nn (fun _ _ => sq_nonneg _)
      (by positivity : 0 < (μ₂ / 2) ^ 2)
    have hvar : ∑ C ∈ B.powerset, wPow B p C * (∑ b ∈ C, (b : ℝ) ^ 2 - μ₂) ^ 2 ≤
        (M : ℝ) ^ 2 * μ₂ := by
      dsimp [μ₂]
      rw [sum_powerset_wPow_var B p (fun b : ℕ => (b : ℝ) ^ 2)]
      have h4_le : ∑ b ∈ B, ((b : ℝ) ^ 2) ^ 2 ≤ (M : ℝ) ^ 2 * ∑ b ∈ B, (b : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun b hb => ?_
        have hbM : (b : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.1 (hB_sub hb)).2
        have hsq : (b : ℝ) ^ 2 ≤ (M : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hbM 2
        calc ((b : ℝ) ^ 2) ^ 2 = (b : ℝ) ^ 2 * (b : ℝ) ^ 2 := sq _
          _ ≤ (M : ℝ) ^ 2 * (b : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
      have h1mp : 1 - p ≤ 1 := by linarith
      have hpm : p * (1 - p) ≤ p * 1 := mul_le_mul_of_nonneg_left h1mp hp0
      calc p * (1 - p) * ∑ b ∈ B, ((b : ℝ) ^ 2) ^ 2
          ≤ p * 1 * ((M : ℝ) ^ 2 * ∑ b ∈ B, (b : ℝ) ^ 2) :=
            mul_le_mul hpm h4_le (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
        _ = (M : ℝ) ^ 2 * (p * ∑ b ∈ B, (b : ℝ) ^ 2) := by ring
    have hdiv_lt : ((M : ℝ) ^ 2 * μ₂) / ((μ₂ / 2) ^ 2) < 1 / 16 := by
      have hsimp : ((M : ℝ) ^ 2 * μ₂) / ((μ₂ / 2) ^ 2) = 4 * (M : ℝ) ^ 2 / μ₂ := by
        field_simp
        norm_num
      rw [hsimp, div_lt_iff₀ hμ₂_pos]
      linarith
    calc ∑ C ∈ S_bad2, wPow B p C
        ≤ (∑ C ∈ B.powerset, wPow B p C * (∑ b ∈ C, (b : ℝ) ^ 2 - μ₂) ^ 2) / ((μ₂ / 2) ^ 2) :=
          hmark
      _ ≤ ((M : ℝ) ^ 2 * μ₂) / ((μ₂ / 2) ^ 2) :=
          div_le_div_of_nonneg_right hvar (by positivity)
      _ < 1 / 16 := hdiv_lt
  have hbad3_bd : ∀ t ∈ arcNet M L, ∑ C ∈ S_bad3 t, wPow B p C ≤ Real.exp (-α) := by
    intro t ht
    have hmem := arcNet_mem_Icc hM ht
    have ht0 : 0 ≤ t := le_trans (by positivity) hmem.1
    have htabs_lo : 1 / (3 * (M : ℝ)) ≤ |t| := by rw [abs_of_nonneg ht0]; exact hmem.1
    have htabs_hi : |t| ≤ 1 / 2 := by rw [abs_of_nonneg ht0]; exact hmem.2
    have hminor_B := minor_arc_sum_d1_sq_ge hM hL hB_sub hB_lb hT_pos hT_le hB_nondiv htabs_lo htabs_hi
    have hmark := weighted_sum_filter_le B.powerset (wPow B p)
      (fun C => Real.exp (- ∑ b ∈ C, (d1 ((b : ℝ) * t)) ^ 2))
      hw_nn (fun _ _ => (Real.exp_pos _).le) (Real.exp_pos (-α))
    have hexp := sum_powerset_wPow_exp_le B hp0 hp1 (fun b => (d1 ((b : ℝ) * t)) ^ 2)
      (fun _ _ => sq_nonneg _) (fun b _ => by
        have := d1_le_half ((b : ℝ) * t)
        have := d1_nonneg ((b : ℝ) * t)
        nlinarith)
    have h1me : 0 ≤ 1 - Real.exp (-1) := by
      have : Real.exp (-1 : ℝ) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
      linarith
    have h2alpha : 2 * α ≤ (1 - Real.exp (-1)) * p * ∑ b ∈ B, (d1 ((b : ℝ) * t)) ^ 2 := by
      dsimp [α, E_min]
      have : E_min ≤ ∑ b ∈ B, (d1 ((b : ℝ) * t)) ^ 2 := hminor_B
      have hfactor : 0 ≤ (1 - Real.exp (-1)) * p := mul_nonneg h1me hp0
      nlinarith
    have hexp2 : Real.exp (-(1 - Real.exp (-1)) * p * ∑ b ∈ B, (d1 ((b : ℝ) * t)) ^ 2) ≤
        Real.exp (-2 * α) := by
      apply Real.exp_le_exp.2
      linarith
    calc ∑ C ∈ S_bad3 t, wPow B p C
        ≤ (∑ C ∈ B.powerset, wPow B p C * Real.exp (- ∑ b ∈ C, (d1 ((b : ℝ) * t)) ^ 2)) /
            Real.exp (-α) := hmark
      _ ≤ Real.exp (-2 * α) / Real.exp (-α) :=
          div_le_div_of_nonneg_right (hexp.trans hexp2) (Real.exp_pos _).le
      _ = Real.exp (-α) := by
          rw [div_eq_iff (Real.exp_ne_zero _), ← Real.exp_add]
          congr 1
          ring
  have hbad3_sum : ∑ C ∈ (arcNet M L).biUnion S_bad3, wPow B p C < 1 / 4 := by
    have hle1 : ∑ C ∈ (arcNet M L).biUnion S_bad3, wPow B p C ≤
        ∑ t ∈ arcNet M L, ∑ C ∈ S_bad3 t, wPow B p C := by
      refine sum_biUnion_le_of_nonneg (arcNet M L) S_bad3 (wPow B p) fun t _ C hC => ?_
      exact hw_nn C (Finset.filter_subset _ _ hC)
    have hle2 : ∑ t ∈ arcNet M L, ∑ C ∈ S_bad3 t, wPow B p C ≤
        ((arcNet M L).card : ℝ) * Real.exp (-α) := by
      calc ∑ t ∈ arcNet M L, ∑ C ∈ S_bad3 t, wPow B p C
          ≤ ∑ _t ∈ arcNet M L, Real.exp (-α) := Finset.sum_le_sum hbad3_bd
        _ = ((arcNet M L).card : ℝ) * Real.exp (-α) := by simp
    have hle3 : ((arcNet M L).card : ℝ) * Real.exp (-α) ≤
        ((M : ℝ) * L ^ 4 + 1) * Real.exp (-α) :=
      mul_le_mul_of_nonneg_right (arcNet_card_le M hLpos.le) (Real.exp_pos _).le
    linarith
  have hS_bad_sub : S_bad ⊆ B.powerset := by
    intro C hC
    simp only [S_bad, Finset.mem_union, Finset.mem_biUnion] at hC
    rcases hC with ((h1 | h2) | ⟨_, _, h3⟩)
    · exact Finset.filter_subset _ _ h1
    · exact Finset.filter_subset _ _ h2
    · exact Finset.filter_subset _ _ h3
  have hbad_lt : ∑ C ∈ S_bad, wPow B p C < 1 := by
    have h12 : ∑ C ∈ S_bad1 ∪ S_bad2, wPow B p C ≤
        ∑ C ∈ S_bad1, wPow B p C + ∑ C ∈ S_bad2, wPow B p C := by
      apply sum_union_le_of_nonneg
      intro C hC
      exact hw_nn C ((Finset.mem_union.1 hC).elim
        (fun h => Finset.filter_subset _ _ h) (fun h => Finset.filter_subset _ _ h))
    have h123 : ∑ C ∈ S_bad, wPow B p C ≤
        ∑ C ∈ S_bad1 ∪ S_bad2, wPow B p C +
          ∑ C ∈ (arcNet M L).biUnion S_bad3, wPow B p C := by
      dsimp [S_bad]
      apply sum_union_le_of_nonneg
      intro C hC
      exact hw_nn C (hS_bad_sub (by simpa [S_bad] using hC))
    linarith
  have hgood_ne : (B.powerset \ S_bad).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hempty
    have heq : S_bad = B.powerset := Subset.antisymm hS_bad_sub hempty
    have hone := sum_powerset_wPow_one B p
    rw [← heq] at hone
    linarith
  obtain ⟨C₀, hC₀_mem⟩ := hgood_ne
  rw [Finset.mem_sdiff, Finset.mem_powerset] at hC₀_mem
  rcases hC₀_mem with ⟨hC₀_sub, hC₀_good⟩
  have hC₀_sum : |∑ b ∈ C₀, (b : ℝ) - 2 * (M' : ℝ)| < 4 * Real.sqrt (2 * (M' : ℝ) * M) := by
    have hnot1 : C₀ ∉ S_bad1 := fun h => hC₀_good (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    simp only [S_bad1, Finset.mem_filter, Finset.mem_powerset, not_and, not_le] at hnot1
    have hsq := hnot1 hC₀_sub
    have hsq2 : (∑ b ∈ C₀, (b : ℝ) - 2 * (M' : ℝ)) ^ 2 < (4 * Real.sqrt (2 * (M' : ℝ) * M)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      linarith
    exact abs_lt.2 (abs_lt_of_sq_lt_sq' hsq2 (by positivity))
  have hC₀_V : μ₂ / 2 < ∑ b ∈ C₀, (b : ℝ) ^ 2 := by
    have hnot2 : C₀ ∉ S_bad2 := fun h => hC₀_good (Finset.mem_union_left _ (Finset.mem_union_right _ h))
    simp only [S_bad2, Finset.mem_filter, Finset.mem_powerset, not_and, not_le] at hnot2
    have hsq := hnot2 hC₀_sub
    have habs : |∑ b ∈ C₀, (b : ℝ) ^ 2 - μ₂| < μ₂ / 2 :=
      abs_lt.2 (abs_lt_of_sq_lt_sq' hsq (by positivity))
    linarith [(abs_lt.1 habs).1]
  have hC₀_net : ∀ t ∈ arcNet M L, α < ∑ b ∈ C₀, (d1 ((b : ℝ) * t)) ^ 2 := by
    intro t ht
    have hnot3 : C₀ ∉ S_bad3 t := fun h =>
      hC₀_good (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨t, ht, h⟩))
    simp only [S_bad3, Finset.mem_filter, Finset.mem_powerset, not_and, not_le] at hnot3
    have hexp := hnot3 hC₀_sub
    rw [Real.exp_lt_exp] at hexp
    linarith
  exact ⟨C₀, hC₀_sub, hC₀_sum, hC₀_V, hC₀_net⟩

lemma exists_subset_sum_of_reduced (B : Finset ℕ) (M M' : ℕ) {L T : ℝ}
    (hM : 1 ≤ M) (hM' : 1 ≤ M') (hL : 10 ≤ L) (hB_sub : B ⊆ Finset.Icc 1 M)
    (hB_lb : (M : ℝ) / (2 * L) ≤ (B.card : ℝ))
    (hT_pos : 0 < T) (hT_le : T ≤ (2 / 5 : ℝ) * (B.card : ℝ))
    (hB_nondiv : ∀ q : ℕ, 2 ≤ q → T ≤ ((B.filter (fun b => ¬ q ∣ b)).card : ℝ))
    (hM'_lt : 2 * (M' : ℝ) < ∑ b ∈ B, (b : ℝ))
    (hM'_hi : (M : ℝ) ^ 2 / L ^ 5 ≤ 2 * (M' : ℝ))
    (hB_sum_hi : 2 * (M' : ℝ) + (M : ℝ) ^ 2 / L ^ 5 ≤ ∑ b ∈ B, (b : ℝ))
    (hmu2_big : 64 * (M : ℝ) ^ 2 < (2 * (M' : ℝ) / ∑ b ∈ B, (b : ℝ)) * ∑ b ∈ B, (b : ℝ) ^ 2)
    (hnet_small : ((M : ℝ) * L ^ 4 + 1) *
      Real.exp (-((1 / 2 : ℝ) * (1 - Real.exp (-1)) *
        (2 * (M' : ℝ) / ∑ b ∈ B, (b : ℝ)) * (T * (3 / (400 * L)) ^ 2))) < 1 / 4)
    (hV_adj : 9 * (M : ℝ) ^ 2 ≤ 16 * (
      ((2 * (M' : ℝ) / ∑ b ∈ B, (b : ℝ)) * ∑ b ∈ B, (b : ℝ) ^ 2) / 2 -
      (4 * Real.sqrt (2 * (M' : ℝ) * M) / ((M : ℝ) / L ^ 5)) * (M : ℝ) ^ 2))
    (harc_win : Real.exp (-2 * (
      (1 / 2 : ℝ) * ((1 / 2 : ℝ) * (1 - Real.exp (-1)) *
        (2 * (M' : ℝ) / ∑ b ∈ B, (b : ℝ)) * (T * (3 / (400 * L)) ^ 2) -
        2 * (M : ℝ) * (1 / L ^ 4) ^ 2) -
      (4 * Real.sqrt (2 * (M' : ℝ) * M) / ((M : ℝ) / L ^ 5)) / 4)) <
      1 / (8 * Real.sqrt ((M : ℝ) ^ 3))) :
    ∃ A ⊆ B, ∑ b ∈ A, b = M' := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hLpos : 0 < L := by linarith only [hL]
  obtain ⟨C₀, hC₀_sub, hC₀_sum, hC₀_V, hC₀_net⟩ :=
    exists_good_C0_of_reduced B M M' hM hM' hL hB_sub hB_lb hT_pos hT_le hB_nondiv
      hM'_lt hmu2_big hnet_small
  set μ₂ : ℝ := (2 * (M' : ℝ) / ∑ b ∈ B, (b : ℝ)) * ∑ b ∈ B, (b : ℝ) ^ 2
  set α : ℝ := (1 / 2 : ℝ) * (1 - Real.exp (-1)) *
    (2 * (M' : ℝ) / ∑ b ∈ B, (b : ℝ)) * (T * (3 / (400 * L)) ^ 2)
  set B_hi : Finset ℕ := B.filter (fun b => (M : ℝ) / L ^ 5 ≤ (b : ℝ))
  have hB_hi_M : ∀ b ∈ B_hi, b ≤ M := fun b hb =>
    (Finset.mem_Icc.1 (hB_sub (Finset.filter_subset _ _ hb))).2
  have hB_lo_sum : ∑ b ∈ B \ B_hi, (b : ℝ) ≤ (M : ℝ) ^ 2 / L ^ 5 := by
    have hterm : ∀ b ∈ B \ B_hi, (b : ℝ) ≤ (M : ℝ) / L ^ 5 := by
      intro b hb
      rw [Finset.mem_sdiff, Finset.mem_filter] at hb
      have : ¬ (M : ℝ) / L ^ 5 ≤ (b : ℝ) := fun h => hb.2 ⟨hb.1, h⟩
      linarith
    calc ∑ b ∈ B \ B_hi, (b : ℝ)
        ≤ ∑ _b ∈ B \ B_hi, (M : ℝ) / L ^ 5 := Finset.sum_le_sum hterm
      _ = ((B \ B_hi).card : ℝ) * ((M : ℝ) / L ^ 5) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (M : ℝ) * ((M : ℝ) / L ^ 5) := by
          have hcard : (B \ B_hi).card ≤ M := by
            have := Finset.card_le_card ((Finset.sdiff_subset (s := B) (t := B_hi)).trans hB_sub)
            rw [Nat.card_Icc] at this
            exact this
          have hcardR : ((B \ B_hi).card : ℝ) ≤ M := by exact_mod_cast hcard
          exact mul_le_mul_of_nonneg_right hcardR (by positivity)
      _ = (M : ℝ) ^ 2 / L ^ 5 := by ring
  have hC₀_lo_sum : ∑ b ∈ C₀ \ B_hi, b ≤ 2 * M' := by
    have hsub : C₀ \ B_hi ⊆ B \ B_hi := Finset.sdiff_subset_sdiff hC₀_sub Subset.rfl
    have h1 : (∑ b ∈ C₀ \ B_hi, (b : ℝ)) ≤ ∑ b ∈ B \ B_hi, (b : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    have h2 : (∑ b ∈ C₀ \ B_hi, (b : ℝ)) ≤ 2 * (M' : ℝ) := h1.trans (hB_lo_sum.trans hM'_hi)
    exact_mod_cast (by simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat] using h2 :
      ((∑ b ∈ C₀ \ B_hi, b : ℕ) : ℝ) ≤ ((2 * M' : ℕ) : ℝ))
  have hB_hi_sum : 2 * M' ≤ ∑ b ∈ C₀ ∪ (B ∩ B_hi), b := by
    have hsub : B ∩ B_hi ⊆ C₀ ∪ (B ∩ B_hi) := Finset.subset_union_right
    have hsum_hi : ∑ b ∈ B, (b : ℝ) - ∑ b ∈ B \ B_hi, (b : ℝ) ≤ ∑ b ∈ B ∩ B_hi, (b : ℝ) := by
      have heq : B \ B_hi ∪ (B ∩ B_hi) = B := Finset.sdiff_union_inter B B_hi
      have hdisj : Disjoint (B \ B_hi) (B ∩ B_hi) := Finset.disjoint_sdiff_inter B B_hi
      have hs : ∑ b ∈ B, (b : ℝ) = ∑ b ∈ B \ B_hi, (b : ℝ) + ∑ b ∈ B ∩ B_hi, (b : ℝ) := by
        rw [← Finset.sum_union hdisj, heq]
      linarith
    have h1 : (2 * (M' : ℝ)) ≤ ∑ b ∈ B ∩ B_hi, (b : ℝ) := by linarith
    have h2 : ∑ b ∈ B ∩ B_hi, (b : ℝ) ≤ ∑ b ∈ C₀ ∪ (B ∩ B_hi), (b : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    exact_mod_cast (by simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat] using h1.trans h2 :
      ((2 * M' : ℕ) : ℝ) ≤ ((∑ b ∈ C₀ ∪ (B ∩ B_hi), b : ℕ) : ℝ))
  have hC_exists : ∃ C ⊆ B,
      |(∑ b ∈ C, (b : ℝ)) - 2 * (M' : ℝ)| ≤ (M : ℝ) ∧
      ((C₀ \ C).card : ℝ) + ((C \ C₀).card : ℝ) ≤
        4 * Real.sqrt (2 * (M' : ℝ) * M) / ((M : ℝ) / L ^ 5) := by
    by_cases hhi : 2 * M' + M < ∑ b ∈ C₀, b
    · obtain ⟨C, hCC₀, hC_ge, hC_le, hdiff⟩ :=
        shrink_exists B_hi C₀ (2 * M') M hB_hi_M (by omega) hC₀_lo_sum
      refine ⟨C, hCC₀.trans hC₀_sub, ?_, ?_⟩
      · have h1 : (2 * (M' : ℝ)) ≤ ∑ b ∈ C, (b : ℝ) := by
          simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat] using (Nat.cast_le (α := ℝ)).2 hC_ge
        have h2 : ∑ b ∈ C, (b : ℝ) ≤ 2 * (M' : ℝ) + M := by
          simpa only [Nat.cast_sum, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
            (Nat.cast_le (α := ℝ)).2 hC_le
        exact abs_le.2 ⟨by linarith, by linarith⟩
      · have hC₀_diff0 : C \ C₀ = ∅ := Finset.sdiff_eq_empty_iff_subset.2 hCC₀
        rw [hC₀_diff0, Finset.card_empty, Nat.cast_zero, add_zero]
        have hsum_diff : ∑ b ∈ C₀ \ C, (b : ℝ) ≤ 4 * Real.sqrt (2 * (M' : ℝ) * M) := by
          have hdisj : Disjoint C (C₀ \ C) := disjoint_sdiff_self_right
          have hunion : C ∪ (C₀ \ C) = C₀ := Finset.union_sdiff_of_subset hCC₀
          have heq : ∑ b ∈ C, (b : ℝ) + ∑ b ∈ C₀ \ C, (b : ℝ) = ∑ b ∈ C₀, (b : ℝ) := by
            rw [← Finset.sum_union hdisj, hunion]
          have hgeR : 2 * (M' : ℝ) ≤ ∑ b ∈ C, (b : ℝ) := by
            simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat] using (Nat.cast_le (α := ℝ)).2 hC_ge
          have hC₀_hi : ∑ b ∈ C₀, (b : ℝ) - 2 * (M' : ℝ) < 4 * Real.sqrt (2 * (M' : ℝ) * M) :=
            (abs_lt.1 hC₀_sum).2
          linarith
        have hlow_sum : ((C₀ \ C).card : ℝ) * ((M : ℝ) / L ^ 5) ≤ ∑ b ∈ C₀ \ C, (b : ℝ) := by
          calc ((C₀ \ C).card : ℝ) * ((M : ℝ) / L ^ 5)
              = ∑ _b ∈ C₀ \ C, ((M : ℝ) / L ^ 5) := by rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ ∑ b ∈ C₀ \ C, (b : ℝ) := by
                refine Finset.sum_le_sum fun b hb => ?_
                exact (Finset.mem_filter.1 (hdiff hb)).2
        rw [le_div_iff₀ (by positivity)]
        exact hlow_sum.trans hsum_diff
    · by_cases hlo : ∑ b ∈ C₀, b + M < 2 * M'
      · obtain ⟨C, hC₀C, hCB, hC_ge, hC_le, hdiff⟩ :=
          grow_exists B B_hi C₀ (2 * M') M hC₀_sub hB_hi_M (by omega) hB_hi_sum
        refine ⟨C, hCB, ?_, ?_⟩
        · have h1 : 2 * (M' : ℝ) ≤ ∑ b ∈ C, (b : ℝ) + M := by
            simpa only [Nat.cast_sum, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
              (Nat.cast_le (α := ℝ)).2 hC_ge
          have h2 : ∑ b ∈ C, (b : ℝ) ≤ 2 * (M' : ℝ) := by
            simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat] using
              (Nat.cast_le (α := ℝ)).2 hC_le
          exact abs_le.2 ⟨by linarith, by linarith⟩
        · have hC₀_diff0 : C₀ \ C = ∅ := Finset.sdiff_eq_empty_iff_subset.2 hC₀C
          rw [hC₀_diff0, Finset.card_empty, Nat.cast_zero, zero_add]
          have hsum_diff : ∑ b ∈ C \ C₀, (b : ℝ) ≤ 4 * Real.sqrt (2 * (M' : ℝ) * M) := by
            have hdisj : Disjoint C₀ (C \ C₀) := disjoint_sdiff_self_right
            have hunion : C₀ ∪ (C \ C₀) = C := Finset.union_sdiff_of_subset hC₀C
            have heq : ∑ b ∈ C₀, (b : ℝ) + ∑ b ∈ C \ C₀, (b : ℝ) = ∑ b ∈ C, (b : ℝ) := by
              rw [← Finset.sum_union hdisj, hunion]
            have hleR : ∑ b ∈ C, (b : ℝ) ≤ 2 * (M' : ℝ) := by
              simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat] using
                (Nat.cast_le (α := ℝ)).2 hC_le
            have hC₀_lo : -(4 * Real.sqrt (2 * (M' : ℝ) * M)) < ∑ b ∈ C₀, (b : ℝ) - 2 * (M' : ℝ) :=
              (abs_lt.1 hC₀_sum).1
            linarith
          have hlow_sum : ((C \ C₀).card : ℝ) * ((M : ℝ) / L ^ 5) ≤ ∑ b ∈ C \ C₀, (b : ℝ) := by
            calc ((C \ C₀).card : ℝ) * ((M : ℝ) / L ^ 5)
                = ∑ _b ∈ C \ C₀, ((M : ℝ) / L ^ 5) := by rw [Finset.sum_const, nsmul_eq_mul]
              _ ≤ ∑ b ∈ C \ C₀, (b : ℝ) := by
                  refine Finset.sum_le_sum fun b hb => ?_
                  exact (Finset.mem_filter.1 (hdiff hb)).2
          rw [le_div_iff₀ (by positivity)]
          exact hlow_sum.trans hsum_diff
      · refine ⟨C₀, hC₀_sub, ?_, ?_⟩
        · push Not at hhi hlo
          have h1 : ∑ b ∈ C₀, (b : ℝ) ≤ 2 * (M' : ℝ) + M := by
            simpa only [Nat.cast_sum, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
              (Nat.cast_le (α := ℝ)).2 hhi
          have h2 : 2 * (M' : ℝ) ≤ ∑ b ∈ C₀, (b : ℝ) + M := by
            simpa only [Nat.cast_sum, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
              (Nat.cast_le (α := ℝ)).2 hlo
          exact abs_le.2 ⟨by linarith, by linarith⟩
        · rw [Finset.sdiff_self, Finset.card_empty, Nat.cast_zero, add_zero]
          positivity
  obtain ⟨C, hC_sub, hC_sum, hC_diff_card⟩ := hC_exists
  have hC_sub_Icc : C ⊆ Finset.Icc 1 M := hC_sub.trans hB_sub
  have hC_sum_half : |(1 / 2 : ℝ) * ∑ b ∈ C, (b : ℝ) - M'| ≤ (M : ℝ) / 2 := by
    have : (1 / 2 : ℝ) * ∑ b ∈ C, (b : ℝ) - M' = ((∑ b ∈ C, (b : ℝ)) - 2 * (M' : ℝ)) / 2 := by ring
    rw [this, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2)]
    linarith
  have hC_V_ge : 9 * (M : ℝ) ^ 2 ≤ 16 * ∑ b ∈ C, (b : ℝ) ^ 2 := by
    have hdrop : ∑ b ∈ C₀, (b : ℝ) ^ 2 - ∑ b ∈ C, (b : ℝ) ^ 2 ≤
        ((C₀ \ C).card : ℝ) * (M : ℝ) ^ 2 := by
      have h1 : ∑ b ∈ C₀, (b : ℝ) ^ 2 ≤ ∑ b ∈ C, (b : ℝ) ^ 2 + ∑ b ∈ C₀ \ C, (b : ℝ) ^ 2 := by
        have hsub : C₀ ⊆ C ∪ (C₀ \ C) := fun x hx => by
          by_cases hxC : x ∈ C <;> simp [Finset.mem_union, hx, hxC]
        calc ∑ b ∈ C₀, (b : ℝ) ^ 2
            ≤ ∑ b ∈ C ∪ (C₀ \ C), (b : ℝ) ^ 2 :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
          _ ≤ ∑ b ∈ C, (b : ℝ) ^ 2 + ∑ b ∈ C₀ \ C, (b : ℝ) ^ 2 :=
              sum_union_le_of_nonneg C (C₀ \ C) (fun b : ℕ => (b : ℝ) ^ 2)
                (fun _ _ => sq_nonneg _)
      have h2 : ∑ b ∈ C₀ \ C, (b : ℝ) ^ 2 ≤ ((C₀ \ C).card : ℝ) * (M : ℝ) ^ 2 := by
        calc ∑ b ∈ C₀ \ C, (b : ℝ) ^ 2
            ≤ ∑ _b ∈ C₀ \ C, (M : ℝ) ^ 2 := by
              refine Finset.sum_le_sum fun b hb => ?_
              have hbM : (b : ℝ) ≤ M :=
                by exact_mod_cast (Finset.mem_Icc.1 (hB_sub (hC₀_sub (Finset.mem_sdiff.1 hb).1))).2
              exact pow_le_pow_left₀ (by positivity) hbM 2
          _ = ((C₀ \ C).card : ℝ) * (M : ℝ) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      linarith only [h1, h2]
    have hcard_le : ((C₀ \ C).card : ℝ) ≤
        4 * Real.sqrt (2 * (M' : ℝ) * M) / ((M : ℝ) / L ^ 5) := by
      have hCdiff_nn : (0 : ℝ) ≤ ((C \ C₀).card : ℝ) := Nat.cast_nonneg _
      linarith only [hC_diff_card, hCdiff_nn]
    have hmul := mul_le_mul_of_nonneg_right hcard_le (sq_nonneg (M : ℝ))
    linarith only [hC₀_V, hdrop, hmul, hV_adj]
  set K_bd : ℝ := 4 * Real.sqrt (2 * (M' : ℝ) * M) / ((M : ℝ) / L ^ 5)
  set c_min : ℝ := (1 / 2 : ℝ) * (α - 2 * (M : ℝ) * (1 / L ^ 4) ^ 2) - K_bd / 4
  have hC_minor : ∀ t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2),
      1 / (3 * (M : ℝ)) ≤ |t| → c_min ≤ ∑ b ∈ C, (d1 ((b : ℝ) * t)) ^ 2 := by
    intro t ht hta
    have ht_pos_case : ∀ u : ℝ, 1 / (3 * (M : ℝ)) ≤ u → u ≤ 1 / 2 →
        c_min ≤ ∑ b ∈ C, (d1 ((b : ℝ) * u)) ^ 2 := by
      intro u hu_lo hu_hi
      obtain ⟨t', ht'_mem, hut'⟩ := arcNet_cover hM (L := L) (by linarith only [hL]) hu_lo hu_hi
      have hnet_val := hC₀_net t' ht'_mem
      have hC₀_u : α - 2 * (M : ℝ) * (1 / L ^ 4) ^ 2 ≤ 2 * ∑ b ∈ C₀, (d1 ((b : ℝ) * u)) ^ 2 := by
        have hpt : ∀ b ∈ C₀, (d1 ((b : ℝ) * t')) ^ 2 ≤
            2 * (d1 ((b : ℝ) * u)) ^ 2 + 2 * (1 / L ^ 4) ^ 2 := by
          intro b hb
          have hbM : (b : ℝ) ≤ M :=
            by exact_mod_cast (Finset.mem_Icc.1 (hB_sub (hC₀_sub hb))).2
          have htri := d1_add_le ((b : ℝ) * u) ((b : ℝ) * (t' - u))
          have harg : (b : ℝ) * u + (b : ℝ) * (t' - u) = (b : ℝ) * t' := by ring
          rw [harg] at htri
          have hdiff : |(b : ℝ) * (t' - u)| ≤ 1 / L ^ 4 := by
            rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg b), abs_sub_comm]
            have hmul := mul_le_mul_of_nonneg_left hut' (Nat.cast_nonneg b)
            have hMmul : (b : ℝ) * (1 / ((M : ℝ) * L ^ 4)) ≤ 1 / L ^ 4 := by
              calc (b : ℝ) * (1 / ((M : ℝ) * L ^ 4))
                  ≤ (M : ℝ) * (1 / ((M : ℝ) * L ^ 4)) := by gcongr
                _ = 1 / L ^ 4 := by field_simp
            exact hmul.trans hMmul
          have hle_sum : d1 ((b : ℝ) * t') ≤ d1 ((b : ℝ) * u) + 1 / L ^ 4 := by
            linarith only [htri, hdiff]
          have hsq1 : (d1 ((b : ℝ) * t')) ^ 2 ≤ (d1 ((b : ℝ) * u) + 1 / L ^ 4) ^ 2 :=
            pow_le_pow_left₀ (d1_nonneg _) hle_sum 2
          have hsq2 : (d1 ((b : ℝ) * u) + 1 / L ^ 4) ^ 2 ≤
              2 * (d1 ((b : ℝ) * u)) ^ 2 + 2 * (1 / L ^ 4) ^ 2 := by
            nlinarith only [sq_nonneg (d1 ((b : ℝ) * u) - 1 / L ^ 4)]
          exact hsq1.trans hsq2
        have hsum_le : ∑ b ∈ C₀, (d1 ((b : ℝ) * t')) ^ 2 ≤
            2 * ∑ b ∈ C₀, (d1 ((b : ℝ) * u)) ^ 2 + 2 * (C₀.card : ℝ) * (1 / L ^ 4) ^ 2 := by
          calc ∑ b ∈ C₀, (d1 ((b : ℝ) * t')) ^ 2
              ≤ ∑ b ∈ C₀, (2 * (d1 ((b : ℝ) * u)) ^ 2 + 2 * (1 / L ^ 4) ^ 2) :=
                Finset.sum_le_sum hpt
            _ = 2 * ∑ b ∈ C₀, (d1 ((b : ℝ) * u)) ^ 2 + 2 * (C₀.card : ℝ) * (1 / L ^ 4) ^ 2 := by
                rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
                ring
        have hC₀_card : (C₀.card : ℝ) ≤ M := by
          have := Finset.card_le_card (hC₀_sub.trans hB_sub)
          rw [Nat.card_Icc] at this
          exact_mod_cast this
        have htail : 2 * (C₀.card : ℝ) * (1 / L ^ 4) ^ 2 ≤ 2 * (M : ℝ) * (1 / L ^ 4) ^ 2 := by
          gcongr
        linarith only [hnet_val, hsum_le, htail]
      have hdrop : ∑ b ∈ C₀, (d1 ((b : ℝ) * u)) ^ 2 - ∑ b ∈ C, (d1 ((b : ℝ) * u)) ^ 2 ≤
          K_bd / 4 := by
        have h1 : ∑ b ∈ C₀, (d1 ((b : ℝ) * u)) ^ 2 ≤
            ∑ b ∈ C, (d1 ((b : ℝ) * u)) ^ 2 + ∑ b ∈ C₀ \ C, (d1 ((b : ℝ) * u)) ^ 2 := by
          have hsub : C₀ ⊆ C ∪ (C₀ \ C) := fun x hx => by
            by_cases hxC : x ∈ C <;> simp [Finset.mem_union, hx, hxC]
          calc ∑ b ∈ C₀, (d1 ((b : ℝ) * u)) ^ 2
              ≤ ∑ b ∈ C ∪ (C₀ \ C), (d1 ((b : ℝ) * u)) ^ 2 :=
                Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
            _ ≤ ∑ b ∈ C, (d1 ((b : ℝ) * u)) ^ 2 + ∑ b ∈ C₀ \ C, (d1 ((b : ℝ) * u)) ^ 2 :=
                sum_union_le_of_nonneg C (C₀ \ C) (fun b : ℕ => (d1 ((b : ℝ) * u)) ^ 2)
                  (fun _ _ => sq_nonneg _)
        have h2 : ∑ b ∈ C₀ \ C, (d1 ((b : ℝ) * u)) ^ 2 ≤ ((C₀ \ C).card : ℝ) / 4 := by
          calc ∑ b ∈ C₀ \ C, (d1 ((b : ℝ) * u)) ^ 2
              ≤ ∑ _b ∈ C₀ \ C, (1 / 4 : ℝ) := by
                refine Finset.sum_le_sum fun b _ => ?_
                have := d1_nonneg ((b : ℝ) * u)
                have := d1_le_half ((b : ℝ) * u)
                nlinarith only [d1_nonneg ((b : ℝ) * u), d1_le_half ((b : ℝ) * u)]
            _ = ((C₀ \ C).card : ℝ) / 4 := by
                rw [Finset.sum_const, nsmul_eq_mul]; ring
        have hcard0 : ((C₀ \ C).card : ℝ) ≤ K_bd := by
          have hCdiff_nn : (0 : ℝ) ≤ ((C \ C₀).card : ℝ) := Nat.cast_nonneg _
          linarith only [hC_diff_card, hCdiff_nn]
        linarith only [h1, h2, hcard0]
      dsimp [c_min]
      linarith only [hC₀_u, hdrop]
    by_cases ht0 : 0 ≤ t
    · rw [abs_of_nonneg ht0] at hta
      exact ht_pos_case t hta ht.2
    · push Not at ht0
      rw [abs_of_neg ht0] at hta
      have heq : ∑ b ∈ C, (d1 ((b : ℝ) * (-t))) ^ 2 = ∑ b ∈ C, (d1 ((b : ℝ) * t)) ^ 2 := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [mul_neg, d1_neg]
      rw [← heq]
      exact ht_pos_case (-t) hta (by linarith [ht.1])
  have hV_le : ∑ b ∈ C, (b : ℝ) ^ 2 ≤ (M : ℝ) ^ 3 := by
    have hC_card : (C.card : ℝ) ≤ M := by
      have := Finset.card_le_card hC_sub_Icc
      have : C.card ≤ M := by simpa [Nat.card_Icc] using this
      exact_mod_cast this
    calc ∑ b ∈ C, (b : ℝ) ^ 2
        ≤ ∑ _b ∈ C, (M : ℝ) ^ 2 := by
          refine Finset.sum_le_sum fun b hb => ?_
          have hbM : (b : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.1 (hC_sub_Icc hb)).2
          exact pow_le_pow_left₀ (by positivity) hbM 2
      _ = (C.card : ℝ) * (M : ℝ) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (M : ℝ) * (M : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hC_card (sq_nonneg _)
      _ = (M : ℝ) ^ 3 := by ring
  have hc_win' : Real.exp (-2 * c_min) < 1 / (8 * Real.sqrt (∑ b ∈ C, (b : ℝ) ^ 2)) := by
    have hVpos : 0 < ∑ b ∈ C, (b : ℝ) ^ 2 := by
      have : 0 < 9 * (M : ℝ) ^ 2 := by positivity
      linarith
    have hsqrt_le : Real.sqrt (∑ b ∈ C, (b : ℝ) ^ 2) ≤ Real.sqrt ((M : ℝ) ^ 3) :=
      Real.sqrt_le_sqrt hV_le
    have hdiv_le : 1 / (8 * Real.sqrt ((M : ℝ) ^ 3)) ≤ 1 / (8 * Real.sqrt (∑ b ∈ C, (b : ℝ) ^ 2)) :=
      one_div_le_one_div_of_le (by positivity) (by gcongr)
    exact lt_of_lt_of_le harc_win hdiv_le
  obtain ⟨A, hAC, hA_sum⟩ :=
    exists_subset_sum_eq_of_arc_bounds C M M' hM hC_sub_Icc hC_sum_half hC_V_ge hC_minor hc_win'
  exact ⟨A, hAC.trans hC_sub, hA_sum⟩

/- ### Part 5: Asymptotic Choice of `s`, `m` via `ψ(x) ~ x` and Final Theorem -/

lemma lcm_Icc_mono {a b : ℕ} (hab : a ≤ b) :
    (Finset.Icc 1 a).lcm (id : ℕ → ℕ) ≤ (Finset.Icc 1 b).lcm (id : ℕ → ℕ) := by
  have hpos : 0 < (Finset.Icc 1 b).lcm (id : ℕ → ℕ) := lcm_Icc_pos b
  apply Nat.le_of_dvd hpos
  apply Finset.lcm_dvd
  intro k hk
  exact Finset.dvd_lcm (Finset.Icc_subset_Icc_right hab hk)

lemma lcm_Icc_succ_le (s : ℕ) :
    (Finset.Icc 1 (s + 1)).lcm (id : ℕ → ℕ) ≤ (Finset.Icc 1 s).lcm (id : ℕ → ℕ) * (s + 1) := by
  have hmem : Finset.Icc 1 (s + 1) = insert (s + 1) (Finset.Icc 1 s) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hmem, Finset.lcm_insert]
  change Nat.lcm (s + 1) ((Finset.Icc 1 s).lcm (id : ℕ → ℕ)) ≤
    (Finset.Icc 1 s).lcm (id : ℕ → ℕ) * (s + 1)
  have hgcd := Nat.lcm_mul_gcd (s + 1) ((Finset.Icc 1 s).lcm (id : ℕ → ℕ))
  have hpos : 1 ≤ Nat.gcd (s + 1) ((Finset.Icc 1 s).lcm (id : ℕ → ℕ)) :=
    Nat.gcd_pos_of_pos_left _ (by omega)
  calc Nat.lcm (s + 1) ((Finset.Icc 1 s).lcm (id : ℕ → ℕ))
      ≤ Nat.lcm (s + 1) ((Finset.Icc 1 s).lcm (id : ℕ → ℕ)) *
          Nat.gcd (s + 1) ((Finset.Icc 1 s).lcm (id : ℕ → ℕ)) := Nat.le_mul_of_pos_right _ hpos
    _ = (s + 1) * (Finset.Icc 1 s).lcm (id : ℕ → ℕ) := hgcd
    _ = (Finset.Icc 1 s).lcm (id : ℕ → ℕ) * (s + 1) := mul_comm _ _

lemma one_half_le_log_two : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have hexp : (1 / 2 : ℝ) ≤ Real.exp (-1 / 2) := by
    linarith [Real.add_one_le_exp (-1 / 2 : ℝ)]
  have hexp2 : Real.exp (1 / 2 : ℝ) ≤ 2 := by
    have hinv : Real.exp (-1 / 2 : ℝ) = (Real.exp (1 / 2 : ℝ))⁻¹ := by
      rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.exp_neg]
    rw [hinv] at hexp
    have hpos : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
    have hmul := mul_le_mul_of_nonneg_left hexp hpos.le
    rw [mul_inv_cancel₀ hpos.ne'] at hmul
    linarith
  rw [Real.le_log_iff_exp_le (by norm_num)]
  exact hexp2

lemma eventually_pow_log_lt_mul_nat (k : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, (Real.log n) ^ k ≤ c * (n : ℝ) := by
  have ho : (fun x : ℝ => (Real.log x) ^ k) =o[atTop] (fun x : ℝ => x ^ (1 : ℝ)) := by
    simpa using (isLittleO_log_rpow_rpow_atTop k (by norm_num : (0 : ℝ) < 1))
  have hbd := tendsto_natCast_atTop_atTop.eventually (ho.bound hc)
  filter_upwards [hbd, eventually_ge_atTop 2] with n hn hn2
  have hnpos : (0 : ℝ) ≤ n := by positivity
  simp only [rpow_one, Real.norm_eq_abs] at hn
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  rw [abs_of_nonneg (pow_nonneg hlog0 k), abs_of_nonneg hnpos] at hn
  exact hn

lemma eventually_log_log_lt_mul_nat {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, Real.log (Real.log n) ≤ c * Real.log n := by
  have ho : (fun x : ℝ => Real.log x) =o[atTop] (fun x : ℝ => x ^ (1 : ℝ)) := by
    simpa using (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1))
  have hbd := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (ho.bound hc)
  have hbig := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop 2)
  filter_upwards [hbd, hbig] with n hn hn2
  simp only [Function.comp_def, rpow_one, Real.norm_eq_abs] at hn hn2
  have hL1 : 1 ≤ Real.log n := by linarith
  have hll0 : 0 ≤ Real.log (Real.log n) := Real.log_nonneg hL1
  rw [abs_of_nonneg hll0, abs_of_nonneg (by linarith)] at hn
  exact hn

lemma exists_s_m_eventually
    (h_psi : Asymptotics.IsEquivalent atTop Chebyshev.psi (fun x : ℝ => x))
    {δ : ℝ} (hδpos : 0 < δ) (hδle : δ ≤ 1 / 16) :
    ∀ᶠ n : ℕ in atTop, ∃ s m : ℕ, 1 ≤ s ∧ 1 ≤ m ∧
      (s : ℝ) ≤ (2 + δ) * Real.log n ∧
      (2 - 2 * δ) * Real.log n ≤ (s + 1 : ℝ) ∧
      (m : ℝ) ≤ (n : ℝ) ^ 2 / (20 * (Real.log n) ^ 2) ∧
      (n : ℝ) ^ 2 / (80 * (Real.log n) ^ 3) ≤ (m : ℝ) ∧
      ∀ d : ℕ, 1 ≤ d → d ≤ s → d ∣ m := by
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.1 (h_psi.isLittleO.bound (by linarith : 0 < δ / 8))
  have h_log_big : ∀ᶠ n : ℕ in atTop, max 1000 (2 * max 0 X₀ + 10 / δ) ≤ Real.log n := by
    have ht := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact ht.eventually (eventually_ge_atTop _)
  have h_log_2 : ∀ᶠ n : ℕ in atTop, (Real.log n) ^ 2 ≤ (1 / 10000 : ℝ) * (n : ℝ) :=
    eventually_pow_log_lt_mul_nat 2 (by norm_num)
  have h_log_ll : ∀ᶠ n : ℕ in atTop, Real.log (Real.log n) ≤ (δ / 16) * Real.log n :=
    eventually_log_log_lt_mul_nat (by positivity)
  have h_log_20_big : ∀ᶠ n : ℕ in atTop, Real.log 20 * 8 / δ ≤ Real.log n := by
    have ht := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact ht.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_ge_atTop 100000, h_log_big, h_log_2, h_log_ll, h_log_20_big]
    with n hn_big hL_big hL2 hll hlog20_big
  set L : ℝ := Real.log n
  have hL1000 : 1000 ≤ L := le_trans (le_max_left _ _) hL_big
  have hLpos : 0 < L := by linarith
  have hL_rhs : 2 * max 0 X₀ + 10 / δ ≤ L := le_trans (le_max_right _ _) hL_big
  have hLX0 : X₀ ≤ (1 / 2 : ℝ) * L := by
    have : 2 * max 0 X₀ ≤ L := by linarith [show 0 ≤ 10 / δ by positivity]
    have : X₀ ≤ max 0 X₀ := le_max_right _ _
    linarith
  have h10d : 10 / δ ≤ L := by
    have : 0 ≤ max 0 X₀ := le_max_left _ _
    linarith
  have h10dl : 10 ≤ δ * L := by
    have := (div_le_iff₀ hδpos).1 h10d
    linarith
  have hpsi_bd : ∀ x : ℝ, (1 / 2 : ℝ) * L ≤ x →
      (1 - δ / 8) * x ≤ Chebyshev.psi x ∧ Chebyshev.psi x ≤ (1 + δ / 8) * x := by
    intro x hx
    have hx_pos : 0 < x := by linarith
    have hb := hX₀ x (by linarith)
    simp only [Pi.sub_apply, Real.norm_eq_abs] at hb
    rw [abs_of_pos hx_pos, abs_le] at hb
    exact ⟨by linarith, by linarith⟩
  have hnpos : (0 : ℝ) < n := by positivity
  have hlog_20 : Real.log (20 * L ^ 2) ≤ (δ / 4) * L := by
    have hlog20 : Real.log 20 ≤ (δ / 8) * L := by
      have := (div_le_iff₀ hδpos).1 hlog20_big
      linarith
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    linarith
  have hPn_pos : ((1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 / (20 * L ^ 2) := by
    rw [Nat.cast_one, one_le_div (by positivity)]
    have h1 : 20 * L ^ 2 ≤ 20 * (1 / 10000 : ℝ) * (n : ℝ) := by linarith
    have h2 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    nlinarith
  set P_n : ℕ := ⌊(n : ℝ) ^ 2 / (20 * L ^ 2)⌋₊
  have hPn1 : 1 ≤ P_n := Nat.le_floor hPn_pos
  set K_hi : ℕ := ⌊(2 + δ) * L⌋₊
  have hK_hi_lo : (2 + δ / 2) * L ≤ (K_hi : ℝ) := by
    have h1 : (2 + δ) * L - 1 < (K_hi : ℝ) := Nat.sub_one_lt_floor _
    linarith
  have hK_hi_win : P_n < (Finset.Icc 1 K_hi).lcm (id : ℕ → ℕ) := by
    have hlog_eq : Real.log (((Finset.Icc 1 K_hi).lcm (id : ℕ → ℕ) : ℕ) : ℝ) = Chebyshev.psi K_hi :=
      log_lcm_Icc_eq_psi K_hi
    have hpsi_hi := (hpsi_bd (K_hi : ℝ) (by nlinarith)).1
    have hpsi_gt : 2 * L < Chebyshev.psi K_hi := by
      have hpos_coef : 2 < (1 - δ / 8) * (2 + δ / 2) := by
        have hpol : (1 - δ / 8) * (2 + δ / 2) = 2 + δ / 4 - δ ^ 2 / 16 := by ring
        nlinarith only [hδpos, hδle, hpol]
      have hcoef : 2 * L < (1 - δ / 8) * ((2 + δ / 2) * L) := by
        rw [← mul_assoc]
        exact mul_lt_mul_of_pos_right hpos_coef hLpos
      have hmul : (1 - δ / 8) * ((2 + δ / 2) * L) ≤ (1 - δ / 8) * (K_hi : ℝ) :=
        mul_le_mul_of_nonneg_left hK_hi_lo (by linarith only [hδle])
      linarith only [hpsi_hi, hcoef, hmul]
    have hPn_log : Real.log (P_n : ℝ) ≤ 2 * L := by
      have hle1 : (P_n : ℝ) ≤ (n : ℝ) ^ 2 / (20 * L ^ 2) := Nat.floor_le (by positivity)
      have hle2 : (n : ℝ) ^ 2 / (20 * L ^ 2) ≤ (n : ℝ) ^ 2 :=
        div_le_self (by positivity) (by nlinarith)
      calc Real.log (P_n : ℝ)
          ≤ Real.log ((n : ℝ) ^ 2) := Real.log_le_log (by exact_mod_cast hPn1) (hle1.trans hle2)
        _ = 2 * L := by rw [Real.log_pow]; push_cast; ring
    have hlt_log : Real.log (P_n : ℝ) <
        Real.log (((Finset.Icc 1 K_hi).lcm (id : ℕ → ℕ) : ℕ) : ℝ) := by
      linarith
    have hltR : (P_n : ℝ) < (((Finset.Icc 1 K_hi).lcm (id : ℕ → ℕ) : ℕ) : ℝ) :=
      (Real.log_lt_log_iff (by exact_mod_cast hPn1) (by exact_mod_cast lcm_Icc_pos K_hi)).1 hlt_log
    exact_mod_cast hltR
  have hex : ∃ k : ℕ, P_n < (Finset.Icc 1 (k + 1)).lcm (id : ℕ → ℕ) :=
    ⟨K_hi, lt_of_lt_of_le hK_hi_win (lcm_Icc_mono (Nat.le_succ K_hi))⟩
  set s : ℕ := Nat.find hex
  have hs_spec : P_n < (Finset.Icc 1 (s + 1)).lcm (id : ℕ → ℕ) := Nat.find_spec hex
  have hs_le_Khi : s ≤ K_hi :=
    Nat.find_le (lt_of_lt_of_le hK_hi_win (lcm_Icc_mono (Nat.le_succ K_hi)))
  have hs_pos : 1 ≤ s := by
    by_contra hs0
    have hs_eq : s = 0 := by omega
    rw [hs_eq] at hs_spec
    have hlcm1 : (Finset.Icc 1 1).lcm (id : ℕ → ℕ) = 1 := by simp
    rw [hlcm1] at hs_spec
    omega
  set m : ℕ := (Finset.Icc 1 s).lcm (id : ℕ → ℕ)
  have hm_pos : 1 ≤ m := lcm_Icc_pos s
  have hm_le_Pn : m ≤ P_n := by
    have hmin := Nat.find_min hex (by omega : s - 1 < s)
    push Not at hmin
    simpa [show s - 1 + 1 = s by omega] using hmin
  have hs_ub : (s : ℝ) ≤ (2 + δ) * L := by
    have h1 : (s : ℝ) ≤ (K_hi : ℝ) := by exact_mod_cast hs_le_Khi
    have h2 : (K_hi : ℝ) ≤ (2 + δ) * L := Nat.floor_le (by positivity)
    linarith
  have hs_lb : (2 - 2 * δ) * L ≤ (s + 1 : ℝ) := by
    set K_lo : ℕ := ⌊(2 - 2 * δ) * L⌋₊
    by_contra hlt_s
    push Not at hlt_s
    have hs1_le : s + 1 ≤ K_lo := by
      have : ((s + 1 : ℕ) : ℝ) < (2 - 2 * δ) * L := by push_cast; linarith
      exact Nat.le_floor this.le
    have hlog_le : Real.log (((Finset.Icc 1 (s + 1)).lcm (id : ℕ → ℕ) : ℕ) : ℝ) ≤
        Chebyshev.psi K_lo := by
      rw [← log_lcm_Icc_eq_psi K_lo]
      apply Real.log_le_log (by exact_mod_cast lcm_Icc_pos (s + 1))
      exact_mod_cast lcm_Icc_mono hs1_le
    have hK_lo_ge : (1 / 2 : ℝ) * L ≤ (K_lo : ℝ) := by
      have h1 : (2 - 2 * δ) * L - 1 < (K_lo : ℝ) := Nat.sub_one_lt_floor _
      have h2 : δ * L ≤ (1 / 16 : ℝ) * L := mul_le_mul_of_nonneg_right hδle hLpos.le
      linarith
    have hpsi_lo := (hpsi_bd (K_lo : ℝ) hK_lo_ge).2
    have hK_lo_le : (K_lo : ℝ) ≤ (2 - 2 * δ) * L := Nat.floor_le (by nlinarith)
    have hpsi_ub : Chebyshev.psi K_lo ≤ (1 + δ / 8) * ((2 - 2 * δ) * L) :=
      hpsi_lo.trans (mul_le_mul_of_nonneg_left hK_lo_le (by positivity))
    have hPn_ge : (n : ℝ) ^ 2 / (20 * L ^ 2) - 1 < (P_n : ℝ) := Nat.sub_one_lt_floor _
    have hPn_half : (n : ℝ) ^ 2 / (40 * L ^ 2) ≤ (P_n : ℝ) := by
      have h1 : 1 ≤ (n : ℝ) ^ 2 / (40 * L ^ 2) := by
        rw [one_le_div (by positivity)]
        have : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
        nlinarith
      have h2 : (n : ℝ) ^ 2 / (40 * L ^ 2) = (n : ℝ) ^ 2 / (20 * L ^ 2) - (n : ℝ) ^ 2 / (40 * L ^ 2) := by
        ring
      linarith
    have hPn_log_ge : (2 - δ / 2) * L ≤ Real.log (P_n : ℝ) := by
      have hle_log : Real.log ((n : ℝ) ^ 2 / (40 * L ^ 2)) ≤ Real.log (P_n : ℝ) :=
        Real.log_le_log (by positivity) hPn_half
      have hlog_40 : Real.log (40 * L ^ 2) ≤ (δ / 2) * L := by
        have h40 : 40 * L ^ 2 = 2 * (20 * L ^ 2) := by ring
        rw [h40, Real.log_mul (by norm_num) (by positivity)]
        have hlog2 : Real.log 2 ≤ 1 := by
          rw [Real.log_le_iff_le_exp (by norm_num)]
          linarith [Real.add_one_le_exp (1 : ℝ)]
        linarith
      have hsplit : Real.log ((n : ℝ) ^ 2 / (40 * L ^ 2)) =
          2 * L - Real.log (40 * L ^ 2) := by
        rw [Real.log_div (by positivity) (by positivity), Real.log_pow]
        push_cast; ring
      linarith
    have hlt_log : Real.log (P_n : ℝ) <
        Real.log (((Finset.Icc 1 (s + 1)).lcm (id : ℕ → ℕ) : ℕ) : ℝ) := by
      apply Real.log_lt_log (by exact_mod_cast hPn1)
      exact_mod_cast hs_spec
    have hcoef : (1 + δ / 8) * ((2 - 2 * δ) * L) < (2 - δ / 2) * L := by
      have hpol : (1 + δ / 8) * (2 - 2 * δ) = 2 - (7 / 4 : ℝ) * δ - δ ^ 2 / 4 := by ring
      nlinarith only [hδpos, hLpos, hpol]
    linarith only [hlog_le, hpsi_ub, hPn_log_ge, hlt_log, hcoef]
  have hm_ub : (m : ℝ) ≤ (n : ℝ) ^ 2 / (20 * L ^ 2) := by
    have h1 : (m : ℝ) ≤ P_n := by exact_mod_cast hm_le_Pn
    have h2 : (P_n : ℝ) ≤ (n : ℝ) ^ 2 / (20 * L ^ 2) := Nat.floor_le (by positivity)
    linarith
  have hm_lb : (n : ℝ) ^ 2 / (80 * L ^ 3) ≤ (m : ℝ) := by
    have hs1_ub : (s + 1 : ℝ) ≤ 3 * L := by
      have : δ * L ≤ (1 / 16 : ℝ) * L := mul_le_mul_of_nonneg_right hδle hLpos.le
      linarith
    have hmul_lt : (P_n : ℝ) < (m : ℝ) * (s + 1 : ℝ) := by
      exact_mod_cast (hs_spec.trans_le (lcm_Icc_succ_le s))
    have hPn_half : (n : ℝ) ^ 2 / (25 * L ^ 2) ≤ (P_n : ℝ) := by
      have h1 : (n : ℝ) ^ 2 / (20 * L ^ 2) - 1 < (P_n : ℝ) := Nat.sub_one_lt_floor _
      have h2 : 1 ≤ (n : ℝ) ^ 2 / (100 * L ^ 2) := by
        rw [one_le_div (by positivity)]
        have : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
        nlinarith
      have h3 : (n : ℝ) ^ 2 / (25 * L ^ 2) = (n : ℝ) ^ 2 / (20 * L ^ 2) - (n : ℝ) ^ 2 / (100 * L ^ 2) := by
        ring
      linarith
    have hm_gt : (n : ℝ) ^ 2 / (25 * L ^ 2) < (m : ℝ) * (3 * L) := by
      have hle : (m : ℝ) * (s + 1 : ℝ) ≤ (m : ℝ) * (3 * L) :=
        mul_le_mul_of_nonneg_left hs1_ub (by positivity)
      linarith
    have hdiv3 : (n : ℝ) ^ 2 / (75 * L ^ 3) < (m : ℝ) := by
      calc (n : ℝ) ^ 2 / (75 * L ^ 3)
          = ((n : ℝ) ^ 2 / (25 * L ^ 2)) / (3 * L) := by ring
        _ < ((m : ℝ) * (3 * L)) / (3 * L) := div_lt_div_of_pos_right hm_gt (by positivity)
        _ = (m : ℝ) := by field_simp
    have h80 : (n : ℝ) ^ 2 / (80 * L ^ 3) ≤ (n : ℝ) ^ 2 / (75 * L ^ 3) := by
      apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_right (by norm_num) (pow_pos hLpos 3).le
    linarith only [hdiv3, h80]
  exact ⟨s, m, hs_pos, hm_pos, hs_ub, hs_lb, hm_ub, hm_lb,
    fun d hd1 hds => Finset.dvd_lcm (Finset.mem_Icc.2 ⟨hd1, hds⟩)⟩

lemma exists_subset_sum_from_B
    (n m d : ℕ) (B : Finset ℕ) (L T η c_win : ℝ)
    (hn_big : 100000 ≤ n) (hm_pos : 1 ≤ m) (hd1 : 1 ≤ d) (hd_dvd_m : d ∣ m)
    (hL_eq : L = Real.log n) (hL1000 : 1000 ≤ L) (hL4c : 4 / c_win ≤ L)
    (hc_win_pos : 0 < c_win) (hc_win_def : 2 * c_win ≤ 9 * η / 51200000)
    (hηpos : 0 < η) (hT_pos : 0 < T)
    (hL24 : L ^ 24 ≤ (c_win / 64) ^ 2 * (n : ℝ))
    (hL22 : L ^ 22 ≤ (1 / 100000000000000 : ℝ) * (n : ℝ))
    (hL14 : L ^ 14 ≤ (c_win / 10) ^ 2 * (n : ℝ))
    (hL2 : L ^ 2 ≤ (1 / 10000 : ℝ) * (n : ℝ))
    (hm_ub : (m : ℝ) ≤ (n : ℝ) ^ 2 / (20 * L ^ 2))
    (hm_lb : (n : ℝ) ^ 2 / (80 * L ^ 3) ≤ (m : ℝ))
    (hd_le_3L : (d : ℝ) ≤ 3 * L)
    (hB_sub : B ⊆ Finset.Icc 1 (n / d))
    (hB_card_ge : (1 / 2 : ℝ) * ((n : ℝ) / L) ≤ (B.card : ℝ))
    (hT_le_B : T ≤ (2 / 5 : ℝ) * (B.card : ℝ))
    (hT_ge_eta : η * (n : ℝ) / (2 * L ^ 2) ≤ T)
    (hB_nondiv : ∀ q : ℕ, 2 ≤ q → T ≤ ((B.filter (fun b => ¬ q ∣ b)).card : ℝ)) :
    ∃ A' ⊆ B, ∑ b ∈ A', b = m / d := by
  have hLpos : 0 < L := by linarith only [hL1000]
  have hnpos : (0 : ℝ) < n := by positivity
  let M : ℕ := n / d
  let M' : ℕ := m / d
  have hM_ge1 : 1 ≤ M := by
    have hB_pos : 0 < B.card := by
      have : (0 : ℝ) < B.card := by linarith [show 0 < (1 / 2 : ℝ) * ((n : ℝ) / L) by positivity]
      exact_mod_cast this
    obtain ⟨b, hb⟩ := Finset.card_pos.1 hB_pos
    have hb_mem := Finset.mem_Icc.1 (hB_sub hb)
    omega
  have hM'_ge1 : 1 ≤ M' := Nat.div_pos (Nat.le_of_dvd hm_pos hd_dvd_m) hd1
  have hM_le_div : (M : ℝ) ≤ (n : ℝ) / (d : ℝ) := Nat.cast_div_le
  have hM_le_n : (M : ℝ) ≤ n := hM_le_div.trans (div_le_self hnpos.le (by exact_mod_cast hd1))
  have hM_ge_4L : (n : ℝ) / (4 * L) ≤ (M : ℝ) := by
    have hM_ge_div : (n : ℝ) / (d : ℝ) - 1 ≤ (M : ℝ) := by
      have hdiv : (n : ℝ) < ((M : ℝ) + 1) * (d : ℝ) := by
        have : n < (M + 1) * d := Nat.lt_mul_of_div_lt (Nat.lt_succ_self M) (by omega : 0 < d)
        exact_mod_cast this
      rw [sub_le_iff_le_add, div_le_iff₀ (by exact_mod_cast hd1)]
      exact hdiv.le
    have h1 : (n : ℝ) / (3 * L) ≤ (n : ℝ) / (d : ℝ) :=
      div_le_div_of_nonneg_left hnpos.le (by exact_mod_cast hd1) hd_le_3L
    have h2 : 1 ≤ (n : ℝ) / (12 * L) := by
      rw [one_le_div (by positivity)]
      nlinarith only [hL1000, hL2]
    have h3 : (n : ℝ) / (4 * L) = (n : ℝ) / (3 * L) - (n : ℝ) / (12 * L) := by ring
    linarith only [hM_ge_div, h1, h2, h3]
  have hM_pos_R : (0 : ℝ) < M := by exact_mod_cast hM_ge1
  have hB_lb_M : (M : ℝ) / (2 * L) ≤ (B.card : ℝ) := by
    calc (M : ℝ) / (2 * L) ≤ (n : ℝ) / (2 * L) := by gcongr
      _ = (1 / 2 : ℝ) * ((n : ℝ) / L) := by ring
      _ ≤ (B.card : ℝ) := hB_card_ge
  have hB_pos_all : ∀ b ∈ B, 1 ≤ b := fun b hb => (Finset.mem_Icc.1 (hB_sub hb)).1
  have hsum_B_ge : (n : ℝ) ^ 2 / (8 * L ^ 2) ≤ ∑ b ∈ B, (b : ℝ) := by
    have hnat := sum_ge_card_sq_div_two B hB_pos_all
    have hR : ((B.card : ℝ) ^ 2) / 2 ≤ ∑ b ∈ B, (b : ℝ) := by
      have h1nat : (B.card : ℝ) * ((B.card : ℝ) + 1) = ((B.card * (B.card + 1) : ℕ) : ℝ) := by
        push_cast; ring
      have h2nat : 2 * ∑ b ∈ B, (b : ℝ) = ((2 * ∑ b ∈ B, b : ℕ) : ℝ) := by push_cast; rfl
      have hnatR : ((B.card * (B.card + 1) : ℕ) : ℝ) ≤ ((2 * ∑ b ∈ B, b : ℕ) : ℝ) := by
        exact_mod_cast hnat
      have h1 : (B.card : ℝ) * ((B.card : ℝ) + 1) ≤ 2 * ∑ b ∈ B, (b : ℝ) := by
        linarith only [h1nat, h2nat, hnatR]
      nlinarith only [h1, show (0 : ℝ) ≤ B.card by positivity]
    have hsq : ((n : ℝ) / (2 * L)) ^ 2 / 2 ≤ ((B.card : ℝ) ^ 2) / 2 := by
      have heq12 : (n : ℝ) / (2 * L) = (1 / 2 : ℝ) * ((n : ℝ) / L) := by ring
      have h1 : (n : ℝ) / (2 * L) ≤ (B.card : ℝ) := by linarith only [hB_card_ge, heq12]
      nlinarith only [h1, show 0 ≤ (n : ℝ) / (2 * L) by positivity]
    have hEq : ((n : ℝ) / (2 * L)) ^ 2 / 2 = (n : ℝ) ^ 2 / (8 * L ^ 2) := by ring
    linarith only [hR, hsq, hEq]
  have hM'_eq_R : (M' : ℝ) = (m : ℝ) / (d : ℝ) := by
    have hm_eq : m = d * M' := (Nat.mul_div_cancel' hd_dvd_m).symm
    have h1 : (m : ℝ) = (d : ℝ) * (M' : ℝ) := by exact_mod_cast hm_eq
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    field_simp [hd0]
    linarith only [h1]
  have hM'_ub : (M' : ℝ) ≤ (n : ℝ) ^ 2 / (20 * L ^ 2) := by
    rw [hM'_eq_R]
    exact (div_le_self (by positivity) (by exact_mod_cast hd1)).trans hm_ub
  have hM'_lb_M : (M : ℝ) * (n : ℝ) / (80 * L ^ 3) ≤ (M' : ℝ) := by
    rw [hM'_eq_R]
    have h1 : (n : ℝ) ^ 2 / (80 * L ^ 3) / (d : ℝ) ≤ (m : ℝ) / (d : ℝ) :=
      div_le_div_of_nonneg_right hm_lb (by positivity)
    have h2 : (M : ℝ) * (n : ℝ) / (80 * L ^ 3) ≤ (n : ℝ) ^ 2 / (80 * L ^ 3) / (d : ℝ) := by
      have heq : (n : ℝ) ^ 2 / (80 * L ^ 3) / (d : ℝ) =
          ((n : ℝ) / (d : ℝ)) * (n : ℝ) / (80 * L ^ 3) := by ring
      rw [heq]
      gcongr
    exact h2.trans h1
  have hB_sum_hi : 2 * (M' : ℝ) + (M : ℝ) ^ 2 / L ^ 5 ≤ ∑ b ∈ B, (b : ℝ) := by
    have hM2 : (M : ℝ) ^ 2 / L ^ 5 ≤ (n : ℝ) ^ 2 / L ^ 5 := by gcongr
    have hL5 : (n : ℝ) ^ 2 / L ^ 5 ≤ (n : ℝ) ^ 2 / (100 * L ^ 2) := by
      apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      have h100' : (10 : ℝ) ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith only [hL1000]) 3
      have h100 : (100 : ℝ) ≤ L ^ 3 := by
        linarith only [h100', show (10 : ℝ) ^ 3 = 1000 by norm_num]
      have hL5eq : L ^ 5 = L ^ 3 * L ^ 2 := by ring
      nlinarith only [h100, hL5eq, sq_nonneg L]
    have hsplit : (n : ℝ) ^ 2 / (8 * L ^ 2) - 2 * ((n : ℝ) ^ 2 / (20 * L ^ 2)) -
        (n : ℝ) ^ 2 / (100 * L ^ 2) = 3 * (n : ℝ) ^ 2 / (200 * L ^ 2) := by ring
    have h3nn : 0 ≤ 3 * (n : ℝ) ^ 2 / (200 * L ^ 2) := by positivity
    linarith only [hM'_ub, hsum_B_ge, hM2, hL5, hsplit, h3nn]
  have hM'_lt : 2 * (M' : ℝ) < ∑ b ∈ B, (b : ℝ) := by
    have : 0 < (M : ℝ) ^ 2 / L ^ 5 := by positivity
    linarith only [hB_sum_hi, this]
  have hM'_hi : (M : ℝ) ^ 2 / L ^ 5 ≤ 2 * (M' : ℝ) := by
    have h1 : (M : ℝ) ^ 2 / L ^ 5 ≤ (M : ℝ) * (n : ℝ) / L ^ 5 := by
      rw [sq]
      gcongr
    have h2 : (M : ℝ) * (n : ℝ) / L ^ 5 ≤ 2 * ((M : ℝ) * (n : ℝ) / (80 * L ^ 3)) := by
      have hL2eq : L ^ 2 = L * L := by ring
      have h40 : 40 ≤ L ^ 2 := by nlinarith only [hL1000, hL2eq]
      have heq : 2 * ((M : ℝ) * (n : ℝ) / (80 * L ^ 3)) = (M : ℝ) * (n : ℝ) / (40 * L ^ 3) := by ring
      rw [heq]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      have hL5eq : L ^ 5 = L ^ 2 * L ^ 3 := by ring
      nlinarith only [h40, hL5eq, pow_pos hLpos 3]
    linarith only [h1, h2, hM'_lb_M]
  set S_B : ℝ := ∑ b ∈ B, (b : ℝ)
  have hS_B_pos : 0 < S_B := by linarith only [hM'_lt]
  set p : ℝ := 2 * (M' : ℝ) / S_B
  have hS_B_ub : S_B ≤ (M : ℝ) ^ 2 := by
    have hcard : (B.card : ℝ) ≤ M := by
      have := Finset.card_le_card hB_sub
      rw [Nat.card_Icc] at this
      exact_mod_cast this
    calc S_B ≤ ∑ _b ∈ B, (M : ℝ) := by
          refine Finset.sum_le_sum fun b hb => ?_
          exact_mod_cast (Finset.mem_Icc.1 (hB_sub hb)).2
      _ = (B.card : ℝ) * (M : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (M : ℝ) * (M : ℝ) := mul_le_mul_of_nonneg_right hcard hM_pos_R.le
      _ = (M : ℝ) ^ 2 := by ring
  have hp_lb : (n : ℝ) / (40 * L ^ 3 * (M : ℝ)) ≤ p := by
    dsimp [p]
    have hnum : (M : ℝ) * (n : ℝ) / (40 * L ^ 3) ≤ 2 * (M' : ℝ) := by
      have heq : (M : ℝ) * (n : ℝ) / (40 * L ^ 3) = 2 * ((M : ℝ) * (n : ℝ) / (80 * L ^ 3)) := by ring
      linarith only [hM'_lb_M, heq]
    calc (n : ℝ) / (40 * L ^ 3 * (M : ℝ))
        = ((M : ℝ) * (n : ℝ) / (40 * L ^ 3)) / (M : ℝ) ^ 2 := by field_simp
      _ ≤ ((M : ℝ) * (n : ℝ) / (40 * L ^ 3)) / S_B :=
          div_le_div_of_nonneg_left (by positivity) hS_B_pos hS_B_ub
      _ ≤ (2 * (M' : ℝ)) / S_B := div_le_div_of_nonneg_right hnum hS_B_pos.le
  have hp_lb2 : 1 / (40 * L ^ 3) ≤ p := by
    have h1 : 1 / (40 * L ^ 3) ≤ (n : ℝ) / (40 * L ^ 3 * (M : ℝ)) := by
      have heq : 1 / (40 * L ^ 3) = (M : ℝ) / (40 * L ^ 3 * (M : ℝ)) := by field_simp
      rw [heq]
      exact div_le_div_of_nonneg_right hM_le_n (by positivity)
    exact h1.trans hp_lb
  have hsum_sq_lb : (M : ℝ) ^ 3 / (64 * L ^ 3) ≤ ∑ b ∈ B, (b : ℝ) ^ 2 := by
    have h1 := sum_sq_ge_card_cube_div_eight B hB_pos_all
    have h2 : ((M : ℝ) / (2 * L)) ^ 3 / 8 ≤ (B.card : ℝ) ^ 3 / 8 := by
      have : 0 ≤ (M : ℝ) / (2 * L) := by positivity
      gcongr
    have heq : ((M : ℝ) / (2 * L)) ^ 3 / 8 = (M : ℝ) ^ 3 / (64 * L ^ 3) := by ring
    linarith only [h1, h2, heq]
  have hmu2_lb : (M : ℝ) ^ 2 * (n : ℝ) / (2560 * L ^ 6) ≤ p * ∑ b ∈ B, (b : ℝ) ^ 2 := by
    have hmul := mul_le_mul hp_lb hsum_sq_lb (by positivity) (by positivity)
    have heq : ((n : ℝ) / (40 * L ^ 3 * (M : ℝ))) * ((M : ℝ) ^ 3 / (64 * L ^ 3)) =
        (M : ℝ) ^ 2 * (n : ℝ) / (2560 * L ^ 6) := by field_simp; ring
    linarith only [hmul, heq]
  have hmu2_big : 64 * (M : ℝ) ^ 2 < p * ∑ b ∈ B, (b : ℝ) ^ 2 := by
    have h16 : 163840 * L ^ 6 < (n : ℝ) := by
      have hL6 : L ^ 6 ≤ L ^ 22 := pow_le_pow_right₀ (by linarith only [hL1000]) (by omega)
      nlinarith only [hL6, hL22, hnpos]
    have h2 : 64 * (M : ℝ) ^ 2 < (M : ℝ) ^ 2 * (n : ℝ) / (2560 * L ^ 6) := by
      rw [lt_div_iff₀ (by positivity)]
      nlinarith only [h16, sq_pos_of_pos hM_pos_R]
    linarith only [h2, hmu2_lb]
  have hK_bd_ub : 4 * Real.sqrt (2 * (M' : ℝ) * M) / ((M : ℝ) / L ^ 5) ≤ 16 * Real.sqrt n * L ^ 5 := by
    have hsq_in : 2 * (M' : ℝ) * (M : ℝ) ≤ (n : ℝ) ^ 3 / L ^ 2 := by
      have h1 : 2 * (M' : ℝ) * (M : ℝ) ≤ 2 * ((n : ℝ) ^ 2 / (20 * L ^ 2)) * (n : ℝ) := by gcongr
      have h10 : 2 * ((n : ℝ) ^ 2 / (20 * L ^ 2)) * (n : ℝ) = (n : ℝ) ^ 3 / (10 * L ^ 2) := by ring
      have hle : (n : ℝ) ^ 3 / (10 * L ^ 2) ≤ (n : ℝ) ^ 3 / L ^ 2 := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith only [sq_pos_of_pos hLpos]
      linarith only [h1, h10, hle]
    have hsq_le : Real.sqrt (2 * (M' : ℝ) * M) ≤ ((n : ℝ) / L) * Real.sqrt n := by
      calc Real.sqrt (2 * (M' : ℝ) * M)
          ≤ Real.sqrt (((n : ℝ) / L) ^ 2 * n) := by
            apply Real.sqrt_le_sqrt
            have heq : ((n : ℝ) / L) ^ 2 * n = (n : ℝ) ^ 3 / L ^ 2 := by ring
            linarith only [hsq_in, heq]
        _ = ((n : ℝ) / L) * Real.sqrt n := by
            rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    have hdiv_M : L ^ 5 / (M : ℝ) ≤ 4 * L ^ 6 / (n : ℝ) := by
      rw [div_le_div_iff₀ hM_pos_R hnpos]
      have h4L : (n : ℝ) ≤ 4 * L * (M : ℝ) := by
        linarith only [(div_le_iff₀ (by positivity : 0 < 4 * L)).1 hM_ge_4L]
      nlinarith only [h4L, pow_pos hLpos 5]
    have heq : 4 * Real.sqrt (2 * (M' : ℝ) * M) / ((M : ℝ) / L ^ 5) =
        4 * Real.sqrt (2 * (M' : ℝ) * M) * (L ^ 5 / (M : ℝ)) := by field_simp
    rw [heq]
    calc 4 * Real.sqrt (2 * (M' : ℝ) * M) * (L ^ 5 / (M : ℝ))
        ≤ 4 * (((n : ℝ) / L) * Real.sqrt n) * (4 * L ^ 6 / (n : ℝ)) := by gcongr
      _ = 16 * Real.sqrt n * L ^ 5 := by field_simp; ring
  have hK_small : 16 * Real.sqrt n * L ^ 5 ≤ (n : ℝ) / (200000 * L ^ 6) := by
    have h1 : (16 * Real.sqrt n * L ^ 5) ^ 2 ≤ ((n : ℝ) / (200000 * L ^ 6)) ^ 2 := by
      have hsq1 : (16 * Real.sqrt n * L ^ 5) ^ 2 = 256 * (n : ℝ) * L ^ 10 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hnpos.le]; ring
      have hsq2 : ((n : ℝ) / (200000 * L ^ 6)) ^ 2 = (n : ℝ) ^ 2 / (40000000000 * L ^ 12) := by ring
      rw [hsq1, hsq2, le_div_iff₀ (by positivity)]
      have heq : 256 * (n : ℝ) * L ^ 10 * (40000000000 * L ^ 12) =
          10240000000000 * L ^ 22 * (n : ℝ) := by ring
      rw [heq]
      have h_bd : 10240000000000 * L ^ 22 ≤ (n : ℝ) := by
        linarith only [hL22, pow_nonneg hLpos.le 22]
      rw [show (n : ℝ) ^ 2 = (n : ℝ) * (n : ℝ) by ring]
      exact mul_le_mul_of_nonneg_right h_bd hnpos.le
    exact le_of_sq_le_sq h1 (by positivity)
  have hV_adj : 9 * (M : ℝ) ^ 2 ≤ 16 * (
      (p * ∑ b ∈ B, (b : ℝ) ^ 2) / 2 -
      (4 * Real.sqrt (2 * (M' : ℝ) * M) / ((M : ℝ) / L ^ 5)) * (M : ℝ) ^ 2) := by
    have h1 : (4 * Real.sqrt (2 * (M' : ℝ) * M) / ((M : ℝ) / L ^ 5)) * (M : ℝ) ^ 2 ≤
        ((n : ℝ) / (200000 * L ^ 6)) * (M : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (hK_bd_ub.trans hK_small) (sq_nonneg _)
    have h2 : (M : ℝ) ^ 2 * (n : ℝ) / (2560 * L ^ 6) / 2 - ((n : ℝ) / (200000 * L ^ 6)) * (M : ℝ) ^ 2 =
        ((n : ℝ) / L ^ 6 * (1 / 5120 - 1 / 200000)) * (M : ℝ) ^ 2 := by ring
    have h3 : 9 ≤ ((n : ℝ) / L ^ 6 * (1 / 5120 - 1 / 200000)) * 16 := by
      have hL6 : L ^ 6 ≤ L ^ 22 := pow_le_pow_right₀ (by linarith only [hL1000]) (by omega)
      have hn_L6 : 1000000 * L ^ 6 ≤ (n : ℝ) := by nlinarith only [hL6, hL22]
      have hdiv : 1000000 ≤ (n : ℝ) / L ^ 6 := (le_div_iff₀ (by positivity)).2 hn_L6
      linarith only [hdiv]
    have h4 : 9 * (M : ℝ) ^ 2 ≤ (((n : ℝ) / L ^ 6 * (1 / 5120 - 1 / 200000)) * 16) * (M : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
    linarith only [hmu2_lb, h1, h2, h4]
  have h1me_half : (1 / 2 : ℝ) ≤ 1 - Real.exp (-1) := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
    have hmul := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-1 : ℝ)).le
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at hmul
    linarith only [hmul]
  set α : ℝ := (1 / 2 : ℝ) * (1 - Real.exp (-1)) * p * (T * (3 / (400 * L)) ^ 2)
  have halpha_ge : 2 * c_win * (n : ℝ) / L ^ 7 ≤ α := by
    have h1 : (1 / 2 : ℝ) * (1 / 2 : ℝ) * (1 / (40 * L ^ 3)) *
        ((η * (n : ℝ) / (2 * L ^ 2)) * (3 / (400 * L)) ^ 2) ≤ α := by
      dsimp [α]
      gcongr
    have heq : (1 / 2 : ℝ) * (1 / 2 : ℝ) * (1 / (40 * L ^ 3)) *
        ((η * (n : ℝ) / (2 * L ^ 2)) * (3 / (400 * L)) ^ 2) =
        (9 * η / 51200000) * (n : ℝ) / L ^ 7 := by ring
    have hmul : 2 * c_win * (n : ℝ) / L ^ 7 ≤ (9 * η / 51200000) * (n : ℝ) / L ^ 7 := by gcongr
    linarith only [h1, heq, hmul]
  have hc_win_eq : (c_win / 2) * (n : ℝ) / L ^ 7 ≤
      (1 / 2 : ℝ) * (α - 2 * (M : ℝ) * (1 / L ^ 4) ^ 2) -
        (4 * Real.sqrt (2 * (M' : ℝ) * M) / ((M : ℝ) / L ^ 5)) / 4 := by
    have htail1 : 2 * (M : ℝ) * (1 / L ^ 4) ^ 2 ≤ (c_win / 2) * (n : ℝ) / L ^ 7 := by
      have h1 : 2 * (M : ℝ) * (1 / L ^ 4) ^ 2 ≤ 2 * (n : ℝ) / L ^ 8 := by
        have heq : 2 * (M : ℝ) * (1 / L ^ 4) ^ 2 = 2 * (M : ℝ) / L ^ 8 := by ring
        rw [heq]
        gcongr
      have h2 : 2 / L ≤ c_win / 2 := by
        rw [div_le_iff₀ hLpos]
        have hmul := mul_le_mul_of_nonneg_left hL4c hc_win_pos.le
        rw [mul_div_cancel₀ _ hc_win_pos.ne'] at hmul
        linarith only [hmul]
      calc 2 * (M : ℝ) * (1 / L ^ 4) ^ 2
          ≤ 2 * (n : ℝ) / L ^ 8 := h1
        _ = (2 / L) * ((n : ℝ) / L ^ 7) := by ring
        _ ≤ (c_win / 2) * ((n : ℝ) / L ^ 7) := by gcongr
        _ = (c_win / 2) * (n : ℝ) / L ^ 7 := by ring
    have htail2 : (4 * Real.sqrt (2 * (M' : ℝ) * M) / ((M : ℝ) / L ^ 5)) / 4 ≤
        (c_win / 4) * (n : ℝ) / L ^ 7 := by
      have h1 : 16 * Real.sqrt n * L ^ 5 ≤ c_win * (n : ℝ) / L ^ 7 := by
        have hsq : (16 * Real.sqrt n * L ^ 5) ^ 2 ≤ (c_win * (n : ℝ) / L ^ 7) ^ 2 := by
          have hsq1 : (16 * Real.sqrt n * L ^ 5) ^ 2 = 256 * (n : ℝ) * L ^ 10 := by
            rw [mul_pow, mul_pow, Real.sq_sqrt hnpos.le]; ring
          have hsq2 : (c_win * (n : ℝ) / L ^ 7) ^ 2 = c_win ^ 2 * (n : ℝ) ^ 2 / L ^ 14 := by ring
          rw [hsq1, hsq2, le_div_iff₀ (by positivity)]
          have heq : 256 * (n : ℝ) * L ^ 10 * L ^ 14 = 256 * L ^ 24 * (n : ℝ) := by ring
          rw [heq]
          have h256 : 256 * L ^ 24 ≤ c_win ^ 2 * (n : ℝ) := by
            have hmul : 4096 * L ^ 24 ≤ 4096 * ((c_win / 64) ^ 2 * (n : ℝ)) :=
              mul_le_mul_of_nonneg_left hL24 (by norm_num)
            have heq2 : 4096 * ((c_win / 64) ^ 2 * (n : ℝ)) = c_win ^ 2 * (n : ℝ) := by ring
            linarith only [hmul, heq2, pow_nonneg hLpos.le 24]
          rw [show c_win ^ 2 * (n : ℝ) ^ 2 = c_win ^ 2 * (n : ℝ) * (n : ℝ) by ring]
          exact mul_le_mul_of_nonneg_right h256 hnpos.le
        exact le_of_sq_le_sq hsq (by positivity)
      have heq_div : (c_win / 4) * (n : ℝ) / L ^ 7 = (c_win * (n : ℝ) / L ^ 7) / 4 := by ring
      linarith only [h1, hK_bd_ub, heq_div]
    have hsplit_c : (c_win / 2) * (n : ℝ) / L ^ 7 =
        (1 / 2 : ℝ) * (2 * c_win * (n : ℝ) / L ^ 7) -
        (1 / 2 : ℝ) * ((c_win / 2) * (n : ℝ) / L ^ 7) -
        (c_win / 4) * (n : ℝ) / L ^ 7 := by ring
    linarith only [halpha_ge, htail1, htail2, hsplit_c]
  have hexp_decay : Real.exp (-c_win * (n : ℝ) / L ^ 7) ≤ ((n : ℝ) ^ 1000)⁻¹ := by
    have hL7 : L ^ 7 ≤ (c_win / 10) * Real.sqrt n := by
      have hsq : (L ^ 7) ^ 2 ≤ ((c_win / 10) * Real.sqrt n) ^ 2 := by
        rw [← pow_mul, mul_pow, Real.sq_sqrt hnpos.le]
        simpa using hL14
      exact le_of_sq_le_sq hsq (by positivity)
    have hsqrt_ge : 100 * L ≤ Real.sqrt n := by
      have hsq : (100 * L) ^ 2 ≤ (Real.sqrt n) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hnpos.le]
        nlinarith only [hL2]
      exact le_of_sq_le_sq hsq (by positivity)
    have hmain : 1000 * L ≤ c_win * (n : ℝ) / L ^ 7 := by
      have hmul : (10 * Real.sqrt n) * L ^ 7 ≤ c_win * (n : ℝ) := by
        have h1 := mul_le_mul_of_nonneg_left hL7 (by positivity : 0 ≤ 10 * Real.sqrt n)
        have heq : 10 * Real.sqrt n * (c_win / 10 * Real.sqrt n) = c_win * (Real.sqrt n) ^ 2 := by ring
        rw [heq, Real.sq_sqrt hnpos.le] at h1
        exact h1
      rw [le_div_iff₀ (by positivity)]
      have h1000 : 1000 * L * L ^ 7 ≤ 10 * Real.sqrt n * L ^ 7 := by
        have h1 : 1000 * L ≤ 10 * Real.sqrt n := by linarith only [hsqrt_ge]
        exact mul_le_mul_of_nonneg_right h1 (by positivity)
      linarith only [hmul, h1000]
    calc Real.exp (-c_win * (n : ℝ) / L ^ 7)
        ≤ Real.exp (-((1000 : ℕ) : ℝ) * L) := by
          apply Real.exp_le_exp.2
          have hneg : -c_win * (n : ℝ) / L ^ 7 = -(c_win * (n : ℝ) / L ^ 7) := by ring
          have hneg2 : -((1000 : ℕ) : ℝ) * L = -(1000 * L) := by push_cast; ring
          rw [hneg, hneg2]
          linarith only [hmain]
      _ = (Real.exp ((1000 : ℕ) * Real.log n))⁻¹ := by
          rw [neg_mul, Real.exp_neg, hL_eq]
      _ = ((n : ℝ) ^ 1000)⁻¹ := by
          rw [Real.exp_nat_mul, Real.exp_log hnpos]
  have hnet_small : ((M : ℝ) * L ^ 4 + 1) * Real.exp (-α) < 1 / 4 := by
    have hexp_a : Real.exp (-α) ≤ ((n : ℝ) ^ 1000)⁻¹ := by
      have hle : Real.exp (-α) ≤ Real.exp (-c_win * (n : ℝ) / L ^ 7) := by
        apply Real.exp_le_exp.2
        have hneg : -c_win * (n : ℝ) / L ^ 7 = -(c_win * (n : ℝ) / L ^ 7) := by ring
        have hpos_cw : 0 ≤ c_win * (n : ℝ) / L ^ 7 := by positivity
        have h2c : 2 * c_win * (n : ℝ) / L ^ 7 = 2 * (c_win * (n : ℝ) / L ^ 7) := by ring
        rw [hneg]
        linarith only [halpha_ge, hpos_cw, h2c]
      exact hle.trans hexp_decay
    have hpoly : (M : ℝ) * L ^ 4 + 1 ≤ 2 * (n : ℝ) ^ 5 := by
      have hL4 : L ^ 4 ≤ n := by
        have hpow : L ^ 4 ≤ L ^ 22 := pow_le_pow_right₀ (by linarith only [hL1000]) (by omega)
        linarith only [hpow, hL22, show (0 : ℝ) ≤ n by positivity]
      have h1 : (M : ℝ) * L ^ 4 ≤ (n : ℝ) * (n : ℝ) := mul_le_mul hM_le_n hL4 (by positivity) hnpos.le
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
      have h1n : (1 : ℝ) ≤ (n : ℝ) ^ 5 := one_le_pow₀ hn1
      have hn25 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 5 := pow_le_pow_right₀ hn1 (by omega)
      have hsq : (n : ℝ) * (n : ℝ) = (n : ℝ) ^ 2 := by ring
      linarith only [h1, h1n, hn25, hsq]
    have hpow : 2 * (n : ℝ) ^ 5 * ((n : ℝ) ^ 1000)⁻¹ < 1 / 4 := by
      have heq : 2 * (n : ℝ) ^ 5 * ((n : ℝ) ^ 1000)⁻¹ = 2 / (n : ℝ) ^ 995 := by
        have h1000 : (n : ℝ) ^ 1000 = (n : ℝ) ^ 5 * (n : ℝ) ^ 995 := by ring
        rw [h1000, div_eq_mul_inv]
        field_simp
      rw [heq, div_lt_iff₀ (by positivity)]
      have hn995 : (100000 : ℝ) ≤ (n : ℝ) ^ 995 := by
        have h1 : (100000 : ℝ) ≤ n := by exact_mod_cast hn_big
        have h2 : (n : ℝ) ≤ (n : ℝ) ^ 995 := le_self_pow₀ (by linarith only [h1]) (by omega)
        linarith only [h1, h2]
      linarith only [hn995]
    have hmul : ((M : ℝ) * L ^ 4 + 1) * Real.exp (-α) ≤ 2 * (n : ℝ) ^ 5 * ((n : ℝ) ^ 1000)⁻¹ :=
      mul_le_mul hpoly hexp_a (Real.exp_pos _).le (by positivity)
    linarith only [hmul, hpow]
  have harc_win : Real.exp (-2 * (
      (1 / 2 : ℝ) * (α - 2 * (M : ℝ) * (1 / L ^ 4) ^ 2) -
      (4 * Real.sqrt (2 * (M' : ℝ) * M) / ((M : ℝ) / L ^ 5)) / 4)) <
      1 / (8 * Real.sqrt ((M : ℝ) ^ 3)) := by
    have hexp_2a : Real.exp (-2 * (
        (1 / 2 : ℝ) * (α - 2 * (M : ℝ) * (1 / L ^ 4) ^ 2) -
        (4 * Real.sqrt (2 * (M' : ℝ) * M) / ((M : ℝ) / L ^ 5)) / 4)) ≤ ((n : ℝ) ^ 1000)⁻¹ := by
      have hle : Real.exp (-2 * (
          (1 / 2 : ℝ) * (α - 2 * (M : ℝ) * (1 / L ^ 4) ^ 2) -
          (4 * Real.sqrt (2 * (M' : ℝ) * M) / ((M : ℝ) / L ^ 5)) / 4)) ≤
          Real.exp (-c_win * (n : ℝ) / L ^ 7) := by
        apply Real.exp_le_exp.2
        have hneg : -c_win * (n : ℝ) / L ^ 7 = -2 * ((c_win / 2) * (n : ℝ) / L ^ 7) := by ring
        rw [hneg]
        linarith only [hc_win_eq]
      exact hle.trans hexp_decay
    have hsqrt_M3 : Real.sqrt ((M : ℝ) ^ 3) ≤ (n : ℝ) ^ 2 := by
      have h1 : (M : ℝ) ^ 3 ≤ ((n : ℝ) ^ 2) ^ 2 := by
        have hM3 : (M : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 := pow_le_pow_left₀ hM_pos_R.le hM_le_n 3
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
        have hn34 : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 4 := pow_le_pow_right₀ hn1 (by omega)
        have h4 : (n : ℝ) ^ 4 = ((n : ℝ) ^ 2) ^ 2 := by ring
        linarith only [hM3, hn34, h4]
      calc Real.sqrt ((M : ℝ) ^ 3)
          ≤ Real.sqrt (((n : ℝ) ^ 2) ^ 2) := Real.sqrt_le_sqrt h1
        _ = (n : ℝ) ^ 2 := Real.sqrt_sq (sq_nonneg _)
    have hcmp : ((n : ℝ) ^ 1000)⁻¹ < 1 / (8 * (n : ℝ) ^ 2) := by
      rw [← one_div, one_div_lt_one_div (by positivity) (by positivity)]
      have hn998 : (8 : ℝ) < (n : ℝ) ^ 998 := by
        have h1 : (100000 : ℝ) ≤ n := by exact_mod_cast hn_big
        have h2 : (n : ℝ) ≤ (n : ℝ) ^ 998 := le_self_pow₀ (by linarith only [h1]) (by omega)
        linarith only [h1, h2]
      have h1000 : (n : ℝ) ^ 1000 = (n : ℝ) ^ 2 * (n : ℝ) ^ 998 := by ring
      rw [h1000]
      nlinarith only [hn998, sq_pos_of_pos hnpos]
    have hdiv_le : 1 / (8 * (n : ℝ) ^ 2) ≤ 1 / (8 * Real.sqrt ((M : ℝ) ^ 3)) := by
      rw [one_div_le_one_div (by positivity) (by positivity)]
      linarith only [hsqrt_M3]
    linarith only [hexp_2a, hcmp, hdiv_le]
  exact exists_subset_sum_of_reduced B M M' hM_ge1 hM'_ge1
    (by linarith only [hL1000]) hB_sub hB_lb_M hT_pos hT_le_B hB_nondiv hM'_lt hM'_hi hB_sum_hi
    hmu2_big hnet_small hV_adj harc_win

lemma exists_m_subset_sum_eventually
    (h_psi : Asymptotics.IsEquivalent atTop Chebyshev.psi (fun x : ℝ => x))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ m : ℕ, 1 ≤ m ∧
      ∀ S ⊆ Finset.Icc 1 n, (1 / 2 + ε) * ((n : ℝ) / Real.log n) < (S.card : ℝ) →
        ∃ A ⊆ S, ∑ a ∈ A, a = m := by
  let ε' : ℝ := min ε 1
  have hε'pos : 0 < ε' := lt_min hε zero_lt_one
  have hε'le1 : ε' ≤ 1 := min_le_right _ _
  have hε'le : ε' ≤ ε := min_le_left _ _
  let δ : ℝ := ε' / 16
  let η : ℝ := ε' / 16
  have hδpos : 0 < δ := by positivity
  have hδle : δ ≤ 1 / 16 := by dsimp [δ]; linarith
  have hηpos : 0 < η := by positivity
  have hηle : η ≤ 1 / 16 := by dsimp [η]; linarith
  let c_win : ℝ := 9 * η / 200000000
  have hc_win_pos : 0 < c_win := by positivity
  have h_log_big : ∀ᶠ n : ℕ in atTop, max 1000 (4 / c_win) ≤ Real.log n := by
    have ht := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact ht.eventually (eventually_ge_atTop _)
  have h_log_24 : ∀ᶠ n : ℕ in atTop, (Real.log n) ^ 24 ≤ (c_win / 64) ^ 2 * (n : ℝ) :=
    eventually_pow_log_lt_mul_nat 24 (by positivity)
  have h_log_22 : ∀ᶠ n : ℕ in atTop, (Real.log n) ^ 22 ≤ (1 / 100000000000000 : ℝ) * (n : ℝ) :=
    eventually_pow_log_lt_mul_nat 22 (by norm_num)
  have h_log_14 : ∀ᶠ n : ℕ in atTop, (Real.log n) ^ 14 ≤ (c_win / 10) ^ 2 * (n : ℝ) :=
    eventually_pow_log_lt_mul_nat 14 (by positivity)
  have h_log_2 : ∀ᶠ n : ℕ in atTop, (Real.log n) ^ 2 ≤ (1 / 10000 : ℝ) * (n : ℝ) :=
    eventually_pow_log_lt_mul_nat 2 (by norm_num)
  filter_upwards [eventually_ge_atTop 100000, exists_s_m_eventually h_psi hδpos hδle,
    h_log_big, h_log_24, h_log_22, h_log_14, h_log_2]
    with n hn_big ⟨s, m, hs_pos, hm_pos, hs_ub, hs_lb, hm_ub, hm_lb, hdvd_m⟩
      hL_big hL24 hL22 hL14 hL2
  let L : ℝ := Real.log n
  have hL1000 : 1000 ≤ L := le_trans (le_max_left _ _) hL_big
  have hLpos : 0 < L := by linarith
  have hL4c : 4 / c_win ≤ L := le_trans (le_max_right _ _) hL_big
  have hnpos : (0 : ℝ) < n := by positivity
  refine ⟨m, hm_pos, fun S hS hS_card => ?_⟩
  let T : ℝ := η * (S.card : ℝ) / L
  have hS_pos_R : (0 : ℝ) < S.card := by
    have : 0 < (1 / 2 + ε) * ((n : ℝ) / L) := by positivity
    linarith
  have hT_pos : 0 < T := by positivity
  have hlog2_ub : (Nat.log 2 n : ℝ) ≤ 2 * L := by
    have h2pow : (2 : ℝ) ^ (Nat.log 2 n : ℝ) ≤ n := by
      have hnat : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
      exact_mod_cast hnat
    have hlog_pow : (Nat.log 2 n : ℝ) * Real.log 2 ≤ L := by
      have := Real.log_le_log (by positivity) h2pow
      rwa [Real.log_rpow (by norm_num)] at this
    have hhalf := one_half_le_log_two
    nlinarith
  have hS_card_T : ((Nat.log 2 n + 1 : ℕ) : ℝ) * T < S.card := by
    push_cast
    have h3L : (Nat.log 2 n : ℝ) + 1 ≤ 3 * L := by linarith
    have h1 : ((Nat.log 2 n : ℝ) + 1) * T ≤ (3 * L) * (η * (S.card : ℝ) / L) :=
      mul_le_mul_of_nonneg_right h3L hT_pos.le
    have h2 : (3 * L) * (η * (S.card : ℝ) / L) = 3 * η * (S.card : ℝ) := by field_simp
    have h3eta : 3 * η * (S.card : ℝ) < (S.card : ℝ) := by nlinarith
    linarith
  have hB_lb_T : (n : ℝ) / (s + 1 : ℝ) < (S.card : ℝ) - (Nat.log 2 n : ℝ) * T := by
    have h1 : (Nat.log 2 n : ℝ) * T ≤ (2 * L) * (η * (S.card : ℝ) / L) :=
      mul_le_mul_of_nonneg_right hlog2_ub hT_pos.le
    have h2 : (2 * L) * (η * (S.card : ℝ) / L) = 2 * η * (S.card : ℝ) := by field_simp
    have hS_sub : (1 - 2 * η) * (S.card : ℝ) ≤ (S.card : ℝ) - (Nat.log 2 n : ℝ) * T := by linarith
    have hS_low : (1 / 2 + ε') * ((n : ℝ) / L) < (S.card : ℝ) := by
      have : (1 / 2 + ε') * ((n : ℝ) / L) ≤ (1 / 2 + ε) * ((n : ℝ) / L) := by gcongr
      linarith
    have h12 : (1 - 2 * η) * ((1 / 2 + ε') * ((n : ℝ) / L)) < (1 - 2 * η) * (S.card : ℝ) :=
      mul_lt_mul_of_pos_left hS_low (by linarith)
    have hs_inv : (n : ℝ) / (s + 1 : ℝ) ≤ (n : ℝ) / ((2 - 2 * δ) * L) :=
      div_le_div_of_nonneg_left hnpos.le (by nlinarith) hs_lb
    have hcoef : 1 / (2 - 2 * δ) < (1 - 2 * η) * (1 / 2 + ε') := by
      rw [div_lt_iff₀ (by linarith only [hδle])]
      have hpol : (1 - 2 * η) * (1 / 2 + ε') * (2 - 2 * δ) =
          1 + (29 / 16 : ℝ) * ε' - (47 / 128 : ℝ) * ε' ^ 2 + (1 / 64 : ℝ) * ε' ^ 3 := by
        dsimp [η, δ]; ring
      nlinarith only [hε'pos, hε'le1, hpol]
    have hcmp : (n : ℝ) / ((2 - 2 * δ) * L) < (1 - 2 * η) * ((1 / 2 + ε') * ((n : ℝ) / L)) := by
      have hL_eq : (n : ℝ) / ((2 - 2 * δ) * L) = (1 / (2 - 2 * δ)) * ((n : ℝ) / L) := by
        field_simp
      have hR_eq : (1 - 2 * η) * ((1 / 2 + ε') * ((n : ℝ) / L)) =
          ((1 - 2 * η) * (1 / 2 + ε')) * ((n : ℝ) / L) := by ring
      rw [hL_eq, hR_eq]
      exact mul_lt_mul_of_pos_right hcoef (by positivity)
    linarith
  obtain ⟨d, B, hd1, hds, hB_sub, hBS, hB_card, hB_nondiv⟩ :=
    divisor_extract_aux n s S hS T hT_pos hS_card_T hB_lb_T 0 1 S
      le_rfl (by omega) (by norm_num) (by simpa using hS) (fun _ hb => by simpa using hb) (by simp)
  have hd_dvd_m : d ∣ m := hdvd_m d hd1 hds
  have hB_card_ge : (1 / 2 : ℝ) * ((n : ℝ) / L) ≤ (B.card : ℝ) := by
    have hS_sub : (1 - 2 * η) * (S.card : ℝ) ≤ (B.card : ℝ) := by
      have h1 : (Nat.log 2 n : ℝ) * T ≤ 2 * η * (S.card : ℝ) := by
        calc (Nat.log 2 n : ℝ) * T ≤ (2 * L) * (η * (S.card : ℝ) / L) :=
              mul_le_mul_of_nonneg_right hlog2_ub hT_pos.le
          _ = 2 * η * (S.card : ℝ) := by field_simp
      linarith
    have h1 : (1 / 2 : ℝ) ≤ (1 - 2 * η) * (1 / 2 + ε') := by
      have hpol : (1 - 2 * η) * (1 / 2 + ε') = 1 / 2 + (15 / 16 : ℝ) * ε' - (1 / 8 : ℝ) * ε' ^ 2 := by
        dsimp [η]; ring
      nlinarith only [hε'pos, hε'le1, hpol]
    have hS_low : (1 / 2 + ε') * ((n : ℝ) / L) ≤ (S.card : ℝ) := by
      have hle : (1 / 2 + ε') * ((n : ℝ) / L) ≤ (1 / 2 + ε) * ((n : ℝ) / L) :=
        mul_le_mul_of_nonneg_right (by linarith only [hε'le]) (by positivity)
      linarith only [hS_card, hle]
    have hlow1 : (1 / 2 : ℝ) * ((n : ℝ) / L) ≤ (1 - 2 * η) * (1 / 2 + ε') * ((n : ℝ) / L) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have hlow2 : (1 - 2 * η) * (1 / 2 + ε') * ((n : ℝ) / L) ≤ (1 - 2 * η) * (S.card : ℝ) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hS_low (by linarith only [hηle])
    linarith only [hS_sub, hlow1, hlow2]
  have hd_le_3L : (d : ℝ) ≤ 3 * L := by
    have : (d : ℝ) ≤ s := by exact_mod_cast hds
    have : δ * L ≤ (1 / 16 : ℝ) * L := mul_le_mul_of_nonneg_right hδle hLpos.le
    linarith
  have hT_le_B : T ≤ (2 / 5 : ℝ) * (B.card : ℝ) := by
    have h1 : (7 / 8 : ℝ) * (S.card : ℝ) ≤ (B.card : ℝ) := by
      have h2 : (Nat.log 2 n : ℝ) * T ≤ 2 * η * (S.card : ℝ) := by
        calc (Nat.log 2 n : ℝ) * T ≤ (2 * L) * (η * (S.card : ℝ) / L) :=
              mul_le_mul_of_nonneg_right hlog2_ub hT_pos.le
          _ = 2 * η * (S.card : ℝ) := by field_simp
      linarith only [hB_card, h2, hηle, hS_pos_R,
        show 2 * η * (S.card : ℝ) ≤ (1 / 8 : ℝ) * (S.card : ℝ) by
          exact mul_le_mul_of_nonneg_right (by linarith only [hηle]) hS_pos_R.le]
    have h2 : T ≤ (1 / 16000 : ℝ) * (S.card : ℝ) := by
      dsimp [T]
      have hηL : η / L ≤ 1 / 16000 := by
        rw [div_le_iff₀ hLpos]
        nlinarith only [hηle, hL1000]
      exact (show η * (S.card : ℝ) / L = (η / L) * (S.card : ℝ) by ring).symm ▸
        mul_le_mul_of_nonneg_right hηL hS_pos_R.le
    linarith only [h1, h2, hS_pos_R]
  have hT_ge_eta : η * (n : ℝ) / (2 * L ^ 2) ≤ T := by
    dsimp [T]
    have hS_low : (1 / 2 : ℝ) * ((n : ℝ) / L) ≤ (S.card : ℝ) := by
      have hle : (1 / 2 : ℝ) * ((n : ℝ) / L) ≤ (1 / 2 + ε) * ((n : ℝ) / L) :=
        mul_le_mul_of_nonneg_right (by linarith only [hε]) (by positivity)
      linarith only [hle, hS_card]
    calc η * (n : ℝ) / (2 * L ^ 2) = η * ((1 / 2 : ℝ) * ((n : ℝ) / L)) / L := by ring
      _ ≤ η * (S.card : ℝ) / L := by gcongr
  have hc_win_def : 2 * c_win ≤ 9 * η / 51200000 := by
    dsimp [c_win]
    linarith only [hηpos]
  obtain ⟨A', hA'B, hA'_sum⟩ := exists_subset_sum_from_B n m d B L T η c_win
    hn_big hm_pos hd1 hd_dvd_m rfl hL1000 hL4c hc_win_pos hc_win_def hηpos hT_pos
    hL24 hL22 hL14 hL2 hm_ub hm_lb hd_le_3L hB_sub hB_card_ge hT_le_B hT_ge_eta
    (fun q hq => (hB_nondiv q hq).le)
  refine ⟨A'.image (fun b => d * b), ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨b, hb, rfl⟩ := hx
    exact hBS b (hA'B hb)
  · rw [Finset.sum_image]
    · calc ∑ b ∈ A', d * b = d * ∑ b ∈ A', b := (Finset.mul_sum _ _ _).symm
        _ = d * (m / d) := by rw [hA'_sum]
        _ = m := Nat.mul_div_cancel' hd_dvd_m
    · intro x _ y _ hxy
      exact Nat.eq_of_mul_eq_mul_left hd1 hxy

lemma alon_freiman_from_psi
    (h_psi : Asymptotics.IsEquivalent atTop Chebyshev.psi (fun x : ℝ => x)) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, (Erdos771.f n : ℝ) ≤ (1 / 2 + ε) * ((n : ℝ) / Real.log n) := by
  intro ε hε
  filter_upwards [exists_m_subset_sum_eventually h_psi hε, eventually_ge_atTop 2]
    with n ⟨m, hm1, hm_prop⟩ hn2
  have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn2)
  have h_le : ∀ k : ℕ, Erdos771.IsAdmissible n k →
      (k : ℝ) ≤ (1 / 2 + ε) * ((n : ℝ) / Real.log n) := by
    intro k hk
    by_contra hgt
    push Not at hgt
    obtain ⟨S, hS, hS_card, hS_avoid⟩ := hk m hm1
    rw [← hS_card] at hgt
    obtain ⟨A, hA_sub, hA_sum⟩ := hm_prop S hS hgt
    exact hS_avoid A hA_sub hA_sum
  have hf_le : Erdos771.f n ≤ ⌊(1 / 2 + ε) * ((n : ℝ) / Real.log n)⌋₊ := by
    dsimp [Erdos771.f]
    apply csSup_le ⟨0, Erdos771.isAdmissible_zero n⟩
    intro k hk
    exact Nat.le_floor (h_le k hk)
  exact ((Nat.cast_le (α := ℝ)).2 hf_le).trans (Nat.floor_le (by positivity))

end OMA.AlonFreiman

end OMA_AlonFreiman

theorem OMA.solution :
    type_of% @Erdos771.erdos_771.variants.alon_freiman_upper :=
  OMA.AlonFreiman.alon_freiman_from_psi WeakPNT''
