import FormalConjectures.Wikipedia.DirichletDivisorProblem
import Mathlib
/-
Ported from an existing public Lean proof; the mathematics and the Lean proof are the original author's.
Original: https://github.com/ChironTheCentaur/rh-lab-divisor-problem/blob/80d65168002a5c5903c5808f619f23f21a21f632/HardyOmegaFC/DivisorHardy.lean  (theorem DirichletDivisorProblem.divisor_error_hardy)
Original author: Sky (GitHub: ChironTheCentaur)   Licence: Apache-2.0 (LICENSE; LICENSE.zeta23 for the Zeta23/ subset)
Submitted to lefttosolve.com by @senamakel; ported to Lean v4.33.1 / formal-conjectures 9097e2f.
Changes: flattened the import closure of HardyOmegaFC/DivisorHardy.lean (HardyOmegaFC/, LeanClassics/,
Zeta23/FromPNTPlus/) into one file and pruned every declaration the final theorem does not depend on;
HardyOmegaFC/LeanClassics code sits in namespace OMAPort_Divisor, the Zeta23/FromPNTPlus code (which
extends Mathlib namespaces) at the root as in the original; dropped the copied FC definitions
(Divisor.lean) in favour of formal-conjectures' own divisorSummatory and divisorError (identical text);
replaced the notations ζ, ζ', ζ₀, Λ, σ and the ArithmeticFunction.zeta notation by the terms they denote;
removed set_option lang.lemmaCmd, one set_option backward.isDefEq.respectTransparency, the module
keywords and one @[fun_prop] attribute (its single use is
now explicit); for the pinned Mathlib: if_neg in place of ite_eq_right, and two `convert _ using 1`
steps replaced by HasDerivAt.congr_deriv / congr_of_eventuallyEq and an explicit rewrite.
-/
/-
NOTICE (from the original package):
HardyDivisorOmega (standalone package), Copyright 2026 Sky (GitHub: ChironTheCentaur).
The original work in this package (HardyOmegaFC/, LeanClassics/, ...) is licensed under the Apache
License, Version 2.0. The definitions divisorSummatory, divisorError and the statement of
divisor_error_hardy are from google-deepmind/formal-conjectures
(FormalConjectures/Wikipedia/DirichletDivisorProblem.lean), Copyright The Formal Conjectures Authors,
licensed under the Apache License, Version 2.0.
Zeta23/ is a subset of zeta-23-lean, Copyright 2026 Anthropic, PBC, licensed under the Apache License,
Version 2.0 (LICENSE.zeta23, NOTICE.zeta23), as ported to Lean v4.35.0 / Mathlib 56a005855ea1. It is not
relicensed. NOTICE.zeta23: This product includes software derived from PrimeNumberTheoremAnd
(https://github.com/AlexKontorovich/PrimeNumberTheoremAnd), Copyright the PrimeNumberTheoremAnd
contributors, licensed under the Apache License, Version 2.0. The derived files are the ones under
Zeta23/FromPNTPlus/; each carries its upstream notice, reproduced below at the start of its section.
Some of those files in turn derive from mathlib, Copyright the mathlib contributors, Apache License,
Version 2.0; their original headers are preserved.
Licensed under the Apache License, Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0); distributed
on an AS IS basis, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND. This file is a modified version.
-/

namespace OMAPort_Divisor

open DirichletDivisorProblem

-- ===== from LeanClassics.ZetaMeanSquare =====
section

/-!
# For `σ > 1`, `(1/T) ∫_0^T |ζ(σ + it)|² dt → ζ(2σ)`

`tendsto_mean_sq_zeta`: for `σ > 1`, `(1/T) ∫_0^T |ζ(σ + it)|² dt → |ζ(2σ)|` as `T → ∞`.

`tendsto_mean_sq` is the general statement it comes from: if `∑ |a_n| < ∞`, the real frequencies
`λ_n` are distinct and `F(t) = ∑ a_n e^{i λ_n t}` is continuous, then
`(1/T) ∫_0^T |F(t)|² dt → ∑ |a_n|²`.

Proof. For a finite sum, expanding `|F|²` leaves the diagonal `T ∑ |a_n|²` plus cross terms
`a_m ā_n ∫_0^T e^{i(λ_m − λ_n)t} dt`, each at most `2|a_m||a_n|/|λ_m − λ_n|` (`finite_mean`). The
tail beyond `N` is uniformly at most `∑_{n ≥ N} |a_n|`. For `ζ`, `a_n = (n + 1)^{−σ}` and
`λ_n = −log(n + 1)`.
-/

open Complex Real Set Filter Topology

noncomputable section

namespace LeanClassics.ZetaMeanSquare

lemma norm_integral_exp_le {c : ℝ} (hc : c ≠ 0) (T : ℝ) :
    ‖∫ t in (0 : ℝ)..T, cexp ((c : ℂ) * t * I)‖ ≤ 2 / |c| := by
  have hcI : (c : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hc) I_ne_zero
  have e : (fun t : ℝ => cexp ((c : ℂ) * t * I)) = fun t : ℝ => cexp ((c : ℂ) * I * t) := by
    funext t; ring_nf
  rw [e, integral_exp_mul_complex hcI, norm_div]
  have h1 : ‖cexp ((c : ℂ) * I * T)‖ = 1 := by
    rw [show (c : ℂ) * I * T = ((c * T : ℝ) : ℂ) * I by push_cast; ring]
    exact norm_exp_ofReal_mul_I _
  have h2 : ‖(c : ℂ) * I‖ = |c| := by simp
  rw [h2]
  apply div_le_div_of_nonneg_right _ (abs_nonneg c)
  calc ‖cexp ((c : ℂ) * I * T) - cexp ((c : ℂ) * I * ((0 : ℝ) : ℂ))‖
      ≤ ‖cexp ((c : ℂ) * I * T)‖ + ‖cexp ((c : ℂ) * I * ((0 : ℝ) : ℂ))‖ := norm_sub_le _ _
    _ = 2 := by rw [h1]; simp; norm_num

lemma term_eq (n : ℕ) (σ t : ℝ) :
    1 / ((n : ℂ) + 1) ^ ((σ : ℂ) + t * I) =
      ((((n : ℝ) + 1) ^ (-σ) : ℝ) : ℂ) * cexp (((-Real.log ((n : ℝ) + 1) : ℝ) : ℂ) * t * I) := by
  have hx : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hc : (n : ℂ) + 1 = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [one_div, ← cpow_neg, hc, cpow_def_of_ne_zero (by exact_mod_cast hx.ne'),
    Real.rpow_def_of_pos hx, Complex.ofReal_exp, ← Complex.exp_add,
    ← Complex.ofReal_log hx.le]
  congr 1
  push_cast; ring

end LeanClassics.ZetaMeanSquare
end

end
-- ===== end LeanClassics.ZetaMeanSquare =====

-- ===== from LeanClassics.ZetaFourthMoment =====
section

/-!
# For `σ > 1`, `(1/T) ∫_0^T |ζ(σ + it)|⁴ dt → ζ(2σ)⁴/ζ(4σ)`

`tendsto_mean_fourth_zeta`: for `σ > 1`,
`(1/T) ∫_0^T |ζ(σ + it)|⁴ dt → ∑_{n ≥ 1} d(n)² n^{−2σ}` as `T → ∞`, where `d = σ₀` counts divisors;
`tendsto_mean_fourth_zeta'`: the limit is `|ζ(2σ)|⁴/|ζ(4σ)|`, by
`tsum_sigma_zero_sq`: `∑ d(n)² n^{−s} = ζ(s)⁴/ζ(2s)` for `Re s > 2` (only this range is proved
here).

Proof. `ζ(s)² = ∑ d(n) n^{−s}` for `Re s > 1` (`sq_zeta_eq`, from Mathlib's `LSeries_mul'` and
`zeta_mul_pow_eq_sigma`), then `ZetaMeanSquare.tendsto_mean_sq` with `a_n = d(n + 1)(n + 1)^{−σ}`,
`λ_n = −log(n + 1)`. For `tsum_sigma_zero_sq`, Mathlib's `EulerProduct.eulerProduct` with Euler
factor `∑_e (e + 1)² x^e = (1 + x)/(1 − x)³ = (1 − x²)/(1 − x)⁴`, `x = p^{−s}`, compared with
`riemannZeta_eulerProduct` at `s` and `2s`.
-/

open Complex Real Set Filter Topology ArithmeticFunction LSeries

noncomputable section

namespace LeanClassics.ZetaFourthMoment

open LeanClassics.ZetaMeanSquare (term_eq)

/-- `ζ(s)² = ∑ d(n) n^{−s}` for `Re s > 1`, with the series absolutely convergent. -/
lemma sq_zeta_eq {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => ((sigma 0 n : ℕ) : ℂ)) s = riemannZeta s ^ 2 ∧
      LSeriesSummable (fun n => ((sigma 0 n : ℕ) : ℂ)) s := by
  set Z : ArithmeticFunction ℂ := ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)
  have hZ : ⇑Z = fun n => ((ArithmeticFunction.zeta n : ℕ) : ℂ) := by funext n; simp [Z]
  have h1 : (fun n => ((sigma 0 n : ℕ) : ℂ)) = ⇑(Z * Z) := by
    rw [← zeta_mul_pow_eq_sigma, pow_zero_eq_zeta]
    funext n; simp only [Z, ← natCoe_mul, natCoe_apply]
  have hsZ : LSeriesSummable ⇑Z s := by rw [hZ]; exact LSeriesSummable_zeta_iff.mpr hs
  refine ⟨?_, ?_⟩
  · rw [h1, LSeries_mul' hsZ hsZ, hZ, LSeries_zeta_eq_riemannZeta hs, sq]
  · rw [h1]; exact LSeriesSummable_mul hsZ hsZ

end LeanClassics.ZetaFourthMoment
end

end
-- ===== end LeanClassics.ZetaFourthMoment =====

-- ===== from HardyOmegaFC.Mellin =====
section

/-!
# Rung D1, part 1: the Mellin transform of the divisor error on `Re s > 1`

`mellin_divisorError_of_one_lt`: for `Re s > 1`,
`∫_{x > 1} Δ(x) x^{−s−1} dx = ζ(s)²/s − 1/(s−1)² − (2γ−1)/(s−1)`, where `Δ = divisorError` (FC's definition).

Proof. Abel summation in Mathlib's form (`LSeries_eq_mul_integral_of_nonneg`) with `f = d = σ₀`, using
`ζ(s)² = Σ d(n) n^{−s}` (`LeanClassics.ZetaFourthMoment.sq_zeta_eq`) and the partial-sum bound
`Σ_{k ≤ n} d(k) ≤ ζ(r)² n^r` for every `r > 1` (`d(k) ≤ d(k) (n/k)^r`). The two elementary integrals are
`∫_{x>1} x · x^{−s−1} = 1/(s−1)` (`integral_Ioi_cpow_of_lt`) and `∫_{x>1} x log x · x^{−s−1} = 1/(s−1)²`
(fundamental theorem of calculus with `F(x) = −log x · x^{1−s}/(s−1) − x^{1−s}/(s−1)²`).
-/

open Filter Asymptotics Real Complex MeasureTheory Set Topology ArithmeticFunction LSeries

noncomputable section

namespace DirichletDivisorProblem.HardyD1

/-- The Mellin-type transform `G(s) = ∫_{x > 1} Δ(x) x^{−(s+1)} dx` of FC's divisor error. -/
def G (s : ℂ) : ℂ := ∫ x in Ioi (1 : ℝ), (divisorError x : ℂ) * (x : ℂ) ^ (-(s + 1))

/-- The polar part `1/(s−1)² + (2γ−1)/(s−1)` of `ζ(s)²/s` at `s = 1`. -/
def P (s : ℂ) : ℂ := 1 / (s - 1) ^ 2 + (2 * eulerMascheroniConstant - 1) / (s - 1)

lemma divisorSummatory_eq_sum (x : ℝ) :
    divisorSummatory x = ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.sigma 0 k : ℕ) : ℝ) := by
  simp only [divisorSummatory, sigma_zero_apply]

lemma measurable_divisorSummatory : Measurable divisorSummatory := by
  have : divisorSummatory = (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (k.divisors.card : ℝ)) ∘ Nat.floor := rfl
  rw [this]
  exact measurable_from_nat.comp Nat.measurable_floor

lemma measurable_divisorError : Measurable divisorError := by
  unfold divisorError
  exact (measurable_divisorSummatory.sub (measurable_id.mul Real.measurable_log)).sub
    (measurable_const.mul measurable_id)

/-- `Σ_{k ≤ n} d(k) ≤ C n^r` for `r > 1`. -/
lemma sum_sigma_zero_le {r : ℝ} (hr : 1 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, ((ArithmeticFunction.sigma 0 k : ℕ) : ℝ) ≤ C * (n : ℝ) ^ r := by
  set f : ℕ → ℂ := fun n => ((ArithmeticFunction.sigma 0 n : ℕ) : ℂ)
  have hS : Summable fun k => ‖term f (r : ℂ) k‖ :=
    (LeanClassics.ZetaFourthMoment.sq_zeta_eq (s := (r : ℂ)) (by simpa using hr)).2.norm
  refine ⟨∑' k, ‖term f (r : ℂ) k‖, tsum_nonneg fun _ => norm_nonneg _, fun n => ?_⟩
  have hk : ∀ k ∈ Finset.Icc 1 n,
      ((ArithmeticFunction.sigma 0 k : ℕ) : ℝ) ≤ (n : ℝ) ^ r * ‖term f (r : ℂ) k‖ := by
    intro k hk
    obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hk
    have hk0 : k ≠ 0 := by omega
    have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk0
    rw [norm_term_eq, if_neg hk0, Complex.ofReal_re]
    simp only [f, Complex.norm_natCast]
    rw [mul_div_assoc', le_div_iff₀ (Real.rpow_pos_of_pos hkpos r), mul_comm]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hkpos.le (Nat.cast_le.mpr hkn) (by linarith)) (Nat.cast_nonneg _)
  calc ∑ k ∈ Finset.Icc 1 n, ((ArithmeticFunction.sigma 0 k : ℕ) : ℝ)
      ≤ ∑ k ∈ Finset.Icc 1 n, (n : ℝ) ^ r * ‖term f (r : ℂ) k‖ := Finset.sum_le_sum hk
    _ = (n : ℝ) ^ r * ∑ k ∈ Finset.Icc 1 n, ‖term f (r : ℂ) k‖ := by rw [Finset.mul_sum]
    _ ≤ (n : ℝ) ^ r * ∑' k, ‖term f (r : ℂ) k‖ :=
        mul_le_mul_of_nonneg_left (hS.sum_le_tsum _ fun k _ => norm_nonneg _) (by positivity)
    _ = _ := mul_comm _ _

/-- Abel summation: `∫_{x>1} D(x) x^{−s−1} dx = ζ(s)²/s` for `Re s > 1`. -/
lemma integral_divisorSummatory {s : ℂ} (hs : 1 < s.re) :
    ∫ x in Ioi (1 : ℝ), (divisorSummatory x : ℂ) * (x : ℂ) ^ (-(s + 1)) = riemannZeta s ^ 2 / s := by
  set r : ℝ := (1 + s.re) / 2
  have hr1 : 1 < r := by simp only [r]; linarith
  have hrs : r < s.re := by simp only [r]; linarith
  obtain ⟨C, hC0, hC⟩ := sum_sigma_zero_le hr1
  have hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, ((ArithmeticFunction.sigma 0 k : ℕ) : ℝ)) =O[atTop] fun n ↦ (n : ℝ) ^ r := by
    refine IsBigO.of_bound C (Eventually.of_forall fun n => ?_)
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _),
      Real.norm_of_nonneg (by positivity)]
    exact hC n
  have h := LSeries_eq_mul_integral_of_nonneg (fun n => ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ)) (by linarith) hrs hO
    (fun n => Nat.cast_nonneg _)
  have hz := (LeanClassics.ZetaFourthMoment.sq_zeta_eq hs).1
  have hs0 : s ≠ 0 := fun h0 => by rw [h0] at hs; simp at hs; linarith
  simp only [Complex.ofReal_natCast] at h
  rw [hz] at h
  rw [h, mul_div_cancel_left₀ _ hs0]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  simp only [divisorSummatory_eq_sum]
  push_cast
  rfl

lemma cpow_mul_self {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (x : ℂ) * (x : ℂ) ^ (-(s + 1)) = (x : ℂ) ^ (-s) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  conv_lhs => arg 1; rw [← Complex.cpow_one (x : ℂ)]
  rw [← Complex.cpow_add _ _ hx0]
  ring_nf

/-- `∫_{x>1} x · x^{−s−1} dx = 1/(s−1)` for `Re s > 1`. -/
lemma integral_id_cpow {s : ℂ} (hs : 1 < s.re) :
    ∫ x in Ioi (1 : ℝ), (x : ℂ) * (x : ℂ) ^ (-(s + 1)) = 1 / (s - 1) := by
  rw [setIntegral_congr_fun measurableSet_Ioi fun x hx => cpow_mul_self (zero_lt_one.trans hx) s,
    integral_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one]
  have : -s + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hs1 : s - 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  simp only [Complex.ofReal_one, Complex.one_cpow]
  rw [div_eq_div_iff this hs1]
  ring

lemma integrableOn_id_cpow {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) * (x : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  refine (integrableOn_Ioi_cpow_of_lt (a := -s) (by simp; linarith) zero_lt_one).congr_fun
    (fun x hx => (cpow_mul_self (zero_lt_one.trans hx) s).symm) measurableSet_Ioi

lemma norm_log_mul_cpow {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ‖(Real.log x : ℂ) * (x : ℂ) ^ (-s)‖ = |Real.log x| * x ^ (-s.re) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

lemma integrableOn_log_cpow {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (Real.log x : ℂ) * (x : ℂ) ^ (-s)) (Ioi 1) := by
  set δ : ℝ := (s.re - 1) / 2
  have hδ : 0 < δ := by simp only [δ]; linarith
  have hint : IntegrableOn (fun x : ℝ => δ⁻¹ * x ^ (δ - s.re)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by simp only [δ]; linarith) zero_lt_one).const_mul _
  refine hint.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi
    have hx0 : 0 < x := zero_lt_one.trans hx
    refine ContinuousAt.continuousWithinAt ?_
    refine ((Complex.continuous_ofReal.continuousAt.comp
      (Real.continuousAt_log hx0.ne'))).mul ?_
    exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (by exact_mod_cast hx0.ne')))
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
    have hx0 : 0 < x := zero_lt_one.trans hx
    rw [norm_log_mul_cpow hx0, abs_of_nonneg (Real.log_nonneg (le_of_lt hx))]
    have hl := Real.log_le_rpow_div hx0.le hδ
    calc Real.log x * x ^ (-s.re) ≤ x ^ δ / δ * x ^ (-s.re) :=
          mul_le_mul_of_nonneg_right hl (by positivity)
      _ = δ⁻¹ * x ^ (δ - s.re) := by
          rw [sub_eq_add_neg, Real.rpow_add hx0]; ring

/-- `∫_{x>1} log x · x^{−s} dx = 1/(s−1)²` for `Re s > 1`. -/
lemma integral_log_cpow {s : ℂ} (hs : 1 < s.re) :
    ∫ x in Ioi (1 : ℝ), (Real.log x : ℂ) * (x : ℂ) ^ (-s) = 1 / (s - 1) ^ 2 := by
  set a : ℂ := s - 1
  have ha : a ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [a] at this; linarith
  have hare : 0 < a.re := by simp [a]; linarith
  set F : ℝ → ℂ := fun x => -((Real.log x : ℂ) * (x : ℂ) ^ (-a)) / a - (x : ℂ) ^ (-a) / a ^ 2
  have hderiv : ∀ x ∈ Ioi (1 : ℝ), HasDerivAt F ((Real.log x : ℂ) * (x : ℂ) ^ (-s)) x := by
    intro x hx
    have hx0 : 0 < x := zero_lt_one.trans hx
    have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-a)) (-a * (x : ℂ) ^ (-a - 1)) x :=
      hasDerivAt_ofReal_cpow_const hx0.ne' (neg_ne_zero.mpr ha)
    have h2 : HasDerivAt (fun y : ℝ => (Real.log y : ℂ)) ((x : ℂ)⁻¹) x := by
      have := (Real.hasDerivAt_log hx0.ne').ofReal_comp
      simpa using this
    have h3 : HasDerivAt F _ x := ((h2.mul h1).neg.div_const a).sub (h1.div_const (a ^ 2))
    refine h3.congr_deriv ?_
    have e1 : (x : ℂ) ^ (-a - 1) = (x : ℂ) ^ (-s) := by congr 1; simp only [a]; ring
    have e2 : (x : ℂ) ^ (-a) = (x : ℂ) * (x : ℂ) ^ (-s) := by
      rw [← e1]
      conv_rhs => arg 1; rw [← Complex.cpow_one (x : ℂ)]
      rw [← Complex.cpow_add _ _ hxc]; ring_nf
    rw [e1, e2]
    field_simp
    ring
  have hlim : Tendsto F atTop (𝓝 0) := by
    have hpow : Tendsto (fun x : ℝ => (x : ℂ) ^ (-a)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine (tendsto_rpow_neg_atTop hare).congr' ?_
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]; simp
    have hlog : Tendsto (fun x : ℝ => (Real.log x : ℂ) * (x : ℂ) ^ (-a)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have := (isLittleO_log_rpow_atTop hare).tendsto_div_nhds_zero
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 1] with x hx
      have hx0 : 0 < x := zero_lt_one.trans hx
      rw [norm_log_mul_cpow hx0, abs_of_nonneg (Real.log_nonneg hx.le), Real.rpow_neg hx0.le,
        div_eq_mul_inv]
    have := ((hlog.neg.div_const a).sub (hpow.div_const (a ^ 2)))
    simp only [neg_zero, zero_div, sub_zero] at this
    exact this
  have hcont : ContinuousWithinAt F (Ici 1) 1 := by
    have : ∃ f', HasDerivAt F f' 1 := by
      have h1 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-a)) (-a * ((1 : ℝ) : ℂ) ^ (-a - 1)) 1 :=
        hasDerivAt_ofReal_cpow_const one_ne_zero (neg_ne_zero.mpr ha)
      have h2 : HasDerivAt (fun y : ℝ => (Real.log y : ℂ)) (((1 : ℝ) : ℂ)⁻¹) 1 := by
        have := (Real.hasDerivAt_log one_ne_zero).ofReal_comp
        simpa using this
      exact ⟨_, ((h2.mul h1).neg.div_const a).sub (h1.div_const (a ^ 2))⟩
    exact this.choose_spec.continuousAt.continuousWithinAt
  have := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv (integrableOn_log_cpow hs) hlim
  rw [this]
  simp only [F, Complex.ofReal_one, Real.log_one, Complex.ofReal_zero, neg_zero, zero_mul, zero_div,
    Complex.one_cpow, zero_sub, sub_neg_eq_add, zero_add, a]

lemma log_mul_cpow {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (x * Real.log x : ℂ) * (x : ℂ) ^ (-(s + 1)) = (Real.log x : ℂ) * (x : ℂ) ^ (-s) := by
  rw [mul_comm (x : ℂ), mul_assoc, cpow_mul_self hx]

/-- `∫_{x>1} D(x) x^{−s−1}` is absolutely convergent for `Re s > 1`. -/
lemma integrableOn_divisorSummatory {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (divisorSummatory x : ℂ) * (x : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  set r : ℝ := (1 + s.re) / 2
  have hr1 : 1 < r := by simp only [r]; linarith
  obtain ⟨C, hC0, hC⟩ := sum_sigma_zero_le hr1
  have hint : IntegrableOn (fun x : ℝ => C * x ^ (r - s.re - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by simp only [r]; linarith) zero_lt_one).const_mul _
  refine hint.mono' ?_ ?_
  · refine ((Complex.measurable_ofReal.comp measurable_divisorSummatory).mul ?_).aestronglyMeasurable
    exact (Complex.measurable_ofReal).pow_const _
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
    have hx0 : 0 < x := zero_lt_one.trans hx
    rw [norm_mul, Complex.norm_real, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hD : ‖divisorSummatory x‖ ≤ C * x ^ r := by
      rw [divisorSummatory_eq_sum, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)]
      refine (hC _).trans ?_
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hx0.le) (by linarith)) hC0
    calc ‖divisorSummatory x‖ * x ^ (-(s + 1)).re ≤ C * x ^ r * x ^ (-(s + 1)).re :=
          mul_le_mul_of_nonneg_right hD (by positivity)
      _ = C * x ^ (r - s.re - 1) := by
          rw [mul_assoc, ← Real.rpow_add hx0]; congr 2; simp; ring

/-- **Item 1.** For `Re s > 1`, `G(s) = ζ(s)²/s − 1/(s−1)² − (2γ−1)/(s−1)`. -/
theorem mellin_divisorError_of_one_lt {s : ℂ} (hs : 1 < s.re) :
    G s = riemannZeta s ^ 2 / s - P s := by
  have hD := integrableOn_divisorSummatory hs
  have hL : IntegrableOn (fun x : ℝ => (x * Real.log x : ℂ) * (x : ℂ) ^ (-(s + 1))) (Ioi 1) :=
    (integrableOn_log_cpow hs).congr_fun
      (fun x hx => (log_mul_cpow (zero_lt_one.trans hx) s).symm) measurableSet_Ioi
  have hI := integrableOn_id_cpow hs
  have hsplit : ∀ x : ℝ, (divisorError x : ℂ) * (x : ℂ) ^ (-(s + 1)) =
      (divisorSummatory x : ℂ) * (x : ℂ) ^ (-(s + 1)) - (x * Real.log x : ℂ) * (x : ℂ) ^ (-(s + 1))
        - (2 * eulerMascheroniConstant - 1 : ℂ) * ((x : ℂ) * (x : ℂ) ^ (-(s + 1))) := by
    intro x; simp only [divisorError]; push_cast; ring
  have hDL : IntegrableOn (fun x : ℝ => (divisorSummatory x : ℂ) * (x : ℂ) ^ (-(s + 1)) -
      (x * Real.log x : ℂ) * (x : ℂ) ^ (-(s + 1))) (Ioi 1) := hD.sub hL
  have hI' : IntegrableOn (fun x : ℝ => (2 * eulerMascheroniConstant - 1 : ℂ) *
      ((x : ℂ) * (x : ℂ) ^ (-(s + 1)))) (Ioi 1) := hI.const_mul _
  unfold G
  simp_rw [hsplit]
  rw [integral_sub hDL hI', integral_sub hD hL, integral_const_mul,
    integral_divisorSummatory hs, integral_id_cpow hs,
    setIntegral_congr_fun measurableSet_Ioi fun x hx => log_mul_cpow (zero_lt_one.trans hx) s,
    integral_log_cpow hs]
  simp only [P]
  ring

end DirichletDivisorProblem.HardyD1
end

end
-- ===== end HardyOmegaFC.Mellin =====

-- ===== from HardyOmegaFC.Continuation =====
section

/-!
# Rung D1, part 2: continuation of `G` to `Re s > 1/4` under `Δ(x) = O(x^{1/4})`

* `exists_bound_of_isBigO`: `Δ = O(x^{1/4})` at `∞` gives `|Δ(x)| ≤ C x^{1/4}` on all of `[1, ∞)` (`D` is monotone,
  `x log x` is bounded on `[1, X]`).
* `differentiableAt_G` (item 2): `G(s) = mellin (1_{x>1} Δ) (−s)`, so Mathlib's
  `mellin_differentiableAt_of_isBigO_rpow` makes `G` complex-differentiable on `Re s > 1/4`.
* `G_eq_of_im_ne_zero` (item 3): `G(s) = ζ(s)²/s − P(s)` for `Re s > 1/4`, `Im s ≠ 0`, by the identity theorem on the
  convex open quarter-planes `{Re s > 1/4, ±Im s > 0}`, which meet `{Re s > 1}` (item 1) and avoid `s = 1`. This
  avoids the removable singularity at `s = 1`: on each vertical line the identity holds off the single point
  `t = 0`, which is all the Plancherel step needs.
-/

open Filter Asymptotics Real Complex MeasureTheory Set Topology

noncomputable section

namespace DirichletDivisorProblem.HardyD1

/-- The divisor error `Δ = O(x^{1/4})` (the hypothesis of the continuation). -/
abbrev QuarterBigO : Prop := divisorError =O[atTop] fun x => x ^ ((1 : ℝ) / 4)

lemma divisorSummatory_nonneg (x : ℝ) : 0 ≤ divisorSummatory x :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

lemma divisorSummatory_mono : Monotone divisorSummatory := fun x y hxy =>
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right (Nat.floor_mono hxy))
    fun _ _ _ => Nat.cast_nonneg _

lemma exists_bound_of_isBigO (h : QuarterBigO) :
    ∃ C, 0 ≤ C ∧ ∀ x, 1 ≤ x → |divisorError x| ≤ C * x ^ ((1 : ℝ) / 4) := by
  obtain ⟨c, hc⟩ := h.bound
  obtain ⟨X, hX⟩ := eventually_atTop.mp hc
  set Y : ℝ := max X 1
  set B : ℝ := divisorSummatory Y + Y * Real.log Y + |2 * eulerMascheroniConstant - 1| * Y
  have hY1 : 1 ≤ Y := le_max_right _ _
  have hB0 : 0 ≤ B := by
    have := divisorSummatory_nonneg Y
    have := Real.log_nonneg hY1
    positivity
  refine ⟨max c 0 + B, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hq1 : 1 ≤ x ^ ((1 : ℝ) / 4) := Real.one_le_rpow hx (by norm_num)
  rcases le_or_gt X x with hXx | hxX
  · have := hX x hXx
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)] at this
    calc |divisorError x| ≤ c * x ^ ((1 : ℝ) / 4) := this
      _ ≤ (max c 0 + B) * x ^ ((1 : ℝ) / 4) := by
          gcongr; linarith [le_max_left c 0]
  · have hxY : x ≤ Y := hxX.le.trans (le_max_left _ _)
    have hD : |divisorSummatory x| ≤ divisorSummatory Y := by
      rw [abs_of_nonneg (divisorSummatory_nonneg x)]; exact divisorSummatory_mono hxY
    have hL : |x * Real.log x| ≤ Y * Real.log Y := by
      rw [abs_of_nonneg (mul_nonneg hx0.le (Real.log_nonneg hx))]
      exact mul_le_mul hxY (Real.log_le_log hx0 hxY) (Real.log_nonneg hx) (by linarith)
    have hlin : |(2 * eulerMascheroniConstant - 1) * x| ≤ |2 * eulerMascheroniConstant - 1| * Y := by
      rw [abs_mul, abs_of_pos hx0]; exact mul_le_mul_of_nonneg_left hxY (abs_nonneg _)
    have hDB : |divisorError x| ≤ B := by
      unfold divisorError
      calc |divisorSummatory x - x * Real.log x - (2 * eulerMascheroniConstant - 1) * x|
          ≤ |divisorSummatory x| + |x * Real.log x| + |(2 * eulerMascheroniConstant - 1) * x| := by
            have := abs_sub (divisorSummatory x - x * Real.log x) ((2 * eulerMascheroniConstant - 1) * x)
            have := abs_sub (divisorSummatory x) (x * Real.log x)
            linarith
        _ ≤ B := by simp only [B]; linarith
    calc |divisorError x| ≤ B := hDB
      _ ≤ B * x ^ ((1 : ℝ) / 4) := le_mul_of_one_le_right hB0 hq1
      _ ≤ (max c 0 + B) * x ^ ((1 : ℝ) / 4) := by
          gcongr; linarith [le_max_right c 0]

/-- `1_{x > 1} Δ(x)`, the function whose Mellin transform at `−s` is `G(s)`. -/
def Gf : ℝ → ℂ := (Ioi (1 : ℝ)).indicator fun x => (divisorError x : ℂ)

lemma G_eq_mellin (s : ℂ) : G s = mellin Gf (-s) := by
  rw [mellin, G]
  have : ∀ t : ℝ, (t : ℂ) ^ (-s - 1) • Gf t =
      (Ioi (1 : ℝ)).indicator (fun x : ℝ => (divisorError x : ℂ) * (x : ℂ) ^ (-(s + 1))) t := by
    intro t
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · simp only [Gf, indicator_of_mem ht, smul_eq_mul]
      rw [mul_comm]; congr 2; ring
    · simp [Gf, indicator_of_notMem ht]
  simp_rw [this]
  rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, sup_eq_right.mpr zero_le_one]

lemma measurable_Gf : Measurable Gf :=
  (Complex.measurable_ofReal.comp measurable_divisorError).indicator measurableSet_Ioi

lemma locallyIntegrable_Gf (h : QuarterBigO) : LocallyIntegrable Gf := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_of_isBigO h
  have hg : Continuous fun y : ℝ => C * (max y 1) ^ ((1 : ℝ) / 4) :=
    continuous_const.mul ((continuous_id.max continuous_const).rpow_const
      fun _ => Or.inr (by norm_num))
  refine hg.locallyIntegrable.mono measurable_Gf.aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  have hm : 0 ≤ C * (max y 1) ^ ((1 : ℝ) / 4) :=
    mul_nonneg hC0 (Real.rpow_nonneg (le_trans zero_le_one (le_max_right _ _)) _)
  rw [Real.norm_of_nonneg hm]
  by_cases hy : y ∈ Ioi (1 : ℝ)
  · simp only [Gf, indicator_of_mem hy, Complex.norm_real, Real.norm_eq_abs]
    have hy1 : (1 : ℝ) < y := hy
    rw [max_eq_left hy1.le]
    exact hC y hy1.le
  · simp only [Gf, indicator_of_notMem hy, norm_zero]; exact hm

/-- **Item 2.** Under `Δ = O(x^{1/4})`, `G` is complex-differentiable at every `s` with `Re s > 1/4`. -/
theorem differentiableAt_G (h : QuarterBigO) {s : ℂ} (hs : 1 / 4 < s.re) :
    DifferentiableAt ℂ G s := by
  have hG : G = fun s => mellin Gf (-s) := funext G_eq_mellin
  rw [hG]
  refine DifferentiableAt.comp (g := mellin Gf) s ?_ differentiableAt_id.neg
  refine mellin_differentiableAt_of_isBigO_rpow (a := -(1 / 4)) (b := -s.re - 1)
    ((locallyIntegrable_Gf h).locallyIntegrableOn _) ?_ (by simp; linarith) ?_ (by simp)
  · obtain ⟨c, hc⟩ := h.bound
    refine IsBigO.of_bound c ?_
    filter_upwards [hc, eventually_gt_atTop 1] with x hx hx1
    simp only [Gf, indicator_of_mem (show x ∈ Ioi (1 : ℝ) from hx1), Complex.norm_real, neg_neg]
    simpa using hx
  · refine (isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds one_pos)] with x hx
    have : x ∉ Ioi (1 : ℝ) := fun h' => lt_asymm hx (show (1:ℝ) < x from h')
    simp [Gf, indicator_of_notMem this]

lemma differentiableAt_rhs {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    DifferentiableAt ℂ (fun s => riemannZeta s ^ 2 / s - P s) s := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hP : DifferentiableAt ℂ P s := by
    unfold P
    have hd : DifferentiableAt ℂ (fun z : ℂ => z - 1) s := differentiableAt_id.sub_const 1
    exact ((differentiableAt_const (1 : ℂ)).div (hd.pow 2) (pow_ne_zero 2 hs1)).add
      ((differentiableAt_const _).div hd hs1)
  exact (((differentiableAt_riemannZeta h1).pow 2).div differentiableAt_id h0).sub hP

/-- Identity theorem on a convex open set inside `{Re s > 1/4} \ {1}` that meets `{Re s > 1}`. -/
lemma G_eqOn_of_convex (h : QuarterBigO) {U : Set ℂ} (hUo : IsOpen U) (hUc : Convex ℝ U)
    (hU : ∀ z ∈ U, 1 / 4 < z.re ∧ z ≠ 1) {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hz₀re : 1 < z₀.re) :
    EqOn G (fun s => riemannZeta s ^ 2 / s - P s) U := by
  have hne0 : ∀ z ∈ U, z ≠ 0 := fun z hz h0 => by
    have := (hU z hz).1; rw [h0] at this; norm_num at this
  have hG : DifferentiableOn ℂ G U := fun z hz =>
    (differentiableAt_G h (hU z hz).1).differentiableWithinAt
  have hR : DifferentiableOn ℂ (fun s => riemannZeta s ^ 2 / s - P s) U := fun z hz =>
    (differentiableAt_rhs (hne0 z hz) (hU z hz).2).differentiableWithinAt
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (hG.analyticOnNhd hUo)
    (hR.analyticOnNhd hUo) hUc.isPreconnected hz₀ ?_
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz₀re] with z hz
  exact mellin_divisorError_of_one_lt hz

/-- **Item 3.** Under `Δ = O(x^{1/4})`: `G(s) = ζ(s)²/s − P(s)` for `Re s > 1/4`, `Im s ≠ 0`. -/
theorem G_eq_of_im_ne_zero (h : QuarterBigO) {s : ℂ} (hs : 1 / 4 < s.re) (him : s.im ≠ 0) :
    G s = riemannZeta s ^ 2 / s - P s := by
  rcases lt_or_gt_of_ne him with hneg | hpos
  · set U : Set ℂ := {z | 1 / 4 < z.re} ∩ {z | z.im < 0}
    have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_im continuous_const)
    have hUc : Convex ℝ U := (convex_halfSpace_re_gt _).inter (convex_halfSpace_im_lt _)
    refine G_eqOn_of_convex h hUo hUc (fun z hz => ⟨hz.1, fun h1 => ?_⟩)
      (z₀ := 2 - I) ⟨by simp; norm_num, by simp⟩ (by simp) ⟨hs, hneg⟩
    have := hz.2; rw [h1] at this; simp at this
  · set U : Set ℂ := {z | 1 / 4 < z.re} ∩ {z | 0 < z.im}
    have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
    have hUc : Convex ℝ U := (convex_halfSpace_re_gt _).inter (convex_halfSpace_im_gt _)
    refine G_eqOn_of_convex h hUo hUc (fun z hz => ⟨hz.1, fun h1 => ?_⟩)
      (z₀ := 2 + I) ⟨by simp; norm_num, by simp⟩ (by simp) ⟨hs, hpos⟩
    have := hz.2; rw [h1] at this; simp at this

end DirichletDivisorProblem.HardyD1
end

end
-- ===== end HardyOmegaFC.Continuation =====

-- ===== from LeanClassics.NymanPlancherel =====
section
/-
Plancherel's identity for integrable square-integrable functions on ℝ, and its Mellin form on the
line Re s = 1/2:

* `integral_norm_sq_fourier`: if `f ∈ L¹ ∩ L²(ℝ)` then `∫ |𝓕 f(ξ)|² dξ = ∫ |f(x)|² dx`, with `𝓕 f`
  Mathlib's pointwise Fourier integral `∫ e^{−2πixξ} f(x) dx`.
* `integral_norm_sq_mellin`: if `g` is measurable and bounded on `(0, 1]`, then
  `∫₀¹ |g(x)|² dx = ∫ |∫₀¹ g(x) x^{s(ξ) − 1} dx|² dξ`, `s(ξ) = 1/2 + 2πiξ`.

Proof. Mathlib defines the L² Fourier transform abstractly (`Lp.fourierTransformₗᵢ`, a linear isometry
extending the Schwartz-space transform). Tested against a smooth compactly supported `g`, it agrees
with the pointwise transform: as tempered distributions `𝓕 F = 𝓕 (F as a distribution)`
(`Lp.fourier_toTemperedDistribution_eq`), and `∫ 𝓕g · f = ∫ g · 𝓕f` for integrable `f` (Fubini,
`VectorFourier.integral_fourierIntegral_smul_eq_flip`). Locally integrable functions with equal
integrals against every such `g` agree almost everywhere (`ae_eq_of_integral_contDiff_smul_eq`), and
the isometry gives the identity. The Mellin form substitutes `x = e^{−u}` (`mellin_eq_fourier`).
-/

open MeasureTheory FourierTransform Complex Set
open scoped ContDiff

noncomputable section

namespace LeanClassics.Nyman.Plancherel

lemma norm_sq_Lp_eq (F : Lp ℂ 2 (volume : Measure ℝ)) : ‖F‖ ^ 2 = ∫ x, ‖F x‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ, MeasureTheory.L2.inner_def, ← integral_re (L2.integrable_inner F F)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]

/-- **Plancherel for `L¹ ∩ L²`.** -/
theorem integral_norm_sq_fourier {f : ℝ → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2) :
    ∫ ξ, ‖𝓕 f ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  set F : Lp ℂ 2 (volume : Measure ℝ) := hf2.toLp f with hF
  have hcont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hf1
  have hae : (𝓕 F : Lp ℂ 2 (volume : Measure ℝ)) =ᵐ[volume] 𝓕 f := by
    refine ae_eq_of_integral_contDiff_smul_eq
      ((Lp.memLp _).locallyIntegrable (by norm_num)) hcont.locallyIntegrable ?_
    intro g hg hgs
    have hgc : ContDiff ℝ ∞ (fun x => (g x : ℂ)) := ofRealCLM.contDiff.comp hg
    have hgcs : HasCompactSupport (fun x => (g x : ℂ)) := hgs.comp_left Complex.ofReal_zero
    set G : SchwartzMap ℝ ℂ := hgcs.toSchwartzMap hgc with hG
    have hGx : ∀ x, G x = (g x : ℂ) := fun x => rfl
    have h1 : ∫ x, g x • (𝓕 F : Lp ℂ 2 (volume : Measure ℝ)) x =
        Lp.toTemperedDistribution (𝓕 F : Lp ℂ 2 (volume : Measure ℝ)) G := by
      rw [Lp.toTemperedDistribution_apply]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [hGx, Complex.real_smul, smul_eq_mul]
    rw [h1, ← Lp.fourier_toTemperedDistribution_eq, TemperedDistribution.fourier_apply,
      Lp.toTemperedDistribution_apply (μ := volume)]
    have h2 : ∫ x, (𝓕 G) x • F x = ∫ x, (𝓕 (G : ℝ → ℂ)) x • f x := by
      refine integral_congr_ae ?_
      filter_upwards [hf2.coeFn_toLp] with x hx
      rw [hF, hx]; rfl
    rw [h2]
    have h3 := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner (G.integrable (μ := volume)) hf1
    have h4 : ∫ x, (𝓕 (G : ℝ → ℂ)) x • f x = ∫ x, G x • 𝓕 f x := by
      have hflip : (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip = innerₗ ℝ := by
        ext; simp
      simp only [smul_eq_mul, hflip] at h3 ⊢; exact h3
    rw [h4]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hGx, Complex.real_smul, smul_eq_mul]
  have hnorm : ‖(𝓕 F : Lp ℂ 2 (volume : Measure ℝ))‖ = ‖F‖ := Lp.norm_fourier_eq F
  have e1 := norm_sq_Lp_eq (𝓕 F)
  have e2 := norm_sq_Lp_eq F
  have e3 : ∫ x, ‖(𝓕 F : Lp ℂ 2 (volume : Measure ℝ)) x‖ ^ 2 = ∫ ξ, ‖𝓕 f ξ‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx; rw [hx]
  have e4 : ∫ x, ‖F x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [hf2.coeFn_toLp] with x hx; rw [hF, hx]
  rw [← e3, ← e1, hnorm, e2, e4]

end LeanClassics.Nyman.Plancherel
end

end
-- ===== end LeanClassics.NymanPlancherel =====

-- ===== from HardyOmegaFC.Plancherel =====
section

/-!
# Rung D1, part 3: Plancherel and the reduction to a lower bound for `∫ |ζ(s)²/s|²`

* `plancherel_G` (item 4): under `Δ = O(x^{1/4})` and `σ > 1/4`, `t ↦ |G(σ+it)|²` is integrable and
  `∫ |G(σ+it)|² dt = 2π ∫ |φ_σ(u)|² du`, `φ_σ(u) = e^{σu} 1_{u<0} Δ(e^{−u})` (so `∫|φ_σ|² = ∫_1^∞ Δ(x)² x^{−2σ−1} dx`).
  `G(σ+it) = 𝓕φ_σ(−t/2π)` is Mathlib's `mellin_eq_fourier`; the identity is
  `LeanClassics.Nyman.Plancherel.integral_norm_sq_fourier` (`L¹ ∩ L²`) and a rescaling. Integrability of the Fourier
  side comes out of the same identity: were it not integrable, its Bochner integral would be `0`, forcing `φ_σ = 0`
  a.e. and so `𝓕φ_σ = 0`, which is integrable.
* `tendsto_eps_mul_integral` (item 5): under `Δ = o(x^{1/4})`, `ε ∫ |G(1/4+ε+it)|² dt → 0` as `ε → 0+`
  (`|φ_σ(u)|² ≤ C² 1_{(−L,0)}(u) + η² e^{2εu} 1_{u<0}`, whose integral is `C² L + η²/(2ε)`).
* `divisor_error_hardy_of_lowerBound` (item 6, the rung's deliverable): if `LowerBoundD` then FC's
  `¬ (divisorError =o[atTop] fun x => x ^ ((1 : ℝ) / 4))`. On `Re s = 1/4+ε`, `ζ(s)²/s = G(s) + P(s)` off `t = 0`,
  `|P(σ+it)|² ≤ K/(1+t²)`, so `ε ∫ |ζ²/s|² ≤ 2ε ∫ |G|² + 2Kπε → 0`, against `LowerBoundD`. `LowerBoundD` asks for the
  lower bound only when the integrand is integrable (here integrability is derived, not assumed), so it is implied by
  the unconditional form `c ≤ ε ∫ |ζ²/s|²` of the plan.
-/

open Filter Asymptotics Real Complex MeasureTheory Set Topology FourierTransform

noncomputable section

namespace DirichletDivisorProblem.HardyD1

/-- `φ_σ(u) = e^{σu} · 1_{e^{−u} > 1} Δ(e^{−u})`. -/
def phi (σ u : ℝ) : ℂ := Real.exp (σ * u) • Gf (Real.exp (-u))

lemma G_eq_fourier (σ t : ℝ) : G (σ + t * I) = 𝓕 (phi σ) (-t / (2 * π)) := by
  rw [G_eq_mellin, mellin_eq_fourier]
  have h1 : (fun u : ℝ => Real.exp (-(-((σ : ℂ) + t * I)).re * u) • Gf (Real.exp (-u))) = phi σ := by
    funext u; simp [phi]
  have h2 : (-((σ : ℂ) + t * I)).im / (2 * π) = -t / (2 * π) := by simp [neg_div]
  rw [h1, h2]

lemma measurable_phi (σ : ℝ) : Measurable (phi σ) :=
  (Real.measurable_exp.comp (measurable_const.mul measurable_id)).smul
    (measurable_Gf.comp (Real.measurable_exp.comp measurable_neg))

lemma phi_of_nonneg (σ : ℝ) {u : ℝ} (hu : 0 ≤ u) : phi σ u = 0 := by
  have : Real.exp (-u) ∉ Ioi (1 : ℝ) := fun h => by
    have : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    exact absurd h (not_lt.mpr this)
  simp [phi, Gf, indicator_of_notMem this]

lemma norm_phi_of_neg (σ : ℝ) {u : ℝ} (hu : u < 0) :
    ‖phi σ u‖ = Real.exp (σ * u) * |divisorError (Real.exp (-u))| := by
  have : Real.exp (-u) ∈ Ioi (1 : ℝ) := Real.one_lt_exp_iff.mpr (by linarith)
  simp only [phi, Gf, indicator_of_mem this, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Complex.norm_real]

lemma exp_neg_rpow_quarter (u : ℝ) : Real.exp (-u) ^ ((1 : ℝ) / 4) = Real.exp (-u / 4) := by
  rw [← Real.exp_mul]; ring_nf

/-- `|φ_σ(u)| ≤ C e^{(σ−1/4)u} 1_{u<0}` from `|Δ(x)| ≤ C x^{1/4}` on `[1, ∞)`. -/
lemma norm_phi_le {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, 1 ≤ x → |divisorError x| ≤ C * x ^ ((1 : ℝ) / 4))
    (σ u : ℝ) : ‖phi σ u‖ ≤ C * (Iio 0).indicator (fun u => Real.exp ((σ - 1 / 4) * u)) u := by
  rcases lt_or_ge u 0 with hu | hu
  · rw [norm_phi_of_neg σ hu, indicator_of_mem (show u ∈ Iio (0 : ℝ) from hu)]
    have h1 : 1 ≤ Real.exp (-u) := Real.one_le_exp_iff.mpr (by linarith)
    calc Real.exp (σ * u) * |divisorError (Real.exp (-u))|
        ≤ Real.exp (σ * u) * (C * Real.exp (-u) ^ ((1 : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_left (hC _ h1) (Real.exp_pos _).le
      _ = C * Real.exp ((σ - 1 / 4) * u) := by
          rw [exp_neg_rpow_quarter, mul_left_comm, ← Real.exp_add]; ring_nf
  · rw [phi_of_nonneg σ hu, norm_zero, indicator_of_notMem (show u ∉ Iio (0 : ℝ) from not_lt.mpr hu),
      mul_zero]

lemma integrable_indicator_exp {a : ℝ} (ha : 0 < a) :
    Integrable ((Iio (0 : ℝ)).indicator fun u => Real.exp (a * u)) :=
  ((integrableOn_exp_mul_Iic ha 0).mono_set Iio_subset_Iic_self).integrable_indicator measurableSet_Iio

lemma indicator_exp_sq (a u : ℝ) :
    ((Iio (0 : ℝ)).indicator (fun u => Real.exp (a * u)) u) ^ 2 =
      (Iio (0 : ℝ)).indicator (fun u => Real.exp ((2 * a) * u)) u := by
  by_cases hu : u ∈ Iio (0 : ℝ)
  · simp only [indicator_of_mem hu, ← Real.exp_nat_mul]; ring_nf
  · simp [indicator_of_notMem hu]

lemma phi_integrable_memLp (h : QuarterBigO) {σ : ℝ} (hσ : 1 / 4 < σ) :
    Integrable (phi σ) ∧ MemLp (phi σ) 2 := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_of_isBigO h
  have ha : 0 < σ - 1 / 4 := by linarith
  have hb := norm_phi_le hC0 hC σ
  refine ⟨((integrable_indicator_exp ha).const_mul C).mono' (measurable_phi σ).aestronglyMeasurable
    (Eventually.of_forall hb), ?_⟩
  refine (memLp_two_iff_integrable_sq_norm (measurable_phi σ).aestronglyMeasurable).mpr ?_
  refine ((integrable_indicator_exp (by linarith : 0 < 2 * (σ - 1 / 4))).const_mul (C ^ 2)).mono'
    ((measurable_phi σ).norm.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  rw [Real.norm_of_nonneg (by positivity), ← indicator_exp_sq, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hb u) 2

/-- The Fourier side of Plancherel is integrable (it has the same, finite, integral as `|f|²`, and a
non-integrable function has Bochner integral `0`). -/
lemma integrable_fourier_sq {f : ℝ → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2) :
    Integrable fun ξ => ‖𝓕 f ξ‖ ^ 2 := by
  by_contra hni
  have hP := LeanClassics.Nyman.Plancherel.integral_norm_sq_fourier hf1 hf2
  rw [integral_undef hni] at hP
  have hint : Integrable fun x => ‖f x‖ ^ 2 :=
    (memLp_two_iff_integrable_sq_norm hf1.aestronglyMeasurable).mp hf2
  have h0 : (fun x => ‖f x‖ ^ 2) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => by positivity) hint).mp hP.symm
  have hF : ∀ ξ, 𝓕 f ξ = 0 := fun ξ => by
    rw [Real.fourier_real_eq]
    refine integral_eq_zero_of_ae (h0.mono fun x hx => ?_)
    have : f x = 0 := by simpa using hx
    simp [this]
  exact hni (by simp only [hF]; simp)

/-- **Item 4 (Plancherel).** Under `Δ = O(x^{1/4})`, for `σ > 1/4`: `t ↦ |G(σ+it)|²` is integrable and
`∫ |G(σ+it)|² dt = 2π ∫ |φ_σ(u)|² du`. -/
theorem plancherel_G (h : QuarterBigO) {σ : ℝ} (hσ : 1 / 4 < σ) :
    Integrable (fun t : ℝ => ‖G (σ + t * I)‖ ^ 2) ∧
      ∫ t : ℝ, ‖G (σ + t * I)‖ ^ 2 = 2 * π * ∫ u, ‖phi σ u‖ ^ 2 := by
  obtain ⟨hφ1, hφ2⟩ := phi_integrable_memLp h hσ
  have hP := LeanClassics.Nyman.Plancherel.integral_norm_sq_fourier hφ1 hφ2
  have hFi := integrable_fourier_sq hφ1 hφ2
  have hfun : (fun t : ℝ => ‖G (σ + t * I)‖ ^ 2) =
      fun t => (fun ξ => ‖𝓕 (phi σ) ξ‖ ^ 2) ((-(1 / (2 * π))) * t) := by
    funext t; rw [G_eq_fourier]; rw [show -t / (2 * π) = -(1 / (2 * π)) * t by ring]
  have hc : (-(1 / (2 * π)) : ℝ) ≠ 0 := by
    have := Real.pi_pos; exact neg_ne_zero.mpr (by positivity)
  refine ⟨by rw [hfun]; exact hFi.comp_mul_left' hc, ?_⟩
  rw [hfun]
  calc ∫ t : ℝ, (fun ξ => ‖𝓕 (phi σ) ξ‖ ^ 2) ((-(1 / (2 * π))) * t)
      = |(-(1 / (2 * π)))⁻¹| • ∫ ξ : ℝ, ‖𝓕 (phi σ) ξ‖ ^ 2 :=
        Measure.integral_comp_mul_left (fun ξ => ‖𝓕 (phi σ) ξ‖ ^ 2) (-(1 / (2 * π)))
    _ = _ := ?_
  rw [hP, smul_eq_mul]
  congr 1
  rw [inv_neg, abs_neg, one_div, inv_inv, abs_of_pos (by positivity)]

/-- **Item 5.** Under `Δ = o(x^{1/4})`: `ε ∫ |G(1/4+ε+it)|² dt → 0` as `ε → 0+`. -/
theorem tendsto_eps_mul_integral (h : divisorError =o[atTop] fun x => x ^ ((1 : ℝ) / 4)) :
    Tendsto (fun ε : ℝ => ε * ∫ t : ℝ, ‖G (((1 / 4 + ε : ℝ)) + t * I)‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have hO : QuarterBigO := h.isBigO
  obtain ⟨C, hC0, hC⟩ := exists_bound_of_isBigO hO
  -- the `φ` form
  have hphi : Tendsto (fun ε : ℝ => ε * ∫ u, ‖phi (1 / 4 + ε) u‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
    refine Metric.tendsto_nhds.mpr fun δ hδ => ?_
    set η : ℝ := Real.sqrt (δ / 2)
    have hη : 0 < η := Real.sqrt_pos.mpr (by linarith)
    have hη2 : η ^ 2 = δ / 2 := Real.sq_sqrt (by linarith)
    obtain ⟨X, hX⟩ := eventually_atTop.mp (h.def hη)
    set L : ℝ := Real.log (max X 1)
    have hL0 : 0 ≤ L := Real.log_nonneg (le_max_right _ _)
    set M : ℝ := C ^ 2 * L
    have hM0 : 0 ≤ M := by positivity
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < δ / (4 * (M + 1)) by positivity))]
      with ε (hε : 0 < ε) (hεδ : ε < δ / (4 * (M + 1)))
    set σ : ℝ := 1 / 4 + ε
    -- pointwise majorant
    set R : ℝ → ℝ := fun u => C ^ 2 * (Ioo (-L) 0).indicator (fun _ => (1 : ℝ)) u +
      η ^ 2 * (Iio (0 : ℝ)).indicator (fun u => Real.exp ((2 * ε) * u)) u
    have hRi : Integrable R :=
      ((integrable_indicator_iff measurableSet_Ioo).mpr (integrableOn_const (by simp))).const_mul _
        |>.add ((integrable_indicator_exp (by linarith : 0 < 2 * ε)).const_mul _)
    have hle : ∀ u, ‖phi σ u‖ ^ 2 ≤ R u := by
      intro u
      have hR1 : 0 ≤ C ^ 2 * (Ioo (-L) 0).indicator (fun _ => (1 : ℝ)) u :=
        mul_nonneg (by positivity) (indicator_nonneg (fun _ _ => zero_le_one) _)
      have hR2 : 0 ≤ η ^ 2 * (Iio (0 : ℝ)).indicator (fun u => Real.exp ((2 * ε) * u)) u :=
        mul_nonneg (by positivity) (indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _)
      rcases lt_or_ge u 0 with hu | hu
      · rcases lt_or_ge (-L) u with hLu | hLu
        · -- `|φ| ≤ C e^{εu} ≤ C`
          have hb := norm_phi_le hC0 hC σ u
          rw [indicator_of_mem (show u ∈ Iio (0 : ℝ) from hu)] at hb
          have he : Real.exp ((σ - 1 / 4) * u) ≤ 1 :=
            Real.exp_le_one_iff.mpr (by simp only [σ]; nlinarith)
          have : ‖phi σ u‖ ^ 2 ≤ C ^ 2 := by
            have h1 : ‖phi σ u‖ ≤ C := hb.trans (by nlinarith)
            exact pow_le_pow_left₀ (norm_nonneg _) h1 2
          simp only [R, indicator_of_mem (show u ∈ Ioo (-L) 0 from ⟨hLu, hu⟩), mul_one]
          linarith
        · -- `x = e^{−u} ≥ max X 1`, so `|Δ(x)| ≤ η x^{1/4}`
          have hx : max X 1 ≤ Real.exp (-u) := by
            rw [← Real.exp_log (lt_of_lt_of_le zero_lt_one (le_max_right X 1))]
            exact Real.exp_le_exp.mpr (by simp only [L] at hLu; linarith)
          have hΔ := hX _ ((le_max_left _ _).trans hx)
          rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity), exp_neg_rpow_quarter] at hΔ
          have h1 : ‖phi σ u‖ ≤ η * Real.exp (ε * u) := by
            rw [norm_phi_of_neg σ hu]
            calc Real.exp (σ * u) * |divisorError (Real.exp (-u))|
                ≤ Real.exp (σ * u) * (η * Real.exp (-u / 4)) :=
                  mul_le_mul_of_nonneg_left hΔ (Real.exp_pos _).le
              _ = η * Real.exp (ε * u) := by
                  rw [mul_left_comm, ← Real.exp_add]; simp only [σ]; ring_nf
          have : ‖phi σ u‖ ^ 2 ≤ η ^ 2 * Real.exp ((2 * ε) * u) := by
            calc ‖phi σ u‖ ^ 2 ≤ (η * Real.exp (ε * u)) ^ 2 :=
                  pow_le_pow_left₀ (norm_nonneg _) h1 2
              _ = η ^ 2 * Real.exp ((2 * ε) * u) := by
                  rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
          simp only [R, indicator_of_mem (show u ∈ Iio (0 : ℝ) from hu)]
          linarith
      · rw [phi_of_nonneg σ hu, norm_zero]
        simp only [R]; norm_num; linarith
    have hint : ∫ u, R u = M + η ^ 2 / (2 * ε) := by
      simp only [R]
      rw [integral_add (((integrable_indicator_iff measurableSet_Ioo).mpr
          (integrableOn_const (by simp))).const_mul _)
          ((integrable_indicator_exp (by linarith : 0 < 2 * ε)).const_mul _),
        integral_const_mul, integral_const_mul, integral_indicator measurableSet_Ioo,
        integral_indicator measurableSet_Iio, setIntegral_const, Real.volume_real_Ioo_of_le (by linarith),
        setIntegral_congr_set Iio_ae_eq_Iic, integral_exp_mul_Iic (by linarith) 0]
      simp only [M, smul_eq_mul, mul_one, sub_neg_eq_add, zero_add, mul_zero, Real.exp_zero]
      ring
    have hI : ∫ u, ‖phi σ u‖ ^ 2 ≤ M + η ^ 2 / (2 * ε) := by
      rw [← hint]
      exact integral_mono_of_nonneg (Eventually.of_forall fun u => by positivity) hRi
        (Eventually.of_forall hle)
    have hI0 : 0 ≤ ∫ u, ‖phi σ u‖ ^ 2 := integral_nonneg fun u => by positivity
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg hε.le hI0)]
    have hεM : ε * M < δ / 4 := by
      have : ε * (M + 1) < δ / 4 := by
        rw [lt_div_iff₀ (by positivity)] at hεδ; nlinarith
      nlinarith
    calc ε * ∫ u, ‖phi σ u‖ ^ 2 ≤ ε * (M + η ^ 2 / (2 * ε)) := mul_le_mul_of_nonneg_left hI hε.le
      _ = ε * M + δ / 4 := by rw [hη2]; field_simp; ring
      _ < δ := by linarith
  have := hphi.const_mul (2 * π)
  rw [mul_zero] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [(plancherel_G hO (by linarith : (1 : ℝ) / 4 < 1 / 4 + ε)).2]
  ring

/-- `|P(σ+it)|² ≤ K/(1+t²)` for `σ ≤ 1/2`, with `K = 4 (2 + |2γ−1|)²`. -/
lemma norm_P_sq_le {σ t : ℝ} (hσ : σ ≤ 1 / 2) :
    ‖P (σ + t * I)‖ ^ 2 ≤
      4 * (2 + ‖(2 * (eulerMascheroniConstant : ℂ) - 1)‖) ^ 2 * (1 + t ^ 2)⁻¹ := by
  set A : ℝ := ‖(2 * (eulerMascheroniConstant : ℂ) - 1)‖
  set w : ℝ := ‖(σ : ℂ) + t * I - 1‖
  have hw2 : w ^ 2 = (σ - 1) ^ 2 + t ^ 2 := by
    simp only [w, Complex.sq_norm, Complex.normSq_apply]
    simp; ring
  have hw0 : 0 ≤ w := norm_nonneg _
  have hw4 : (1 + t ^ 2) / 4 ≤ w ^ 2 := by rw [hw2]; nlinarith
  have hwh : 1 / 2 ≤ w := by nlinarith
  have hwpos : 0 < w := by linarith
  have hA : 0 ≤ A := norm_nonneg _
  have hP : ‖P (σ + t * I)‖ ≤ (2 + A) / w := by
    unfold P
    calc ‖1 / ((σ : ℂ) + t * I - 1) ^ 2 + (2 * (eulerMascheroniConstant : ℂ) - 1) /
          ((σ : ℂ) + t * I - 1)‖
        ≤ ‖1 / ((σ : ℂ) + t * I - 1) ^ 2‖ + ‖(2 * (eulerMascheroniConstant : ℂ) - 1) /
          ((σ : ℂ) + t * I - 1)‖ := norm_add_le _ _
      _ = 1 / w ^ 2 + A / w := by rw [norm_div, norm_div, norm_one, norm_pow]
      _ ≤ (2 + A) / w := by
          rw [add_div]
          have : 1 / w ^ 2 ≤ 2 / w := by
            rw [div_le_div_iff₀ (by positivity) hwpos]; nlinarith
          linarith
  calc ‖P (σ + t * I)‖ ^ 2 ≤ ((2 + A) / w) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hP 2
    _ = (2 + A) ^ 2 / w ^ 2 := by rw [div_pow]
    _ ≤ (2 + A) ^ 2 / ((1 + t ^ 2) / 4) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hw4
    _ = 4 * (2 + A) ^ 2 * (1 + t ^ 2)⁻¹ := by field_simp

/-- The lower bound that rungs D2-D4 must prove: `ε ∫ |ζ(1/4+ε+it)|⁴/|1/4+ε+it|² dt ≥ c > 0` for small `ε > 0`,
asked only when the integrand is integrable. -/
def LowerBoundD : Prop :=
  ∃ c > (0 : ℝ), ∀ᶠ ε : ℝ in 𝓝[>] 0,
    Integrable (fun t : ℝ => ‖riemannZeta (1 / 4 + (ε : ℂ) + t * I) ^ 2 / (1 / 4 + (ε : ℂ) + t * I)‖ ^ 2) →
      c ≤ ε * ∫ t : ℝ, ‖riemannZeta (1 / 4 + (ε : ℂ) + t * I) ^ 2 / (1 / 4 + (ε : ℂ) + t * I)‖ ^ 2

lemma line_ne {ε t : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 4) :
    (1 / 4 + ε + t * I : ℂ) ≠ 0 ∧ (1 / 4 + ε + t * I : ℂ) ≠ 1 := by
  constructor <;> intro h <;> have := congrArg Complex.re h <;> simp at this <;> linarith

/-- **Item 6 (rung D1's deliverable).** `LowerBoundD` implies formal-conjectures' `divisor_error_hardy`
statement. -/
theorem divisor_error_hardy_of_lowerBound (hL : LowerBoundD) :
    ¬ (divisorError =o[atTop] fun x => x ^ ((1 : ℝ) / 4)) := by
  intro ho
  have hO : QuarterBigO := ho.isBigO
  obtain ⟨c, hc, hev⟩ := hL
  set A : ℝ := ‖(2 * (eulerMascheroniConstant : ℂ) - 1)‖
  set K : ℝ := 4 * (2 + A) ^ 2
  have hT := tendsto_eps_mul_integral ho
  have hT2 : Tendsto (fun ε : ℝ => 2 * (ε * ∫ t : ℝ, ‖G (((1 / 4 + ε : ℝ)) + t * I)‖ ^ 2) +
      2 * K * π * ε) (𝓝[>] 0) (𝓝 0) := by
    have h2 : Tendsto (fun ε : ℝ => 2 * K * π * ε) (𝓝[>] 0) (𝓝 0) := by
      have := (tendsto_id (x := 𝓝[>] (0 : ℝ))).mono_right nhdsWithin_le_nhds |>.const_mul (2 * K * π)
      simpa using this
    simpa using (hT.const_mul 2).add h2
  have hsmall := hT2.eventually_lt_const hc
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < 1 / 4 :=
    (eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)).and
      (nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num)))
  obtain ⟨ε, hε1, hε2, hε0, hε14⟩ := (hev.and (hsmall.and hpos)).exists
  have hε2' : 2 * (ε * ∫ t : ℝ, ‖G (((1 / 4 + ε : ℝ)) + t * I)‖ ^ 2) + 2 * K * π * ε < c := hε2
  set Z : ℝ → ℝ := fun t => ‖riemannZeta (1 / 4 + (ε : ℂ) + t * I) ^ 2 / (1 / 4 + (ε : ℂ) + t * I)‖ ^ 2
  have hσ : (1 : ℝ) / 4 < 1 / 4 + ε := by linarith
  obtain ⟨hGi, -⟩ := plancherel_G hO hσ
  have hs : ∀ t : ℝ, ((1 / 4 + ε : ℝ) : ℂ) + t * I = 1 / 4 + ε + t * I := fun t => by push_cast; ring
  have key : ∀ t : ℝ, t ≠ 0 →
      Z t ≤ 2 * ‖G (((1 / 4 + ε : ℝ)) + t * I)‖ ^ 2 + 2 * (K * (1 + t ^ 2)⁻¹) := by
    intro t ht
    have hre : 1 / 4 < (((1 / 4 + ε : ℝ) : ℂ) + t * I).re := by simp; linarith
    have him : (((1 / 4 + ε : ℝ) : ℂ) + t * I).im ≠ 0 := by simpa using ht
    have hGe := G_eq_of_im_ne_zero hO hre him
    have hZ : riemannZeta (1 / 4 + (ε : ℂ) + t * I) ^ 2 / (1 / 4 + (ε : ℂ) + t * I) =
        G (((1 / 4 + ε : ℝ)) + t * I) + P (((1 / 4 + ε : ℝ)) + t * I) := by
      rw [← hs t, hGe]; ring
    have hPb := norm_P_sq_le (σ := 1 / 4 + ε) (t := t) (by linarith)
    have hK : K * (1 + t ^ 2)⁻¹ = 4 * (2 + A) ^ 2 * (1 + t ^ 2)⁻¹ := rfl
    simp only [Z, hZ]
    set g := ‖G (((1 / 4 + ε : ℝ)) + t * I)‖
    set p := ‖P (((1 / 4 + ε : ℝ)) + t * I)‖
    have hadd : ‖G (((1 / 4 + ε : ℝ)) + t * I) + P (((1 / 4 + ε : ℝ)) + t * I)‖ ≤ g + p :=
      norm_add_le _ _
    have h0 : 0 ≤ g := norm_nonneg _
    have h1 : 0 ≤ p := norm_nonneg _
    have h2 : ‖G (((1 / 4 + ε : ℝ)) + t * I) + P (((1 / 4 + ε : ℝ)) + t * I)‖ ^ 2 ≤ (g + p) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hadd 2
    nlinarith [sq_nonneg (g - p)]
  have hZc : Continuous Z := by
    have hsc : Continuous fun t : ℝ => (1 / 4 + ε + t * I : ℂ) := by fun_prop
    have hζ : Continuous fun t : ℝ => riemannZeta (1 / 4 + ε + t * I) := by
      refine continuous_iff_continuousAt.mpr fun t => ?_
      exact ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => (1 / 4 + ε + t * I : ℂ))
        (differentiableAt_riemannZeta (line_ne hε0 hε14).2).continuousAt hsc.continuousAt
    exact ((hζ.pow 2).div hsc fun t => (line_ne hε0 hε14).1).norm.pow 2
  have hmaj : Integrable fun t : ℝ =>
      2 * ‖G (((1 / 4 + ε : ℝ)) + t * I)‖ ^ 2 + 2 * (K * (1 + t ^ 2)⁻¹) :=
    (hGi.const_mul 2).add ((integrable_inv_one_add_sq.const_mul K).const_mul 2)
  have hae : ∀ᵐ t ∂(volume : Measure ℝ),
      Z t ≤ 2 * ‖G (((1 / 4 + ε : ℝ)) + t * I)‖ ^ 2 + 2 * (K * (1 + t ^ 2)⁻¹) :=
    (Measure.ae_ne volume 0).mono fun t ht => key t ht
  have hZi : Integrable Z := hmaj.mono' hZc.aestronglyMeasurable
    (hae.mono fun t ht => by rw [Real.norm_of_nonneg (by positivity)]; exact ht)
  have hle : ∫ t, Z t ≤ 2 * (∫ t : ℝ, ‖G (((1 / 4 + ε : ℝ)) + t * I)‖ ^ 2) + 2 * K * π := by
    have := integral_mono_of_nonneg (Eventually.of_forall fun t => by positivity) hmaj hae
    rw [integral_add (hGi.const_mul 2) ((integrable_inv_one_add_sq.const_mul K).const_mul 2),
      integral_const_mul, integral_const_mul, integral_const_mul, integral_univ_inv_one_add_sq] at this
    linarith
  have hc' := hε1 hZi
  have : ε * ∫ t, Z t ≤ ε * (2 * (∫ t : ℝ, ‖G (((1 / 4 + ε : ℝ)) + t * I)‖ ^ 2) + 2 * K * π) :=
    mul_le_mul_of_nonneg_left hle hε0.le
  have hcZ : c ≤ ε * ∫ t, Z t := hc'
  nlinarith

end DirichletDivisorProblem.HardyD1
end

end
-- ===== end HardyOmegaFC.Plancherel =====

-- ===== from HardyOmegaFC.Vendor.HeatFlowStirling =====
section

/-!
# Heat-flow D4d-2: an explicit vertical Stirling bound, uniform in the real part

HB (arXiv:2610.12803, main.tex:300-319, eq. (vertical-stirling)): for `v₀ = |Im z| > 1`,

  `Γ(z) = exp((z − 1/2) Log z − z + ½ log(2π) + θ(z))`,   `|θ(z)| < 1/(12(v₀ − 1))`,

uniformly in `Re z`, including its unbounded negative tail. HB get `θ` from fourth-order Euler-Maclaurin
on `Re z > 0` and continue it analytically. Here no continuation is needed:

* `θ(z) := 1/(12z) + Σ_{k≥0} h(z+k)`, where `g(w) = (w + 1/2)(Log(w+1) − Log w) − 1` (Gudermann's term)
  and `h(w) = g(w) − (1/(12w) − 1/(12(w+1))) = −(1/3) ∫₀¹ B₃(u)/(w+u)³ du` (`hT_eq_integral`, by an explicit
  antiderivative), so `θ = Σ g(z+k)` (third-order Euler-Maclaurin, one interval at a time).
* `|B₃| ≤ 1/16` on `[0,1]` and `∫ ((a+u)² + v²)^{−3/2} du` telescopes through `φ_v(s) = s/(v²√(s²+v²))`, so
  `‖θ(z)‖ ≤ 1/(12|v|) + 1/(24v²)` for every `z` with `v = Im z ≠ 0` (`norm_theta_le`), which is
  `< 1/(12(|v| − 1))` once `|v| > 1` (`norm_theta_lt`, HB's displayed bound).
* `Γ(z) = exp(...)` (`Gamma_eq_exp`) for every `z` off the real axis: summation by parts turns Euler's limit
  `Γ(z) = lim n^z n!/∏_{j≤n}(z+j)` (Mathlib `GammaSeq_tendsto_Gamma`) into the partial sums of `θ`, plus
  `log n! − (n+1/2) log n + n → ½ log(2π)` (Mathlib's Stirling) and `(z+n+1/2)(Log(z+n) − log n) → z`.

HB's intermediate display `|θ| ≤ 1/(12v₀) + (1/360 + π/240)/v₀³` (fourth order) is NOT proved here; only the
conclusion `|θ| < 1/(12(v₀ − 1))` that HB carry forward, and the weaker-by-one-order `1/(12|v|) + 1/(24v²)`.
`θ` here is a function (not just an existential), equal to HB's `θ` on the upper half-plane by uniqueness of
the continued `log Γ` branch, but that identification is not stated. `vertical_stirling` is HB's statement.

No hypotheses. Imports Mathlib only.
-/

open Complex Filter Topology Set MeasureTheory intervalIntegral
open scoped Real Nat

namespace HardyOmegaFC.Vendor.Stirling

/-- The third Bernoulli polynomial `B₃(u) = u³ − 3u²/2 + u/2`. -/
noncomputable def B3 (u : ℝ) : ℝ := u ^ 3 - 3 / 2 * u ^ 2 + 1 / 2 * u

lemma abs_B3_le {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : |B3 u| ≤ 1 / 16 := by
  unfold B3
  have h01 := mul_nonneg h0 (sub_nonneg.2 h1)
  rw [abs_le]; constructor <;>
    nlinarith [mul_nonneg h01 (sq_nonneg (u - 1 / 2)), sq_nonneg (u - 1 / 2), mul_nonneg h0 h01,
      mul_nonneg (sub_nonneg.2 h1) h01]

/-- Gudermann's term `g(w) = (w + 1/2)(Log(w+1) − Log w) − 1`. -/
noncomputable def gT (w : ℂ) : ℂ := (w + 1 / 2) * (log (w + 1) - log w) - 1

/-- `g(w)` minus its telescoping main part `1/(12w) − 1/(12(w+1))`. -/
noncomputable def hT (w : ℂ) : ℂ := gT w - (1 / (12 * w) - 1 / (12 * (w + 1)))

lemma slit {w : ℂ} (hw : w.im ≠ 0) (u : ℝ) : w + u ∈ slitPlane := by
  rw [mem_slitPlane_iff]; right; simpa using hw

lemma ne0 {w : ℂ} (hw : w.im ≠ 0) (u : ℝ) : w + (u : ℂ) ≠ 0 := slitPlane_ne_zero (slit hw u)

/-- An antiderivative of `B₃(u)/(w+u)³` in `t = u`. -/
noncomputable def prim (w t : ℂ) : ℂ :=
  t + (-3 * (w + 1 / 2)) * log (w + t) - (3 * w ^ 2 + 3 * w + 1 / 2) * (w + t)⁻¹
    + (w * (w + 1) * (w + 1 / 2) / 2) * ((w + t) ^ 2)⁻¹

lemma hasDerivAt_prim {w : ℂ} (hw : w.im ≠ 0) (u : ℝ) :
    HasDerivAt (fun u : ℝ => prim w u) ((B3 u : ℂ) / (w + u) ^ 3) u := by
  have h0 := ne0 hw u
  have hl : HasDerivAt (fun t : ℂ => w + t) 1 (u : ℂ) := (hasDerivAt_id _).const_add w
  have h2 := (hl.clog (slit hw u)).const_mul (-3 * (w + 1 / 2))
  have h3 := (hl.inv h0).const_mul (3 * w ^ 2 + 3 * w + 1 / 2)
  have h4 := ((hl.pow 2).inv (pow_ne_zero 2 h0)).const_mul (w * (w + 1) * (w + 1 / 2) / 2)
  have H := (((hasDerivAt_id (u : ℂ)).add h2).sub h3).add h4
  have H' := H.comp_ofReal
  convert H' using 1
  · funext y; simp only [prim, Pi.add_apply, Pi.sub_apply, Pi.inv_apply, Pi.pow_apply, id]
  · simp only [B3, Pi.pow_apply]; push_cast; field_simp; ring

lemma continuous_integrand {w : ℂ} (hw : w.im ≠ 0) :
    Continuous fun u : ℝ => (B3 u : ℂ) / (w + u) ^ 3 := by
  refine Continuous.div ?_ (by fun_prop) (fun u => pow_ne_zero 3 (ne0 hw u))
  unfold B3; push_cast; fun_prop

lemma hT_eq_integral {w : ℂ} (hw : w.im ≠ 0) :
    hT w = -(1 / 3) * ∫ u in (0 : ℝ)..1, (B3 u : ℂ) / (w + u) ^ 3 := by
  rw [integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_prim hw u)
    ((continuous_integrand hw).intervalIntegrable _ _)]
  have hw0 : w ≠ 0 := by simpa using ne0 hw 0
  have hw1 : w + 1 ≠ 0 := by simpa using ne0 hw 1
  simp only [hT, gT, prim, ofReal_one, ofReal_zero, add_zero]
  field_simp
  ring

/-- `φ_v(s) = s / (v² √(s² + v²))`, an antiderivative of `(s² + v²)^{-3/2}`. -/
noncomputable def phi (v s : ℝ) : ℝ := s / (v ^ 2 * √(s ^ 2 + v ^ 2))

lemma hasDerivAt_phi {v : ℝ} (hv : v ≠ 0) (s : ℝ) :
    HasDerivAt (phi v) (1 / ((s ^ 2 + v ^ 2) * √(s ^ 2 + v ^ 2))) s := by
  have hq : 0 < s ^ 2 + v ^ 2 := by positivity
  have hr : 0 < √(s ^ 2 + v ^ 2) := Real.sqrt_pos.2 hq
  have hs : HasDerivAt (fun s : ℝ => s ^ 2 + v ^ 2) (2 * s) s := by
    simpa using (hasDerivAt_pow 2 s).add_const (v ^ 2)
  have H := (hasDerivAt_id s).div ((hs.sqrt hq.ne').const_mul (v ^ 2))
    (by positivity)
  have hsq := Real.sq_sqrt hq.le
  refine (H.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  · symm
    simp only [id]
    rw [div_eq_div_iff (by positivity) (by positivity)]
    field_simp
    rw [hsq]; ring
  all_goals simp [phi]

lemma abs_phi_le {v : ℝ} (hv : v ≠ 0) (s : ℝ) : |phi v s| ≤ 1 / v ^ 2 := by
  have hq : 0 < s ^ 2 + v ^ 2 := by positivity
  have hr : 0 < √(s ^ 2 + v ^ 2) := Real.sqrt_pos.2 hq
  have hv2 : 0 < v ^ 2 := by positivity
  have habs : |s| ≤ √(s ^ 2 + v ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith)
  rw [phi, abs_div, abs_of_pos (by positivity : 0 < v ^ 2 * √(s ^ 2 + v ^ 2)), div_le_div_iff₀
    (by positivity) hv2]
  nlinarith

lemma norm_integrand_le {w : ℂ} (hw : w.im ≠ 0) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    ‖(B3 u : ℂ) / (w + u) ^ 3‖ ≤ 1 / 16 * (1 / (((w.re + u) ^ 2 + w.im ^ 2)
      * √((w.re + u) ^ 2 + w.im ^ 2))) := by
  have hq : 0 < (w.re + u) ^ 2 + w.im ^ 2 := by positivity
  have hn : ‖w + (u : ℂ)‖ = √((w.re + u) ^ 2 + w.im ^ 2) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]; simp
  have hcube : ‖w + (u : ℂ)‖ ^ 3 = ((w.re + u) ^ 2 + w.im ^ 2) * √((w.re + u) ^ 2 + w.im ^ 2) := by
    rw [hn, pow_succ, Real.sq_sqrt hq.le]
  rw [norm_div, norm_pow, hcube, Complex.norm_real, Real.norm_eq_abs, div_eq_mul_one_div (|B3 u|)]
  gcongr
  exact abs_B3_le hu.1 hu.2

/-- The per-term bound `‖h(w)‖ ≤ (φ_v(a+1) − φ_v(a))/48`, `a = Re w`, `v = Im w`. -/
lemma norm_hT_le {w : ℂ} (hw : w.im ≠ 0) :
    ‖hT w‖ ≤ 1 / 48 * (phi w.im (w.re + 1) - phi w.im w.re) := by
  rw [hT_eq_integral hw, norm_mul]
  have hb : ∀ u : ℝ, 0 < (w.re + u) ^ 2 + w.im ^ 2 := fun u => by positivity
  have hcont : Continuous fun u : ℝ => 1 / (((w.re + u) ^ 2 + w.im ^ 2) * √((w.re + u) ^ 2 + w.im ^ 2)) := by
    refine Continuous.div continuous_const (by fun_prop) (fun u => ?_)
    have := hb u; positivity
  have hI : ∫ u in (0 : ℝ)..1, 1 / (((w.re + u) ^ 2 + w.im ^ 2) * √((w.re + u) ^ 2 + w.im ^ 2))
      = phi w.im (w.re + 1) - phi w.im w.re := by
    rw [integral_eq_sub_of_hasDerivAt (f := fun u => phi w.im (w.re + u))
      (fun u _ => ((hasDerivAt_phi hw (w.re + u)).comp u ((hasDerivAt_id u).const_add w.re)).congr_deriv
        (by simp)) (hcont.intervalIntegrable _ _)]
    simp
  calc ‖-(1 / 3 : ℂ)‖ * ‖∫ u in (0 : ℝ)..1, (B3 u : ℂ) / (w + u) ^ 3‖
      ≤ 1 / 3 * ∫ u in (0 : ℝ)..1, ‖(B3 u : ℂ) / (w + u) ^ 3‖ := by
        gcongr
        · norm_num
        · exact intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ 1 / 3 * ∫ u in (0 : ℝ)..1, 1 / 16 * (1 / (((w.re + u) ^ 2 + w.im ^ 2)
          * √((w.re + u) ^ 2 + w.im ^ 2))) := by
        gcongr
        refine intervalIntegral.integral_mono_on zero_le_one
          ((continuous_integrand hw).norm.intervalIntegrable _ _)
          ((hcont.const_mul _).intervalIntegrable _ _) (fun u hu => norm_integrand_le hw hu)
    _ = 1 / 48 * (phi w.im (w.re + 1) - phi w.im w.re) := by
        rw [intervalIntegral.integral_const_mul, hI]; ring

lemma norm_hT_add_le {z : ℂ} (hz : z.im ≠ 0) (k : ℕ) :
    ‖hT (z + k)‖ ≤ 1 / 48 * (phi z.im (z.re + (k + 1 : ℕ)) - phi z.im (z.re + k)) := by
  have hw : (z + k).im ≠ 0 := by simpa using hz
  have := norm_hT_le hw
  simp only [add_re, natCast_re, add_im, natCast_im, add_zero] at this
  push_cast; convert this using 3; ring_nf

lemma sum_norm_hT_le {z : ℂ} (hz : z.im ≠ 0) (n : ℕ) :
    ∑ k ∈ Finset.range n, ‖hT (z + k)‖ ≤ 1 / (24 * z.im ^ 2) := by
  calc ∑ k ∈ Finset.range n, ‖hT (z + k)‖
      ≤ ∑ k ∈ Finset.range n, 1 / 48 * (phi z.im (z.re + (k + 1 : ℕ)) - phi z.im (z.re + k)) :=
        Finset.sum_le_sum fun k _ => norm_hT_add_le hz k
    _ = 1 / 48 * (phi z.im (z.re + n) - phi z.im (z.re + (0 : ℕ))) := by
        rw [← Finset.mul_sum, Finset.sum_range_sub (fun k : ℕ => phi z.im (z.re + k))]
    _ ≤ 1 / 48 * (1 / z.im ^ 2 + 1 / z.im ^ 2) := by
        have h1 := abs_phi_le hz (z.re + n)
        have h2 := abs_phi_le hz (z.re + (0 : ℕ))
        rw [abs_le] at h1 h2
        gcongr; linarith
    _ = 1 / (24 * z.im ^ 2) := by
        have : z.im ^ 2 ≠ 0 := by positivity
        field_simp; ring

lemma summable_hT {z : ℂ} (hz : z.im ≠ 0) : Summable fun k : ℕ => hT (z + k) :=
  Summable.of_norm (summable_of_sum_range_le (fun _ => norm_nonneg _) (sum_norm_hT_le hz))

lemma norm_tsum_hT_le {z : ℂ} (hz : z.im ≠ 0) : ‖∑' k : ℕ, hT (z + k)‖ ≤ 1 / (24 * z.im ^ 2) :=
  (norm_tsum_le_tsum_norm (summable_of_sum_range_le (fun _ => norm_nonneg _) (sum_norm_hT_le hz))).trans
    (Real.tsum_le_of_sum_range_le (fun _ => norm_nonneg _) (sum_norm_hT_le hz))

/-- The Stirling remainder `θ(z) = 1/(12z) + Σ_{k≥0} h(z+k)` (equal to Gudermann's series `Σ g(z+k)`). -/
noncomputable def theta (z : ℂ) : ℂ := 1 / (12 * z) + ∑' k : ℕ, hT (z + k)

/-- Explicit bound, every real part: `‖θ(z)‖ ≤ 1/(12|Im z|) + 1/(24 (Im z)²)`. -/
theorem norm_theta_le {z : ℂ} (hz : z.im ≠ 0) :
    ‖theta z‖ ≤ 1 / (12 * |z.im|) + 1 / (24 * z.im ^ 2) := by
  have hz0 : z ≠ 0 := fun h => hz (by simp [h])
  refine (norm_add_le _ _).trans (add_le_add ?_ (norm_tsum_hT_le hz))
  rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat]
  gcongr
  exact Complex.abs_im_le_norm z

/-- HB main.tex (eq:vertical-stirling): `‖θ(z)‖ < 1/(12(v₀ − 1))` for `v₀ = |Im z| > 1`. -/
theorem norm_theta_lt {z : ℂ} (hz : 1 < |z.im|) : ‖theta z‖ < 1 / (12 * (|z.im| - 1)) := by
  have hz0 : z.im ≠ 0 := fun h => by simp [h] at hz; linarith
  refine (norm_theta_le hz0).trans_lt ?_
  set v := |z.im| with hv
  have hsq : z.im ^ 2 = v ^ 2 := (sq_abs _).symm
  rw [hsq]
  have hv1 : 0 < v - 1 := by linarith
  have hv0 : 0 < v := by linarith
  rw [div_add_div _ _ (by positivity) (by positivity), div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos hv0 hv1, mul_pos (mul_pos hv0 hv0) hv1]

/-! ### `Γ(z) = exp((z − 1/2) Log z − z + log(2π)/2 + θ(z))` from Euler's limit -/

/-- Summation by parts: `Σ_{j≤n} Log(z+j) = (z+n+1/2) Log(z+n) − (z−1/2) Log z − n − Σ_{k<n} g(z+k)`. -/
lemma sum_log_eq (z : ℂ) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), log (z + j) =
      (z + n + 1 / 2) * log (z + n) - (z - 1 / 2) * log z - n - ∑ k ∈ Finset.range n, gT (z + k) := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, gT]
    push_cast
    rw [add_assoc z (n : ℂ) 1]
    ring

lemma GammaSeq_eq_exp {z : ℂ} (hz : z.im ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    GammaSeq z n = cexp (z * (Real.log n : ℂ) + (Real.log (n ! : ℕ) : ℂ)
      - ∑ j ∈ Finset.range (n + 1), log (z + j)) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hj : ∀ j : ℕ, z + j ≠ 0 := fun j => by simpa using ne0 hz j
  rw [GammaSeq, exp_sub, exp_add, exp_sum, cpow_def_of_ne_zero hn', natCast_log, natCast_log,
    exp_log (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n))]
  congr 1
  · rw [mul_comm z]
  · exact Finset.prod_congr rfl fun j _ => (exp_log (hj j)).symm

/-- `log n! − (n + 1/2) log n + n → log(2π)/2` (Mathlib's Stirling). -/
lemma tendsto_log_factorial :
    Tendsto (fun n : ℕ => Real.log (n ! : ℕ) - (n + 1 / 2) * Real.log n + n) atTop
      (𝓝 (Real.log (2 * π) / 2)) := by
  have h := ((Real.continuousAt_log (by positivity : √π ≠ 0)).tendsto.comp
    Stirling.tendsto_stirlingSeq_sqrt_pi).add_const (1 / 2 * Real.log 2)
  have hlim : Real.log √π + 1 / 2 * Real.log 2 = Real.log (2 * π) / 2 := by
    rw [Real.log_sqrt (by positivity), Real.log_mul (by norm_num) (by positivity)]; ring
  rw [hlim] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Function.comp, Stirling.log_stirlingSeq_formula]
  rw [Real.log_mul (by norm_num) hn0.ne', Real.log_div hn0.ne' (Real.exp_pos 1).ne', Real.log_exp]
  ring

/-- `(z + n + 1/2)(Log(z+n) − log n) → z`. -/
lemma tendsto_log_shift {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun n : ℕ => (z + n + 1 / 2) * (log (z + n) - (Real.log n : ℂ))) atTop (𝓝 z) := by
  have hz0 : z ≠ 0 := by simpa using ne0 hz 0
  have hu : Tendsto (fun n : ℕ => z / n) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_const_div_atTop_nhds_zero_nat z, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact div_ne_zero hz0 (Nat.cast_ne_zero.2 (by omega))
  have hd : HasDerivAt log 1 1 := by
    simpa using hasDerivAt_log (by simp : (1 : ℂ) ∈ slitPlane)
  have hs := hd.tendsto_slope_zero.comp hu
  have hc : Tendsto (fun n : ℕ => z + z * (z + 1 / 2) * (1 / (n : ℂ))) atTop (𝓝 z) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (1 : ℂ)).const_mul (z * (z + 1 / 2)) |>.const_add z
  have := hc.mul hs
  rw [mul_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h1 : (1 : ℂ) + z / n ≠ 0 := by
    have := ne0 hz n
    contrapose! this
    have : z + n = n * (1 + z / n) := by field_simp; ring
    simp_all
  have hsplit : log (z + n) = (Real.log n : ℂ) + log (1 + z / n) := by
    rw [← log_ofReal_mul hn0 h1]; congr 1; push_cast; field_simp; ring
  simp only [Function.comp, log_one, sub_zero, smul_eq_mul, hsplit, add_sub_cancel_left]
  field_simp
  ring

/-- The partial Gudermann sums converge to `θ(z)`. -/
lemma tendsto_sum_gT {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, gT (z + k)) atTop (𝓝 (theta z)) := by
  have hj : ∀ j : ℕ, z + j ≠ 0 := fun j => by simpa using ne0 hz j
  have hf : Tendsto (fun n : ℕ => 1 / (12 * (z + n))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (z / n + 1)⁻¹ * (1 / (n : ℂ)) / 12) atTop (𝓝 ((0 + 1)⁻¹ * 0 / 12)) :=
      ((((tendsto_const_div_atTop_nhds_zero_nat z).add_const 1).inv₀ (by norm_num)).mul
        (tendsto_const_div_atTop_nhds_zero_nat (1 : ℂ))).div_const 12
    simp only [zero_add, inv_one, mul_zero, zero_div] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have h2 : z / n + 1 ≠ 0 := by
      intro h; apply hj n; field_simp at h; linear_combination h
    field_simp
  have hS := (summable_hT hz).hasSum.tendsto_sum_nat
  have := ((hf.const_sub (1 / (12 * z))).add hS)
  simp only [sub_zero] at this
  refine this.congr' (Eventually.of_forall fun n => ?_)
  have hg : ∀ k : ℕ, gT (z + (k : ℂ)) = (1 / (12 * (z + (k : ℂ))) - 1 / (12 * (z + ((k + 1 : ℕ) : ℂ))))
      + hT (z + (k : ℂ)) := by
    intro k; simp only [hT]; push_cast; rw [add_assoc]; ring
  have hsum : ∑ k ∈ Finset.range n, gT (z + (k : ℂ)) = (1 / (12 * z) - 1 / (12 * (z + (n : ℂ))))
      + ∑ k ∈ Finset.range n, hT (z + (k : ℂ)) := by
    rw [Finset.sum_congr rfl (fun k _ => hg k), Finset.sum_add_distrib,
      Finset.sum_range_sub' (fun k : ℕ => 1 / (12 * (z + (k : ℂ))))]
    simp
  exact hsum.symm

/-- **Stirling's formula with the Gudermann remainder**, valid for every `z` off the real axis:
`Γ(z) = exp((z − 1/2) Log z − z + log(2π)/2 + θ(z))`. -/
theorem Gamma_eq_exp {z : ℂ} (hz : z.im ≠ 0) :
    Gamma z = cexp ((z - 1 / 2) * log z - z + (Real.log (2 * π) / 2 : ℝ) + theta z) := by
  have hE : Tendsto (fun n : ℕ => (z - 1 / 2) * log z + ∑ k ∈ Finset.range n, gT (z + k)
      + ((Real.log (n ! : ℕ) - (n + 1 / 2) * Real.log n + n : ℝ) : ℂ)
      - (z + n + 1 / 2) * (log (z + n) - (Real.log n : ℂ))) atTop
      (𝓝 ((z - 1 / 2) * log z + theta z + ((Real.log (2 * π) / 2 : ℝ) : ℂ) - z)) :=
    ((((tendsto_sum_gT hz).const_add _).add
      ((continuous_ofReal.tendsto _).comp tendsto_log_factorial)).sub (tendsto_log_shift hz))
  have hG : Tendsto (GammaSeq z) atTop
      (𝓝 (cexp ((z - 1 / 2) * log z + theta z + ((Real.log (2 * π) / 2 : ℝ) : ℂ) - z))) := by
    refine ((continuous_exp.tendsto _).comp hE).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [GammaSeq_eq_exp hz (by omega), Function.comp, sum_log_eq]
    congr 1
    push_cast
    ring
  rw [tendsto_nhds_unique (GammaSeq_tendsto_Gamma z) hG]
  congr 1
  ring

/-- HB arXiv:2610.12803 main.tex:300-319, eq. (vertical-stirling), in the form it is used: for
`v₀ = |Im z| > 1` and every real part, `Γ(z) = exp((z − 1/2) Log z − z + log(2π)/2 + θ)` with
`|θ| < 1/(12(v₀ − 1))`. -/
theorem vertical_stirling {z : ℂ} (hz : 1 < |z.im|) :
    ∃ θ : ℂ, ‖θ‖ < 1 / (12 * (|z.im| - 1)) ∧
      Gamma z = cexp ((z - 1 / 2) * log z - z + (Real.log (2 * π) / 2 : ℝ) + θ) := by
  have hz0 : z.im ≠ 0 := fun h => by simp [h] at hz; linarith
  exact ⟨theta z, norm_theta_lt hz, Gamma_eq_exp hz0⟩

end HardyOmegaFC.Vendor.Stirling

end
-- ===== end HardyOmegaFC.Vendor.HeatFlowStirling =====

-- ===== from HardyOmegaFC.Chi =====
section

/-!
# Hardy Ω, rung D2: the functional-equation factor `χ` is large left of the critical line

With Mathlib's functional equation `riemannZeta_one_sub` (applied at `1 − s`),

  `ζ(s) = χ(s) ζ(1 − s)`,   `χ(s) = 2 (2π)^{s−1} Γ(1 − s) cos(π(1 − s)/2)`,

and for `0 ≤ σ = Re s ≤ 1/2`, `|t| = |Im s| ≥ 2`:

  `‖χ(s)‖ ≥ |t|^{1/2−σ} / (4π e²)`                                   (`norm_chi_ge`),

so `‖ζ(s)‖ ≥ |t|^{1/2−σ}/(4π e²) · ‖ζ(1 − s)‖` (`norm_zeta_ge`) and, in the shape rung D4 integrates,
`‖ζ(s)²/s‖² ≥ |t|^{−4σ} / (2 (4π e²)⁴) · ‖ζ(1 − s)‖⁴` (`norm_zeta_sq_div_sq_ge`); at `σ = 1/4 + ε` the
exponent is `−1 − 4ε`.

Pieces: `‖Γ(x + iy)‖ ≥ e^{−2} |y|^{x−1/2} e^{−π|y|/2}` for `x ∈ [1/2, 1]`, `|y| ≥ 2` from the vendored explicit
vertical Stirling formula (`HardyOmegaFC.Vendor.Stirling.vertical_stirling`, remainder `< 1/(12(|y| − 1))`), using
only `|y · arg z| ≤ |y| π/2` (so no case split on the sign of `y`); `‖cos w‖ ≥ (e^{|Im w|} − 1)/2` by the reverse
triangle inequality; `‖(2π)^{s−1}‖ = (2π)^{σ−1} ≥ 1/(2π)`. Constants are not sharp. No hypotheses beyond the
stated ranges; Mathlib plus the vendored file only.
-/

open Complex
open scoped Real

namespace DirichletDivisorProblem.HardyD2

/-- The functional-equation factor in Mathlib's normalisation: `ζ(s) = χ(s) ζ(1 − s)` (`zeta_eq_chi_mul`). -/
noncomputable def chi (s : ℂ) : ℂ :=
  2 * (2 * π) ^ (s - 1) * Gamma (1 - s) * cos (π * (1 - s) / 2)

/-- `ζ(s) = χ(s) ζ(1 − s)` off the real axis (Mathlib `riemannZeta_one_sub` at `1 − s`). -/
theorem zeta_eq_chi_mul {s : ℂ} (hs : s.im ≠ 0) : riemannZeta s = chi s * riemannZeta (1 - s) := by
  have h1 : ∀ n : ℕ, (1 - s) ≠ -(n : ℂ) := by
    intro n h
    apply hs
    have := congrArg Complex.im h
    simpa using this
  have h2 : (1 - s) ≠ 1 := by
    intro h
    apply hs
    have : s = 0 := by linear_combination -h
    simp [this]
  have := riemannZeta_one_sub h1 h2
  rw [sub_sub_cancel] at this
  rw [this, chi, neg_sub]

/-- Lower bound for `Γ` on vertical lines, real part in `[1/2, 1]`, from the explicit vertical Stirling formula. -/
theorem norm_Gamma_ge {z : ℂ} (hx0 : 1 / 2 ≤ z.re) (hx1 : z.re ≤ 1) (hy : 2 ≤ |z.im|) :
    Real.exp (-2) * |z.im| ^ (z.re - 1 / 2) * Real.exp (-(π * |z.im| / 2)) ≤ ‖Gamma z‖ := by
  obtain ⟨θ, hθ, hG⟩ := HardyOmegaFC.Vendor.Stirling.vertical_stirling (z := z) (by linarith)
  have hy0 : 0 < |z.im| := by linarith
  rw [hG, Complex.norm_exp]
  have hre : ((z - 1 / 2) * log z - z + ((Real.log (2 * π) / 2 : ℝ) : ℂ) + θ).re
      = (z.re - 1 / 2) * Real.log ‖z‖ - z.im * arg z - z.re + Real.log (2 * π) / 2 + θ.re := by
    simp [Complex.mul_re, Complex.log_re, Complex.log_im]
  rw [hre, Real.rpow_def_of_pos hy0, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  -- the four estimates
  have hlog : Real.log |z.im| ≤ Real.log ‖z‖ :=
    Real.log_le_log hy0 (Complex.abs_im_le_norm z)
  have harg : z.im * arg z ≤ |z.im| * (π / 2) := by
    have h1 : |arg z| ≤ π / 2 := Complex.abs_arg_le_pi_div_two_iff.mpr (by linarith)
    calc z.im * arg z ≤ |z.im * arg z| := le_abs_self _
      _ = |z.im| * |arg z| := abs_mul _ _
      _ ≤ |z.im| * (π / 2) := by gcongr
  have hc : 0 ≤ Real.log (2 * π) / 2 := by
    have : (1 : ℝ) ≤ 2 * π := by nlinarith [Real.pi_gt_three]
    have := Real.log_nonneg this
    linarith
  have hθre : -(1 / 12 : ℝ) ≤ θ.re := by
    have h1 : -‖θ‖ ≤ θ.re := by
      have := Complex.abs_re_le_norm θ
      have := neg_abs_le θ.re
      linarith
    have h2 : 1 / (12 * (|z.im| - 1)) ≤ 1 / 12 := by
      apply one_div_le_one_div_of_le (by norm_num)
      linarith
    linarith
  have hmul : (z.re - 1 / 2) * Real.log |z.im| ≤ (z.re - 1 / 2) * Real.log ‖z‖ :=
    mul_le_mul_of_nonneg_left hlog (by linarith)
  nlinarith

/-- `‖cos w‖ ≥ (e^{|Im w|} − 1)/2`. -/
theorem norm_cos_ge (w : ℂ) : (Real.exp |w.im| - 1) / 2 ≤ ‖cos w‖ := by
  have hcos : cos w = (cexp (w * I) + cexp (-w * I)) / 2 := Complex.cos.eq_1 w
  have ha : ‖cexp (w * I)‖ = Real.exp (-w.im) := by rw [Complex.norm_exp]; simp
  have hb : ‖cexp (-w * I)‖ = Real.exp w.im := by rw [Complex.norm_exp]; simp
  rw [hcos, norm_div, Complex.norm_ofNat]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  rcases le_total 0 w.im with h | h
  · rw [abs_of_nonneg h]
    have : ‖cexp (-w * I)‖ - ‖cexp (w * I)‖ ≤ ‖cexp (w * I) + cexp (-w * I)‖ := by
      have := norm_sub_le (cexp (w * I) + cexp (-w * I)) (cexp (w * I))
      simp only [add_sub_cancel_left] at this
      linarith
    have : Real.exp (-w.im) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [ha, hb] at *
    linarith
  · rw [abs_of_nonpos h]
    have : ‖cexp (w * I)‖ - ‖cexp (-w * I)‖ ≤ ‖cexp (w * I) + cexp (-w * I)‖ := by
      have := norm_sub_le (cexp (w * I) + cexp (-w * I)) (cexp (-w * I))
      simp only [add_sub_cancel_right] at this
      linarith
    have : Real.exp w.im ≤ 1 := Real.exp_le_one_iff.mpr h
    rw [ha, hb] at *
    linarith

/-- The constant of D2: `K = 4π e²`. -/
noncomputable def K : ℝ := 4 * π * Real.exp 2

lemma K_pos : 0 < K := by unfold K; positivity

/-- **D2.** For `0 ≤ σ ≤ 1/2` and `|t| ≥ 2`: `‖χ(σ + it)‖ ≥ |t|^{1/2−σ} / (4π e²)`. -/
theorem norm_chi_ge {s : ℂ} (hσ0 : 0 ≤ s.re) (hσ1 : s.re ≤ 1 / 2) (ht : 2 ≤ |s.im|) :
    |s.im| ^ (1 / 2 - s.re) / K ≤ ‖chi s‖ := by
  have ht0 : 0 < |s.im| := by linarith
  have h2π : (0 : ℝ) < 2 * π := by positivity
  -- the power of `2π`
  have hpow : 1 / π ≤ 2 * ‖((2 * π : ℝ) : ℂ) ^ (s - 1)‖ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos h2π]
    have : (2 * π) ^ (-1 : ℝ) ≤ (2 * π) ^ (s - 1).re := by
      apply Real.rpow_le_rpow_of_exponent_le (by nlinarith [Real.pi_gt_three])
      simp; linarith
    rw [Real.rpow_neg_one] at this
    have hπ : 0 < π := Real.pi_pos
    calc 1 / π = 2 * (2 * π)⁻¹ := by field_simp
      _ ≤ _ := by linarith
  -- Gamma
  have hG := norm_Gamma_ge (z := 1 - s) (by simp; linarith) (by simp; linarith)
    (by simpa [abs_neg] using ht)
  simp only [sub_re, one_re, sub_im, one_im, zero_sub, abs_neg] at hG
  -- cos
  have hC := norm_cos_ge (π * (1 - s) / 2)
  have him : (π * (1 - s) / 2 : ℂ).im = -(π * s.im / 2) := by simp; ring
  rw [him, abs_neg, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_two] at hC
  have hE : 2 ≤ Real.exp (π * |s.im| / 2) := by
    have := Real.add_one_le_exp (π * |s.im| / 2)
    nlinarith [Real.pi_gt_three]
  have hC' : Real.exp (π * |s.im| / 2) / 4 ≤ ‖cos (π * (1 - s) / 2)‖ := by linarith
  -- assemble
  have hnorm : ‖chi s‖ = 2 * ‖((2 * π : ℝ) : ℂ) ^ (s - 1)‖ * ‖Gamma (1 - s)‖
      * ‖cos (π * (1 - s) / 2)‖ := by
    simp only [chi, norm_mul, Complex.norm_ofNat]
    push_cast
    ring
  rw [hnorm]
  have hrp : 0 ≤ |s.im| ^ (1 - s.re - 1 / 2) := Real.rpow_nonneg (abs_nonneg _) _
  have hexp : Real.exp (-(π * |s.im| / 2)) * Real.exp (π * |s.im| / 2) = 1 := by
    rw [← Real.exp_add]; simp
  have he : (1 - s.re - 1 / 2) = 1 / 2 - s.re := by ring
  rw [he] at hG hrp
  calc |s.im| ^ (1 / 2 - s.re) / K
      = 1 / π * (Real.exp (-2) * |s.im| ^ (1 / 2 - s.re) * Real.exp (-(π * |s.im| / 2)))
          * (Real.exp (π * |s.im| / 2) / 4) := by
        unfold K
        have hπ : 0 < π := Real.pi_pos
        rw [Real.exp_neg]
        field_simp
        rw [← Real.exp_add]
        simp
    _ ≤ _ := by
        gcongr

/-- **D2, zeta form.** For `0 ≤ σ ≤ 1/2` and `|t| ≥ 2`: `‖ζ(s)‖ ≥ |t|^{1/2−σ}/(4π e²) · ‖ζ(1 − s)‖`. -/
theorem norm_zeta_ge {s : ℂ} (hσ0 : 0 ≤ s.re) (hσ1 : s.re ≤ 1 / 2) (ht : 2 ≤ |s.im|) :
    |s.im| ^ (1 / 2 - s.re) / K * ‖riemannZeta (1 - s)‖ ≤ ‖riemannZeta s‖ := by
  have hs : s.im ≠ 0 := by intro h; rw [h, abs_zero] at ht; linarith
  rw [zeta_eq_chi_mul hs, norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_chi_ge hσ0 hσ1 ht) (norm_nonneg _)

/-- **D2, D4's shape.** For `0 ≤ σ ≤ 1/2` and `|t| ≥ 2`:
`‖ζ(s)²/s‖² ≥ |t|^{−4σ} / (2 K⁴) · ‖ζ(1 − s)‖⁴` (at `σ = 1/4 + ε` the exponent is `−1 − 4ε`). -/
theorem norm_zeta_sq_div_sq_ge {s : ℂ} (hσ0 : 0 ≤ s.re) (hσ1 : s.re ≤ 1 / 2) (ht : 2 ≤ |s.im|) :
    |s.im| ^ (-4 * s.re) / (2 * K ^ 4) * ‖riemannZeta (1 - s)‖ ^ 4
      ≤ ‖riemannZeta s ^ 2 / s‖ ^ 2 := by
  have ht0 : 0 < |s.im| := by linarith
  have hs0 : s ≠ 0 := by intro h; rw [h] at ht; simp at ht; linarith
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hZ := norm_zeta_ge hσ0 hσ1 ht
  set A := |s.im| ^ (1 / 2 - s.re) / K with hA
  have hA0 : 0 ≤ A := div_nonneg (Real.rpow_nonneg (abs_nonneg _) _) K_pos.le
  -- `‖s‖² ≤ 2 t²`
  have hss : ‖s‖ ^ 2 ≤ 2 * |s.im| ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, sq_abs]
    have : |s.re| ≤ |s.im| := by rw [abs_of_nonneg hσ0]; linarith
    have h2 := sq_le_sq.mpr this
    nlinarith [h2]
  -- `A⁴ = |t|^{2−4σ}/K⁴ = |t|^{−4σ} t² / K⁴`
  have hA4 : A ^ 4 = |s.im| ^ (-4 * s.re) * |s.im| ^ 2 / K ^ 4 := by
    rw [hA, div_pow, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), ← Real.rpow_natCast (|s.im|) 2,
      ← Real.rpow_add ht0]
    congr 2
    push_cast
    ring
  rw [norm_div, norm_pow, div_pow, ← pow_mul]
  rw [le_div_iff₀ (by positivity)]
  have hZ4 : (A * ‖riemannZeta (1 - s)‖) ^ 4 ≤ ‖riemannZeta s‖ ^ (2 * 2) :=
    pow_le_pow_left₀ (mul_nonneg hA0 (norm_nonneg _)) hZ 4
  rw [mul_pow, hA4] at hZ4
  have hK4 : 0 < K ^ 4 := pow_pos K_pos 4
  have hp : 0 ≤ |s.im| ^ (-4 * s.re) := Real.rpow_nonneg (abs_nonneg _) _
  have hz4 : 0 ≤ ‖riemannZeta (1 - s)‖ ^ 4 := by positivity
  calc |s.im| ^ (-4 * s.re) / (2 * K ^ 4) * ‖riemannZeta (1 - s)‖ ^ 4 * ‖s‖ ^ 2
      ≤ |s.im| ^ (-4 * s.re) / (2 * K ^ 4) * ‖riemannZeta (1 - s)‖ ^ 4 * (2 * |s.im| ^ 2) := by
        gcongr
    _ = |s.im| ^ (-4 * s.re) * |s.im| ^ 2 / K ^ 4 * ‖riemannZeta (1 - s)‖ ^ 4 := by
        field_simp
    _ ≤ _ := hZ4

end DirichletDivisorProblem.HardyD2

end
-- ===== end HardyOmegaFC.Chi =====

end OMAPort_Divisor

-- ===== from Zeta23.FromPNTPlus.Auxiliary =====
section
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/Auxiliary.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: none besides this header (upstream has no blueprint annotations
or intra-project imports in this file).
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/
/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/

/-!
### Auxiliary lemmas
-/

lemma DifferentiableAt.comp_ofReal {e : ℂ → ℂ} {z : ℝ} (hf : DifferentiableAt ℂ e z) :
    DifferentiableAt ℝ (fun x : ℝ ↦ e x) z :=
  hf.hasDerivAt.comp_ofReal.differentiableAt

end
-- ===== end Zeta23.FromPNTPlus.Auxiliary =====

-- ===== from Zeta23.FromPNTPlus.ResidueCalcOnRectangles =====
section
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: removed the Architect blueprint tooling (import Architect,
blueprint_comment blocks, @[blueprint ...] attributes) and redirected intra-project
imports to Zeta23.FromPNTPlus.*.
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/

open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

/- An UpperUIntegral is the integral of a function over a |\_| shape. -/

/- A LowerUIntegral is the integral of a function over a |-| shape. -/

/-- A function is `HolomorphicOn` a set if it is complex
  differentiable on that set. -/
abbrev HolomorphicOn (f : ℂ → E) (s : Set ℂ) : Prop :=
    DifferentiableOn ℂ f s

/-! ## Residue calculus: residues, simple poles, and the rectangle residue theorem

The simple-pole `residue`, `sumResiduesIn`, the `HasSimplePolesOn` scaffold, and the rectangle
residue theorem `RectangleIntegral'_eq_sumResiduesIn`. Extracted from `CH2.lean` as general,
reusable contour-integration lemmas (see issue #1537). -/

-- If two functions `f g : ℂ → ℂ` agree on a `codiscreteWithin R` full set, and `φ : ℝ → ℂ` is
-- an analytic non-constant path mapping `[a,b]` into `R`, then `∫ f(φ x) dx = ∫ g(φ x) dx`.
-- (a.e. agreement along the preimage suffices for interval integrals)

-- Under `HasSimplePolesOn f U`, every point with strictly negative meromorphic order has order
-- exactly -1: the simple-pole hypothesis gives `(-1 : ℤ) ≤ order`, negativity gives `order < 0`,
-- so the only integer fitting both is -1.

-- At a simple pole `p` of `f` inside `U`, the residue of the meromorphic normal form
-- `toMeromorphicNFOn f U` equals the residue of `f`. The two functions agree on a punctured
-- neighborhood of `p` (by definition of the normal form), so their `(z - p) * ·` limits coincide.

-- Non-constancy of horizontal paths `x ↦ x + h * I`.

-- Non-constancy of vertical paths `y ↦ r + y * I`.

-- Helper for horizontal integral congruence on codiscrete set

-- Helper for vertical integral congruence on codiscrete set

-- At the boundary, `f` and its normal-form representative differ only at a discrete set
-- of poles, so their boundary integrals coincide.

-- Since no poles lie on the boundary of the rectangle, the principal part is continuous
-- on the boundary and therefore integrable.

-- The integral of a sum of simple pole terms `c p / (s - p)` along the boundary of the rectangle
-- equals the sum of the coefficients `c p` for all points `p` in the interior.

-- Splits the integral of `fNF` into the integral of its holomorphic part and its principal part.

end
-- ===== end Zeta23.FromPNTPlus.ResidueCalcOnRectangles =====

-- ===== from Zeta23.FromPNTPlus.EulerMaclaurin =====
section
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/EulerMaclaurin.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: none (verbatim copy).
New in the v4.32.2 port set: upstream split this file's content (the first-order
Euler–Maclaurin section: B1 ... sum_eq_integral_add_integral_deriv) out of
PrimeNumberTheoremAnd/Mertens.lean, where our original v4.29.0 port carried it
inside Zeta23/FromPNTPlus/Mertens.lean; that file now imports this one instead.
Added when the project moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/

/-! We prove the 1st order Euler-Maclaurin formula by specialising Abel summation and manipulating integrals. -/

open Finset Interval MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}

/-- The 1st Bernoulli function. -/
noncomputable def B1 (x : ℝ) : ℝ := x - ⌊x⌋₊ - 1 / 2

lemma aestronglyMeasurable_B1 : AEStronglyMeasurable B1 := by
  unfold B1
  fun_prop

lemma abs_B1_le_half {x : ℝ} (hx : 0 ≤ x) : |B1 x| ≤ 1 / 2 := by
  unfold B1
  refine abs_le.mpr ⟨?_, ?_⟩
  · grind [Nat.floor_le hx]
  · grind [Nat.lt_succ_floor x]

lemma integral_deriv_mul_add_const (c : 𝕜) (hab : a ≤ b) (h_int : IntervalIntegrable (deriv f) volume a b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) :
    ∫ t in a..b, (t + c) * deriv f t = (b + c) * f b - (a + c) * f a - ∫ t in a..b, f t := by
  rw [← Set.uIcc_of_le hab] at hf_diff
  have : ∀ t ∈ [[a, b]], HasDerivAt (fun (t : ℝ) ↦ t + c) 1 t := by
    intro t ht
    simp only [hasDerivAt_add_const_iff]
    convert! ContinuousLinearMap.hasDerivAt (RCLike.ofRealCLM (K := 𝕜)) using 1
    simp
  replace hf_diff := fun t ht ↦ (hf_diff t ht).hasDerivAt
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul this hf_diff (by simp) h_int]
  simp

lemma intervalIntegrable_deriv_mul_B1 (ha : 0 ≤ a) (hab : a ≤ b) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    IntervalIntegrable (fun t ↦ deriv f t * B1 t) volume a b := by
  refine IntervalIntegrable.continuousOn_mul ?_ h_cont
  rw [intervalIntegrable_iff']
  apply MeasureTheory.Measure.integrableOn_of_bounded (by simp)
    (RCLike.continuous_ofReal.comp_aestronglyMeasurable aestronglyMeasurable_B1) (M := 1 / 2)
  filter_upwards [self_mem_ae_restrict (by measurability)] with x hx
  rw [Set.uIcc_of_le hab, Set.mem_Icc] at hx
  norm_cast
  exact abs_B1_le_half (by linarith)

lemma integral_deriv_mul_floor_add_one (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∫ t in a..b, deriv f t * (⌊t⌋₊ + 1) = (b + 1 / 2) * f b - (a + 1 / 2) * f a - (∫ t in a..b, f t) - ∫ t in a..b, deriv f t * B1 t := by
  calc
  _ = ∫ t in a..b, (deriv f t * (t + 1 / 2) -deriv f t * B1 t) := by
    congr
    ext
    simp only [B1]
    push_cast
    ring
  _ = (∫ t in a..b, deriv f t * (t + 1 / 2)) - ∫ t in a..b, deriv f t * B1 t := by
    exact intervalIntegral.integral_sub (ContinuousOn.intervalIntegrable (by fun_prop)) (intervalIntegrable_deriv_mul_B1 ha hab h_cont)
  _ = _ := by
    conv => lhs; arg 1; arg 1; ext; rw [mul_comm]
    rw [integral_deriv_mul_add_const _ hab h_cont.intervalIntegrable hf_diff]

theorem sum_eq_integral_add_integral_deriv (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k =
      f a * B1 a - f b * B1 b + (∫ t in a..b, f t) + ∫ t in a..b, deriv f t * B1 t  := by
  have := sum_mul_eq_sub_sub_integral_mul (fun _ ↦ 1) ha hab hf_diff (Set.uIcc_of_le hab ▸ h_cont).integrableOn_Icc
  simp only [mul_one, sum_const, Nat.card_Icc, tsub_zero, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one] at this
  rw [this, ← intervalIntegral.integral_of_le hab]
  rw [integral_deriv_mul_floor_add_one ha hab hf_diff h_cont]
  unfold B1
  push_cast
  ring

end
-- ===== end Zeta23.FromPNTPlus.EulerMaclaurin =====

-- ===== from Zeta23.FromPNTPlus.ZetaBounds =====
section
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/ZetaBounds.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: removed the Architect blueprint tooling (import Architect,
blueprint_comment blocks, @[blueprint ...] attributes), redirected intra-project
imports to Zeta23.FromPNTPlus.*, and added a (name := ...) tag to the local notation.
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/

open Complex Topology Filter Interval Set Asymptotics

lemma div_cpow_eq_cpow_neg (a x s : ℂ) : a / x ^ s = a * x ^ (-s) := by
  rw [div_eq_mul_inv, cpow_neg]

-- Main theorem: if functions agree on a punctured set, their derivatives agree there too

/- New two theorems to be proven -/

-- Alternative cleaner proof using more direct approach

/- The set should be open so that f'(p) = O(1) for all p ∈ U -/

noncomputable def riemannZeta0 (N : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
  (- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)

/-- We use `ζ` to denote the Rieman zeta function and `ζ₀` to denote the alternative Rieman zeta
function. -/

lemma riemannZeta0_apply (N : ℕ) (s : ℂ) : riemannZeta0 N s =
    (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
    ((- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))) := by
  simp_rw [riemannZeta0, div_cpow_eq_cpow_neg]; ring

-- move near `Real.differentiableAt_rpow_const_of_ne`
lemma Real.differentiableAt_cpow_const_of_ne (s : ℂ) {x : ℝ} (xpos : 0 < x) :
    DifferentiableAt ℝ (fun (x : ℝ) ↦ (x : ℂ) ^ s) x := by
  apply DifferentiableAt.comp_ofReal (e := fun z ↦ z ^ s)
  apply DifferentiableAt.cpow (by simp) (by simp) (by simp [xpos])

lemma Complex.one_div_cpow_eq {s : ℂ} {x : ℝ} (x_ne : x ≠ 0) :
    1 / (x : ℂ) ^ s = (x : ℂ) ^ (-s) := by
  refine (eq_one_div_of_mul_eq_one_left ?_).symm
  rw [← cpow_add _ _ <| mod_cast x_ne, neg_add_cancel, cpow_zero]

lemma sum_eq_int_deriv {φ : ℝ → ℂ} {a b : ℝ} (apos : 0 ≤ a) (a_lt_b : a < b)
    (φDiff : ∀ x ∈ [[a, b]], HasDerivAt φ (deriv φ x) x)
    (derivφCont : ContinuousOn (deriv φ) [[a, b]]) :
    ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, φ n =
      (∫ x in a..b, φ x) + (⌊b⌋₊ + 1 / 2 - b) * φ b - (⌊a⌋₊ + 1 / 2 - a) * φ a
        - ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * deriv φ x := by
  rw [uIcc_of_le a_lt_b.le] at φDiff
  convert sum_eq_integral_add_integral_deriv apos a_lt_b.le (fun t ht ↦ (φDiff t ht).differentiableAt) derivφCont using 1
  unfold B1
  push_cast
  suffices ∫ (x : ℝ) in a..b, (↑⌊x⌋ + 1 / 2 - ↑x) * deriv φ x = -∫ (t : ℝ) in a..b, deriv φ t * (↑t - ↑⌊t⌋₊ - 1 / 2) by
    rw [this]
    ring_nf!
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun x hx ↦ ?_
  rw [uIcc_of_le a_lt_b.le, mem_Icc] at hx
  rw [← Int.natCast_floor_eq_floor (by linarith)]
  norm_cast
  push_cast
  ring

lemma xpos_of_uIcc {a b : ℕ} (ha : a ∈ Ioo 0 b) {x : ℝ} (x_in : x ∈ [[(a : ℝ), b]]) :
    0 < x := by
  rw [uIcc_of_le (by exact_mod_cast ha.2.le), mem_Icc] at x_in
  linarith [(by exact_mod_cast ha.1 : (0 : ℝ) < a)]

lemma ZetaSum_aux1₁ {a b : ℕ} {s : ℂ} (s_ne_one : s ≠ 1) (ha : a ∈ Ioo 0 b) :
    (∫ (x : ℝ) in a..b, 1 / (x : ℂ) ^ s) =
    (b ^ (1 - s) - a ^ (1 - s)) / (1 - s) := by
  convert integral_cpow (a := a) (b := b) (r := -s) ?_ using 1
  · refine intervalIntegral.integral_congr fun x hx ↦ one_div_cpow_eq ?_
    exact (xpos_of_uIcc ha hx).ne'
  · norm_cast; ring_nf
  · right; refine ⟨(by grind), ?_⟩
    exact fun hx ↦ (lt_self_iff_false 0).mp <| xpos_of_uIcc ha hx

lemma ZetaSum_aux1φDiff {s : ℂ} {x : ℝ} (xpos : 0 < x) :
    HasDerivAt (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) (deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) x) x := by
  exact hasDerivAt_deriv_iff.mpr <|
    DifferentiableAt.div (differentiableAt_const _)
      (Real.differentiableAt_cpow_const_of_ne s xpos) (by simp [cpow_eq_zero_iff, xpos.ne'])

lemma ZetaSum_aux1φderiv {s : ℂ} (s_ne_zero : s ≠ 0) {x : ℝ} (xpos : 0 < x) :
    deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) x = (fun (x : ℝ) ↦ -s * (x : ℂ) ^ (-(s + 1))) x := by
  let r := -s - 1
  have r_add1_ne_zero : r + 1 ≠ 0 := fun hr ↦ by simp [neg_ne_zero.mpr s_ne_zero, r] at hr
  have r_ne_neg1 : r ≠ -1 := fun hr ↦ (hr ▸ r_add1_ne_zero) <| by norm_num
  have hasDeriv := hasDerivAt_ofReal_cpow_const' xpos.ne' r_ne_neg1
  have := hasDeriv.deriv ▸ deriv_const_mul (-s) (hasDeriv).differentiableAt
  convert! this using 2
  · ext y
    by_cases y_zero : (y : ℂ) = 0
    · simp only [y_zero, ne_eq, s_ne_zero, not_false_eq_true, zero_cpow, div_zero,
      r_add1_ne_zero, zero_div, mul_zero]
    · have : (y : ℂ) ^ s ≠ 0 := fun hy ↦ y_zero ((cpow_eq_zero_iff _ _).mp hy).1
      simp only [one_div, sub_add_cancel, cpow_neg, neg_mul, r]
      field_simp
  · simp only [r]
    ring_nf

lemma ZetaSum_aux1derivφCont {s : ℂ} (s_ne_zero : s ≠ 0) {a b : ℕ} (ha : a ∈ Ioo 0 b) :
    ContinuousOn (deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s)) [[a, b]] := by
  have : EqOn _ (fun (t : ℝ) ↦ -s * (t : ℂ) ^ (-(s + 1))) [[a, b]] :=
    fun x hx ↦ ZetaSum_aux1φderiv s_ne_zero <| xpos_of_uIcc ha hx
  refine continuous_ofReal.continuousOn.cpow_const ?_ |>.const_smul (c := -s) |>.congr this
  exact fun x hx ↦ ofReal_mem_slitPlane.mpr <| xpos_of_uIcc ha hx

lemma ZetaSum_aux1 {a b : ℕ} {s : ℂ} (s_ne_one : s ≠ 1) (s_ne_zero : s ≠ 0) (ha : a ∈ Ioo 0 b) :
    ∑ n ∈ Finset.Ioc a b, 1 / (n : ℂ) ^ s =
    (b ^ (1 - s) - a ^ (1 - s)) / (1 - s) + 1 / 2 * (1 / b ^ (s)) - 1 / 2 * (1 / a ^ s)
      + s * ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) := by
  let φ := fun (x : ℝ) ↦ 1 / (x : ℂ) ^ s
  let φ' := fun (x : ℝ) ↦ -s * (x : ℂ) ^ (-(s + 1))
  have xpos : ∀ x ∈ [[(a : ℝ), b]], 0 < x := fun x hx ↦ xpos_of_uIcc ha hx
  have φDiff : ∀ x ∈ [[(a : ℝ), b]], HasDerivAt φ (deriv φ x) x :=
    fun x hx ↦ ZetaSum_aux1φDiff (xpos x hx)
  have φderiv : ∀ x ∈ [[(a : ℝ), b]], deriv φ x = φ' x := by
    exact fun x hx ↦ ZetaSum_aux1φderiv s_ne_zero (xpos x hx)
  have derivφCont : ContinuousOn (deriv φ) [[a, b]] := ZetaSum_aux1derivφCont s_ne_zero ha
  convert sum_eq_int_deriv (by linarith) (by exact_mod_cast ha.2) φDiff derivφCont using 1
  · congr <;> simp only [Nat.floor_natCast]
  · rw [Nat.floor_natCast, Nat.floor_natCast, ← intervalIntegral.integral_const_mul]
    simp_rw [mul_div, ← mul_div, φ, ZetaSum_aux1₁ s_ne_one ha]
    conv => rhs; rw [sub_eq_add_neg]
    congr; any_goals norm_cast; simp only [one_div, add_sub_cancel_left]
    rw [← intervalIntegral.integral_neg, intervalIntegral.integral_congr]
    simp only [φ, one_div] at φderiv
    intro x hx; simp_rw [φderiv x hx, φ']; ring_nf

lemma ZetaSum_aux1_3 (x : ℝ) : ‖(⌊x⌋ + 1/2 - x)‖ ≤ 1/2 :=
  abs_le.mpr ⟨(by linarith [Int.lt_floor_add_one x]), (by linarith [Int.floor_le x])⟩

lemma Finset.Ioc_eq_Ico (M N : ℕ) : Finset.Ioc N M = Finset.Ico (N + 1) (M + 1) := by
  ext a; simp only [Finset.mem_Ioc, Finset.mem_Ico]; constructor <;> intro ⟨h₁, h₂⟩ <;> omega

lemma finsetSum_tendsto_tsum {N : ℕ} {f : ℕ → ℂ} (hf : Summable f) :
    Tendsto (fun (k : ℕ) ↦ ∑ n ∈ Finset.Ico N k, f n) atTop (𝓝 (∑' (n : ℕ), f (n + N))) := by
  have := Summable.hasSum_iff_tendsto_nat hf (m := ∑' (n : ℕ), f n) |>.mp hf.hasSum
  have const := tendsto_const_nhds (α := ℕ) (x := ∑ i ∈ Finset.range N, f i) (f := atTop)
  have := Filter.Tendsto.sub this const
  rw [← hf.sum_add_tsum_nat_add N, add_comm, add_sub_cancel_right] at this
  apply this.congr'
  filter_upwards [Filter.mem_atTop (N + 1)]
  intro M hM
  rw [Finset.sum_Ico_eq_sub]
  linarith

lemma Complex.cpow_tendsto {s : ℂ} (s_re_gt : 1 < s.re) :
    Tendsto (fun (x : ℕ) ↦ (x : ℂ) ^ (1 - s)) atTop (𝓝 0) := by
  have one_sub_s_re_ne : (1 - s).re ≠ 0 := by simp only [sub_re, one_re]; linarith
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [Complex.norm_natCast_cpow_of_re_ne_zero _ (one_sub_s_re_ne)]
  rw [(by simp only [sub_re, one_re, neg_sub] : (1 - s).re = - (s - 1).re)]
  apply (tendsto_rpow_neg_atTop _).comp tendsto_natCast_atTop_atTop; simp [s_re_gt]

lemma Complex.cpow_inv_tendsto {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun (x : ℕ) ↦ ((x : ℂ) ^ s)⁻¹) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_inv, Complex.norm_natCast_cpow_of_re_ne_zero _ <| ne_of_gt hs]
  apply Filter.Tendsto.inv_tendsto_atTop
  exact (tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop

lemma ZetaSum_aux2a : ∃ C, ∀ (x : ℝ), ‖⌊x⌋ + 1 / 2 - x‖ ≤ C := by
  use 1 / 2; exact ZetaSum_aux1_3

lemma ZetaSum_aux3 {N : ℕ} {s : ℂ} (s_re_gt : 1 < s.re) :
    Tendsto (fun k ↦ ∑ n ∈ Finset.Ioc N k, 1 / (n : ℂ) ^ s) atTop
    (𝓝 (∑' (n : ℕ), 1 / (n + N + 1 : ℂ) ^ s)) := by
  let f := fun (n : ℕ) ↦ 1 / (n : ℂ) ^ s
  have hf := summable_one_div_nat_cpow.mpr s_re_gt
  simp_rw [Finset.Ioc_eq_Ico]
  convert finsetSum_tendsto_tsum (f := fun n ↦ f (n + 1)) (N := N) ?_ using 1
  · ext k
    rw [Finset.sum_Ico_add']
  · congr; ext n; simp only [one_div, Nat.cast_add, Nat.cast_one, f]
  · rwa [summable_nat_add_iff (k := 1)]

lemma integrableOn_of_Zeta0_fun {N : ℕ} (N_pos : 0 < N) {s : ℂ} (s_re_gt : 0 < s.re) :
    MeasureTheory.IntegrableOn (fun (x : ℝ) ↦ (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))) (Ioi N)
    MeasureTheory.volume := by
  obtain ⟨c, hc⟩ := ZetaSum_aux2a
  apply MeasureTheory.Integrable.bdd_mul (c := c) ?_ ?_
  · apply MeasureTheory.ae_of_all
    convert hc; simp only [← Complex.norm_real]; simp
  · apply integrableOn_Ioi_cpow_iff (by positivity) |>.mpr (by simp [s_re_gt])
  · refine Measurable.add ?_ measurable_const |>.sub (by fun_prop) |>.aestronglyMeasurable
    exact Measurable.comp (by exact fun _ _ ↦ trivial) Int.measurable_floor

lemma ZetaSum_aux2 {N : ℕ} (N_pos : 0 < N) {s : ℂ} (s_re_gt : 1 < s.re) :
    ∑' (n : ℕ), 1 / (n + N + 1 : ℂ) ^ s =
    (- N ^ (1 - s)) / (1 - s) - N ^ (-s) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) := by
  have s_ne_zero : s ≠ 0 := fun hs ↦ by linarith [zero_re ▸ hs ▸ s_re_gt]
  have s_ne_one : s ≠ 1 := fun hs ↦ (lt_self_iff_false _).mp <| one_re ▸ hs ▸ s_re_gt
  apply tendsto_nhds_unique (X := ℂ) (Y := ℕ) (l := atTop)
    (f := fun k ↦ ((k : ℂ) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s) +
      1 / 2 * (1 / ↑k ^ s) - 1 / 2 * (1 / ↑N ^ s)
      + s * ∫ (x : ℝ) in (N : ℝ)..k, (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)))
    (b := (- N ^ (1 - s)) / (1 - s) - N ^ (-s) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)))
  · apply Filter.Tendsto.congr'
      (f₁ := fun (k : ℕ) ↦ ∑ n ∈ Finset.Ioc N k, 1 / (n : ℂ) ^ s) (l₁ := atTop)
    · apply Filter.eventually_atTop.mpr
      use N + 1
      intro k hk
      exact ZetaSum_aux1 (a := N) (b := k) s_ne_one s_ne_zero ⟨N_pos, hk⟩
    · exact ZetaSum_aux3 s_re_gt
  · apply (Tendsto.sub ?_ ?_).add (Tendsto.const_mul _ ?_)
    · rw [(by ring : -↑N ^ (1 - s) / (1 - s) = (0 - ↑N ^ (1 - s)) / (1 - s) + 0)]
      apply cpow_tendsto s_re_gt |>.sub_const _ |>.div_const _ |>.add
      simp_rw [mul_comm_div, one_mul, one_div, (by congr; ring : 𝓝 (0 : ℂ) = 𝓝 ((0 : ℂ) / 2))]
      apply Tendsto.div_const <| cpow_inv_tendsto (by positivity)
    · simp_rw [mul_comm_div, one_mul, one_div, cpow_neg]; exact tendsto_const_nhds
    · exact MeasureTheory.intervalIntegral_tendsto_integral_Ioi (a := N)
        (b := (fun (n : ℕ) ↦ (n : ℝ)))
        (integrableOn_of_Zeta0_fun N_pos <| by positivity) tendsto_natCast_atTop_atTop

lemma isOpen_aux : IsOpen {z : ℂ | z ≠ 1 ∧ 0 < z.re} := by
  refine IsOpen.inter isOpen_ne ?_
  exact isOpen_lt (g := fun (z : ℂ) ↦ z.re) (by continuity) (by continuity)

open MeasureTheory in
lemma integrable_log_over_pow {r : ℝ} (rneg : r < 0) {N : ℕ} (Npos : 0 < N) :
    IntegrableOn (fun (x : ℝ) ↦ ‖x ^ (r - 1)‖ * ‖Real.log x‖) <| Ioi N := by
  apply IntegrableOn.mono_set (hst := Set.Ioi_subset_Ici <| le_refl (N : ℝ))
  apply LocallyIntegrableOn.integrableOn_of_isBigO_atTop (g := fun x ↦ x ^ (r / 2 - 1))
  · apply ContinuousOn.abs ?_ |>.mul ?_ |>.locallyIntegrableOn (by simp)
    · apply ContinuousOn.rpow (by fun_prop) (by fun_prop)
      intro x hx; left; contrapose! Npos with h; exact_mod_cast h ▸ mem_Ici.mp hx
    · apply continuous_id.continuousOn.log ?_ |>.abs
      intro x hx; simp only [id_eq]; contrapose! Npos with h; exact_mod_cast h ▸ mem_Ici.mp hx
  · have := isLittleO_log_rpow_atTop (r := -r / 2) (by linarith) |>.isBigO
    rw [Asymptotics.isBigO_iff_eventually, Filter.eventually_atTop] at this
    obtain ⟨C, hC⟩ := this
    have hh := hC C (by simp)
    rw [Asymptotics.isBigO_atTop_iff_eventually_exists]
    have := Filter.eventually_atTop.mp hh
    obtain ⟨x₀, hx₀ ⟩ := this
    filter_upwards [hh, Filter.mem_atTop x₀, Filter.mem_atTop 1]
    intro x hx x_gt x_pos
    use C
    intro y hy
    simp only [norm_mul, Real.norm_eq_abs, _root_.abs_abs]
    simp only [Real.norm_eq_abs] at hx
    have y_pos : 0 < y := by linarith
    have : y ^ (r / 2 - 1) = y ^ (r - 1) * y ^ (-r / 2) := by
      rw [← Real.rpow_add y_pos]; ring_nf
    rw [this, abs_mul]
    have y_gt : y ≥ x₀ := by linarith
    have := hx₀ y y_gt
    simp only [Real.norm_eq_abs] at this
    rw [← mul_assoc, mul_comm C, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hbc := this) (a := |y ^ (r - 1)|) (ha := by simp)
  · have := integrableOn_Ioi_rpow_iff (s := r / 2 - 1) (t := N) (by simp [Npos]) |>.mpr
      (by linarith [rneg])
    exact integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin.mp this |>.1

open MeasureTheory in
lemma integrableOn_of_Zeta0_fun_log {N : ℕ} (Npos : 0 < N) {s : ℂ} (s_re_gt : 0 < s.re) :
    IntegrableOn (fun (x : ℝ) ↦ (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) * (-Real.log x)) (Ioi N)
    volume := by
  simp_rw [mul_assoc]
  obtain ⟨c, hc⟩ := ZetaSum_aux2a
  apply Integrable.bdd_mul (c := c) ?_ ?_ ?_
  · simp only [neg_add_rev, mul_neg, add_comm, ← sub_eq_add_neg]
    apply integrable_norm_iff ?_ |>.mp ?_ |>.neg
    · apply ContinuousOn.mul ?_ ?_ |>.aestronglyMeasurable (by simp)
      · intro x hx
        apply ContinuousWithinAt.cpow ?_ continuous_const.continuousWithinAt ?_
        · exact RCLike.continuous_ofReal.continuousWithinAt
        · simp only [ofReal_mem_slitPlane]; linarith [mem_Ioi.mp hx]
      · apply RCLike.continuous_ofReal.continuousOn.comp ?_ (mapsTo_image _ _)
        refine continuous_id.continuousOn.log ?_
        intro x hx; simp only [id_eq]; linarith [mem_Ioi.mp hx]
    · simp only [norm_mul, norm_real]
      have := integrable_log_over_pow (r := -s.re) (by linarith) Npos
      apply IntegrableOn.congr_fun this ?_ (by simp)
      intro x hx
      simp only [mul_eq_mul_right_iff, norm_eq_zero, Real.log_eq_zero]
      left
      have xpos : 0 < x := by linarith [mem_Ioi.mp hx]
      simp [norm_cpow_eq_rpow_re_of_pos xpos, Real.abs_rpow_of_nonneg xpos.le,
        abs_eq_self.mpr xpos.le]
  · apply Measurable.add ?_ measurable_const |>.sub (by fun_prop) |>.aestronglyMeasurable
    exact Measurable.comp (fun _ _ ↦ trivial) Int.measurable_floor
  · apply MeasureTheory.ae_of_all
    convert hc with _ x; simp only [← Complex.norm_real]; simp

open MeasureTheory in
lemma hasDerivAt_Zeta0Integral {N : ℕ} (Npos : 0 < N) {s : ℂ} (hs : s ∈ {s | 0 < s.re}) :
  HasDerivAt (fun z ↦ ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-z - 1))
    (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x)) s := by
  simp only [mem_setOf_eq] at hs
  set f : ℝ → ℂ := fun x ↦ (⌊x⌋ : ℂ) + 1 / 2 - x
  set F : ℂ → ℝ → ℂ := fun s x ↦ (x : ℂ) ^ (- s - 1) * f x
  set F' : ℂ → ℝ → ℂ := fun s x ↦ (x : ℂ) ^ (- s - 1) * (- Real.log x) * f x
  set ε := s.re / 2
  have ε_pos : 0 < ε := by aesop
  set bound : ℝ → ℝ := fun x ↦ |x ^ (- s.re / 2 - 1)| * |Real.log x|
  let μ : Measure ℝ := volume.restrict (Ioi (N : ℝ))
  have hF_meas : ∀ᶠ (z : ℂ) in 𝓝 s, AEStronglyMeasurable (F z) μ := by
    have : {z : ℂ | 0 < z.re} ∈ 𝓝 s := by
      rw [mem_nhds_iff]
      refine ⟨{z | 0 < z.re}, fun ⦃a⦄ a ↦ a, isOpen_lt continuous_const Complex.continuous_re, hs⟩
    filter_upwards [this] with z hz
    convert! integrableOn_of_Zeta0_fun Npos hz |>.aestronglyMeasurable using 1
    simp only [F, f]; ext x; ring_nf
  have hF_int : Integrable (F s) μ := by
    convert! integrableOn_of_Zeta0_fun Npos hs |>.integrable using 1
    simp only [F, f]; ext x; ring_nf
  have hF'_meas : AEStronglyMeasurable (F' s) μ := by
    convert! integrableOn_of_Zeta0_fun_log Npos hs |>.aestronglyMeasurable using 1
    simp only [F', f]; ext x; ring_nf
  have IoiSubIoi1 : (Ioi (N : ℝ)) ⊆ {x | 1 < x} :=
      fun x hx ↦ lt_of_le_of_lt (by simp only [Nat.one_le_cast]; omega) <| mem_Ioi.mp hx
  have measSetIoi1 : MeasurableSet {x : ℝ | 1 < x} := (isOpen_lt' 1).measurableSet
  have h_bound1 :
    ∀ᵐ (x : ℝ) ∂volume.restrict {x | 1 < x}, ∀ z ∈ Metric.ball s ε, ‖F' z x‖ ≤ bound x := by
    filter_upwards [self_mem_ae_restrict measSetIoi1] with x hx
    intro z hz
    simp only [F', f, bound]
    calc _ = ‖(x : ℂ) ^ (-z - 1)‖ * ‖-(Real.log x)‖ * ‖(⌊x⌋ + 1 / 2 - x)‖ := by
            simp only [mul_neg, one_div, neg_mul, norm_neg, norm_mul, norm_real, Real.norm_eq_abs,
              ← (by simp : (((⌊x⌋ + 2⁻¹ - x) : ℝ) : ℂ) = (⌊x⌋ : ℂ) + 2⁻¹ - ↑x),
              Complex.norm_real]
         _ = ‖x ^ (-z.re - 1)‖ * ‖-(Real.log x)‖ * ‖(⌊x⌋ + 1 / 2 - x)‖ := ?_
         _ = |x ^ (-z.re - 1)| * |(Real.log x)| * |(⌊x⌋ + 1 / 2 - x)| := by simp
         _ ≤ _ := ?_
    · congr! 2
      simp only [Real.norm_eq_abs, norm_cpow_eq_rpow_re_of_pos (by linarith),
        sub_re, neg_re, one_re]
      apply abs_eq_self.mpr ?_ |>.symm
      positivity
    · rw [mul_comm, ← mul_assoc]
      apply mul_le_mul_of_nonneg_right ?_ <| abs_nonneg _
      simp only [Metric.mem_ball, ε, Complex.dist_eq] at hz
      apply le_trans (b := 1 * |x ^ (-z.re - 1)|)
      · apply mul_le_mul_of_nonneg_right (le_trans (ZetaSum_aux1_3 _) (by norm_num)) <| abs_nonneg _
      · simp_rw [one_mul, Real.abs_rpow_of_nonneg (by linarith : 0 ≤ x)]
        apply Real.rpow_le_rpow_of_exponent_le <| le_abs.mpr (by left; exact hx.le)
        have := abs_le.mp <| le_trans (abs_re_le_norm (z-s)) hz.le
        simp only [sub_re, neg_le_sub_iff_le_add, tsub_le_iff_right] at this
        linarith [this.1]
  have h_bound : ∀ᵐ x ∂μ, ∀ z ∈ Metric.ball s ε, ‖F' z x‖ ≤ bound x := by
    apply ae_restrict_of_ae_restrict_of_subset IoiSubIoi1
    exact h_bound1
  have bound_integrable : Integrable bound μ := by
    simp only [bound]
    convert! integrable_log_over_pow (r := -s.re / 2) (by linarith) Npos using 0
  have h_diff : ∀ᵐ x ∂μ, ∀ z ∈ Metric.ball s ε, HasDerivAt (fun w ↦ F w x) (F' z x) z := by
    simp only [F, F', f]
    apply ae_restrict_of_ae_restrict_of_subset IoiSubIoi1
    filter_upwards [h_bound1, self_mem_ae_restrict measSetIoi1] with x _ one_lt_x
    intro z hz
    convert! HasDerivAt.mul_const (c := fun (w : ℂ) ↦ (x : ℂ) ^ (-w-1))
      (c' := (x : ℂ) ^ (-z-1) * -Real.log x) (d := (⌊x⌋ : ℝ) + 1 / 2 - x) ?_ using 1
    convert! HasDerivAt.comp (h := fun w ↦ -w-1) (h' := -1) (h₂ := fun w ↦ x ^ w)
      (h₂' := x ^ (-z-1) * Real.log x) (x := z) ?_ ?_ using 0
    · simp only [mul_neg, mul_one]; congr! 2
    · convert! HasDerivAt.const_cpow (c := (x : ℂ)) (f := fun w ↦ w) (f' := 1) (x := -z-1)
        (hasDerivAt_id _) ?_ using 1
      · simp only [mul_one, mul_eq_mul_left_iff, cpow_eq_zero_iff, ofReal_eq_zero, ne_eq]
        left
        rw [Complex.ofReal_log]
        linarith
      · right
        intro h
        simp only [Metric.mem_ball, ε, Complex.dist_eq,
          neg_eq_iff_eq_neg.mp <| sub_eq_zero.mp h] at hz
        have := (abs_le.mp <| le_trans (abs_re_le_norm (-1-s)) hz.le).1
        simp only [sub_re, neg_re, one_re, neg_le_sub_iff_le_add, le_neg_add_iff_add_le] at this
        linarith
    · apply hasDerivAt_id _ |>.neg |>.sub_const
  convert! (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F') (x₀ := s)
    (s := Metric.ball s ε) (bound := bound) (μ := μ) (Metric.ball_mem_nhds s ε_pos)
    hF_meas hF_int hF'_meas h_bound bound_integrable h_diff).2 using 3
  · ext a; simp only [one_div, F, f]; ring_nf
  · simp only [one_div, mul_neg, neg_mul, neg_inj, F', f]; ring_nf

noncomputable def ζ₀' (N : ℕ) (s : ℂ) : ℂ :=
    ∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ s * Real.log n +
    (-N ^ (1 - s) / (1 - s) ^ 2 + Real.log N * N ^ (1 - s) / (1 - s)) +
    Real.log N * N ^ (-s) / 2 +
    (1 * (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1)) +
    s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x))

lemma HasDerivAt_neg_cpow_over2 {N : ℕ} (Npos : 0 < N) (s : ℂ) :
    HasDerivAt (fun x : ℂ ↦ -(N : ℂ) ^ (-x) / 2) (-((- Real.log N) * (N : ℂ) ^ (-s)) / 2) s := by
  convert! hasDerivAt_neg' s |>.const_cpow (c := N) (by aesop) |>.neg |>.div_const _ using 1
  simp [mul_comm]

lemma HasDerivAt_cpow_over_var (N : ℕ) {z : ℂ} (z_ne_zero : z ≠ 0) :
    HasDerivAt (fun z ↦ -(N : ℂ) ^ z / z)
      (((N : ℂ) ^ z / z ^ 2) - (Real.log N * N ^ z / z)) z := by
  simp_rw [div_eq_mul_inv]
  convert! HasDerivAt.mul (c := fun z ↦ - (N : ℂ) ^ z) (d := fun z ↦ z⁻¹)
    (c' := - (N : ℂ) ^ z * Real.log N)
    (d' := - (z ^ 2)⁻¹) ?_ ?_ using 1
  · simp only [natCast_log, neg_mul, mul_neg, neg_neg]
    ring_nf
  · simp only [natCast_log, neg_mul]
    apply HasDerivAt.neg
    convert! HasDerivAt.const_cpow (c := (N : ℂ)) (f := id) (f' := 1) (x := z) (hasDerivAt_id z)
      (by simp [z_ne_zero]) using 1
    simp only [id_eq, mul_one]
  · exact hasDerivAt_inv z_ne_zero

lemma HasDerivAtZeta0 {N : ℕ} (Npos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re) (s_ne_one : s ≠ 1) :
    HasDerivAt (riemannZeta0 N) (ζ₀' N s) s := by
  unfold riemannZeta0 ζ₀'
  apply HasDerivAt.fun_sum ?_ |>.add ?_ |>.add ?_ |>.add ?_
  · intro n _
    convert! hasDerivAt_neg' s |>.const_cpow (c := n) (by aesop) using 1
    all_goals (ring_nf; simp [cpow_neg])
  · convert! HasDerivAt.comp (h₂ := fun z ↦ -(N : ℂ) ^ z / z) (h := fun z ↦ 1 - z) (h' := -1)
      (h₂' := ((N : ℂ) ^ (1 - s) / (1 - s) ^ 2 - Real.log (N : ℝ) * (N : ℂ) ^ (1 - s) / (1 - s)))
      (x := s) ?_ ?_ using 1
    · ring_nf
    · exact HasDerivAt_cpow_over_var N (by rw [sub_ne_zero]; exact s_ne_one.symm)
    · convert! hasDerivAt_const s _ |>.sub (hasDerivAt_id _) using 1; simp
  · convert! HasDerivAt_neg_cpow_over2 Npos s using 1; simp only [natCast_log, neg_mul, neg_neg]
  · simp_rw [div_cpow_eq_cpow_neg, neg_add, ← sub_eq_add_neg]
    convert! hasDerivAt_id s |>.mul <| hasDerivAt_Zeta0Integral Npos reS_pos using 1

lemma HolomorphicOn_riemannZeta0 {N : ℕ} (N_pos : 0 < N) :
    HolomorphicOn (riemannZeta0 N) {s : ℂ | s ≠ 1 ∧ 0 < s.re} :=
  fun _ ⟨hs₁, hs₂⟩ ↦ (HasDerivAtZeta0 N_pos hs₂ hs₁).differentiableAt.differentiableWithinAt

-- MOVE TO MATHLIB near `differentiableAt_riemannZeta`
lemma HolomorphicOn_riemannZeta :
    HolomorphicOn riemannZeta {s : ℂ | s ≠ 1} := by
  intro z hz
  simp only [mem_setOf_eq] at hz
  exact (differentiableAt_riemannZeta hz).differentiableWithinAt

lemma isPathConnected_aux : IsPathConnected {z : ℂ | z ≠ 1 ∧ 0 < z.re} := by
  use (2 : ℂ)
  constructor
  · simp
  intro w hw; simp only [ne_eq, mem_setOf_eq] at hw
  by_cases w_im : w.im = 0
  · apply JoinedIn.trans (y := 1 + I)
    · let f : ℝ → ℂ := fun t ↦ (1 + I) * t + 2 * (1 - t)
      have cont : Continuous f := by continuity
      apply JoinedIn.ofLine cont.continuousOn (by simp [f]) (by simp [f])
      simp only [unitInterval, ne_eq, image_subset_iff, preimage_setOf_eq, add_re, mul_re, one_re,
        I_re, add_zero, ofReal_re, one_mul, add_im, one_im, I_im, zero_add, ofReal_im, mul_zero,
        sub_zero, re_ofNat, sub_re, im_ofNat, sub_im, sub_self, f]
      intro x hx; simp only [mem_Icc] at hx
      refine ⟨?_, by linarith⟩
      intro h
      rw [Complex.ext_iff] at h; simp [(by apply And.right; simpa [w_im] using h : x = 0)] at h
    · let f : ℝ → ℂ := fun t ↦ w * t + (1 + I) * (1 - t)
      have cont : Continuous f := by continuity
      apply JoinedIn.ofLine cont.continuousOn (by simp [f]) (by simp [f])
      simp only [unitInterval, ne_eq, image_subset_iff, preimage_setOf_eq, add_re, mul_re,
        ofReal_re, ofReal_im, mul_zero, sub_zero, one_re, I_re, add_zero, sub_re, one_mul, add_im,
        one_im, I_im, zero_add, sub_im, sub_self, f]
      intro x hx; simp only [mem_Icc] at hx
      simp only [mem_setOf_eq]
      constructor
      · intro h
        refine hw.1 ?_
        rw [Complex.ext_iff] at h
        have : x = 1 := by linarith [(by apply And.right; simpa [w_im] using h : 1 - x = 0)]
        rw [Complex.ext_iff, one_re, one_im]; exact ⟨by simpa [this, w_im] using h, w_im⟩
      · by_cases hxx : x = 0
        · simp only [hxx]; linarith
        · have : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hxx)
          have : 0 ≤ 1 - x := by linarith
          have := hw.2
          positivity
  · let f : ℝ → ℂ := fun t ↦ w * t + 2 * (1 - t)
    have cont : Continuous f := by continuity
    apply JoinedIn.ofLine cont.continuousOn (by simp [f]) (by simp [f])
    simp only [unitInterval, ne_eq, image_subset_iff, preimage_setOf_eq, add_re, mul_re, ofReal_re,
      ofReal_im, mul_zero, sub_zero, re_ofNat, sub_re, one_re, im_ofNat, sub_im, one_im, sub_self,
      f]
    intro x hx; simp only [mem_Icc] at hx
    constructor
    · intro h
      rw [Complex.ext_iff] at h;
      simp [(by apply And.right; simpa [w_im] using h : x = 0)] at h
    · by_cases hxx : x = 0
      · simp only [hxx]; linarith
      · have : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hxx)
        have : 0 ≤ 1 - x := by linarith
        have := hw.2
        positivity

lemma Zeta0EqZeta {N : ℕ} (N_pos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re) (s_ne_one : s ≠ 1) :
    riemannZeta0 N s = riemannZeta s := by
  let f := riemannZeta
  let g := riemannZeta0 N
  let U := {z : ℂ | z ≠ 1 ∧ 0 < z.re}
  have f_an : AnalyticOnNhd ℂ f U := by
    apply (HolomorphicOn_riemannZeta.analyticOnNhd isOpen_ne).mono
    simp only [ne_eq, setOf_subset_setOf, and_imp, U]
    exact fun a ha _ ↦ ha
  have g_an : AnalyticOnNhd ℂ g U := (HolomorphicOn_riemannZeta0 N_pos).analyticOnNhd isOpen_aux
  have preconU : IsPreconnected U := by
    apply IsConnected.isPreconnected
    apply (IsOpen.isConnected_iff_isPathConnected isOpen_aux).mpr isPathConnected_aux
  have h2 : (2 : ℂ) ∈ U := by simp [U]
  have s_mem : s ∈ U := by simp [U, reS_pos, s_ne_one]
  convert (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq f_an g_an preconU h2 ?_ s_mem).symm
  have u_mem : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) := by
    apply mem_nhds_iff.mpr
    use {z : ℂ | 1 < z.re}
    simp only [setOf_subset_setOf, imp_self, forall_const, mem_setOf_eq, re_ofNat,
      Nat.one_lt_ofNat, and_true, true_and]
    exact isOpen_lt (by continuity) (by continuity)
  filter_upwards [u_mem]
  intro z hz
  simp only [f,g, zeta_eq_tsum_one_div_nat_cpow hz, riemannZeta0_apply]
  nth_rewrite 2 [neg_div]
  rw [← sub_eq_add_neg, ← ZetaSum_aux2 N_pos hz,
    ← (summable_one_div_nat_cpow.mpr hz).sum_add_tsum_nat_add (N + 1)]
  norm_cast

-- **Another AlphaProof collaboration (thanks to Thomas Hubert!)**

-- **End collaboration 6/20/25**

/-% ** Bad delimiters on purpose **
Annoying: we have reciprocals of $log |t|$ in the bounds, and we've assumed that $|t|>3$; but we
want to make things uniform in $t$. Let's change to things like $log (|t|+3)$ instead of $log |t|$.
\begin{lemma}[LogLeLog]\label{LogLeLog}\lean{LogLeLog}\leanok
There is a constant $C>0$ so that for all $t>3$,
$$
1/\log t \le C / \log (t + 3).
$$
\end{lemma}
%-/
/-%
\begin{proof}
Write
$$
\log (t + 3) = \log t + \log (1 + 3/t) = \log t + O(1/t).
$$
Then we can bound $1/\log t$ by $C / \log (t + 3)$ for some constant $C>0$.
\end{proof}
%-/

-- **Begin collaboration with the Alpha Proof team! 5/29/25**

-- **End collaboration**

open ArithmeticFunction (vonMangoldt)
--TODO generalize to any LSeries with nonnegative coefficients

end
-- ===== end Zeta23.FromPNTPlus.ZetaBounds =====

namespace OMAPort_Divisor

open DirichletDivisorProblem

open DirichletDivisorProblem

-- ===== from LeanClassics.DensityTail =====
section

/-!
# Mean square of the Euler–Maclaurin remainder of `ζ` on a vertical line

`integral_norm_sq_tail_le`: for `σ ≥ 1/2`, real `N > 0` and any `a ≤ b`,
`∫_a^b |∫_N^∞ (⌊x⌋ + 1/2 − x) x^{−(σ+it)−1} dx|² dt ≤ (π/2) N^{−2σ}`; the integrand `tailFn`
is integrable over the whole line (`integrable_norm_sq_tailFn`).

Proof. Substituting `x = N/w`, the inner integral is `N^{−s}` times the Mellin transform on `(0, 1]`
of `g(w) = (⌊N/w⌋ + 1/2 − N/w) w^{σ − 1/2}` (for `w < 1`; `0` at `w = 1`) at `1/2 + it`
(`mellin_comp_inv`, `mellin_comp_mul_left`). `|g| ≤ 1/2` on `(0, 1]`, so Plancherel in Mellin form
(`Nyman.Plancherel.integral_norm_sq_mellin`) bounds the integral over the whole line by
`2π N^{−2σ} ∫_0^1 |g|² ≤ (π/2) N^{−2σ}`.
-/

open Complex Real Set MeasureTheory Filter

noncomputable section

namespace LeanClassics.Density

open LeanClassics.Nyman.Plancherel

/-- The tail on `Re s = σ`, as a function of `t`. -/
def tailFn (N σ t : ℝ) : ℂ :=
  ∫ x in Ioi N, ((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ)) / (x : ℂ) ^ (((σ : ℂ) + t * I) + 1)

end LeanClassics.Density
end

end
-- ===== end LeanClassics.DensityTail =====

-- ===== from LeanClassics.DensityMeanSquare =====
section

/-!
# Mean square of `ζ` on `Re s = σ > 1/2`: `∫_1^X |ζ(σ + it)|² dt ≪ X`, uniformly in `σ`

`integral_norm_sq_zeta_le`: for `1/2 < σ₁ ≤ σ₂` there is `C` with
`∫_1^X |ζ(σ + it)|² dt ≤ C X` for all `σ ∈ [σ₁, σ₂]` and `X ≥ 1` (Hardy–Littlewood's upper bound;
the asymptotic `∼ ζ(2σ) X` is not proved here).

Proof. With `N = ⌈X⌉`, PNT+'s Euler–Maclaurin form (`Zeta0EqZeta`, vendored in zeta23) writes
`ζ(s) = ∑_{n<N} (n+1)^{−s} − N^{1−s}/(1 − s) − N^{−s}/2 + s ∫_N^∞ (⌊x⌋ + 1/2 − x) x^{−s−1} dx`.
The Dirichlet polynomial has mean square `≤ X ∑ (n+1)^{−2σ₁} + 52 N` (`DensityMV`,
Montgomery–Vaughan),
`|N^{1−s}/(1 − s)|² ≤ N/t²` integrates to `≤ N`, `|N^{−s}/2|² ≤ 1/4`, and the remainder has mean
square `≤ (σ₂² + X²) (π/2) N^{−2σ} ≤ (π/2)(σ₂² + X)` (`DensityTail`, Plancherel). Then
`|a + b + c + d|² ≤ 4(|a|² + |b|² + |c|² + |d|²)`.
-/

open Complex Real Set MeasureTheory Filter

noncomputable section

namespace LeanClassics.Density

lemma line_ne_one {σ t : ℝ} (ht : t ≠ 0) : (σ : ℂ) + t * I ≠ 1 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact ht this

lemma zeta_split {σ t : ℝ} (hσ : 0 < σ) (ht : t ≠ 0) {N : ℕ} (hN : 0 < N) :
    riemannZeta ((σ : ℂ) + t * I) =
      (∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1) ^ ((σ : ℂ) + t * I))
      + (-((N : ℂ) ^ (1 - ((σ : ℂ) + t * I)))) / (1 - ((σ : ℂ) + t * I))
      + (-((N : ℂ) ^ (-((σ : ℂ) + t * I)))) / 2
      + ((σ : ℂ) + t * I) * tailFn N σ t := by
  set s : ℂ := (σ : ℂ) + t * I with hs
  have hre : 0 < s.re := by simpa [hs] using hσ
  have hs0 : s ≠ 0 := fun h => by rw [h] at hre; simp at hre
  rw [← Zeta0EqZeta hN hre (line_ne_one ht), riemannZeta0, Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_cpow hs0, div_zero, add_zero, Nat.cast_add, Nat.cast_one]
  rfl

end LeanClassics.Density
end

end
-- ===== end LeanClassics.DensityMeanSquare =====

-- ===== from HardyOmegaFC.FourthMoment =====
section

/-!
# Hardy Ω, rung D3: the fourth moment of `ζ` is large right of the critical line

For `5/8 ≤ σ ≤ 3/4` and `T ≥ 1`:

  `‖∫_T^{2T} ζ(σ + it) dt − T‖ ≤ 40 T^{3/4}`                         (`first_moment`),

and for `T ≥ 80⁴`:

  `T / 16 ≤ ∫_T^{2T} ‖ζ(σ + it)‖⁴ dt`  and  `T / 16 ≤ ∫_T^{2T} ‖ζ(σ − it)‖⁴ dt`
                                         (`fourth_moment_ge`, `fourth_moment_ge_neg`).

Proof of the first moment. Euler–Maclaurin at `N = ⌈T²⌉` (`LeanClassics.Density.zeta_split`):
`ζ(s) = ∑_{n ≤ N} n^{−s} − N^{1−s}/(1−s) − N^{−s}/2 + s·R_N(s)` with
`‖R_N(s)‖ ≤ N^{−σ}/(2σ)` (`norm_tailFn_le`, from `|⌊x⌋ + 1/2 − x| ≤ 1/2`). Integrated over `[T, 2T]`: the term
`n = 1` gives `T`; each `n ≥ 2` gives at most `4 n^{−σ}/log 2` (`norm_integral_exp_Icc_le`), and
`∑_{2 ≤ n ≤ N} n^{−5/8} ≤ (8/3) N^{3/8}` (`sum_rpow_le`); the other three terms are `O(T^{3/4})` because
`T² ≤ N ≤ 2T²` and `σ ≥ 5/8`. Then `∫‖ζ‖ ≥ ‖∫ζ‖ ≥ T/2` and Cauchy–Schwarz twice
(`sq_integral_le`: `(∫f)² ≤ (b − a) ∫f²`) give `∫‖ζ‖⁴ ≥ (T/2)⁴ / T³`.

Negative `t` by `riemannZeta_conj`. Constants are not sharp. No hypotheses beyond the stated ranges.
-/

open Complex MeasureTheory Set
open scoped Real Interval

noncomputable section

namespace DirichletDivisorProblem.HardyD3

open LeanClassics.Density (zeta_split tailFn line_ne_one)
open LeanClassics.ZetaMeanSquare (norm_integral_exp_le term_eq)

/-- The Euler–Maclaurin remainder is at most `N^{−σ}/(2σ)` pointwise. -/
lemma norm_tailFn_le {σ N : ℝ} (hσ : 0 < σ) (hN : 0 < N) (t : ℝ) :
    ‖tailFn N σ t‖ ≤ N ^ (-σ) / (2 * σ) := by
  unfold tailFn
  have hint : IntegrableOn (fun x : ℝ => (1 / 2 : ℝ) * x ^ (-σ - 1)) (Ioi N) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hN).const_mul _
  calc _ ≤ ∫ x in Ioi N, (1 / 2 : ℝ) * x ^ (-σ - 1) := by
        refine norm_integral_le_of_norm_le hint ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hx0 : 0 < x := lt_trans hN hx
        rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
        have hre : ((σ : ℂ) + t * I + 1).re = σ + 1 := by simp
        rw [hre]
        have hfl : ‖((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ))‖ ≤ 1 / 2 := by
          have e : ((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ)) = (((⌊x⌋ : ℝ) + 1 / 2 - x : ℝ) : ℂ) := by
            push_cast; ring
          rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
          have h1 := Int.floor_le x
          have h2 := Int.lt_floor_add_one x
          constructor <;> linarith
        have hpos : 0 < x ^ (σ + 1) := Real.rpow_pos_of_pos hx0 _
        rw [show x ^ (-σ - 1) = (x ^ (σ + 1))⁻¹ by rw [← Real.rpow_neg hx0.le, neg_add'] ]
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hfl (inv_nonneg.mpr hpos.le)
    _ = N ^ (-σ) / (2 * σ) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hN]
        have : -σ - 1 + 1 = -σ := by ring
        rw [this]
        field_simp

/-- `‖∫_a^b e^{ict} dt‖ ≤ 4/|c|`. -/
lemma norm_integral_exp_Icc_le {c : ℝ} (hc : c ≠ 0) (a b : ℝ) :
    ‖∫ t in a..b, cexp ((c : ℂ) * t * I)‖ ≤ 4 / |c| := by
  have hi : ∀ x y : ℝ, IntervalIntegrable (fun t : ℝ => cexp ((c : ℂ) * t * I)) volume x y :=
    fun x y => (by fun_prop : Continuous fun t : ℝ => cexp ((c : ℂ) * t * I)).intervalIntegrable _ _
  rw [← intervalIntegral.integral_interval_sub_left (hi 0 b) (hi 0 a)]
  calc _ ≤ ‖∫ t in (0 : ℝ)..b, cexp ((c : ℂ) * t * I)‖ +
          ‖∫ t in (0 : ℝ)..a, cexp ((c : ℂ) * t * I)‖ := norm_sub_le _ _
    _ ≤ 2 / |c| + 2 / |c| := add_le_add (norm_integral_exp_le hc b) (norm_integral_exp_le hc a)
    _ = 4 / |c| := by ring

/-- `∑_{1 ≤ i < N} (i + 1)^{−a} ≤ N^{1−a}/(1 − a)` for `0 < a < 1`. -/
lemma sum_rpow_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : 1 ≤ N) :
    ∑ i ∈ Finset.Ico 1 N, ((i : ℝ) + 1) ^ (-a) ≤ (N : ℝ) ^ (1 - a) / (1 - a) := by
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-a)) (Icc ((1 : ℕ) : ℝ) ((N : ℕ) : ℝ)) := by
    intro x hx y hy hxy
    simp only [Set.mem_Icc, Nat.cast_one] at hx hy
    exact Real.rpow_le_rpow_of_nonpos (by linarith) hxy (by linarith)
  have hint := AntitoneOn.sum_le_integral_Ico hN hanti
  push_cast at hint
  refine hint.trans ?_
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [integral_rpow (Or.inl (by linarith)), Real.one_rpow, show -a + 1 = 1 - a by ring]
  have : 0 < 1 - a := by linarith
  exact div_le_div_of_nonneg_right (by linarith) this.le

/-- Cauchy–Schwarz on an interval: `(∫_a^b f)² ≤ (b − a) ∫_a^b f²`. -/
lemma sq_integral_le {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun x => f x ^ 2) volume a b) :
    (∫ x in a..b, f x) ^ 2 ≤ (b - a) * ∫ x in a..b, f x ^ 2 := by
  rcases hab.eq_or_lt with h | h
  · subst h; simp
  set L := b - a with hL
  have hL0 : 0 < L := by rw [hL]; linarith
  set I1 := ∫ x in a..b, f x
  set I2 := ∫ x in a..b, f x ^ 2
  set m := I1 / L with hm
  have hnn : 0 ≤ ∫ x in a..b, (f x - m) ^ 2 :=
    intervalIntegral.integral_nonneg hab fun x _ => sq_nonneg _
  have hexp : ∫ x in a..b, (f x - m) ^ 2 = I2 - 2 * m * I1 + m ^ 2 * L := by
    have e : (fun x => (f x - m) ^ 2) = fun x => (f x ^ 2 - (2 * m) * f x) + m ^ 2 := by
      funext x; ring
    rw [e, intervalIntegral.integral_add (hf2.sub (hf.const_mul _)) intervalIntegrable_const,
      intervalIntegral.integral_sub hf2 (hf.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hexp] at hnn
  have hmL : m * L = I1 := by rw [hm]; field_simp
  have e2 : I2 - 2 * m * I1 + m ^ 2 * L = I2 - m ^ 2 * L := by rw [← hmL]; ring
  have : m ^ 2 * L ≤ I2 := by linarith
  calc I1 ^ 2 = (m * L) ^ 2 := by rw [hmL]
    _ = L * (m ^ 2 * L) := by ring
    _ ≤ L * I2 := mul_le_mul_of_nonneg_left this hL0.le

/-- `N^e ≤ 2 T^{3/4}` for `1 ≤ N ≤ 2T²`, `e ≤ 3/8`. -/
lemma rpow_le_of_le_two_sq {T N e : ℝ} (hT : 1 ≤ T) (hN1 : 1 ≤ N) (hN : N ≤ 2 * T ^ 2)
    (he : e ≤ 3 / 8) : N ^ e ≤ 2 * T ^ ((3 : ℝ) / 4) := by
  have hT0 : 0 ≤ T := by linarith
  calc N ^ e ≤ N ^ ((3 : ℝ) / 8) := Real.rpow_le_rpow_of_exponent_le hN1 he
    _ ≤ (2 * T ^ 2) ^ ((3 : ℝ) / 8) := Real.rpow_le_rpow (by linarith) hN (by norm_num)
    _ = 2 ^ ((3 : ℝ) / 8) * T ^ ((3 : ℝ) / 4) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast T 2,
          ← Real.rpow_mul hT0]
        norm_num
    _ ≤ 2 * T ^ ((3 : ℝ) / 4) := by
        gcongr
        calc (2 : ℝ) ^ ((3 : ℝ) / 8) ≤ 2 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := Real.rpow_one 2

/-- `N^{−σ} ≤ T^{−5/4}` for `N ≥ T² ≥ 1`, `σ ≥ 5/8`. -/
lemma rpow_neg_le {T N σ : ℝ} (hT : 1 ≤ T) (hN : T ^ 2 ≤ N) (hσ : 5 / 8 ≤ σ) :
    N ^ (-σ) ≤ T ^ (-(5 : ℝ) / 4) := by
  have hT0 : 0 ≤ T := by linarith
  have hT2 : 1 ≤ T ^ 2 := by nlinarith
  have hN1 : 1 ≤ N := le_trans hT2 hN
  calc N ^ (-σ) ≤ N ^ (-(5 : ℝ) / 8) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    _ ≤ (T ^ 2) ^ (-(5 : ℝ) / 8) := Real.rpow_le_rpow_of_nonpos (by positivity) hN (by norm_num)
    _ = T ^ (-(5 : ℝ) / 4) := by
        rw [← Real.rpow_natCast T 2, ← Real.rpow_mul hT0]
        norm_num

lemma continuousOn_zeta_line (σ : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (fun t : ℝ => riemannZeta ((σ : ℂ) + t * I)) (uIcc a b) := by
  intro t ht
  rw [uIcc_of_le hab] at ht
  have ht0 : t ≠ 0 := (lt_of_lt_of_le ha ht.1).ne'
  have h1 : ContinuousAt (fun t : ℝ => (σ : ℂ) + t * I) t := by fun_prop
  have h2 : ContinuousAt riemannZeta ((σ : ℂ) + t * I) :=
    (differentiableAt_riemannZeta (line_ne_one ht0)).continuousAt
  exact (ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => (σ : ℂ) + t * I) h2 h1).continuousWithinAt

/-- **First moment of `ζ` right of the critical line.** For `5/8 ≤ σ ≤ 3/4` and `T ≥ 1`,
`‖∫_T^{2T} ζ(σ + it) dt − T‖ ≤ 40 T^{3/4}`. -/
theorem first_moment {σ : ℝ} (hσ1 : 5 / 8 ≤ σ) (hσ2 : σ ≤ 3 / 4) {T : ℝ} (hT : 1 ≤ T) :
    ‖(∫ t in T..2 * T, riemannZeta ((σ : ℂ) + t * I)) - T‖ ≤ 40 * T ^ ((3 : ℝ) / 4) := by
  have hT0 : 0 < T := by linarith
  have hTT : T ≤ 2 * T := by linarith
  set θ := T ^ ((3 : ℝ) / 4) with hθ
  have hθ0 : 0 ≤ θ := by positivity
  set ρ := T ^ (-(5 : ℝ) / 4) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hTTρ : T * T * ρ = θ := by
    rw [hρ, hθ, show ((3 : ℝ) / 4) = 1 + 1 + (-(5 : ℝ) / 4) by norm_num, Real.rpow_add hT0,
      Real.rpow_add hT0, Real.rpow_one]
  -- the cut-off `N = ⌈T²⌉`
  set N : ℕ := ⌈T ^ 2⌉₊ with hNdef
  have hT2 : 1 ≤ T ^ 2 := by nlinarith
  have hNlo : T ^ 2 ≤ (N : ℝ) := Nat.le_ceil _
  have hNhi : (N : ℝ) ≤ 2 * T ^ 2 := by
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ T ^ 2)
    linarith
  have hN1 : (1 : ℝ) ≤ N := le_trans hT2 hNlo
  have hNpos : 0 < N := by exact_mod_cast (lt_of_lt_of_le one_pos hN1)
  have hNR : (0 : ℝ) < N := by linarith
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
  -- the pieces
  set Z : ℝ → ℂ := fun t => riemannZeta ((σ : ℂ) + t * I) with hZ
  set A : ℝ → ℂ := fun t => ∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1) ^ ((σ : ℂ) + t * I) with hA
  set B : ℝ → ℂ := fun t => (-((N : ℂ) ^ (1 - ((σ : ℂ) + t * I)))) / (1 - ((σ : ℂ) + t * I))
    with hB
  set C : ℝ → ℂ := fun t => (-((N : ℂ) ^ (-((σ : ℂ) + t * I)))) / 2 with hC
  have hmem : ∀ t ∈ uIcc T (2 * T), T ≤ t ∧ t ≤ 2 * T := fun t ht => by
    rw [uIcc_of_le hTT] at ht; exact ht
  have hmem' : ∀ t ∈ Ι T (2 * T), T ≤ t ∧ t ≤ 2 * T := fun t ht => by
    rw [uIoc_of_le hTT] at ht; exact ⟨ht.1.le, ht.2⟩
  have hsub1 : ∀ t : ℝ, t ≠ 0 → 1 - ((σ : ℂ) + t * I) ≠ 0 := fun t ht =>
    sub_ne_zero.mpr (line_ne_one ht).symm
  -- integrability
  have hZi : IntervalIntegrable Z volume T (2 * T) :=
    (continuousOn_zeta_line σ hT0 hTT).intervalIntegrable
  have hterm : ∀ n : ℕ, (fun t : ℝ => 1 / ((n : ℂ) + 1) ^ ((σ : ℂ) + t * I)) = fun t : ℝ =>
      ((((n : ℝ) + 1) ^ (-σ) : ℝ) : ℂ) * cexp (((-Real.log ((n : ℝ) + 1) : ℝ) : ℂ) * t * I) :=
    fun n => funext (term_eq n σ)
  have htermi : ∀ n : ℕ, IntervalIntegrable (fun t : ℝ => 1 / ((n : ℂ) + 1) ^ ((σ : ℂ) + t * I))
      volume T (2 * T) := fun n => by
    rw [hterm n]; exact (by fun_prop : Continuous _).intervalIntegrable _ _
  have hAi : IntervalIntegrable A volume T (2 * T) := by
    have := IntervalIntegrable.sum (Finset.range N) fun n _ => htermi n
    have e : A = ∑ n ∈ Finset.range N, (fun t : ℝ => 1 / ((n : ℂ) + 1) ^ ((σ : ℂ) + t * I)) := by
      funext t; simp [hA]
    rw [e]; exact this
  have hBi : IntervalIntegrable B volume T (2 * T) := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.div ?_ (by fun_prop) fun t ht => hsub1 t (by linarith [(hmem t ht).1])
    exact (Continuous.const_cpow (by fun_prop) (Or.inl hNC)).neg.continuousOn
  have hCi : IntervalIntegrable C volume T (2 * T) :=
    ((Continuous.const_cpow (by fun_prop) (Or.inl hNC)).neg.div_const _).intervalIntegrable _ _
  -- split
  have hsplit : (∫ t in T..2 * T, Z t) - T = ((∫ t in T..2 * T, A t) - T) + (∫ t in T..2 * T, B t)
      + (∫ t in T..2 * T, C t) + ∫ t in T..2 * T, (Z t - A t - B t - C t) := by
    rw [intervalIntegral.integral_sub ((hZi.sub hAi).sub hBi) hCi,
      intervalIntegral.integral_sub (hZi.sub hAi) hBi, intervalIntegral.integral_sub hZi hAi]
    ring
  have hlen : |2 * T - T| = T := by rw [show 2 * T - T = T by ring, abs_of_pos hT0]
  -- the Dirichlet polynomial
  have hAb : ‖(∫ t in T..2 * T, A t) - T‖ ≤ 32 * θ := by
    have e1 : (∫ t in T..2 * T, A t) = ∑ n ∈ Finset.range N,
        ∫ t in T..2 * T, 1 / ((n : ℂ) + 1) ^ ((σ : ℂ) + t * I) :=
      intervalIntegral.integral_finsetSum fun n _ => htermi n
    rw [e1, Finset.sum_range_eq_add_Ico _ hNpos]
    have e0 : (∫ t in T..2 * T, 1 / (((0 : ℕ) : ℂ) + 1) ^ ((σ : ℂ) + t * I)) = T := by
      simp only [Nat.cast_zero, zero_add, one_cpow, div_one, intervalIntegral.integral_const]
      rw [Complex.real_smul, mul_one]
      push_cast; ring
    rw [e0, add_sub_cancel_left]
    have hlog2 : (2 / 3 : ℝ) < Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    have hb : ∀ n ∈ Finset.Ico 1 N,
        ‖∫ t in T..2 * T, 1 / ((n : ℂ) + 1) ^ ((σ : ℂ) + t * I)‖ ≤
          (4 / Real.log 2) * ((n : ℝ) + 1) ^ (-(5 : ℝ) / 8) := by
      intro n hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ico.mp hn).1
      have hlogpos : Real.log 2 ≤ Real.log ((n : ℝ) + 1) :=
        Real.log_le_log (by norm_num) (by linarith)
      have hlog0 : 0 < Real.log 2 := by linarith
      have hc : -Real.log ((n : ℝ) + 1) ≠ 0 := by linarith
      rw [hterm n, intervalIntegral.integral_const_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      calc ((n : ℝ) + 1) ^ (-σ) * ‖∫ t in T..2 * T,
              cexp (((-Real.log ((n : ℝ) + 1) : ℝ) : ℂ) * t * I)‖
          ≤ ((n : ℝ) + 1) ^ (-(5 : ℝ) / 8) * (4 / Real.log 2) := by
            have hn1' : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
            have hp : ((n : ℝ) + 1) ^ (-σ) ≤ ((n : ℝ) + 1) ^ (-(5 : ℝ) / 8) :=
              Real.rpow_le_rpow_of_exponent_le hn1' (by linarith)
            have hi : ‖∫ t in T..2 * T, cexp (((-Real.log ((n : ℝ) + 1) : ℝ) : ℂ) * t * I)‖ ≤
                4 / Real.log 2 := by
              refine (norm_integral_exp_Icc_le hc _ _).trans ?_
              rw [abs_neg, abs_of_pos (by linarith)]
              exact div_le_div_of_nonneg_left (by norm_num) hlog0 hlogpos
            exact mul_le_mul hp hi (norm_nonneg _) (by positivity)
        _ = (4 / Real.log 2) * ((n : ℝ) + 1) ^ (-(5 : ℝ) / 8) := by ring
    calc _ ≤ ∑ n ∈ Finset.Ico 1 N, ‖∫ t in T..2 * T, 1 / ((n : ℂ) + 1) ^ ((σ : ℂ) + t * I)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Ico 1 N, (4 / Real.log 2) * ((n : ℝ) + 1) ^ (-(5 : ℝ) / 8) :=
          Finset.sum_le_sum hb
      _ = (4 / Real.log 2) * ∑ n ∈ Finset.Ico 1 N, ((n : ℝ) + 1) ^ (-(5 / 8 : ℝ)) := by
          rw [Finset.mul_sum]; norm_num
      _ ≤ (4 / Real.log 2) * ((N : ℝ) ^ (1 - 5 / 8 : ℝ) / (1 - 5 / 8)) := by
          gcongr
          exact sum_rpow_le (by norm_num) (by norm_num) (by exact_mod_cast hNpos)
      _ ≤ (4 / Real.log 2) * ((2 * θ) / (1 - 5 / 8)) := by
          gcongr
          exact rpow_le_of_le_two_sq hT hN1 hNhi (by norm_num)
      _ ≤ 32 * θ := by
          rw [div_mul_div_comm, div_le_iff₀ (by linarith)]
          nlinarith
  -- `N^{1−s}/(1−s)`
  have hBb : ‖∫ t in T..2 * T, B t‖ ≤ 2 * θ := by
    have hpt : ∀ t ∈ Ι T (2 * T), ‖B t‖ ≤ 2 * θ / T := by
      intro t ht
      obtain ⟨h1, -⟩ := hmem' t ht
      have hne := hsub1 t (by linarith)
      simp only [hB, norm_div, norm_neg]
      rw [Complex.norm_natCast_cpow_of_pos hNpos]
      have hre : (1 - ((σ : ℂ) + t * I)).re = 1 - σ := by simp
      have him : T ≤ ‖1 - ((σ : ℂ) + t * I)‖ := by
        refine le_trans ?_ (Complex.abs_im_le_norm _)
        simp; rw [abs_of_pos (by linarith)]; exact h1
      rw [hre]
      gcongr
      exact rpow_le_of_le_two_sq hT hN1 hNhi (by linarith)
    calc _ ≤ 2 * θ / T * |2 * T - T| := intervalIntegral.norm_integral_le_of_norm_le_const hpt
      _ = 2 * θ := by rw [hlen]; field_simp
  -- `N^{−s}/2`
  have hCb : ‖∫ t in T..2 * T, C t‖ ≤ θ := by
    have hpt : ∀ t ∈ Ι T (2 * T), ‖C t‖ ≤ ρ := by
      intro t _
      simp only [hC, norm_div, norm_neg]
      rw [Complex.norm_natCast_cpow_of_pos hNpos]
      have hre : (-((σ : ℂ) + t * I)).re = -σ := by simp
      rw [hre]
      have := rpow_neg_le hT hNlo hσ1
      have h0 : 0 ≤ (N : ℝ) ^ (-σ) := by positivity
      simp only [RCLike.norm_ofNat]
      linarith
    calc _ ≤ ρ * |2 * T - T| := intervalIntegral.norm_integral_le_of_norm_le_const hpt
      _ = T * ρ := by rw [hlen]; ring
      _ ≤ T * T * ρ := by nlinarith
      _ = θ := hTTρ
  -- the remainder `s R_N(s)`
  have hDb : ‖∫ t in T..2 * T, (Z t - A t - B t - C t)‖ ≤ 3 * θ := by
    have hpt : ∀ t ∈ Ι T (2 * T), ‖Z t - A t - B t - C t‖ ≤ 3 * T * ρ := by
      intro t ht
      obtain ⟨h1, h2⟩ := hmem' t ht
      have ht0 : t ≠ 0 := by linarith
      have e : Z t - A t - B t - C t = ((σ : ℂ) + t * I) * tailFn N σ t := by
        simp only [hZ, hA, hB, hC]
        rw [zeta_split (by linarith) ht0 hNpos]
        ring
      rw [e, norm_mul]
      have hs : ‖(σ : ℂ) + t * I‖ ≤ 3 * T := by
        refine (norm_add_le _ _).trans ?_
        rw [Complex.norm_real, Real.norm_of_nonneg (by linarith), norm_mul, Complex.norm_I,
          mul_one, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
        linarith
      have hR : ‖tailFn N σ t‖ ≤ ρ := by
        refine (norm_tailFn_le (by linarith) hNR t).trans ?_
        have := rpow_neg_le hT hNlo hσ1
        have h0 : 0 ≤ (N : ℝ) ^ (-σ) := by positivity
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      calc _ ≤ (3 * T) * ρ := mul_le_mul hs hR (norm_nonneg _) (by linarith)
        _ = 3 * T * ρ := rfl
    calc _ ≤ 3 * T * ρ * |2 * T - T| := intervalIntegral.norm_integral_le_of_norm_le_const hpt
      _ = 3 * (T * T * ρ) := by rw [hlen]; ring
      _ = 3 * θ := by rw [hTTρ]
  rw [hsplit]
  calc _ ≤ ‖(∫ t in T..2 * T, A t) - T‖ + ‖∫ t in T..2 * T, B t‖ + ‖∫ t in T..2 * T, C t‖ +
        ‖∫ t in T..2 * T, (Z t - A t - B t - C t)‖ := norm_add₄_le
    _ ≤ 32 * θ + 2 * θ + θ + 3 * θ := by gcongr
    _ ≤ 40 * θ := by linarith

/-- **Fourth moment of `ζ` right of the critical line, lower bound.** For `5/8 ≤ σ ≤ 3/4` and
`T ≥ 80⁴`, `T/16 ≤ ∫_T^{2T} ‖ζ(σ + it)‖⁴ dt`. -/
theorem fourth_moment_ge {σ : ℝ} (hσ1 : 5 / 8 ≤ σ) (hσ2 : σ ≤ 3 / 4) {T : ℝ}
    (hT : (80 : ℝ) ^ 4 ≤ T) :
    T / 16 ≤ ∫ t in T..2 * T, ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 4 := by
  have hT1 : 1 ≤ T := le_trans (by norm_num) hT
  have hT0 : 0 < T := by linarith
  have hTT : T ≤ 2 * T := by linarith
  set θ := T ^ ((3 : ℝ) / 4) with hθ
  -- `80 θ ≤ T`
  have h80 : 80 * θ ≤ T := by
    have hq : (80 : ℝ) ≤ T ^ ((1 : ℝ) / 4) := by
      calc (80 : ℝ) = ((80 : ℝ) ^ 4) ^ ((1 : ℝ) / 4) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
        _ ≤ T ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow (by positivity) hT (by norm_num)
    have e : T = T ^ ((1 : ℝ) / 4) * θ := by
      rw [hθ, ← Real.rpow_add hT0]; norm_num
    have hθ0 : 0 ≤ θ := by positivity
    calc 80 * θ ≤ T ^ ((1 : ℝ) / 4) * θ := mul_le_mul_of_nonneg_right hq hθ0
      _ = T := e.symm
  set Z : ℝ → ℂ := fun t => riemannZeta ((σ : ℂ) + t * I) with hZ
  have hc := continuousOn_zeta_line σ hT0 hTT
  -- `∫ ‖ζ‖ ≥ T/2`
  have h1 := first_moment hσ1 hσ2 hT1
  have hI : T / 2 ≤ ∫ t in T..2 * T, ‖Z t‖ := by
    have hnorm : ‖(∫ t in T..2 * T, Z t)‖ ≤ ∫ t in T..2 * T, ‖Z t‖ :=
      intervalIntegral.norm_integral_le_integral_norm hTT
    have hrev : ‖((T : ℝ) : ℂ)‖ - ‖(∫ t in T..2 * T, Z t)‖ ≤ ‖(∫ t in T..2 * T, Z t) - T‖ := by
      have := norm_sub_norm_le ((T : ℝ) : ℂ) (∫ t in T..2 * T, Z t)
      rwa [norm_sub_rev] at this
    rw [Complex.norm_real, Real.norm_of_nonneg hT0.le] at hrev
    linarith
  -- Cauchy–Schwarz twice
  have hg : IntervalIntegrable (fun t => ‖Z t‖) volume T (2 * T) := hc.norm.intervalIntegrable
  have hg2 : IntervalIntegrable (fun t => ‖Z t‖ ^ 2) volume T (2 * T) :=
    (hc.norm.pow 2).intervalIntegrable
  have hg4 : IntervalIntegrable (fun t => (‖Z t‖ ^ 2) ^ 2) volume T (2 * T) :=
    ((hc.norm.pow 2).pow 2).intervalIntegrable
  have cs1 := sq_integral_le hTT hg hg2
  have cs2 := sq_integral_le hTT hg2 hg4
  have e4 : (∫ t in T..2 * T, (‖Z t‖ ^ 2) ^ 2) = ∫ t in T..2 * T, ‖Z t‖ ^ 4 := by
    congr 1; funext t; ring
  rw [e4, show 2 * T - T = T by ring] at cs2
  rw [show 2 * T - T = T by ring] at cs1
  set J1 := ∫ t in T..2 * T, ‖Z t‖
  set J2 := ∫ t in T..2 * T, ‖Z t‖ ^ 2
  set J4 := ∫ t in T..2 * T, ‖Z t‖ ^ 4
  have hJ1 : 0 ≤ J1 := by linarith
  have hsq : (T / 2) ^ 2 ≤ J1 ^ 2 := pow_le_pow_left₀ (by linarith) hI 2
  have hJ2 : (T / 2) ^ 2 ≤ T * J2 := le_trans hsq cs1
  have hJ2' : T / 4 ≤ J2 := by nlinarith
  have hJ4 : (T / 4) ^ 2 ≤ T * J4 := le_trans (pow_le_pow_left₀ (by linarith) hJ2' 2) cs2
  nlinarith

/-- `ζ(σ − it)` has the same norm as `ζ(σ + it)` (`riemannZeta_conj`). -/
lemma norm_zeta_neg (σ t : ℝ) :
    ‖riemannZeta ((σ : ℂ) - t * I)‖ = ‖riemannZeta ((σ : ℂ) + t * I)‖ := by
  have e : (σ : ℂ) - t * I = (starRingEnd ℂ) ((σ : ℂ) + t * I) := by
    simp [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
  rw [e, riemannZeta_conj, Complex.norm_conj]

/-- **Fourth moment at negative height** (the shape `ζ(1 − s)`, `s = 1/4 + ε + it`, that D2 produces). -/
theorem fourth_moment_ge_neg {σ : ℝ} (hσ1 : 5 / 8 ≤ σ) (hσ2 : σ ≤ 3 / 4) {T : ℝ}
    (hT : (80 : ℝ) ^ 4 ≤ T) :
    T / 16 ≤ ∫ t in T..2 * T, ‖riemannZeta ((σ : ℂ) - t * I)‖ ^ 4 := by
  simp_rw [norm_zeta_neg]
  exact fourth_moment_ge hσ1 hσ2 hT

end DirichletDivisorProblem.HardyD3
end

end
-- ===== end HardyOmegaFC.FourthMoment =====

-- ===== from HardyOmegaFC.Glue =====
section

/-!
# Rung D4: dyadic glue, `LowerBoundD` proved

For `0 < ε ≤ 1/8` write `f ε t = ‖ζ(1/4+ε+it)² / (1/4+ε+it)‖²`.

* Item 1 (`pointwise_ge`): for `t ≥ 2`, `t^{−4(1/4+ε)} / (2K⁴) · ‖ζ((3/4−ε) − it)‖⁴ ≤ f ε t` (D2 at
  `s = 1/4+ε+it`, `1 − s = (3/4−ε) − it`).
* Item 2 (`block_ge`): for `T ≥ 80⁴`, `∫_T^{2T} f ε ≥ (2T)^{−4(1/4+ε)} · T / (32 K⁴)` (item 1, the monotone
  bound `t^{−a} ≥ (2T)^{−a}` on `[T, 2T]`, and D3 at `σ = 3/4 − ε ∈ [5/8, 3/4]`).
* Item 3 (`eps_mul_integral_ge`, `lowerBoundD`): blocks `[T₀2^j, T₀2^{j+1}]`, `T₀ = 80⁴`, `j < M = ⌈1/ε⌉₊`.
  Every block is `≥ B^{−4ε} / (64 K⁴)` with `B = T₀ 2^M`, and `B^{4ε} ≤ T₀^{1/2} · 2^5 = 6400 · 32`, so the
  `M ≥ 1/ε` blocks give `ε ∫_ℝ f ε ≥ c := 1 / (6400 · 32 · 64 · K⁴)`. No geometric series.
-/

open Filter Asymptotics Real Complex MeasureTheory Set Topology
open scoped Interval

noncomputable section

namespace DirichletDivisorProblem.HardyD4

open DirichletDivisorProblem.HardyD2 (K K_pos norm_zeta_sq_div_sq_ge)
open DirichletDivisorProblem.HardyD3 (fourth_moment_ge_neg)

/-- The integrand of `LowerBoundD`. -/
def f (ε t : ℝ) : ℝ := ‖riemannZeta (1 / 4 + (ε : ℂ) + t * I) ^ 2 / (1 / 4 + (ε : ℂ) + t * I)‖ ^ 2

lemma f_nonneg (ε t : ℝ) : 0 ≤ f ε t := by unfold f; positivity

lemma continuous_f {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 4) : Continuous (f ε) := by
  rw [continuous_iff_continuousAt]
  intro t
  obtain ⟨h0, h1⟩ := DirichletDivisorProblem.HardyD1.line_ne (t := t) hε hε'
  have hl : ContinuousAt (fun t : ℝ => (1 / 4 + (ε : ℂ) + t * I)) t := by fun_prop
  have hz : ContinuousAt riemannZeta (1 / 4 + (ε : ℂ) + t * I) :=
    (differentiableAt_riemannZeta h1).continuousAt
  have hzc : ContinuousAt (fun t : ℝ => riemannZeta (1 / 4 + (ε : ℂ) + t * I)) t :=
    ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => (1 / 4 + (ε : ℂ) + t * I)) hz hl
  unfold f
  exact (((hzc.pow 2).div hl h0).norm).pow 2

/-- **Item 1.** Pointwise lower bound on `Re s = 1/4 + ε`, `t ≥ 2`. -/
theorem pointwise_ge {ε t : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (ht : 2 ≤ t) :
    t ^ (-4 * (1 / 4 + ε)) / (2 * K ^ 4) * ‖riemannZeta (((3 / 4 - ε : ℝ) : ℂ) - t * I)‖ ^ 4 ≤ f ε t := by
  set s : ℂ := 1 / 4 + (ε : ℂ) + t * I with hs
  have hre : s.re = 1 / 4 + ε := by simp [hs]
  have him : s.im = t := by simp [hs]
  have h1s : 1 - s = (((3 / 4 - ε : ℝ) : ℂ) - t * I) := by rw [hs]; push_cast; ring
  have h := norm_zeta_sq_div_sq_ge (s := s) (by rw [hre]; linarith) (by rw [hre]; linarith)
    (by rw [him, abs_of_nonneg (by linarith)]; exact ht)
  rw [hre, him, abs_of_nonneg (by linarith), h1s] at h
  exact h

/-- **Item 2.** One block `[T, 2T]`, `T ≥ 80⁴`. -/
theorem block_ge {ε T : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (hT : (80 : ℝ) ^ 4 ≤ T) :
    (2 * T) ^ (-4 * (1 / 4 + ε)) * T / (32 * K ^ 4) ≤ ∫ t in T..2 * T, f ε t := by
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hTT : T ≤ 2 * T := by linarith
  have hT2 : 2 ≤ T := le_trans (by norm_num) hT
  set σ : ℝ := 3 / 4 - ε with hσ
  set a : ℝ := -4 * (1 / 4 + ε) with ha
  have ha0 : a ≤ 0 := by rw [ha]; linarith
  set g : ℝ → ℝ := fun t => ‖riemannZeta ((σ : ℂ) - t * I)‖ ^ 4 with hg
  have hD3 : T / 16 ≤ ∫ t in T..2 * T, g t :=
    fourth_moment_ge_neg (by rw [hσ]; linarith) (by rw [hσ]; linarith) hT
  have hgc : ContinuousOn g (uIcc T (2 * T)) := by
    have hc := DirichletDivisorProblem.HardyD3.continuousOn_zeta_line σ hT0 hTT
    have e : g = fun t : ℝ => ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 4 := by
      funext t; rw [hg]; exact congrArg (· ^ 4) (DirichletDivisorProblem.HardyD3.norm_zeta_neg σ t)
    rw [e]; exact (hc.norm).pow 4
  have hgi : IntervalIntegrable g volume T (2 * T) := hgc.intervalIntegrable
  have hfi : IntervalIntegrable (f ε) volume T (2 * T) :=
    (continuous_f hε (by linarith)).intervalIntegrable _ _
  set C : ℝ := (2 * T) ^ a / (2 * K ^ 4) with hC
  have hC0 : 0 ≤ C := by rw [hC]; have := K_pos; positivity
  have hmono : ∫ t in T..2 * T, C * g t ≤ ∫ t in T..2 * T, f ε t := by
    apply intervalIntegral.integral_mono_on hTT (hgi.const_mul C) hfi
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hT0 ht.1
    have hp : (2 * T) ^ a ≤ t ^ a := Real.rpow_le_rpow_of_nonpos ht0 ht.2 ha0
    have h1 := pointwise_ge hε hε' (le_trans hT2 ht.1)
    have hK : 0 < 2 * K ^ 4 := by have := K_pos; positivity
    calc C * g t = (2 * T) ^ a / (2 * K ^ 4) * ‖riemannZeta (((3 / 4 - ε : ℝ) : ℂ) - t * I)‖ ^ 4 := by
            rw [hC, hg]
      _ ≤ t ^ a / (2 * K ^ 4) * ‖riemannZeta (((3 / 4 - ε : ℝ) : ℂ) - t * I)‖ ^ 4 := by
            gcongr
      _ ≤ f ε t := h1
  rw [intervalIntegral.integral_const_mul] at hmono
  have hK4 : 0 < K ^ 4 := pow_pos K_pos 4
  calc (2 * T) ^ a * T / (32 * K ^ 4) = C * (T / 16) := by rw [hC]; field_simp; ring
    _ ≤ C * ∫ t in T..2 * T, g t := mul_le_mul_of_nonneg_left hD3 hC0
    _ ≤ _ := hmono

/-- `T₀ = 80⁴`, the start of the first block. -/
def T₀ : ℝ := (80 : ℝ) ^ 4

lemma T₀_pos : 0 < T₀ := by unfold T₀; norm_num

/-- `T₀^{4ε} ≤ 6400` for `0 ≤ ε ≤ 1/8`. -/
lemma T₀_rpow_le {ε : ℝ} (_hε : 0 ≤ ε) (hε' : ε ≤ 1 / 8) : T₀ ^ (4 * ε) ≤ 6400 := by
  have h1 : T₀ ^ (4 * ε) ≤ T₀ ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by unfold T₀; norm_num) (by linarith)
  have h2 : T₀ ^ ((1 : ℝ) / 2) = 6400 := by
    unfold T₀
    rw [show ((80 : ℝ) ^ 4) = (6400 : ℝ) ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num)]
    norm_num
  linarith

/-- `(2^M)^{4ε} ≤ 32` when `M ε ≤ 1 + ε` and `ε ≤ 1/8`. -/
lemma two_pow_rpow_le {ε : ℝ} (_hε : 0 ≤ ε) (hε' : ε ≤ 1 / 8) {M : ℕ} (hM : (M : ℝ) * ε ≤ 1 + ε) :
    ((2 : ℝ) ^ M) ^ (4 * ε) ≤ 32 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  calc (2 : ℝ) ^ ((M : ℝ) * (4 * ε)) ≤ (2 : ℝ) ^ (5 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
    _ = 32 := by norm_num

/-- The constant of `LowerBoundD`. -/
def c : ℝ := 1 / (6400 * 32 * 64 * K ^ 4)

lemma c_pos : 0 < c := by unfold c; have := K_pos; positivity

/-- **Item 3.** `ε ∫_ℝ f ε ≥ c` for `0 < ε ≤ 1/8`, when `f ε` is integrable. -/
theorem eps_mul_integral_ge {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (hint : Integrable (f ε)) :
    c ≤ ε * ∫ t, f ε t := by
  set M : ℕ := ⌈1 / ε⌉₊ with hM
  have hM1 : 1 / ε ≤ M := Nat.le_ceil _
  have hM2 : (M : ℝ) < 1 / ε + 1 := Nat.ceil_lt_add_one (by positivity)
  have hMε : 1 ≤ (M : ℝ) * ε := by
    have := mul_le_mul_of_nonneg_right hM1 hε.le
    rwa [one_div, inv_mul_cancel₀ hε.ne'] at this
  have hMε' : (M : ℝ) * ε ≤ 1 + ε := by
    have := mul_le_mul_of_nonneg_right hM2.le hε.le
    rwa [add_mul, one_div, inv_mul_cancel₀ hε.ne', one_mul] at this
  set a : ℕ → ℝ := fun j => T₀ * 2 ^ j with ha
  set B : ℝ := T₀ * 2 ^ M with hB
  have hB0 : 0 < B := by rw [hB]; have := T₀_pos; positivity
  have hK4 : 0 < K ^ 4 := pow_pos K_pos 4
  -- `B^{−4ε} ≥ 1/(6400·32)`
  have hBpow : B ^ (4 * ε) ≤ 6400 * 32 := by
    rw [hB, Real.mul_rpow T₀_pos.le (by positivity)]
    exact mul_le_mul (T₀_rpow_le hε.le hε') (two_pow_rpow_le hε.le hε' hMε') (by positivity)
      (by norm_num)
  -- every block is `≥ c'`
  set c' : ℝ := 1 / (6400 * 32 * 64 * K ^ 4) with hc'
  have hblock : ∀ j < M, c' ≤ ∫ t in a j..a (j + 1), f ε t := by
    intro j hj
    have haj : (80 : ℝ) ^ 4 ≤ a j := by
      rw [ha]; show T₀ ≤ T₀ * 2 ^ j
      exact le_mul_of_one_le_right T₀_pos.le (one_le_pow₀ (by norm_num))
    have haj0 : 0 < a j := lt_of_lt_of_le (by norm_num) haj
    have hsucc : a (j + 1) = 2 * a j := by rw [ha]; simp only; rw [pow_succ]; ring
    have h := block_ge hε hε' haj
    rw [← hsucc] at h
    -- `(2 a_j)^{−1−4ε} a_j = (2a_j)^{−4ε}/2 ≥ B^{−4ε}/2`
    have hle : a (j + 1) ≤ B := by
      rw [ha, hB]; exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hj) T₀_pos.le
    have hs0 : 0 < a (j + 1) := by rw [hsucc]; linarith
    have hsplit : a (j + 1) ^ (-4 * (1 / 4 + ε)) * a j = (a (j + 1) ^ (4 * ε))⁻¹ / 2 := by
      rw [show -4 * (1 / 4 + ε) = -(4 * ε) + (-1) by ring, Real.rpow_add hs0, Real.rpow_neg hs0.le,
        Real.rpow_neg_one, hsucc]
      field_simp
    have hpow : a (j + 1) ^ (4 * ε) ≤ 6400 * 32 :=
      le_trans (Real.rpow_le_rpow hs0.le hle (by linarith)) hBpow
    have hpos : 0 < a (j + 1) ^ (4 * ε) := Real.rpow_pos_of_pos hs0 _
    rw [hsplit] at h
    refine le_trans ?_ h
    rw [hc', div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    rw [one_mul]
    have : (a (j + 1) ^ (4 * ε))⁻¹ * (6400 * 32) ≥ 1 := by
      rw [ge_iff_le, ← div_eq_inv_mul, le_div_iff₀ hpos, one_mul]; exact hpow
    nlinarith
  -- glue the blocks
  have hcont := continuous_f hε (by linarith)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := f ε) (a := a) (n := M)
    (fun k _ => hcont.intervalIntegrable _ _)
  have hge : (M : ℝ) * c' ≤ ∫ t in a 0..a M, f ε t := by
    rw [← hsum]
    have := Finset.sum_le_sum (s := Finset.range M) (fun j hj => hblock j (Finset.mem_range.mp hj))
    simpa using this
  have ha0M : a 0 ≤ a M := by
    rw [ha]; exact mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num)) T₀_pos.le |>.trans_eq' (by simp)
  have hR : (∫ t in a 0..a M, f ε t) ≤ ∫ t, f ε t := by
    rw [intervalIntegral.integral_of_le ha0M]
    exact setIntegral_le_integral hint (Eventually.of_forall (f_nonneg ε))
  have hc'0 : 0 < c' := by rw [hc']; positivity
  calc c = c' := rfl
    _ ≤ ε * ((M : ℝ) * c') := by nlinarith
    _ ≤ ε * ∫ t, f ε t := mul_le_mul_of_nonneg_left (hge.trans hR) hε.le

/-- **D4.** `LowerBoundD` holds, with `c = 1/(6400·32·64·K⁴)`, no hypothesis. -/
theorem lowerBoundD : DirichletDivisorProblem.HardyD1.LowerBoundD := by
  refine ⟨c, c_pos, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 8 by norm_num)] with ε hε hint
  exact eps_mul_integral_ge hε.1 hε.2.le hint

end DirichletDivisorProblem.HardyD4
end

end
-- ===== end HardyOmegaFC.Glue =====

end OMAPort_Divisor

open Filter Asymptotics Real

/-- Hardy: `¬ (divisorError =o[atTop] fun x => x ^ ((1 : ℝ) / 4))` (original proof: D1 applied to D4). -/
theorem OMA.solution : type_of% @DirichletDivisorProblem.divisor_error_hardy :=
  OMAPort_Divisor.DirichletDivisorProblem.HardyD1.divisor_error_hardy_of_lowerBound OMAPort_Divisor.DirichletDivisorProblem.HardyD4.lowerBoundD
