import OMAStatements.S_oeis_a143412
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# A143412: Gaussian expectations of even Chebyshev polynomials

Source: https://oeis.org/A143412
Proof: @CubeJerry. Canonical statement: @krezojh (PR32885).

We prove polynomial Gaussian integration by parts, then combine the Chebyshev
recurrence with T'_m = m U_(m-1). The expectations satisfy the same recurrence
and initial conditions as A143412. All analytic and polynomial identities are
checked by Lean using Mathlib; no numerical or external oracle is used.
-/

open MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal

namespace A143412Proof

lemma integrable_poly (p : ℝ[X]) :
    Integrable (fun x : ℝ => p.eval x) (gaussianReal 0 1) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [eval_add]
    exact hp.fun_add hq
  | monomial n c =>
    have h := integrable_pow_of_mem_interior_integrableExpSet
      (X := fun x : ℝ => x) (μ := gaussianReal 0 1) (by simp) n
    simpa only [eval_monomial] using h.const_mul c

lemma integrable_weighted (p : ℝ[X]) :
    Integrable (fun x : ℝ => gaussianPDFReal 0 1 x * p.eval x) := by
  have h := integrable_poly p
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)] at h
  have h' := (integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF 0 1) (ae_of_all _ fun _ => gaussianPDF_lt_top)).mp h
  simpa only [toReal_gaussianPDF, smul_eq_mul] using h'

lemma gaussian_deriv (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have h : HasDerivAt
      (fun y : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2))
      ((Real.sqrt (2 * Real.pi))⁻¹ * (Real.exp (-x ^ 2 / 2) * (-(2 * x) / 2))) x := by
    simpa only [Pi.pow_apply, Pi.neg_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub,
      pow_one, mul_one] using
      (((hasDerivAt_id x).pow 2).neg.div_const 2).exp.const_mul
        ((Real.sqrt (2 * Real.pi))⁻¹)
  have h' := h.congr_deriv (g' := -x *
    ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2))) (by ring)
  simpa only [gaussianPDFReal_def, NNReal.coe_one, sub_zero, mul_one] using h'

lemma stein (p : ℝ[X]) :
    (∫ x : ℝ, x * p.eval x ∂gaussianReal 0 1) =
      ∫ x : ℝ, p.derivative.eval x ∂gaussianReal 0 1 := by
  have hp := integrable_weighted p
  have hd := integrable_weighted p.derivative
  have hx := (integrable_weighted (X * p)).neg
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x : ℝ => p.eval x) (u' := fun x : ℝ => p.derivative.eval x)
    (v := gaussianPDFReal 0 1) (v' := fun x : ℝ => -x * gaussianPDFReal 0 1 x)
    (fun x _ => p.hasDerivAt x) (fun x _ => gaussian_deriv x)
    (by
      convert hx using 1
      funext x
      simp only [Pi.mul_apply, Pi.neg_apply, eval_mul, eval_X]
      ring)
    (by
      convert hd using 1
      funext x
      exact mul_comm _ _)
    (by
      convert hp using 1
      funext x
      exact mul_comm _ _)
  simp only [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    smul_eq_mul]
  have heq : (fun x : ℝ => p.eval x * (-x * gaussianPDFReal 0 1 x)) =
      fun x : ℝ => -(gaussianPDFReal 0 1 x * (x * p.eval x)) := by
    funext x
    ring
  rw [heq, integral_neg] at h
  have heq' : (fun x : ℝ => p.derivative.eval x * gaussianPDFReal 0 1 x) =
      fun x : ℝ => gaussianPDFReal 0 1 x * p.derivative.eval x := by
    funext x
    ring
  rw [heq'] at h
  exact neg_injective h

end A143412Proof

open MeasureTheory ProbabilityTheory Polynomial Polynomial.Chebyshev

namespace A143412Proof

noncomputable def expect (p : ℝ[X]) : ℝ :=
  ∫ x : ℝ, p.eval x ∂gaussianReal 0 1

lemma expect_sub (p q : ℝ[X]) : expect (p - q) = expect p - expect q := by
  simp only [expect, eval_sub]
  exact integral_sub (integrable_poly p) (integrable_poly q)

lemma expect_const_mul (c : ℝ) (p : ℝ[X]) :
    expect (Polynomial.C c * p) = c * expect p := by
  simp only [expect, eval_mul, eval_C, integral_const_mul]

@[simp] lemma expect_one : expect 1 = 1 := by simp [expect]

lemma expect_stein (p : ℝ[X]) : expect (X * p) = expect p.derivative := by
  simpa only [expect, eval_mul, eval_X] using stein p

lemma U_difference (m : ℤ) :
    U ℝ (m + 4) - U ℝ m = 4 * X * T ℝ (m + 3) := by
  have h1 : U ℝ (m + 4) = 2 * X * U ℝ (m + 3) - U ℝ (m + 2) := by
    simpa only [add_assoc, Int.reduceAdd] using U_add_two ℝ (m + 2)
  have h2 := U_add_two ℝ m
  have ht : 2 * T ℝ (m + 3) = U ℝ (m + 3) - U ℝ (m + 1) := by
    simpa only [add_assoc, Int.reduceAdd] using two_mul_T_eq_U_sub_U ℝ (m + 1)
  linear_combination h1 - h2 - 2 * X * ht

lemma expected_U_rec (m : ℤ) :
    expect (U ℝ (m + 4)) =
      4 * ((m + 3 : ℤ) : ℝ) * expect (U ℝ (m + 2)) + expect (U ℝ m) := by
  have hd : (T ℝ (m + 3)).derivative = (m + 3 : ℤ) * U ℝ (m + 2) := by
    simpa only [show m + 3 - 1 = m + 2 by ring] using
      T_derivative_eq_U (R := ℝ) (m + 3)
  have he : expect (U ℝ (m + 4)) - expect (U ℝ m) =
      4 * ((m + 3 : ℤ) : ℝ) * expect (U ℝ (m + 2)) := by
    calc
      _ = expect (U ℝ (m + 4) - U ℝ m) := (expect_sub _ _).symm
      _ = 4 * expect (X * T ℝ (m + 3)) := by
        rw [U_difference]
        simp only [expect, eval_mul, eval_ofNat, mul_assoc, integral_const_mul]
      _ = 4 * expect (T ℝ (m + 3)).derivative := by rw [expect_stein]
      _ = _ := by
        rw [hd]
        simp only [expect, eval_mul, eval_intCast, integral_const_mul]
        ring
  linear_combination he

lemma expected_U_two : expect (U ℝ 2) = 3 := by
  have hx : expect (X ^ 2) = 1 := by
    simpa only [pow_two, derivative_X, expect_one] using expect_stein X
  rw [U_two, expect_sub]
  have h4 : expect (4 * X ^ 2) = 4 * expect (X ^ 2) := by
    simpa only [C_ofNat] using expect_const_mul 4 (X ^ 2)
  rw [h4, hx, expect_one]
  norm_num

lemma solution : type_of% @OMA.S_oeis_a143412.main := by
  intro n
  change expect (U ℝ (2 * (n : ℤ))) = (OMA.S_oeis_a143412.a n : ℝ)
  induction n using Nat.twoStepInduction with
  | zero => simp [OMA.S_oeis_a143412.a]
  | one => simpa [OMA.S_oeis_a143412.a] using expected_U_two
  | more n ih0 ih1 =>
    have h := expected_U_rec (2 * (n : ℤ))
    have h4 : (2 * ((n + 2 : ℕ) : ℤ)) = 2 * (n : ℤ) + 4 := by push_cast; ring
    have h2 : (2 * ((n + 1 : ℕ) : ℤ)) = 2 * (n : ℤ) + 2 := by push_cast; ring
    rw [h4, h, ← h2, ih1, ih0, OMA.S_oeis_a143412.a]
    push_cast
    ring

end A143412Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a143412.main := A143412Proof.solution
