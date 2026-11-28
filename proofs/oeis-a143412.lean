import OMAStatements.S_oeis_a143412
import Mathlib

open MeasureTheory ProbabilityTheory Polynomial

namespace OMA.S_oeis_a143412

lemma integ (p : ℝ[X]) : Integrable (fun x : ℝ => p.eval x * Real.exp (-x ^ 2 / 2)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    refine (hp.add hq).congr (Filter.Eventually.of_forall fun x => ?_)
    simp [add_mul]
  | monomial n c =>
    have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num) (s := n)
      (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    refine (h.const_mul c).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Polynomial.eval_monomial, Real.rpow_natCast]
    rw [show -(1 / 2 : ℝ) * x ^ 2 = -x ^ 2 / 2 by ring]
    ring

lemma stein (p : ℝ[X]) :
    ∫ x : ℝ, (X * p).eval x * Real.exp (-x ^ 2 / 2)
      = ∫ x : ℝ, (derivative p).eval x * Real.exp (-x ^ 2 / 2) := by
  have hv : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Real.exp (-x ^ 2 / 2))
      (-x * Real.exp (-x ^ 2 / 2)) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => -x ^ 2 / 2) (-x) x := by
      have := ((hasDerivAt_pow 2 x).neg).div_const 2
      have e : -((2 : ℕ) * x ^ (2 - 1)) / 2 = -x := by norm_num; ring
      rw [e] at this
      exact this
    have := h1.exp
    convert this using 1
    ring
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x : ℝ => p.eval x) (v := fun x : ℝ => Real.exp (-x ^ 2 / 2))
    (u' := fun x : ℝ => (derivative p).eval x) (v' := fun x : ℝ => -x * Real.exp (-x ^ 2 / 2))
    (fun x _ => p.hasDerivAt x) (fun x _ => hv x)
    ((integ (X * p)).neg.congr (Filter.Eventually.of_forall fun x => by
      simp only [Pi.neg_apply, Pi.mul_apply, eval_mul, eval_X]; ring))
    (integ (derivative p)) (integ p)
  have e : ∀ x : ℝ, (X * p).eval x * Real.exp (-x ^ 2 / 2)
      = -(p.eval x * (-x * Real.exp (-x ^ 2 / 2))) := by
    intro x; simp only [eval_mul, eval_X]; ring
  simp only [e, integral_neg, h, neg_neg]

lemma conv (p : ℝ[X]) :
    ∫ x : ℝ, p.eval x ∂(gaussianReal 0 1)
      = (√(2 * Real.pi))⁻¹ * ∫ x : ℝ, p.eval x * Real.exp (-x ^ 2 / 2) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num), ← integral_const_mul]
  congr 1
  ext x
  simp [gaussianPDFReal]
  ring

lemma polyId (m : ℤ) :
    Chebyshev.U ℝ (m + 2) = X * (C 4 * Chebyshev.T ℝ (m + 1)) + Chebyshev.U ℝ (m - 2) := by
  have h1 := Chebyshev.U_add_two ℝ m
  have h2 := Chebyshev.U_sub_two ℝ m
  have h3 := Chebyshev.T_eq_U_sub_X_mul_U ℝ (m + 1)
  rw [add_sub_cancel_right] at h3
  have h4 := Chebyshev.U_sub_one ℝ m
  have h5 : (C 4 : ℝ[X]) = 4 := rfl
  rw [h5]
  linear_combination h1 - h2 - 4 * X * h3 - 2 * X * h4

lemma recE (m : ℤ) :
    ∫ x : ℝ, (Chebyshev.U ℝ (m + 2)).eval x ∂(gaussianReal 0 1)
      = 4 * (m + 1) * ∫ x : ℝ, (Chebyshev.U ℝ m).eval x ∂(gaussianReal 0 1)
        + ∫ x : ℝ, (Chebyshev.U ℝ (m - 2)).eval x ∂(gaussianReal 0 1) := by
  rw [conv, conv, conv, polyId]
  simp only [eval_add]
  simp only [add_mul]
  rw [integral_add (integ _) (integ _), stein]
  have e : ∀ x : ℝ, (derivative (C 4 * Chebyshev.T ℝ (m + 1))).eval x * Real.exp (-x ^ 2 / 2)
      = 4 * (m + 1) * ((Chebyshev.U ℝ m).eval x * Real.exp (-x ^ 2 / 2)) := by
    intro x
    simp [Chebyshev.T_derivative_eq_U]
    ring
  simp only [e, integral_const_mul]
  ring

end OMA.S_oeis_a143412

open OMA.S_oeis_a143412 in
theorem OMA.solution : type_of% @OMA.S_oeis_a143412.main := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => simp [a]
  | one =>
    have h := recE 0
    simp at h
    simp [a]
    rw [h]
    norm_num
  | more n h0 h1 =>
    have h := recE (2 * (n : ℤ) + 2)
    rw [show 2 * ((n + 2 : ℕ) : ℤ) = 2 * (n : ℤ) + 2 + 2 by push_cast; ring, h,
      show 2 * (n : ℤ) + 2 - 2 = 2 * (n : ℤ) by ring,
      show 2 * (n : ℤ) + 2 = 2 * ((n + 1 : ℕ) : ℤ) by push_cast; ring, h0, h1]
    simp only [a]
    push_cast
    ring
