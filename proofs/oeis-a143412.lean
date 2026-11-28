import OMAStatements.S_oeis_a143412
import Mathlib

/-!
# OEIS A143412: Main diagonal of A143410.

Source: https://oeis.org/A143412
Credit: @krezojh

The proof uses Stein's identity for polynomials, a four-step Chebyshev
identity, and induction on consecutive pairs of terms.
-/

open MeasureTheory ProbabilityTheory Polynomial
open Polynomial.Chebyshev

namespace A143412

open OMA.S_oeis_a143412 (a)

/-! ## 1. Problem statement -/

/-- The mean of the even-indexed Chebyshev polynomial
under a standard normal law. -/
noncomputable def gaussianMean (n : ℕ) : ℝ :=
  ∫ x : ℝ, (Polynomial.Chebyshev.U ℝ (2 * (n : ℤ))).eval x
    ∂(gaussianReal 0 1)

/-- The OEIS claim, stated as a proposition. -/
def conjecture : Prop :=
  ∀ n : ℕ, gaussianMean n = (a n : ℝ)


/-! ## 2. Standard Gaussian density -/

set_option maxHeartbeats 1000000 in
/-- Explicit formula for the standard Gaussian density. -/
lemma standard_pdf_eq :
    gaussianPDFReal 0 1 =
      fun x : ℝ =>
        (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
  funext x
  simp only [gaussianPDFReal_def, NNReal.coe_one,
    sub_zero, mul_one]
  have h :
      -(x ^ 2) / 2 =
        -(1 / 2 : ℝ) * x ^ 2 := by
    ring
  rw [h]


set_option maxHeartbeats 1000000 in
/-- The derivative of the standard Gaussian density. -/
lemma standard_pdf_hasDerivAt (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1)
      (-x * gaussianPDFReal 0 1 x) x := by
  rw [standard_pdf_eq]

  have hpow :
      HasDerivAt (fun y : ℝ => y ^ 2)
        (2 * x) x := by
    simpa using hasDerivAt_pow 2 x

  have hinner :=
    hpow.const_mul (-(1 / 2 : ℝ))

  have h₁ : -(1 / 2 : ℝ) * (2 * x) = -x := by
    ring

  rw [h₁] at hinner

  have h :=
    hinner.exp.const_mul
      ((Real.sqrt (2 * Real.pi))⁻¹)

  have h₂ :
      (Real.sqrt (2 * Real.pi))⁻¹ *
        (Real.exp (-(1 / 2 : ℝ) * x ^ 2) * (-x)) =
      -x * ((Real.sqrt (2 * Real.pi))⁻¹ *
        Real.exp (-(1 / 2 : ℝ) * x ^ 2)) := by
    ring

  rw [← h₂]
  exact h


/-! ## 3. Integrability of Gaussian-weighted polynomials -/

set_option maxHeartbeats 1000000 in
/-- Every monomial times the Gaussian weight is integrable. -/
lemma gaussian_weighted_pow_integrable (n : ℕ) :
    Integrable (fun x : ℝ =>
      x ^ n * Real.exp (-(1 / 2 : ℝ) * x ^ 2))
      volume := by

  have hn₀ : (0 : ℝ) ≤ (n : ℝ) :=
    Nat.cast_nonneg n

  have hn : (-1 : ℝ) < (n : ℝ) := by
    linarith

  simpa only [Real.rpow_natCast] using
    (integrable_rpow_mul_exp_neg_mul_sq
      (b := (1 / 2 : ℝ))
      (by norm_num) hn)


set_option maxHeartbeats 1000000 in
/-- Every polynomial times the Gaussian density is integrable. -/
lemma gaussian_weighted_poly_integrable
    (p : Polynomial ℝ) :
    Integrable (fun x : ℝ =>
      gaussianPDFReal 0 1 x * p.eval x)
      volume := by

  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have he :
        (fun x : ℝ =>
          gaussianPDFReal 0 1 x * (p + q).eval x) =
        ((fun x : ℝ =>
          gaussianPDFReal 0 1 x * p.eval x) +
        (fun x : ℝ =>
          gaussianPDFReal 0 1 x * q.eval x)) := by
      funext x
      simp only [Polynomial.eval_add,
        Pi.add_apply, mul_add]

    rw [he]
    exact hp.add hq

  | monomial n c =>
    rw [standard_pdf_eq]

    have h :=
      (gaussian_weighted_pow_integrable n).const_mul
        ((Real.sqrt (2 * Real.pi))⁻¹ * c)

    have he :
        (fun x : ℝ =>
          ((Real.sqrt (2 * Real.pi))⁻¹ *
            Real.exp (-(1 / 2 : ℝ) * x ^ 2)) *
            (Polynomial.monomial n c).eval x) =
        (fun x : ℝ =>
          ((Real.sqrt (2 * Real.pi))⁻¹ * c) *
            (x ^ n *
              Real.exp (-(1 / 2 : ℝ) * x ^ 2))) := by
      funext x
      simp only [Polynomial.eval_monomial]
      ring

    rw [he]
    exact h


set_option maxHeartbeats 1000000 in
/-- The analytic derivative agrees with the formal
polynomial derivative. -/
lemma polynomial_hasDerivAt_aux
    (p : Polynomial ℝ) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => p.eval y)
      (p.derivative.eval x) x := by
  exact (Polynomial.hasStrictDerivAt p x).hasDerivAt


/-! ## 4. Stein's identity -/

set_option maxHeartbeats 1000000 in
/-- Stein's identity for polynomials under the standard normal law:
E[X p(X)] = E[p'(X)]. -/
lemma gaussian_stein_polynomial (p : Polynomial ℝ) :
    (∫ x : ℝ, x * p.eval x ∂(gaussianReal 0 1)) =
    (∫ x : ℝ, p.derivative.eval x
      ∂(gaussianReal 0 1)) := by

  have hp := gaussian_weighted_poly_integrable p

  have hdp :=
    gaussian_weighted_poly_integrable p.derivative

  have hxp :
      Integrable (fun x : ℝ =>
        gaussianPDFReal 0 1 x * (x * p.eval x))
        volume := by

    have he :
        (fun x : ℝ =>
          gaussianPDFReal 0 1 x *
            (Polynomial.X * p).eval x) =
        (fun x : ℝ =>
          gaussianPDFReal 0 1 x *
            (x * p.eval x)) := by
      funext x
      rw [Polynomial.eval_mul, Polynomial.eval_X]

    rw [← he]
    exact gaussian_weighted_poly_integrable
      (Polynomial.X * p)

  have hderiv (x : ℝ) :
      HasDerivAt
        (fun y : ℝ =>
          gaussianPDFReal 0 1 y * p.eval y)
        (gaussianPDFReal 0 1 x * p.derivative.eval x -
          gaussianPDFReal 0 1 x *
            (x * p.eval x)) x := by

    have h :=
      (standard_pdf_hasDerivAt x).mul
        (polynomial_hasDerivAt_aux p x)

    have he :
        (-x * gaussianPDFReal 0 1 x) * p.eval x +
          gaussianPDFReal 0 1 x * p.derivative.eval x =
        gaussianPDFReal 0 1 x * p.derivative.eval x -
          gaussianPDFReal 0 1 x * (x * p.eval x) := by
      ring

    rw [← he]
    exact h

  have hsub :
      Integrable
        (fun x : ℝ =>
          gaussianPDFReal 0 1 x * p.derivative.eval x -
          gaussianPDFReal 0 1 x *
            (x * p.eval x))
        volume := by
    exact hdp.sub hxp

  have hzero :
      (∫ x : ℝ,
        gaussianPDFReal 0 1 x * p.derivative.eval x -
          gaussianPDFReal 0 1 x *
            (x * p.eval x)) = 0 := by
    exact integral_eq_zero_of_hasDerivAt_of_integrable
      hderiv hsub hp

  rw [integral_sub hdp hxp] at hzero

  rw [integral_gaussianReal_eq_integral_smul
        (by norm_num),
      integral_gaussianReal_eq_integral_smul
        (by norm_num)]

  simp only [smul_eq_mul]
  linarith


/-! ## 5. Chebyshev polynomial identity -/

set_option maxHeartbeats 1000000 in
/-- U_(k+4) - U_k = 4 X T_(k+3). -/
lemma chebyshev_four_step (k : ℤ) :
    U ℝ (k + 4) - U ℝ k =
      4 * X * T ℝ (k + 3) := by

  have h1 :
      U ℝ (k + 4) =
        2 * X * U ℝ (k + 3) -
          U ℝ (k + 2) := by
    simpa only [
      show k + 2 + 2 = k + 4 by omega,
      show k + 2 + 1 = k + 3 by omega
    ] using U_add_two ℝ (k + 2)

  have h2 := U_add_two ℝ k

  have h3 :
      2 * T ℝ (k + 3) =
        U ℝ (k + 3) - U ℝ (k + 1) := by
    simpa only [
      show k + 1 + 2 = k + 3 by omega
    ] using two_mul_T_eq_U_sub_U ℝ (k + 1)

  linear_combination h1 - h2 - (2 * X) * h3


/-! ## 6. Gaussian expectations of polynomials -/

/-- The expectation of a polynomial under the standard normal law. -/
noncomputable def polyMean (p : Polynomial ℝ) : ℝ :=
  ∫ x : ℝ, p.eval x ∂(gaussianReal 0 1)


set_option maxHeartbeats 1000000 in
/-- Linearity of Gaussian expectation with respect to subtraction. -/
lemma polyMean_sub (p q : Polynomial ℝ) :
    polyMean (p - q) = polyMean p - polyMean q := by
  unfold polyMean
  simp_rw [
    integral_gaussianReal_eq_integral_smul
      (by norm_num : (1 : NNReal) ≠ 0),
    smul_eq_mul
  ]
  simp only [Polynomial.eval_sub, mul_sub]
  exact integral_sub
    (gaussian_weighted_poly_integrable p)
    (gaussian_weighted_poly_integrable q)


set_option maxHeartbeats 1000000 in
/-- Stein's identity expressed using polyMean. -/
lemma polyMean_X (p : Polynomial ℝ) :
    polyMean (X * p) = polyMean p.derivative := by
  unfold polyMean
  simp only [Polynomial.eval_mul, Polynomial.eval_X]
  exact gaussian_stein_polynomial p


set_option maxHeartbeats 1000000 in
/-- Compatibility with multiplication by four. -/
lemma polyMean_four_mul (p : Polynomial ℝ) :
    polyMean (4 * p) = 4 * polyMean p := by
  unfold polyMean
  simp only [Polynomial.eval_mul, Polynomial.eval_ofNat]
  rw [integral_const_mul]


set_option maxHeartbeats 1000000 in
/-- Compatibility with integer scalar multiplication. -/
lemma polyMean_int_mul (k : ℤ) (p : Polynomial ℝ) :
    polyMean ((k : Polynomial ℝ) * p) =
      (k : ℝ) * polyMean p := by
  unfold polyMean
  simp only [Polynomial.eval_mul, Polynomial.eval_intCast]
  rw [integral_const_mul]


/-! ## 7. Recurrence for Gaussian Chebyshev expectations -/

set_option maxHeartbeats 1000000 in
/-- The four-step recurrence obtained from the Chebyshev
identity and Stein's identity. -/
lemma polyMean_four_step (k : ℤ) :
    polyMean (U ℝ (k + 4)) =
      4 * ((k : ℝ) + 3) *
        polyMean (U ℝ (k + 2)) +
      polyMean (U ℝ k) := by

  have h := congrArg polyMean
    (chebyshev_four_step k)

  rw [polyMean_sub, mul_assoc,
    polyMean_four_mul, polyMean_X] at h

  rw [T_derivative_eq_U,
    show k + 3 - 1 = k + 2 by omega,
    polyMean_int_mul] at h

  push_cast at h
  linarith


/-! ## 8. Initial conditions -/

set_option maxHeartbeats 1000000 in
/-- The zeroth Gaussian Chebyshev expectation equals a(0). -/
lemma gaussianMean_zero :
    gaussianMean 0 = (a 0 : ℝ) := by
  simp [gaussianMean, a, Polynomial.Chebyshev.U_zero]


set_option maxHeartbeats 1000000 in
/-- The first Gaussian Chebyshev expectation equals a(1). -/
lemma gaussianMean_one :
    gaussianMean 1 = (a 1 : ℝ) := by

  let μ := gaussianReal 0 1

  have hx : MemLp (id : ℝ → ℝ) 2 μ :=
    memLp_id_gaussianReal 2

  have hsquare :
      Integrable (fun x : ℝ => x ^ 2) μ := by
    simpa only [id_eq] using hx.integrable_sq

  have hsecond :
      (∫ x : ℝ, x ^ 2 ∂μ) = 1 := by

    have hmean :
        (∫ x : ℝ, id x ∂μ) = 0 :=
      integral_id_gaussianReal

    have hvar :
        variance (id : ℝ → ℝ) μ = 1 := by
      simpa only [NNReal.coe_one] using
        (variance_id_gaussianReal (μ := 0) (v := 1))

    rw [variance_eq_integral hx.aemeasurable,
      hmean] at hvar

    simpa only [id_eq, sub_zero] using hvar

  change
    (∫ x : ℝ, (Polynomial.Chebyshev.U ℝ 2).eval x ∂μ) =
      (a 1 : ℝ)

  simp only [
    Polynomial.Chebyshev.U_two,
    Polynomial.eval_sub,
    Polynomial.eval_mul,
    Polynomial.eval_ofNat,
    Polynomial.eval_pow,
    Polynomial.eval_X,
    Polynomial.eval_one
  ]

  rw [integral_sub (hsquare.const_mul 4)
    (integrable_const (1 : ℝ)),
    integral_const_mul, hsecond]

  norm_num [a]


/-! ## 9. Recurrence for natural number indices -/

set_option maxHeartbeats 1000000 in
/-- The Gaussian expectations satisfy the OEIS recurrence. -/
lemma gaussianMean_recurrence (n : ℕ) :
    gaussianMean (n + 2) =
      4 * (2 * (n : ℝ) + 3) *
        gaussianMean (n + 1) +
      gaussianMean n := by

  have h := polyMean_four_step (2 * (n : ℤ))

  have h₁ :
      2 * ((n + 1 : ℕ) : ℤ) =
        2 * (n : ℤ) + 2 := by
    push_cast
    ring

  have h₂ :
      2 * ((n + 2 : ℕ) : ℤ) =
        2 * (n : ℤ) + 4 := by
    push_cast
    ring

  change
    polyMean (U ℝ (2 * ((n + 2 : ℕ) : ℤ))) =
      4 * (2 * (n : ℝ) + 3) *
        polyMean (U ℝ (2 * ((n + 1 : ℕ) : ℤ))) +
      polyMean (U ℝ (2 * (n : ℤ)))

  rw [h₁, h₂]

  push_cast at h
  exact h


/-! ## 10. Main theorem -/

set_option maxHeartbeats 1000000 in
/-- Proof of OEIS A143412.

The Gaussian expectations of even-indexed Chebyshev
polynomials of the second kind agree with the sequence
defined by the OEIS recurrence.

The proof follows from Stein's identity, the Chebyshev
polynomial identities, and induction on consecutive
pairs of terms. -/
theorem conjecture_proved : conjecture := by

  unfold conjecture

  have hpair : ∀ n : ℕ,
      gaussianMean n = (a n : ℝ) ∧
      gaussianMean (n + 1) = (a (n + 1) : ℝ) := by

    intro n
    induction n with
    | zero =>
      exact ⟨gaussianMean_zero, gaussianMean_one⟩

    | succ n ih =>
      constructor

      · exact ih.2

      · change gaussianMean (n + 2) =
          (a (n + 2) : ℝ)

        have ha :
            a (n + 2) =
              4 * (2 * n + 3) * a (n + 1) + a n := rfl

        rw [gaussianMean_recurrence, ih.1, ih.2, ha]

        push_cast
        ring

  intro n
  exact (hpair n).1

end A143412


/-- The proof of the exact approved statement. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a143412.main := by
  exact A143412.conjecture_proved
