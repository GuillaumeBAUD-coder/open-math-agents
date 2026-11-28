import OMAStatements.S_mo_120636
import Mathlib

/-!
# Binomial expectations and forward differences

Josh asked the question. User39430 supplied the derivative in a comment.
The identity is Theorem 7.12 of George M. Phillips, Interpolation and
Approximation by Polynomials (2003). We sum the derivatives of the
Bernstein basis and use summation by parts. One Bernoulli trial and the
positive convex function 2^x show the implicit equation can have a full
interval of solutions.

Source: https://mathoverflow.net/questions/120636
Formalization: @dwilfand-sys, using Codex.
-/

namespace OMA.MO120636

noncomputable def expectation (n : ℕ) (f : ℕ → ℝ) (p : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), f j * (bernsteinPolynomial ℝ n j).eval p

lemma telescope (f b : ℕ → ℝ) (m : ℕ) :
    -(f 0 * b 0) + (∑ j ∈ Finset.range m, f (j + 1) * (b j - b (j + 1))) =
      (∑ j ∈ Finset.range m, (f (j + 1) - f j) * b j) - f m * b m := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [Finset.sum_range_succ]
    linarith only [ih, show f (m + 1) * (b m - b (m + 1)) =
      (f (m + 1) - f m) * b m + f m * b m - f (m+1) * b (m+1) by ring]

lemma expectation_derivative (f : ℕ → ℝ) (n : ℕ) (p : ℝ) :
    HasDerivAt (expectation n f)
      ((n : ℝ) * expectation (n - 1) (fun j => f (j + 1) - f j) p) p := by
  cases n with
  | zero =>
    simpa [expectation, bernsteinPolynomial] using hasDerivAt_const p (f 0)
  | succ n =>
    let b : ℕ → ℝ := fun j => (bernsteinPolynomial ℝ n j).eval p
    have ht := telescope f b (n + 1)
    have hz : b (n + 1) = 0 := by
      simp [b, bernsteinPolynomial.eq_zero_of_lt ℝ (Nat.lt_succ_self n)]
    rw [hz, mul_zero, sub_zero] at ht
    have diff : HasDerivAt (expectation (n+1) f)
        (∑ j ∈ Finset.range (n+1+1), f j *
          (Polynomial.derivative (bernsteinPolynomial ℝ (n+1) j)).eval p) p := by
      apply HasDerivAt.fun_sum
      intro j hj
      exact ((bernsteinPolynomial ℝ (n+1) j).hasDerivAt p).const_mul (f j)
    convert diff using 1
    change ((n+1 : ℕ) : ℝ) * (∑ j ∈ Finset.range (n+1), (f (j+1) - f j) * b j) =
      ∑ j ∈ Finset.range (n+1+1), f j *
        (Polynomial.derivative (bernsteinPolynomial ℝ (n+1) j)).eval p
    rw [← ht, Finset.sum_range_succ' (fun j => f j *
      (Polynomial.derivative (bernsteinPolynomial ℝ (n+1) j)).eval p)]
    simp only [bernsteinPolynomial.derivative_zero, bernsteinPolynomial.derivative_succ_aux,
      Nat.add_sub_cancel, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_add,
      Polynomial.eval_neg, Polynomial.eval_natCast, Polynomial.eval_one, Nat.cast_add,
      Nat.cast_one]
    change ((n : ℝ)+1) * (-(f 0 * b 0) + ∑ j ∈ Finset.range (n+1),
      f (j+1) * (b j - b (j+1))) =
      (∑ j ∈ Finset.range (n+1), f (j+1) * (((n : ℝ)+1) * (b j - b (j+1)))) +
        f 0 * (-((n : ℝ)+1) * b 0)
    rw [mul_add, Finset.mul_sum]
    have hs : (∑ j ∈ Finset.range (n+1), ((n : ℝ)+1) * (f (j+1) * (b j - b (j+1)))) =
        ∑ j ∈ Finset.range (n+1), f (j+1) * (((n : ℝ)+1) * (b j - b (j+1))) := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hs]
    ring

end OMA.MO120636

theorem OMA.solution : type_of% @OMA.S_mo_120636.main := by
  constructor
  · exact OMA.MO120636.expectation_derivative
  · refine ⟨fun x : ℝ => (2 : ℝ) ^ x, 1, fun x => Real.rpow_pos_of_pos (by norm_num) x,
      convexOn_rpow_left (by norm_num), ?_⟩
    intro p hp
    norm_num [Finset.sum_range_succ, bernsteinPolynomial] <;> ring
