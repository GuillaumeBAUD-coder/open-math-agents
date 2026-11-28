import OMAStatements.S_oeis_a144503
import Mathlib

/-!
# Proof of OEIS A144503 (Chebyshev U Exponential Integral for Gift Exchange Sequence)

We prove for all `n : N`:
  `giftExchange n = 1 + int_{(0, infty)} U_{n-1}(x + 1) / exp(x) dx`.

Proof:
1. For any real polynomial `P`, integration by parts via `integral_Ioi_of_hasDerivAt_of_tendsto'`
   on `F(x) = -P(x + 1) * exp(-x)` gives
     `int_{(0, infty)} (P(x + 1) - P'(x + 1)) / exp(x) dx = P(1)`.
2. For `P = U_{k+1} - U_{k-1} = 2 * T_{k+1}` (`two_mul_T_eq_U_sub_U`), Mathlib's
   `T_derivative_eq_U` gives `P' = 2 * (k + 1) * U_k`, and `U_eval_one` gives `P(1) = 2`.
3. Hence `J(n) = int_{(0, infty)} U_{n-1}(x + 1) / exp(x) dx` satisfies
   `J(k + 2) = 2 * (k + 1) * J(k + 1) + J(k) + 2` with `J(0) = 0` and `J(1) = 1`,
   so `1 + J(n)` satisfies the exact defining recurrence and initial conditions of `giftExchange n`.
-/

namespace A144503Proof

open MeasureTheory Filter Topology Real Set Polynomial
open scoped BigOperators

lemma integrableOn_pow_div_exp (i : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ i / Real.exp x) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (i : ℝ)) (p := 1) (b := 1)
    (by linarith [Nat.cast_nonneg (α := ℝ) i]) zero_lt_one zero_lt_one
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
  dsimp only
  rw [Real.rpow_natCast, Real.rpow_one, neg_mul, one_mul, Real.exp_neg, div_eq_mul_inv]

lemma integrableOn_poly_eval_div_exp (P : ℝ[X]) :
    IntegrableOn (fun x : ℝ => P.eval (x + 1) / Real.exp x) (Ioi 0) := by
  let Q : ℝ[X] := P.comp (X + 1)
  have heq : ∀ x : ℝ, P.eval (x + 1) / Real.exp x =
      ∑ i ∈ Q.support, (Q.coeff i) * (x ^ i / Real.exp x) := by
    intro x
    have hQ : P.eval (x + 1) = Q.eval x := by simp [Q, Polynomial.eval_comp]
    rw [hQ, Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  simp_rw [heq]
  exact integrable_finsetSum _ fun i _ => (integrableOn_pow_div_exp i).const_mul (Q.coeff i)

lemma tendsto_neg_poly_eval_div_exp (P : ℝ[X]) :
    Tendsto (fun x : ℝ => -P.eval (x + 1) / Real.exp x) atTop (𝓝 0) := by
  let Q : ℝ[X] := P.comp (X + 1)
  have heq : (fun x : ℝ => -P.eval (x + 1) / Real.exp x) =
      fun x => ∑ i ∈ Q.support, (-Q.coeff i) * (x ^ i * Real.exp (-x)) := by
    funext x
    have hQ : P.eval (x + 1) = Q.eval x := by simp [Q, Polynomial.eval_comp]
    rw [hQ, Polynomial.eval_eq_sum, Polynomial.sum_def, ← Finset.sum_neg_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.exp_neg, div_eq_mul_inv]; ring
  rw [heq]
  have hsum : Tendsto (fun x : ℝ => ∑ i ∈ Q.support, (-Q.coeff i) * (x ^ i * Real.exp (-x)))
      atTop (𝓝 (∑ _i ∈ Q.support, (0 : ℝ))) := by
    refine tendsto_finsetSum _ fun i _ => ?_
    simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero i).const_mul (-Q.coeff i)
  simpa using hsum

lemma integral_poly_sub_deriv (P : ℝ[X]) :
    ∫ x in Ioi (0 : ℝ), (P.eval (x + 1) - (Polynomial.derivative P).eval (x + 1)) / Real.exp x =
      P.eval 1 := by
  have hderiv : ∀ x ∈ Ici (0 : ℝ),
      HasDerivAt (fun t : ℝ => -P.eval (t + 1) / Real.exp t)
        ((P.eval (x + 1) - (Polynomial.derivative P).eval (x + 1)) / Real.exp x) x := by
    intro x _
    have hP := (P.hasDerivAt (x + 1)).comp x ((hasDerivAt_id x).add_const (1 : ℝ))
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (-t)) (Real.exp (-x) * -1) x :=
      (hasDerivAt_id x).neg.exp
    have hmul : HasDerivAt (fun t : ℝ => -P.eval (t + 1) / Real.exp t)
        (-((Polynomial.derivative P).eval (x + 1) * 1) * Real.exp (-x) +
          -P.eval (x + 1) * (Real.exp (-x) * -1)) x :=
      (hP.neg.mul hexp).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by
        simp only [Pi.mul_apply, Pi.neg_apply, Function.comp_apply, id_eq, Real.exp_neg, div_eq_mul_inv])
    have hder : -((Polynomial.derivative P).eval (x + 1) * 1) * Real.exp (-x) +
        -P.eval (x + 1) * (Real.exp (-x) * -1) =
        (P.eval (x + 1) - (Polynomial.derivative P).eval (x + 1)) / Real.exp x := by
      rw [Real.exp_neg, div_eq_mul_inv]; ring
    exact hder ▸ hmul
  have hint : IntegrableOn
      (fun x : ℝ => (P.eval (x + 1) - (Polynomial.derivative P).eval (x + 1)) / Real.exp x)
      (Ioi 0) := by
    have h := (integrableOn_poly_eval_div_exp P).sub (integrableOn_poly_eval_div_exp (Polynomial.derivative P))
    refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
    rw [Pi.sub_apply, sub_div]
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint (tendsto_neg_poly_eval_div_exp P)
  simpa using hftc

noncomputable def J (n : ℕ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), (Polynomial.Chebyshev.U ℝ ((n : ℤ) - 1)).eval (x + 1) / Real.exp x

lemma J_zero : J 0 = 0 := by
  simp [J, Polynomial.Chebyshev.U_neg_one]

lemma J_one : J 1 = 1 := by
  have h := integral_poly_sub_deriv (1 : ℝ[X])
  simpa [J, Polynomial.Chebyshev.U_zero] using h

lemma J_recurrence (k : ℕ) :
    J (k + 2) = 2 * ((k : ℝ) + 1) * J (k + 1) + J k + 2 := by
  let P : ℝ[X] :=
    Polynomial.Chebyshev.U ℝ ((k : ℤ) + 1) - Polynomial.Chebyshev.U ℝ ((k : ℤ) - 1)
  have hP_eq : P = 2 * Polynomial.Chebyshev.T ℝ ((k : ℤ) + 1) := by
    have h := Polynomial.Chebyshev.two_mul_T_eq_U_sub_U ℝ ((k : ℤ) - 1)
    rw [show ((k : ℤ) - 1) + 2 = (k : ℤ) + 1 by ring] at h
    exact h.symm
  have hP_deriv : Polynomial.derivative P =
      C (2 * ((k : ℝ) + 1)) * Polynomial.Chebyshev.U ℝ (k : ℤ) := by
    rw [hP_eq, derivative_mul, derivative_ofNat, zero_mul, zero_add,
      Polynomial.Chebyshev.T_derivative_eq_U]
    rw [show ((k : ℤ) + 1) - 1 = (k : ℤ) by ring]
    simp only [map_mul, map_add, map_ofNat, map_one, map_natCast]
    push_cast
    ring
  have hP_one : P.eval 1 = 2 := by
    simp only [P, Polynomial.eval_sub, Polynomial.Chebyshev.U_eval_one]
    push_cast; ring
  have hibp := integral_poly_sub_deriv P
  rw [hP_one, hP_deriv] at hibp
  have h1 : IntegrableOn (fun x : ℝ => (Polynomial.Chebyshev.U ℝ ((k : ℤ) + 1)).eval (x + 1) / Real.exp x) (Ioi 0) :=
    integrableOn_poly_eval_div_exp _
  have h2 : IntegrableOn (fun x : ℝ => (Polynomial.Chebyshev.U ℝ ((k : ℤ) - 1)).eval (x + 1) / Real.exp x) (Ioi 0) :=
    integrableOn_poly_eval_div_exp _
  have h12 : IntegrableOn (fun x : ℝ =>
      (Polynomial.Chebyshev.U ℝ ((k : ℤ) + 1)).eval (x + 1) / Real.exp x -
        (Polynomial.Chebyshev.U ℝ ((k : ℤ) - 1)).eval (x + 1) / Real.exp x) (Ioi 0) := h1.sub h2
  have h3 : IntegrableOn (fun x : ℝ => (2 * ((k : ℝ) + 1)) * ((Polynomial.Chebyshev.U ℝ (k : ℤ)).eval (x + 1) / Real.exp x)) (Ioi 0) :=
    (integrableOn_poly_eval_div_exp _).const_mul _
  have hrew : ∫ x in Ioi (0 : ℝ),
      (P.eval (x + 1) - (C (2 * ((k : ℝ) + 1)) * Polynomial.Chebyshev.U ℝ (k : ℤ)).eval (x + 1)) / Real.exp x =
      J (k + 2) - J k - 2 * ((k : ℝ) + 1) * J (k + 1) := by
    have hpt : ∀ x : ℝ,
        (P.eval (x + 1) - (C (2 * ((k : ℝ) + 1)) * Polynomial.Chebyshev.U ℝ (k : ℤ)).eval (x + 1)) / Real.exp x =
        ((Polynomial.Chebyshev.U ℝ ((k : ℤ) + 1)).eval (x + 1) / Real.exp x -
          (Polynomial.Chebyshev.U ℝ ((k : ℤ) - 1)).eval (x + 1) / Real.exp x) -
        (2 * ((k : ℝ) + 1)) * ((Polynomial.Chebyshev.U ℝ (k : ℤ)).eval (x + 1) / Real.exp x) := by
      intro x
      simp only [P, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
      ring
    simp_rw [hpt]
    rw [integral_sub h12 h3, integral_sub h1 h2, integral_const_mul]
    simp only [J]
    have ha1 : (((k + 2 : ℕ) : ℤ) - 1) = (k : ℤ) + 1 := by omega
    have ha2 : (((k + 1 : ℕ) : ℤ) - 1) = (k : ℤ) := by omega
    rw [ha1, ha2]
  rw [hrew] at hibp
  linarith

theorem main_proof : ∀ n : ℕ, (OMA.S_oeis_a144503.giftExchange n : ℝ) =
    1 + ∫ x in Set.Ioi (0 : ℝ), (Polynomial.Chebyshev.U ℝ ((n : ℤ) - 1)).eval (x + 1) /
      Real.exp x := by
  have hstrong : ∀ n : ℕ,
      (OMA.S_oeis_a144503.giftExchange n : ℝ) = 1 + J n ∧
      (OMA.S_oeis_a144503.giftExchange (n + 1) : ℝ) = 1 + J (n + 1) := by
    intro n
    induction n with
    | zero =>
      constructor
      · simp [OMA.S_oeis_a144503.giftExchange, J_zero]
      · simp [OMA.S_oeis_a144503.giftExchange, J_one]; norm_num
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      simp only [OMA.S_oeis_a144503.giftExchange]
      push_cast
      rw [ih.1, ih.2, J_recurrence k]
      ring
  intro n
  exact (hstrong n).1

end A144503Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a144503.main :=
  A144503Proof.main_proof
