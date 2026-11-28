import OMAStatements.S_mo_239436
import Mathlib

namespace MO239436Aux

open Polynomial in
lemma poly4 (a : Fin (3 + 1) → ℝ) :
    OMA.S_mo_239436.polynomialOfCoeffs a
      = C (a 0) + C (a 1) * X + C (a 2) * X ^ 2 + C (a 3) * X ^ 3 := by
  unfold OMA.S_mo_239436.polynomialOfCoeffs
  rw [Fin.sum_univ_four]
  simp [← C_mul_X_pow_eq_monomial]

open Polynomial in
noncomputable def W (a b : Fin (3 + 1) → ℝ) : ℝ[X] :=
  C (a 0 * b 1 - a 1 * b 0) + C (2 * (a 0 * b 2 - a 2 * b 0)) * X
    + C (3 * (a 0 * b 3 - a 3 * b 0) + (a 1 * b 2 - a 2 * b 1)) * X ^ 2
    + C (2 * (a 1 * b 3 - a 3 * b 1)) * X ^ 3
    + C (a 2 * b 3 - a 3 * b 2) * X ^ 4

open Polynomial in
lemma wr (a b : Fin (3 + 1) → ℝ) :
    OMA.S_mo_239436.polynomialOfCoeffs a * derivative (OMA.S_mo_239436.polynomialOfCoeffs b)
      - derivative (OMA.S_mo_239436.polynomialOfCoeffs a) * OMA.S_mo_239436.polynomialOfCoeffs b
    = W a b := by
  unfold W
  rw [poly4, poly4]
  simp only [derivative_add, derivative_mul, derivative_C, derivative_X, derivative_X_pow,
    C_mul, C_add, C_sub, C_ofNat, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  ring

open Polynomial in
lemma coeffs (c0 c1 c2 c3 c4 : ℝ) :
    (C c0 + C c1 * X + C c2 * X ^ 2 + C c3 * X ^ 3 + C c4 * X ^ 4 : ℝ[X]).coeff 0 = c0
    ∧ (C c0 + C c1 * X + C c2 * X ^ 2 + C c3 * X ^ 3 + C c4 * X ^ 4 : ℝ[X]).coeff 1 = c1
    ∧ (C c0 + C c1 * X + C c2 * X ^ 2 + C c3 * X ^ 3 + C c4 * X ^ 4 : ℝ[X]).coeff 2 = c2
    ∧ (C c0 + C c1 * X + C c2 * X ^ 2 + C c3 * X ^ 3 + C c4 * X ^ 4 : ℝ[X]).coeff 3 = c3
    ∧ (C c0 + C c1 * X + C c2 * X ^ 2 + C c3 * X ^ 3 + C c4 * X ^ 4 : ℝ[X]).coeff 4 = c4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [coeff_X, coeff_C, coeff_X_pow]

open Polynomial in
lemma W0 (a b : Fin (3 + 1) → ℝ) : (W a b).coeff 0 = a 0 * b 1 - a 1 * b 0 :=
  (coeffs _ _ _ _ _).1

open Polynomial in
lemma W1 (a b : Fin (3 + 1) → ℝ) : (W a b).coeff 1 = 2 * (a 0 * b 2 - a 2 * b 0) :=
  (coeffs _ _ _ _ _).2.1

open Polynomial in
lemma W2 (a b : Fin (3 + 1) → ℝ) :
    (W a b).coeff 2 = 3 * (a 0 * b 3 - a 3 * b 0) + (a 1 * b 2 - a 2 * b 1) :=
  (coeffs _ _ _ _ _).2.2.1

open Polynomial in
lemma W3 (a b : Fin (3 + 1) → ℝ) : (W a b).coeff 3 = 2 * (a 1 * b 3 - a 3 * b 1) :=
  (coeffs _ _ _ _ _).2.2.2.1

open Polynomial in
lemma W4 (a b : Fin (3 + 1) → ℝ) : (W a b).coeff 4 = a 2 * b 3 - a 3 * b 2 :=
  (coeffs _ _ _ _ _).2.2.2.2

open Polynomial in
lemma val (a b : Fin (3 + 1) → ℝ) (k : ℕ) (hk : k < 2 * 3 - 1) :
    OMA.S_mo_239436.wronskianMap 3 (a, b) ⟨k, hk⟩ = (W a b).coeff k := by
  show (OMA.S_mo_239436.polynomialOfCoeffs a
      * derivative (OMA.S_mo_239436.polynomialOfCoeffs b)
      - derivative (OMA.S_mo_239436.polynomialOfCoeffs a)
        * OMA.S_mo_239436.polynomialOfCoeffs b).coeff k = _
  rw [wr]

end MO239436Aux

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_239436.main) := by
  intro h
  obtain ⟨⟨a, b⟩, hab⟩ := h 3 (by norm_num)
    (fun i => if i.val = 1 ∨ i.val = 3 then 1 else 0)
  have e0 : OMA.S_mo_239436.wronskianMap 3 (a, b) ⟨0, by norm_num⟩ = 0 := by
    rw [hab]; simp
  have e1 : OMA.S_mo_239436.wronskianMap 3 (a, b) ⟨1, by norm_num⟩ = 1 := by
    rw [hab]; simp
  have e2 : OMA.S_mo_239436.wronskianMap 3 (a, b) ⟨2, by norm_num⟩ = 0 := by
    rw [hab]; simp
  have e3 : OMA.S_mo_239436.wronskianMap 3 (a, b) ⟨3, by norm_num⟩ = 1 := by
    rw [hab]; simp
  have e4 : OMA.S_mo_239436.wronskianMap 3 (a, b) ⟨4, by norm_num⟩ = 0 := by
    rw [hab]; simp
  rw [MO239436Aux.val, MO239436Aux.W0] at e0
  rw [MO239436Aux.val, MO239436Aux.W1] at e1
  rw [MO239436Aux.val, MO239436Aux.W2] at e2
  rw [MO239436Aux.val, MO239436Aux.W3] at e3
  rw [MO239436Aux.val, MO239436Aux.W4] at e4
  have key : (3 * (a 0 * b 3 - a 3 * b 0) + (a 1 * b 2 - a 2 * b 1)) ^ 2
      - 3 * (2 * (a 0 * b 2 - a 2 * b 0)) * (2 * (a 1 * b 3 - a 3 * b 1))
      + 12 * (a 0 * b 1 - a 1 * b 0) * (a 2 * b 3 - a 3 * b 2)
      = (3 * (a 0 * b 3 - a 3 * b 0) - (a 1 * b 2 - a 2 * b 1)) ^ 2 := by ring
  rw [e0, e1, e2, e3, e4] at key
  have hsq := sq_nonneg (3 * (a 0 * b 3 - a 3 * b 0) - (a 1 * b 2 - a 2 * b 1))
  rw [← key] at hsq
  norm_num at hsq
