import OMAStatements.S_mo_239436
import Mathlib

namespace MO239436Aux

open Polynomial OMA.S_mo_239436

private lemma cubic_expansion (a : Fin 4 → ℝ) :
    polynomialOfCoeffs a = C (a 0) + C (a 1) * X + C (a 2) * X ^ 2 + C (a 3) * X ^ 3 := by
  unfold polynomialOfCoeffs
  rw [Fin.sum_univ_four]
  simp [← C_mul_X_pow_eq_monomial]

/-- A coefficient expression that is a square for every real cubic Wronskian. -/
lemma nonnegative_coefficients (a b : Fin 4 → ℝ) :
    let w := wronskianMap 3 (a, b)
    0 ≤ w 2 ^ 2 - 3 * w 1 * w 3 + 12 * w 0 * w 4 := by
  let p : ℝ[X] :=
    C (a 0 * b 1 - a 1 * b 0) + C (2 * (a 0 * b 2 - a 2 * b 0)) * X
      + C (3 * (a 0 * b 3 - a 3 * b 0) + (a 1 * b 2 - a 2 * b 1)) * X ^ 2
      + C (2 * (a 1 * b 3 - a 3 * b 1)) * X ^ 3
      + C (a 2 * b 3 - a 3 * b 2) * X ^ 4
  have hpoly : polynomialOfCoeffs a * (polynomialOfCoeffs b).derivative
      - (polynomialOfCoeffs a).derivative * polynomialOfCoeffs b = p := by
    dsimp only [p]
    rw [cubic_expansion a, cubic_expansion b]
    simp only [derivative_add, derivative_mul, derivative_C, derivative_X, derivative_X_pow,
      C_mul, C_add, C_sub, C_ofNat, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    ring
  have hcoeff (i : Fin 5) : wronskianMap 3 (a, b) i = p.coeff i.val := by
    exact congrArg (fun q : ℝ[X] => q.coeff i.val) hpoly
  dsimp only
  simp only [hcoeff, p, coeff_add, coeff_C_mul, coeff_X, coeff_X_pow, coeff_C]
  norm_num
  nlinarith only [sq_nonneg (3 * (a 0 * b 3 - a 3 * b 0) - (a 1 * b 2 - a 2 * b 1))]

end MO239436Aux

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_239436.main) := by
  intro h
  let target (i : Fin (2 * 3 - 1)) : ℝ := if i.val = 1 ∨ i.val = 3 then 1 else 0
  obtain ⟨⟨a, b⟩, hab⟩ := h 3 (by decide) target
  have hn := MO239436Aux.nonnegative_coefficients a b
  dsimp only at hn
  rw [hab] at hn
  norm_num [target] at hn
