import OMAStatements.S_mo_371077
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-!
The counterexample is due to Alexandre Eremenko in his MathOverflow comment
on user159888's question (CC BY-SA 4.0).
https://mathoverflow.net/questions/371077/#comment938706_371077

Formalization credit: @grp06
-/

open Polynomial

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_371077.main) := by
  intro h
  let a : ℂ := ((2 / 3 : ℝ) : ℂ)
  let b : ℂ := ((-1 / 3 : ℝ) : ℂ)
  let p : ℂ[X] := C a * X + C b
  have ha : a ≠ 0 := by
    change ((2 / 3 : ℝ) : ℂ) ≠ 0
    rw [ne_eq, Complex.ofReal_eq_zero]
    norm_num
  have hna : ‖a‖ = 2 / 3 := by
    norm_num [a, Complex.norm_real, Real.norm_eq_abs]
  have hnb : ‖b‖ = 1 / 3 := by
    norm_num [b, Complex.norm_real, Real.norm_eq_abs]
  have heval (z : ℂ) : p.eval z = a * z + b := by
    simp only [p, eval_add, eval_mul, eval_C, eval_X]
  have hnormalized : OMA.S_mo_371077.Normalized p := by
    constructor
    · intro z hz
      rw [heval]
      calc
        ‖a * z + b‖ ≤ ‖a * z‖ + ‖b‖ := norm_add_le _ _
        _ = 1 := by rw [norm_mul, hz, hna, hnb]; norm_num
    · refine ⟨-1, by simp, ?_⟩
      have hminus : p.eval (-1) = ((-1 : ℝ) : ℂ) := by
        calc
          p.eval (-1) = a * (-1) + b := heval _
          _ = ((((2 / 3 : ℝ) * (-1) + (-1 / 3)) : ℝ) : ℂ) := by
            simp only [a, b, Complex.ofReal_add, Complex.ofReal_mul,
              Complex.ofReal_neg, Complex.ofReal_one]
          _ = ((-1 : ℝ) : ℂ) :=
            congrArg Complex.ofReal (by norm_num)
      rw [hminus, Complex.ofReal_neg, Complex.ofReal_one, norm_neg, norm_one]
  have hone : p.eval 1 = ((1 / 3 : ℝ) : ℂ) := by
    rw [heval, mul_one]
    change ((2 / 3 : ℝ) : ℂ) + ((-1 / 3 : ℝ) : ℂ) = ((1 / 3 : ℝ) : ℂ)
    rw [← Complex.ofReal_add]
    exact congrArg Complex.ofReal (by norm_num)
  have hone_ne : p.eval 1 ≠ 0 := by
    rw [hone, ne_eq, Complex.ofReal_eq_zero]
    norm_num
  have hp : p ≠ 0 := by
    intro hp_zero
    apply hone_ne
    rw [hp_zero, eval_zero]
  have hdegree : p.natDegree = 1 := natDegree_linear ha
  have hleading : p.leadingCoeff = a := leadingCoeff_linear ha
  have hconstant : p.coeff 0 = b := by
    simp only [p, coeff_add, coeff_C_mul, coeff_X_zero, mul_zero, coeff_C_zero, zero_add]
  have hderivative : p.derivative.eval 1 = a := by
    simp only [p, derivative_add, derivative_C_mul_X, derivative_C, add_zero, eval_C]
  have hlog : ((1 : ℂ) * p.derivative.eval 1 / p.eval 1).re = 2 := by
    rw [one_mul, hderivative, hone]
    change (((2 / 3 : ℝ) : ℂ) / ((1 / 3 : ℝ) : ℂ)).re = 2
    rw [← Complex.ofReal_div, Complex.ofReal_re]
    norm_num
  have hbound := h p hp hnormalized 1 (by simp) hone_ne
  rw [hlog, hdegree, hconstant, hleading, hnb, hna] at hbound
  norm_num at hbound
