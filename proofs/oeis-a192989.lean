import OMAStatements.S_oeis_a192989
import Mathlib

namespace A192989

open PowerSeries OMA.S_oeis_a192989

lemma hg : HasSubst ((1 + X) ^ 3 - 1 : PowerSeries ℚ) := by
  apply HasSubst.of_constantCoeff_zero'
  simp

lemma ode : PowerSeries.derivative ℚ egf = egf * (3 + 6 * X + 3 * X ^ 2) := by
  unfold egf
  rw [derivative_subst hg, derivative_exp]
  congr 1
  rw [map_sub, derivative_pow, map_add, derivative_one, derivative_X]
  push_cast
  ring

lemma coeff_rec (m : ℕ) :
    coeff (m + 3) egf * ((m : ℚ) + 3) =
      3 * coeff (m + 2) egf + 6 * coeff (m + 1) egf + 3 * coeff m egf := by
  have h := congrArg (coeff (m + 2)) ode
  rw [coeff_derivative] at h
  have e : egf * (3 + 6 * X + 3 * X ^ 2) =
      C (3 : ℚ) * egf + C (6 : ℚ) * (egf * X) + C (3 : ℚ) * (egf * X ^ 2) := by
    simp only [map_ofNat]
    ring
  rw [e, map_add, map_add, coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_succ_mul_X,
    coeff_mul_X_pow] at h
  push_cast at h
  linarith

end A192989

theorem OMA.solution : type_of% @OMA.S_oeis_a192989.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h := A192989.coeff_rec m
  have e1 : m + 3 - 1 = m + 2 := by omega
  have e2 : m + 3 - 2 = m + 1 := by omega
  have e3 : m + 3 - 3 = m := by omega
  rw [e1, e2, e3]
  unfold OMA.S_oeis_a192989.a
  have f3 : ((m + 3).factorial : ℚ) = ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * m.factorial := by
    rw [Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have f2 : ((m + 2).factorial : ℚ) = ((m : ℚ) + 2) * ((m : ℚ) + 1) * m.factorial := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have f1 : ((m + 1).factorial : ℚ) = ((m : ℚ) + 1) * m.factorial := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [f3, f2, f1]
  push_cast
  linear_combination ((m : ℚ) + 2) * ((m : ℚ) + 1) * (m.factorial : ℚ) * h
