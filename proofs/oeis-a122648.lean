import OMAStatements.S_oeis_a122648
import Mathlib

namespace A122648

open PowerSeries OMA.S_oeis_a122648

lemma hE : HasSubst (X ^ 2 : PowerSeries ℚ) := HasSubst.X_pow (by norm_num)

lemma hH : HasSubst (C (2:ℚ) * X : PowerSeries ℚ) := by
  apply HasSubst.of_constantCoeff_zero'
  simp

lemma dE : PowerSeries.derivative ℚ E = E * (C (2:ℚ) * X) := by
  unfold E
  rw [derivative_subst hE, derivative_exp, derivative_pow, derivative_X]
  have h2 : (C (2:ℚ) : PowerSeries ℚ) = 2 := map_ofNat (C : ℚ →+* PowerSeries ℚ) 2
  rw [h2]
  simp

lemma dH : PowerSeries.derivative ℚ H = H * C (2:ℚ) := by
  unfold H
  rw [derivative_subst hH, derivative_exp, Derivation.leibniz, derivative_X, derivative_C]
  simp

lemma derivC (c : ℚ) (f : PowerSeries ℚ) :
    PowerSeries.derivative ℚ (C c * f) = C c * PowerSeries.derivative ℚ f := by
  rw [Derivation.leibniz, derivative_C]
  simp

lemma ode1 : PowerSeries.derivative ℚ egf =
    C (2:ℚ) * (C (1/2:ℚ) * E * H) + C (2:ℚ) * X * egf := by
  unfold egf
  simp only [Derivation.leibniz, map_add, derivative_one, derivative_C, dE, dH, smul_eq_mul,
    add_zero]
  ring

lemma odeU : PowerSeries.derivative ℚ (C (1/2:ℚ) * E * H) =
    (C (2:ℚ) * X + C (2:ℚ)) * (C (1/2:ℚ) * E * H) := by
  simp only [Derivation.leibniz, derivative_C, dE, dH, smul_eq_mul]
  ring

lemma ode2 : PowerSeries.derivative ℚ (PowerSeries.derivative ℚ egf) =
    (4 * X + 2) * PowerSeries.derivative ℚ egf + (2 - 4 * X ^ 2 - 4 * X) * egf := by
  have h2 : (C (2:ℚ) : PowerSeries ℚ) = 2 := map_ofNat (C : ℚ →+* PowerSeries ℚ) 2
  have p1 : PowerSeries.derivative ℚ (C (2:ℚ) * (C (1/2:ℚ) * E * H)) =
      C (2:ℚ) * PowerSeries.derivative ℚ (C (1/2:ℚ) * E * H) := derivC _ _
  have p2 : PowerSeries.derivative ℚ (C (2:ℚ) * X * egf) =
      C (2:ℚ) * X * PowerSeries.derivative ℚ egf + egf * C (2:ℚ) := by
    rw [Derivation.leibniz, derivC, derivative_X]
    simp only [smul_eq_mul, mul_one]
  have e0 : PowerSeries.derivative ℚ (PowerSeries.derivative ℚ egf) =
      PowerSeries.derivative ℚ (C (2:ℚ) * (C (1/2:ℚ) * E * H) + C (2:ℚ) * X * egf) :=
    congrArg _ ode1
  have ode1' := ode1
  rw [h2] at ode1'
  rw [e0, map_add, p1, p2, odeU, h2]
  linear_combination (-(2 * X + 2)) * ode1'

lemma coeff_rec (k : ℕ) :
    coeff (k + 4) egf * ((k:ℚ) + 4) * ((k:ℚ) + 3) =
      (4 * ((k:ℚ) + 2) + 2) * coeff (k + 2) egf + 2 * ((k:ℚ) + 3) * coeff (k + 3) egf -
        4 * coeff k egf - 4 * coeff (k + 1) egf := by
  have h := congrArg (coeff (k + 2)) ode2
  have e : (4 * X + 2) * PowerSeries.derivative ℚ egf + (2 - 4 * X ^ 2 - 4 * X) * egf =
      C (4:ℚ) * (X * PowerSeries.derivative ℚ egf) + C (2:ℚ) * PowerSeries.derivative ℚ egf +
        C (2:ℚ) * egf - C (4:ℚ) * (X ^ 2 * egf) - C (4:ℚ) * (X * egf) := by
    simp only [map_ofNat]
    ring
  rw [e] at h
  simp only [map_add, map_sub, coeff_C_mul, coeff_succ_X_mul, coeff_X_pow_mul,
    coeff_derivative] at h
  push_cast at h
  have h4 : k + 2 + 1 + 1 = k + 4 := by ring
  have h3 : k + 2 + 1 = k + 3 := by ring
  have h2' : k + 1 + 1 = k + 2 := by ring
  simp only [h4, h3, h2'] at h
  linarith

end A122648

theorem OMA.solution : type_of% @OMA.S_oeis_a122648.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have h := A122648.coeff_rec k
  have e1 : k + 4 - 1 = k + 3 := by omega
  have e2 : k + 4 - 2 = k + 2 := by omega
  have e3 : k + 4 - 3 = k + 1 := by omega
  have e4 : k + 4 - 4 = k := by omega
  rw [e1, e2, e3, e4]
  unfold OMA.S_oeis_a122648.a
  have f4 : ((k + 4).factorial : ℚ) =
      ((k:ℚ) + 4) * ((k:ℚ) + 3) * ((k:ℚ) + 2) * ((k:ℚ) + 1) * k.factorial := by
    rw [Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have f3 : ((k + 3).factorial : ℚ) = ((k:ℚ) + 3) * ((k:ℚ) + 2) * ((k:ℚ) + 1) * k.factorial := by
    rw [Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have f2 : ((k + 2).factorial : ℚ) = ((k:ℚ) + 2) * ((k:ℚ) + 1) * k.factorial := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have f1 : ((k + 1).factorial : ℚ) = ((k:ℚ) + 1) * k.factorial := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [f4, f3, f2, f1]
  push_cast
  linear_combination (k.factorial : ℚ) * ((k:ℚ) + 1) * ((k:ℚ) + 2) * h
