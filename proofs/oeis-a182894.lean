import OMAStatements.S_oeis_a182894
import Mathlib

open OMA.S_oeis_a182894 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a182894.main := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have e (c : ℕ) [c.AtLeastTwo] : (OfNat.ofNat c : ℚ⟦X⟧) = C (OfNat.ofNat c) := (map_ofNat C c).symm
  have hb : PowerSeries.binomialSeries ℚ (1/2:ℚ)^2 = 1+X := by
    rw [sq, ← PowerSeries.binomialSeries_add, show (1/2+1/2:ℚ) = (1:ℕ) by norm_num, PowerSeries.binomialSeries_nat, pow_one]
  have hS : S^2 = 1 - 2*X - X^2 - 2*X^3 + X^4 := by
    rw [S, ← coe_substAlgHom (HasSubst.of_constantCoeff_zero' (by simp [R])), ← map_pow, hb, map_add, map_one, substAlgHom_X, R]
    ring
  simp only [a]
  generalize hd : ((-X - X ^ 2 + S) * (1 - 2 * X - 2 * X ^ 2 - 4 * X ^ 3 : ℚ⟦X⟧)⁻¹) = G
  have hG : (1 - 2*X - 2*X^2 - 4*X^3)*G = -X - X^2 + S := by
    rw [← hd, mul_comm, mul_assoc, PowerSeries.inv_mul_cancel _ (by simp [e]), mul_one]
  have t (i : ℕ) : coeff i (X * derivative ℚ G) = i * coeff i G := by
    cases i <;> simp [coeff_derivative, mul_comm]
  have h1 := congrArg (derivative ℚ) hS
  have h2 := congrArg (derivative ℚ) hG
  simp [e, Derivation.leibniz] at h1 h2
  simp only [map_ofNat] at h1 h2
  have key : 2*(X*derivative ℚ G) - 8*(X*(X*derivative ℚ G)) + 2*(X^2*(X*derivative ℚ G)) + 30*(X^4*(X*derivative ℚ G)) + 12*(X^5*(X*derivative ℚ G)) + 12*(X^6*(X*derivative ℚ G)) - 8*(X^7*(X*derivative ℚ G)) - 2*(X*G) - 2*(X^2*G) - 6*(X^3*G) + 36*(X^4*G) + 24*(X^5*G) + 24*(X^6*G) - 8*(X^7*G) = -2*X - 2*X^2 + 6*X^3 + 4*X^5 := by
    linear_combination X*((2 - 4*X - 2*X^2 - 4*X^3 + 2*X^4)*h2 - (-2 - 2*X - 6*X^2 + 4*X^3)*hG + (1)^2*(-((2)*derivative ℚ S + (0)*S)*hS + (1)*S*h1))
  have h := congrArg (coeff (m+7)) key
  simp [e, coeff_C_mul, t, coeff_X_pow_mul'] at h ⊢
  linear_combination h/(2)
