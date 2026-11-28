import OMAStatements.S_oeis_a125306
import Mathlib

open PowerSeries OMA.S_oeis_a125306 in
theorem OMA.solution : type_of% @OMA.S_oeis_a125306.main := by
  have hs : HasSubst (R - 1) := HasSubst.of_constantCoeff_zero' (by simp [R])
  have hS : S^2 = R := by
    rw [S, ← subst_pow hs, sq (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)),
      ← binomialSeries_add, show (1/2 + 1/2 : ℚ) = (1:ℕ) by norm_num,
      binomialSeries_nat, pow_one, ← coe_substAlgHom hs, map_add, map_one, coe_substAlgHom hs,
      subst_X hs]
    ring
  obtain ⟨G, hG⟩ : ∃ G, G = (1 - 2*X + 4*X^2 + 3*X^4 + (-1 - 2*X^2 - X^4)*S)
      * (4 + 4*X + 4*X^2 + 2*X^3 : ℚ⟦X⟧)⁻¹ := ⟨_, rfl⟩
  have g : G * (4 + 4*X + 4*X^2 + 2*X^3) = 1 - 2*X + 4*X^2 + 3*X^4 + (-1 - 2*X^2 - X^4)*S := by
    rw [hG, mul_assoc, PowerSeries.inv_mul_cancel _
      (by simp only [← map_ofNat (C (R := ℚ))]; simp), mul_one]
  have s : (4 + 4*X + 4*X^2 + 2*X^3)*G - (1 - 2*X + 4*X^2 + 3*X^4) = -(1+X^2)^2*S := by
    linear_combination g
  unfold R at hS
  have y : (1 + X^2 : ℚ⟦X⟧) ≠ 0 := fun q => by simpa using congrArg (coeff 0) q
  have hL : ((4 + 4*X + 4*X^2 + 2*X^3)*G - (1 - 2*X + 4*X^2 + 3*X^4))^2 = (1+X^2)^4*(1-4*X) := by
    linear_combination (1+X^2)^4*hS
      + ((4 + 4*X + 4*X^2 + 2*X^3)*G - (1 - 2*X + 4*X^2 + 3*X^4) - (1+X^2)^2*S)*s
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simp only [a, ← hG]
  have h := congrArg (derivative ℚ) hL
  simp only [← map_ofNat (C (R := ℚ))] at h
  simp [Derivation.leibniz, pow_succ] at h
  simp only [map_ofNat] at h
  have E : 2*((1+X^2)*((1-4*X)*((4 + 4*X + 4*X^2 + 2*X^3)*derivative ℚ G)))
      + (2*(1+X^2)*(1-4*X)*(4+8*X+6*X^2) + (4-8*X+36*X^2)*(4 + 4*X + 4*X^2 + 2*X^3))*G
      - 2*((1+X^2)*((1-4*X)*(-2+8*X+12*X^3))) - (4-8*X+36*X^2)*(1 - 2*X + 4*X^2 + 3*X^4) = 0 :=
    (mul_eq_zero.1 ((mul_eq_zero.1 (by
      linear_combination ((1+X^2)^4*(1-4*X))*h
        - (8*X*(1+X^2)^3*(1-4*X) + (1+X^2)^4*(-4))*hL :
        ((4 + 4*X + 4*X^2 + 2*X^3)*G - (1 - 2*X + 4*X^2 + 3*X^4)) * ((1+X^2)^3 * _) = 0)).resolve_left
      (by
        rw [s]
        exact mul_ne_zero (neg_ne_zero.2 (pow_ne_zero 2 y))
          (by rintro q; rw [q] at hS; simpa using congrArg (coeff 0) hS)))).resolve_left
      (pow_ne_zero 3 y)
  simp only [← map_ofNat (C (R := ℚ))] at E
  have c := congrArg (coeff (m+7)) E
  simp [mul_add, mul_sub, add_mul, sub_mul, mul_assoc, pow_succ, coeff_derivative, coeff_X,
    coeff_one] at c ⊢
  linear_combination (1/4 : ℚ) * c
