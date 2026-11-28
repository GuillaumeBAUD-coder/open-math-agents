import OMAStatements.S_oeis_a188464
import Mathlib

open PowerSeries OMA.S_oeis_a188464 in
theorem OMA.solution : type_of% @OMA.S_oeis_a188464.main := by
  have hs : HasSubst (R - 1) := HasSubst.of_constantCoeff_zero' (by simp [R])
  have hS : S^2 = R := by
    rw [S, ← subst_pow hs, sq, ← binomialSeries_add, show (1/2 + 1/2 : ℚ) = (1:ℕ) by norm_num,
      binomialSeries_nat, pow_one, ← coe_substAlgHom hs, map_add, map_one, coe_substAlgHom hs,
      subst_X hs]
    ring
  obtain ⟨G, hG⟩ : ∃ G, G = (1 - 3*X + X^2 - X^3 + (-1 + X)*S) * (2 : ℚ⟦X⟧)⁻¹ := ⟨_, rfl⟩
  have g : G * 2 = 1 - 3*X + X^2 - X^3 + (-1 + X)*S := by
    rw [hG, mul_assoc, PowerSeries.inv_mul_cancel _ (by rw [← map_ofNat (C (R := ℚ)) 2]; simp),
      mul_one]
  have s : 2*G - (1 - 3*X + X^2 - X^3) = (X-1)*S := by linear_combination g
  unfold R at hS
  have x : (X - 1 : ℚ⟦X⟧) ≠ 0 := fun q => by simpa using congrArg (coeff 0) q
  have hL : (2*G - (1 - 3*X + X^2 - X^3))^2 = (X-1)^2*(1-4*X+2*X^2+X^4) := by
    linear_combination (X-1)^2*hS + (2*G - (1 - 3*X + X^2 - X^3) + (X-1)*S)*s
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simp only [a, ← hG]
  have h := congrArg (derivative ℚ) hL
  simp only [← map_ofNat (C (R := ℚ))] at h
  simp [Derivation.leibniz, pow_succ] at h
  simp only [map_ofNat] at h
  have E : 4*((1-4*X+2*X^2+X^4)*derivative ℚ G) + 2*((6-10*X-2*X^2-6*X^3)*G)
      - 2*((1-4*X+2*X^2+X^4)*(-3+2*X-3*X^2)) - (6-10*X-2*X^2-6*X^3)*(1-3*X+X^2-X^3) = 0 :=
    (mul_eq_zero.1 ((mul_eq_zero.1 ((mul_eq_zero.1 (by
      linear_combination ((X-1)^2*(1-4*X+2*X^2+X^4))*h
        - (2*(X-1)*(1-4*X+2*X^2+X^4) + (X-1)^2*(-4+4*X+4*X^3))*hL :
        (2*G - (1 - 3*X + X^2 - X^3)) * ((X-1) * ((X-1) * _)) = 0)).resolve_left
      (by
        rw [s]
        exact mul_ne_zero x (by rintro q; rw [q] at hS; simpa using congrArg (coeff 0) hS)))).resolve_left
      x)).resolve_left x
  simp only [← map_ofNat (C (R := ℚ))] at E
  have c := congrArg (coeff (m+7)) E
  simp [mul_add, mul_sub, add_mul, sub_mul, mul_assoc, pow_succ, coeff_derivative, coeff_X,
    coeff_one] at c ⊢
  linear_combination (1/4 : ℚ) * c
