import OMAStatements.S_oeis_a217333
import Mathlib

open PowerSeries OMA.S_oeis_a217333 in
theorem OMA.solution : type_of% @OMA.S_oeis_a217333.main := by
  have hs : HasSubst (R - 1) := HasSubst.of_constantCoeff_zero' (by simp [R])
  have hS : S^2 = R := by
    rw [S, ← subst_pow hs, sq, ← binomialSeries_add, show (1/2 + 1/2 : ℚ) = (1:ℕ) by norm_num,
      binomialSeries_nat, pow_one, ← coe_substAlgHom hs, map_add, map_one, coe_substAlgHom hs,
      subst_X hs]
    ring
  obtain ⟨G, hG⟩ : ∃ G, G = (1 - 2*X - S) * (2 : ℚ⟦X⟧)⁻¹ := ⟨_, rfl⟩
  have g : G * 2 = 1 - 2*X - S := by
    rw [hG, mul_assoc, PowerSeries.inv_mul_cancel _ (by rw [← map_ofNat (C (R := ℚ)) 2]; simp),
      mul_one]
  have s : S = 1 - 2*X - 2*G := by linear_combination g
  unfold R at hS
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simp only [a, ← hG]
  have h := congrArg (derivative ℚ) hS
  have t := congrArg (derivative ℚ) s
  simp only [← map_ofNat (C (R := ℚ))] at h t
  simp [Derivation.leibniz, pow_succ] at h t
  simp only [map_ofNat] at h t
  have E : -4*((1-4*X+4*X^2-4*X^3+4*X^4)*derivative ℚ G) + 2*((-4+8*X-12*X^2+16*X^3)*G)
      - 4*(1-4*X+4*X^2-4*X^3+4*X^4) - (-4+8*X-12*X^2+16*X^3)*(1-2*X) = 0 :=
    (mul_eq_zero.1 (by
      linear_combination (1-4*X+4*X^2-4*X^3+4*X^4)*h - (-4+8*X-12*X^2+16*X^3)*hS
        - 2*S*(1-4*X+4*X^2-4*X^3+4*X^4)*t + S*(-4+8*X-12*X^2+16*X^3)*s :
        S * _ = 0)).resolve_left
      (by rintro q; rw [q] at hS; simpa using congrArg (coeff 0) hS)
  simp only [← map_ofNat (C (R := ℚ))] at E
  have c := congrArg (coeff (m+6)) E
  simp [mul_add, mul_sub, add_mul, sub_mul, mul_assoc, pow_succ, coeff_derivative, coeff_X,
    coeff_one] at c ⊢
  linear_combination (-1/4 : ℚ) * c
