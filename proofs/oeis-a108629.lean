import OMAStatements.S_oeis_a108629
import Mathlib

open PowerSeries OMA.S_oeis_a108629 in
theorem OMA.solution : type_of% @OMA.S_oeis_a108629.main := by
  have hs : HasSubst radicandTail := HasSubst.of_constantCoeff_zero' (by simp [radicandTail])
  have hS : rootSeries^2 = 1 - 2*X - 3*X^2 - 4*X^3 := by
    rw [rootSeries, ← subst_pow hs, sq (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)),
      ← binomialSeries_add, show (1/2 + 1/2 : ℚ) = (1:ℕ) by norm_num,
      binomialSeries_nat, pow_one, ← coe_substAlgHom hs, map_add, map_one, coe_substAlgHom hs,
      subst_X hs, radicandTail]
    ring
  have g : series * (2*(1+X+X^2)) = 1 + X - rootSeries := by
    rw [series, mul_assoc, PowerSeries.inv_mul_cancel _
      (by rw [← map_ofNat (C (R := ℚ)) 2]; simp), mul_one]
  have s : rootSeries = 1 + X - 2*((1+X+X^2)*series) := by linear_combination g
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simp only [a]
  have h := congrArg (derivative ℚ) hS
  have t := congrArg (derivative ℚ) s
  simp only [← map_ofNat (C (R := ℚ))] at h t
  simp [Derivation.leibniz, pow_succ] at h t
  simp only [map_ofNat] at h t
  have E : -4*((1-2*X-3*X^2-4*X^3)*((1+X+X^2)*derivative ℚ series))
      + (-4*(1-2*X-3*X^2-4*X^3)*(1+2*X) + 2*(-2-6*X-12*X^2)*(1+X+X^2))*series
      + 4 + 4*X + 12*X^2 + 4*X^3 = 0 :=
    (mul_eq_zero.1 (by
      linear_combination (1-2*X-3*X^2-4*X^3)*h - (-2-6*X-12*X^2)*hS
        - 2*rootSeries*(1-2*X-3*X^2-4*X^3)*t + rootSeries*(-2-6*X-12*X^2)*s :
        rootSeries * _ = 0)).resolve_left
      (by rintro q; rw [q] at hS; simpa using congrArg (coeff 0) hS)
  simp only [← map_ofNat (C (R := ℚ))] at E
  have c := congrArg (coeff (m+5)) E
  simp [mul_add, mul_sub, add_mul, sub_mul, mul_assoc, pow_succ, coeff_derivative, coeff_X] at c ⊢
  linear_combination (-1/4 : ℚ) * c
