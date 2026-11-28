import OMAStatements.S_oeis_a368773
import Mathlib

open PowerSeries OMA.S_oeis_a368773 in
theorem OMA.solution : type_of% @OMA.S_oeis_a368773.main := by
  have hs : HasSubst (-10*X^2 + 9*X^4 : ℚ⟦X⟧) := HasSubst.of_constantCoeff_zero' (by simp)
  have hS : radical^2 = 1 - 10*X^2 + 9*X^4 := by
    rw [radical, ← subst_pow hs, sq (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)), ← binomialSeries_add, show (1/2 + 1/2 : ℚ) = (1:ℕ) by norm_num,
      binomialSeries_nat, pow_one, ← coe_substAlgHom hs, map_add, map_one, coe_substAlgHom hs,
      subst_X hs]
    ring
  obtain ⟨G, hG⟩ : ∃ G, G = B - 1 + X := ⟨_, rfl⟩
  have b : B * (1-3*X) = radical := by
    rw [B, mul_assoc, PowerSeries.inv_mul_cancel _ (by simp), mul_one]
  have l : (1-3*X)*(G+1-X) = radical := by
    rw [hG]
    linear_combination b
  have hL : ((1-3*X)*(G+1-X))^2 = 1 - 10*X^2 + 9*X^4 := by rw [l, hS]
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simp only [a, ← hG]
  have h := congrArg (derivative ℚ) hL
  simp only [← map_ofNat (C (R := ℚ))] at h
  simp [Derivation.leibniz, pow_succ] at h
  simp only [map_ofNat] at h
  have E : 2*((1-10*X^2+9*X^4)*derivative ℚ G) - (6-2*X-6*X^2+18*X^3)*G
      - 8 + 8*X + 24*X^2 - 24*X^3 = 0 :=
    (mul_eq_zero.1 ((mul_eq_zero.1 (by
      linear_combination (1-10*X^2+9*X^4)*h - (-20*X+36*X^3)*hL :
        ((1-3*X)*(G+1-X)) * ((1-3*X) * _) = 0)).resolve_left
      (by
        rw [l]
        rintro q
        rw [q] at hS
        simpa using congrArg (coeff 0) hS))).resolve_left
      (fun q => by simpa using congrArg (coeff 0) q)
  simp only [← map_ofNat (C (R := ℚ))] at E
  have c := congrArg (coeff (m+4)) E
  simp [mul_add, mul_sub, add_mul, sub_mul, mul_assoc, pow_succ, coeff_derivative, coeff_X] at c ⊢
  linear_combination (1/8 : ℚ) * c
