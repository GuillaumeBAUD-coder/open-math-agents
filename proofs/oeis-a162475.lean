import OMAStatements.S_oeis_a162475
import Mathlib

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a162475.main := by
  intro T G hT h0 hG n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have w : (1-X)^4 - 2*(X*G) = (1-X)^4*T := by linear_combination -hG
  have h := congrArg (derivative ℚ) hT
  have t := congrArg (derivative ℚ) w
  simp only [← map_ofNat (C (R := ℚ))] at h t
  simp [Derivation.leibniz, pow_succ] at h t
  simp only [map_ofNat] at h t
  have E : 2*(-2*(X*(((1-X)^4-4*X)*((1-X)*derivative ℚ G)))
      - 2*((((1-X)^4-4*X)*(1-X) + X*(4*((1-X)^4-4*X)+2+6*X))*G) + (2+6*X)*(1-X)^4) = 0 :=
    (mul_eq_zero.1 (by
      linear_combination (1-X)*(((1-X)^4-4*X)*h - (-4*(1-X)^3-4)*hT)
        + 2*T*(((1-X)^4-4*X)*(1-X)*t + (4*((1-X)^4-4*X)+2+6*X)*w) : T * _ = 0)).resolve_left
      (by rintro rfl; simp at h0)
  simp only [← map_ofNat (C (R := ℚ))] at E
  have c := congrArg (coeff (m+6)) E
  simp [mul_add, mul_sub, add_mul, sub_mul, mul_assoc, pow_succ, coeff_derivative, coeff_X,
    coeff_one] at c ⊢
  linear_combination (-1/4 : ℚ) * c
