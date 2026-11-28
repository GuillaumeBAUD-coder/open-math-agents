import OMAStatements.S_oeis_a188314
import Mathlib

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a188314.main := by
  intro T G hT h0 hG n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have w : (1-X^2) - 2*(X*G) = (1-X^2)*T := by linear_combination -hG
  have h := congrArg (derivative ℚ) hT
  have t := congrArg (derivative ℚ) w
  simp only [← map_ofNat (C (R := ℚ))] at h t
  simp [Derivation.leibniz, pow_succ] at h t
  simp only [map_ofNat] at h t
  have x : (1 - X : ℚ⟦X⟧) ≠ 0 := fun q => by simpa using congrArg (coeff 0) q
  have E : 2*(-2*(X*((1-5*X-X^2+X^3)*((1+X)*((1+5*X)*derivative ℚ G))))
      - 2*((1+5*X)*((1-2*X-X^4)*G)) + (1+5*X)*((1+X)*(2+2*X+4*X^2))) = 0 :=
    (mul_eq_zero.1 ((mul_eq_zero.1 ((mul_eq_zero.1 (by
      linear_combination (1+5*X)*((1-X^2)*(((1-X)*(1-X^2)-4*X)*h - (-5-2*X+3*X^2)*hT)
        + 2*(1-X)*T*(((1-X)*(1-X^2)-4*X)*(1-X^2)*t
          + (2+2*X+4*X^2+2*X*((1-X)*(1-X^2)-4*X))*w)) :
        T * ((1-X) * ((1-X) * _)) = 0)).resolve_left
      (by rintro rfl; simp at h0))).resolve_left x)).resolve_left x
  simp only [← map_ofNat (C (R := ℚ))] at E
  have c := congrArg (coeff (m+5)) E
  rcases m with _ | m <;>
  simp [mul_add, mul_sub, add_mul, sub_mul, mul_assoc, pow_succ, coeff_derivative, coeff_X,
    coeff_one] at c ⊢ <;>
  linear_combination (-1/4 : ℚ) * c
