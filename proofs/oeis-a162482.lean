import OMAStatements.S_oeis_a162482
import Mathlib

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a162482.main := by
  intro T G hT h0 hG n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have w : (1-X)^3 - X - 2*(X^2*G) = (1-X)^3*T := by linear_combination -hG
  have hW : ((1-X)^3 - X - 2*(X^2*G))^2 = 1-8*X+18*X^2-26*X^3+17*X^4-6*X^5+X^6 := by
    linear_combination hT + ((1-X)^3 - X - 2*(X^2*G) + (1-X)^3*T)*w
  have h := congrArg (derivative ℚ) hW
  simp only [← map_ofNat (C (R := ℚ))] at h
  simp [Derivation.leibniz, pow_succ] at h
  simp only [map_ofNat] at h
  have E : -4*(X*(X*((1-8*X+18*X^2-26*X^3+17*X^4-6*X^5+X^6)*derivative ℚ G)))
      - 8*(X*((1-8*X+18*X^2-26*X^3+17*X^4-6*X^5+X^6)*G))
      + 2*(X*(X*((-8+36*X-78*X^2+68*X^3-30*X^4+6*X^5)*G))) + 8*X - 24*X^3 + 16*X^4 = 0 :=
    (mul_eq_zero.1 (by
      linear_combination (1-8*X+18*X^2-26*X^3+17*X^4-6*X^5+X^6)*h
        - (-8+36*X-78*X^2+68*X^3-30*X^4+6*X^5)*hW :
        ((1-X)^3 - X - 2*(X^2*G)) * _ = 0)).resolve_left
      (fun q => by simpa using congrArg (coeff 0) q)
  simp only [← map_ofNat (C (R := ℚ))] at E
  have c := congrArg (coeff (m+7)) E
  rcases m with _ | m <;>
  simp [mul_add, mul_sub, add_mul, sub_mul, mul_assoc, pow_succ, coeff_derivative, coeff_X,
    coeff_one] at c ⊢ <;>
  linear_combination (-1/4 : ℚ) * c
