import OMAStatements.S_oeis_a116406
import Mathlib

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a116406.main := by
  intro S G hS h0 hG n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have x1 : (1 + X : ℚ⟦X⟧) ≠ 0 := fun q => by simpa using congrArg (coeff 0) q
  have x2 : (1 + 2*X : ℚ⟦X⟧) ≠ 0 := fun q => by simpa using congrArg (coeff 0) q
  have l : 2*(1-4*X^2)*G - (1+X-2*X^2) = (1+X)*S := by linear_combination hG
  have hL : (2*(1-4*X^2)*G - (1+X-2*X^2))^2 = (1+X)^2*(1-4*X^2) := by
    linear_combination (1+X)^2*hS + (2*(1-4*X^2)*G - (1+X-2*X^2) + (1+X)*S)*l
  have h := congrArg (derivative ℚ) hL
  simp only [← map_ofNat (C (R := ℚ))] at h
  simp [Derivation.leibniz, pow_succ] at h
  simp only [map_ofNat] at h
  have E : 2*(2*(1+X)*(1-2*X)^2*(1+2*X)*derivative ℚ G - 2*(1-2*X)*(1+4*X)*G - 6*X^2) = 0 :=
    (mul_eq_zero.1 ((mul_eq_zero.1 ((mul_eq_zero.1 (by
      linear_combination ((1+X)^2*(1-4*X^2))*h
        - (2*(1+X)*(1-4*X^2) + (1+X)^2*(-8*X))*hL :
        (2*(1-4*X^2)*G - (1+X-2*X^2)) * ((1+X) * ((1+2*X) * _)) = 0)).resolve_left
      (by rw [l]; exact mul_ne_zero x1 (by rintro rfl; simp at h0)))).resolve_left x1)).resolve_left x2
  have d := congrArg (derivative ℚ) E
  simp only [← map_ofNat (C (R := ℚ))] at d
  simp [Derivation.leibniz, pow_succ] at d
  simp only [map_ofNat] at d
  have F : 4*(X*((1-2*X-4*X^2+8*X^3)*derivative ℚ (derivative ℚ G)))
      + 2*((-4+4*X-8*X^2+32*X^3)*derivative ℚ G) + 8*G = 0 :=
    (mul_eq_zero.1 (by linear_combination 2*X*d - 2*E : (1+X : ℚ⟦X⟧) * _ = 0)).resolve_left x1
  simp only [← map_ofNat (C (R := ℚ))] at F
  have c := congrArg (coeff (m+2)) F
  rcases m with _ | _ | m <;>
  simp [mul_add, mul_sub, add_mul, sub_mul, mul_assoc, pow_succ, coeff_derivative, coeff_X,
    coeff_one] at c ⊢ <;>
  linear_combination (1/4 : ℚ) * c
