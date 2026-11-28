import OMAStatements.S_oeis_a162479
import Mathlib

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a162479.main := by
  intro T G hT h0 hG n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have hK : G^2 * ((1-X)^4 - 4*X) = (1-X)^2 := by
    linear_combination -G^2*hT + (1-X)^2*(G*((1-X)*T) + 1)*hG
  have h := congrArg (derivative ℚ) hK
  simp only [← map_ofNat (C (R := ℚ))] at h
  simp [Derivation.leibniz, pow_succ] at h
  simp only [map_ofNat] at h
  have E : 2*((1-X)*(((1-X)^4-4*X)*derivative ℚ G))
      + (2*((1-X)^4-4*X) + (1-X)*(-4*(1-X)^3-4))*G = 0 :=
    (mul_eq_zero.1 (by linear_combination (1-X)*h + 2*hK : G * _ = 0)).resolve_left
      (by rintro rfl; simp at hG)
  simp only [← map_ofNat (C (R := ℚ))] at E
  have c := congrArg (coeff (m+4)) E
  rcases m with _ | m <;>
  simp [mul_add, mul_sub, add_mul, sub_mul, mul_assoc, pow_succ, coeff_derivative, coeff_X,
    coeff_one] at c ⊢ <;>
  linear_combination (1/2 : ℚ) * c
