import OMAStatements.S_oeis_a132364
import Mathlib

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a132364.main := by
  intro S c G hS h0 hc hG n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have K : G * (2 - X + X*S) = 2 := by linear_combination 2*hG + G*X*hc
  have s : 2 - X - (2-2*X+2*X^3)*G = X*S :=
    mul_left_cancel₀ (fun q => by
      have := congrArg (coeff 0) q
      rw [← map_ofNat (C (R := ℚ)) 2] at this
      simp at this : 2 - X + X*S ≠ 0)
      (by linear_combination -X^2*hS - (2-2*X+2*X^3)*K)
  have hL : (2 - X - (2-2*X+2*X^3)*G)^2 = X^2*(1-4*X) := by
    linear_combination X^2*hS + (2 - X - (2-2*X+2*X^3)*G + X*S)*s
  have h := congrArg (derivative ℚ) hL
  simp only [← map_ofNat (C (R := ℚ))] at h
  simp [Derivation.leibniz, pow_succ] at h
  simp only [map_ofNat] at h
  have E : -2*(X*((1-4*X)*((2-2*X+2*X^3)*derivative ℚ G)))
      + (2*X*(1-4*X)*(2-6*X^2) + (2-12*X)*(2-2*X+2*X^3))*G - 4 + 24*X - 4*X^2 = 0 :=
    (mul_eq_zero.1 ((mul_eq_zero.1 (by
      linear_combination (X^2*(1-4*X))*h - (2*X-12*X^2)*hL :
        (2 - X - (2-2*X+2*X^3)*G) * (X * _) = 0)).resolve_left
      (by rw [s]; exact mul_ne_zero X_ne_zero (by rintro rfl; simp at h0)))).resolve_left X_ne_zero
  simp only [← map_ofNat (C (R := ℚ))] at E
  have c := congrArg (coeff (m+4)) E
  rcases m with _ | m <;>
  simp [mul_add, mul_sub, add_mul, sub_mul, mul_assoc, pow_succ, coeff_derivative, coeff_X,
    coeff_one] at c ⊢ <;>
  linear_combination (1/4 : ℚ) * c
