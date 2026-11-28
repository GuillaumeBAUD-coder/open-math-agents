import OMAStatements.S_oeis_a166076
import Mathlib

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a166076.main := by
  intro S G hS h0 hG n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have s : S = 7 + 5*X - 2*((3+5*X+2*X^2)*G) := by linear_combination hG
  have h := congrArg (derivative ℚ) hS
  have t := congrArg (derivative ℚ) s
  simp only [← map_ofNat (C (R := ℚ))] at h t
  simp [Derivation.leibniz, pow_succ] at h t
  simp only [map_ofNat] at h t
  have E : 2*((1-10*X-7*X^2)*(5 - 2*((5+4*X)*G) - 2*((3+5*X+2*X^2)*derivative ℚ G)))
      + (10+14*X)*(7+5*X - 2*((3+5*X+2*X^2)*G)) = 0 :=
    (mul_eq_zero.1 (by
      linear_combination (1-10*X-7*X^2)*h + (10+14*X)*hS - 2*S*(1-10*X-7*X^2)*t
        - S*(10+14*X)*s : S * _ = 0)).resolve_left (by rintro rfl; simp at h0)
  simp only [← map_ofNat (C (R := ℚ))] at E
  have c := congrArg (coeff (m+3)) E
  rcases m with _ | m <;>
  simp [mul_add, mul_sub, add_mul, sub_mul, mul_assoc, pow_succ, coeff_derivative, coeff_X] at c ⊢ <;>
  linear_combination (-1/4 : ℚ) * c
