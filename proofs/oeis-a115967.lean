import OMAStatements.S_oeis_a115967
import Mathlib

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a115967.main := by
  intro S G hS h0 hG n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have s : (3-8*X-12*X^2)*G - 1 = S + S := by linear_combination (2*S+1)*hG - 4*G*hS
  have hL : ((3-8*X-12*X^2)*G - 1)^2 = 4*(1-2*X-3*X^2) := by
    linear_combination 4*hS + ((3-8*X-12*X^2)*G - 1 + 2*S)*s
  have h := congrArg (derivative ℚ) hL
  simp only [← map_ofNat (C (R := ℚ))] at h
  simp [Derivation.leibniz, pow_succ] at h
  simp only [map_ofNat] at h
  have E : 2*((1-2*X-3*X^2)*((3-8*X-12*X^2)*derivative ℚ G))
      + (2*(1-2*X-3*X^2)*(-8-24*X) + (2+6*X)*(3-8*X-12*X^2))*G - (2+6*X) = 0 :=
    (mul_eq_zero.1 (by
      linear_combination (1-2*X-3*X^2)*h - (-2-6*X)*hL :
        ((3-8*X-12*X^2)*G - 1) * _ = 0)).resolve_left
      (fun q => by
        have := congrArg (coeff 0) (s.symm.trans q)
        simp at this h0
        linarith)
  simp only [← map_ofNat (C (R := ℚ))] at E
  have c := congrArg (coeff (m+3)) E
  rcases m with _ | m <;>
  simp [mul_add, mul_sub, add_mul, sub_mul, mul_assoc, pow_succ, coeff_derivative, coeff_X,
    coeff_one] at c ⊢ <;>
  linear_combination (1/2 : ℚ) * c
