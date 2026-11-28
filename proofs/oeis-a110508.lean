import OMAStatements.S_oeis_a110508
import Mathlib
open PowerSeries
theorem OMA.solution : type_of% @OMA.S_oeis_a110508.main := by
  intro S c G h1 _ h2 h3 n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have z (k : ℕ) [k.AtLeastTwo] : d⁄dX ℚ (OfNat.ofNat k) = 0 := Derivation.map_natCast _ k
  have hD : (8*X^2 + 16*X^4 + 8*X^5)*G = 12*X^2 - 4*X^3 + (-4*X^2 - 4*X^3)*S := by
    linear_combination (12*X^2 - 4*X^3 + (-4*X^2 - 4*X^3)*S)*h3 + ((3*X^2 + 2*X^3 - X^4)*G + (-X^2 - 2*X^3 - X^4)*S*G)*h2 + ((X^2 + 2*X^3 + X^4)*G)*h1
  have e1 := congrArg (d⁄dX ℚ) h1
  have e2 := congrArg (d⁄dX ℚ) hD
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at e1 e2
  have h : d⁄dX ℚ G * (1 - 7*X - 6*X^2 - 13*X^3 - 23*X^4 - 8*X^5) + G * (3 + 16*X - 19*X^2 - 26*X^3 - 12*X^4) = 4 + 20*X - 2*X^2 :=
    mul_left_cancel₀ (show (X^4*(-64) : ℚ⟦X⟧) ≠ 0 from mul_ne_zero (pow_ne_zero _ X_ne_zero) (fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h)) (by linear_combination (-8*X^2 + 56*X^3 + 64*X^4)*e2 - (-16*X + 136*X^2 + 224*X^3)*hD + (16*X^4 + 32*X^5 + 16*X^6)*(S*e1 - 2*d⁄dX ℚ S*h1))
  have d1 := congrArg (d⁄dX ℚ) h
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at d1
  have h : (d⁄dX ℚ) (d⁄dX ℚ G) * (3*X^2 - 24*X^3 + 6*X^4 - 45*X^5 - 24*X^6) + d⁄dX ℚ G * (-4*X + 20*X^2 + 16*X^3 - 138*X^4 - 124*X^5) + G * (-12*X - 4*X^2 - 34*X^3 - 96*X^4) = -16*X - 4*X^2 :=
    mul_left_cancel₀ (show (1 + X : ℚ⟦X⟧) ≠ 0 from fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h) (by linear_combination (-4*X)*h + (3*X^2)*d1)
  have h := congrArg (coeff (m+4)) h
  rcases m with _|_|m <;>
  simp [pow_succ, mul_sub, mul_add, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_derivative, ← map_ofNat (C : ℚ →+* _)] at h ⊢ <;>
  linarith
