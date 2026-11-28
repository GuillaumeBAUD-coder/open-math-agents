import OMAStatements.S_oeis_a155051
import Mathlib
open PowerSeries
theorem OMA.solution : type_of% @OMA.S_oeis_a155051.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have z (k : ℕ) [k.AtLeastTwo] : d⁄dX ℚ (OfNat.ofNat k) = 0 := Derivation.map_natCast _ k
  have hD : (4*X^4 - 8*X^5 + 4*X^6)*G = 2*X^2 - 2*X^4 + (-2*X^2 + 2*X^4)*S := by
    linear_combination ((2*X^2 - 2*X^3))*hG + (0)*hS
  have h1 := congrArg (d⁄dX ℚ) hS
  have h2 := congrArg (d⁄dX ℚ) hD
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at h1 h2
  have h : d⁄dX ℚ G * (-X + 5*X^3 - 4*X^5) + G * (-2 + 2*X + 6*X^2 - 8*X^3 - 4*X^4) = -2 - 4*X - 2*X^2 := by
    exact mul_left_cancel₀ (show (X^5*(16 - 32*X + 16*X^2) : ℚ⟦X⟧) ≠ 0 from mul_ne_zero (pow_ne_zero _ X_ne_zero) (fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h)) (by linear_combination (-4*X^2 + 20*X^4 - 16*X^6)*h2 - (-8*X + 64*X^3 - 80*X^5)*hD + (4*X^4 - 8*X^6 + 4*X^8)*(S*h1 - 2*d⁄dX ℚ S*hS))
  have d1 := congrArg (d⁄dX ℚ) h
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at d1
  have h : (d⁄dX ℚ) (d⁄dX ℚ G) * (-X^2 + X^3 + 4*X^4 - 4*X^5) + d⁄dX ℚ G * (2*X^2 + 4*X^3 - 12*X^4) + G * (6 - 10*X + 4*X^2 - 4*X^3) = 6 + 2*X :=
    mul_left_cancel₀ (show (1 + X : ℚ⟦X⟧) ≠ 0 from fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h) (by linear_combination (-3)*h + (X)*d1)
  have h := congrArg (coeff (m+3)) h
  rcases m with _|_|m <;>
  simp [pow_succ, mul_sub, mul_add, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_derivative, ← map_ofNat (C : ℚ →+* _)] at h ⊢ <;>
  linarith
