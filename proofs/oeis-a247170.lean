import OMAStatements.S_oeis_a247170
import Mathlib
open PowerSeries
theorem OMA.solution : type_of% @OMA.S_oeis_a247170.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have z (k : ℕ) [k.AtLeastTwo] : d⁄dX ℚ (OfNat.ofNat k) = 0 := Derivation.map_natCast _ k
  have hD : (-4*X^2 + 8*X^4 + 16*X^5 - 4*X^6)*G = 6*X^2 - 12*X^4 - 24*X^5 + 6*X^6 + (-6*X^2 - 2*X^4)*S := by
    linear_combination ((-2*X)*S)*hG + ((6*X^2) + (4*X^2)*G)*hS
  have h1 := congrArg (d⁄dX ℚ) hS
  have h2 := congrArg (d⁄dX ℚ) hD
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at h1 h2
  have h : d⁄dX ℚ G * (-3 + 5*X^2 + 12*X^3 - X^4 + 4*X^5 - X^6) + G * (8*X + 18*X^2 - 8*X^3 - 2*X^4) = -12*X - 27*X^2 + 12*X^3 + 3*X^4 := by
    exact mul_left_cancel₀ (show (X^4*(-16 + 32*X^2 + 64*X^3 - 16*X^4) : ℚ⟦X⟧) ≠ 0 from mul_ne_zero (pow_ne_zero _ X_ne_zero) (fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h)) (by linear_combination (-12*X^2 + 20*X^4 + 48*X^5 - 4*X^6 + 16*X^7 - 4*X^8)*h2 - (-24*X + 56*X^3 + 168*X^4 - 8*X^5 + 88*X^6 - 24*X^7)*hD + (36*X^4 + 24*X^6 + 4*X^8)*(S*h1 - 2*d⁄dX ℚ S*hS))
  have d1 := congrArg (d⁄dX ℚ) h
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at d1
  have h : (d⁄dX ℚ) (d⁄dX ℚ G) * (2*X^2 + 2*X^3 - 4*X^4 - 12*X^5 - 6*X^6 + 2*X^7) + d⁄dX ℚ G * (-5*X - 5*X^2 - 2*X^3 - 18*X^4 - 9*X^5 + 7*X^6) + G * (8*X^2 + 14*X^3 + 6*X^4) = -12*X^2 - 21*X^3 - 9*X^4 :=
    mul_left_cancel₀ (show (3 + X^2 : ℚ⟦X⟧) ≠ 0 from fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h) (by linear_combination (5*X + 5*X^2)*h + (-2*X^2 - 2*X^3)*d1)
  have h := congrArg (coeff (m+5)) h
  rcases m with _|_|m <;>
  simp [pow_succ, mul_sub, mul_add, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_derivative, ← map_ofNat (C : ℚ →+* _)] at h ⊢ <;>
  linarith
