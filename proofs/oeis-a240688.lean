import OMAStatements.S_oeis_a240688
import Mathlib
open PowerSeries
theorem OMA.solution : type_of% @OMA.S_oeis_a240688.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have z (k : ℕ) [k.AtLeastTwo] : d⁄dX ℚ (OfNat.ofNat k) = 0 := Derivation.map_natCast _ k
  have hD : (-4*X + 4*X^2 + 52*X^3 + 92*X^4 + 64*X^5 + 16*X^6)*G = -2*X + 4*X^2 + 22*X^3 + 24*X^4 + 8*X^5 + (-2*X - 8*X^2 - 10*X^3 - 4*X^4)*S := by
    linear_combination ((-1 + 3*X + 8*X^2 + 4*X^3) + (-1 - X)*S)*hG + ((X + X^2) + (1 + 2*X + X^2)*G)*hS
  have h1 := congrArg (d⁄dX ℚ) hS
  have h2 := congrArg (d⁄dX ℚ) hD
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at h1 h2
  have h : d⁄dX ℚ G * (-1 + X + 14*X^2 + 20*X^3 + 8*X^4) + G * (3 + 6*X + 12*X^2 + 8*X^3) = 2 := by
    exact mul_left_cancel₀ (show (X^2*(-16 + 224*X^2 + 576*X^3 + 624*X^4 + 320*X^5 + 64*X^6) : ℚ⟦X⟧) ≠ 0 from mul_ne_zero (pow_ne_zero _ X_ne_zero) (fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h)) (by linear_combination (-4*X + 60*X^3 + 136*X^4 + 112*X^5 + 32*X^6)*h2 - (-4 - 8*X + 132*X^2 + 440*X^3 + 464*X^4 + 160*X^5)*hD + (4*X^2 + 32*X^3 + 104*X^4 + 176*X^5 + 164*X^6 + 80*X^7 + 16*X^8)*(S*h1 - 2*d⁄dX ℚ S*hS))
  have d1 := congrArg (d⁄dX ℚ) h
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at d1
  have h : (d⁄dX ℚ) (d⁄dX ℚ G) * (X^2 - 3*X^3 - 8*X^4 - 4*X^5) + d⁄dX ℚ G * (-4*X^2 - 26*X^3 - 20*X^4) + G * (-6*X^2 - 12*X^3) = 0 :=
    mul_left_cancel₀ (show (1 + 2*X : ℚ⟦X⟧) ≠ 0 from fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h) (by linear_combination (-X^2)*d1)
  have h := congrArg (coeff (m+3)) h
  rcases m with _|_|m <;>
  simp [pow_succ, mul_sub, mul_add, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_derivative, ← map_ofNat (C : ℚ →+* _)] at h ⊢ <;>
  linarith
