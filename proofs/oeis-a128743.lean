import OMAStatements.S_oeis_a128743
import Mathlib
open PowerSeries
theorem OMA.solution : type_of% @OMA.S_oeis_a128743.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have z (k : ℕ) [k.AtLeastTwo] : d⁄dX ℚ (OfNat.ofNat k) = 0 := Derivation.map_natCast _ k
  have hD : (-4*X^2 + 24*X^3 - 20*X^4)*G = 2*X - 14*X^2 + 22*X^3 - 10*X^4 + (-2*X + 8*X^2 - 2*X^3)*S := by
    linear_combination ((-2*X)*S)*hG + ((2*X - 2*X^2) + (4*X^2)*G)*hS
  have h1 := congrArg (d⁄dX ℚ) hS
  have h2 := congrArg (d⁄dX ℚ) hD
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at h1 h2
  have h : d⁄dX ℚ G * (X - 10*X^2 + 30*X^3 - 26*X^4 + 5*X^5) + G * (1 - 9*X + 21*X^2 - 17*X^3) = 6*X^2 - 6*X^3 := by
    exact mul_left_cancel₀ (show (X^2*(16 - 96*X + 80*X^2) : ℚ⟦X⟧) ≠ 0 from mul_ne_zero (pow_ne_zero _ X_ne_zero) (fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h)) (by linear_combination (-4*X + 40*X^2 - 120*X^3 + 104*X^4 - 20*X^5)*h2 - (-4 + 68*X - 292*X^2 + 324*X^3 - 80*X^4)*hD + (4*X^2 - 32*X^3 + 72*X^4 - 32*X^5 + 4*X^6)*(S*h1 - 2*d⁄dX ℚ S*hS))
  have d1 := congrArg (d⁄dX ℚ) h
  have d2 := congrArg (d⁄dX ℚ) d1
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at d1 d2
  have h : (d⁄dX ℚ) ((d⁄dX ℚ) (d⁄dX ℚ G)) * (X^3 - 6*X^4 + 5*X^5) + (d⁄dX ℚ) (d⁄dX ℚ G) * (-15*X^3 + 25*X^4) + d⁄dX ℚ G * (-2*X + 2*X^2 + 20*X^3) + G * (4) = 0 :=
    mul_left_cancel₀ (show (1 - 8*X + 18*X^2 - 8*X^3 + X^4 : ℚ⟦X⟧) ≠ 0 from fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h) (by linear_combination (4 - 23*X + 9*X^2)*h + (-3*X + 16*X^2 - 5*X^3)*d1 + (X^2 - 4*X^3 + X^4)*d2)
  have h := congrArg (coeff (m+2)) h
  rcases m with _|_|_|m <;>
  simp [pow_succ, mul_sub, mul_add, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_derivative, ← map_ofNat (C : ℚ →+* _)] at h ⊢ <;>
  linarith
