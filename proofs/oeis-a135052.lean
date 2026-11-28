import OMAStatements.S_oeis_a135052
import Mathlib
open PowerSeries
theorem OMA.solution : type_of% @OMA.S_oeis_a135052.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have z (k : ℕ) [k.AtLeastTwo] : d⁄dX ℚ (OfNat.ofNat k) = 0 := Derivation.map_natCast _ k
  have hD : (4*X^4 - 8*X^5 + 4*X^6)*G = 2*X^2 - 6*X^3 + 4*X^4 + (-2*X^2 + 2*X^3)*S := by
    linear_combination ((2*X^2 - 2*X^3))*hG + (0)*hS
  have h1 := congrArg (d⁄dX ℚ) hS
  have h2 := congrArg (d⁄dX ℚ) hD
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at h1 h2
  have h : d⁄dX ℚ G * (-X + 5*X^2 - 4*X^3 - 8*X^4 + 12*X^5 - 4*X^6) + G * (-2 + 9*X - 10*X^2 - 4*X^3 + 12*X^4 - 4*X^5) = -2 + 6*X - 8*X^2 + 4*X^3 := by
    exact mul_left_cancel₀ (show (X^5*(16 - 32*X + 16*X^2) : ℚ⟦X⟧) ≠ 0 from mul_ne_zero (pow_ne_zero _ X_ne_zero) (fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h)) (by linear_combination (-4*X^2 + 20*X^3 - 16*X^4 - 32*X^5 + 48*X^6 - 16*X^7)*h2 - (-8*X + 52*X^2 - 56*X^3 - 112*X^4 + 208*X^5 - 80*X^6)*hD + (4*X^4 - 8*X^5 + 4*X^6)*(S*h1 - 2*d⁄dX ℚ S*hS))
  have h := congrArg (coeff (m+5)) h
  rcases m with _|m <;>
  simp [pow_succ, mul_sub, mul_add, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_derivative, ← map_ofNat (C : ℚ →+* _)] at h ⊢ <;>
  linarith
