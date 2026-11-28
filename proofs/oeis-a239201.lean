import OMAStatements.S_oeis_a239201
import Mathlib
open PowerSeries
theorem OMA.solution : type_of% @OMA.S_oeis_a239201.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have z (k : ℕ) [k.AtLeastTwo] : d⁄dX ℚ (OfNat.ofNat k) = 0 := Derivation.map_natCast _ k
  have hD : (-4*X^2 + 32*X^3 - 72*X^4 + 64*X^5 - 20*X^6)*G = -2*X^3 + 14*X^4 - 22*X^5 + 10*X^6 + (-6*X^3 + 12*X^4 - 6*X^5)*S := by
    linear_combination ((-1 + 7*X - 11*X^2 + 5*X^3) + (-1 + 4*X - 3*X^2)*S)*hG + ((X - 4*X^2 + 3*X^3) + (1 - 8*X + 22*X^2 - 24*X^3 + 9*X^4)*G)*hS
  have h1 := congrArg (d⁄dX ℚ) hS
  have h2 := congrArg (d⁄dX ℚ) hD
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at h1 h2
  have h : d⁄dX ℚ G * (-X + 7*X^2 - 11*X^3 + 5*X^4) + G * (1 - 4*X + 3*X^2) = X^2 := by
    exact mul_left_cancel₀ (show (X^4*(-48 + 432*X - 1248*X^2 + 1632*X^3 - 1008*X^4 + 240*X^5) : ℚ⟦X⟧) ≠ 0 from mul_ne_zero (pow_ne_zero _ X_ne_zero) (fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h)) (by linear_combination (-12*X^3 + 96*X^4 - 216*X^5 + 192*X^6 - 60*X^7)*h2 - (-36*X^2 + 348*X^3 - 948*X^4 + 996*X^5 - 360*X^6)*hD + (36*X^6 - 144*X^7 + 216*X^8 - 144*X^9 + 36*X^10)*(S*h1 - 2*d⁄dX ℚ S*hS))
  have h := congrArg (coeff (m+3)) h
  rcases m with _|m <;>
  simp [pow_succ, mul_sub, mul_add, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_derivative, ← map_ofNat (C : ℚ →+* _)] at h ⊢ <;>
  linarith
