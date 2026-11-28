import OMAStatements.S_oeis_a182881
import Mathlib
open PowerSeries
theorem OMA.solution : type_of% @OMA.S_oeis_a182881.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have z (k : ℕ) [k.AtLeastTwo] : d⁄dX ℚ (OfNat.ofNat k) = 0 := Derivation.map_natCast _ k
  have hD : (-1 + 6*X - 9*X^2 + 2*X^3 - 18*X^4 + 30*X^5 + 7*X^6 + 30*X^7 - 18*X^8 + 2*X^9 - 9*X^10 + 6*X^11 - X^12)*G = 0 + (-2*X^3 + 4*X^4 + 2*X^5 + 4*X^6 - 2*X^7)*S := by
    linear_combination ((-1 + 2*X + X^2 + 2*X^3 - X^4)*S)*hG + ((1 - 4*X + 2*X^2 + 11*X^4 + 2*X^6 - 4*X^7 + X^8)*G)*hS
  have h1 := congrArg (d⁄dX ℚ) hS
  have h2 := congrArg (d⁄dX ℚ) hD
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at h1 h2
  have h : d⁄dX ℚ G * (X - 2*X^2 - X^3 - 2*X^4 + X^5) + G * (-3 + 3*X - 3*X^3 + 3*X^4) = 0 := by
    exact mul_left_cancel₀ (show (X^2*(4 - 32*X + 80*X^2 - 64*X^3 + 104*X^4 - 352*X^5 + 192*X^6 - 96*X^7 + 652*X^8 - 96*X^9 + 192*X^10 - 352*X^11 + 104*X^12 - 64*X^13 + 80*X^14 - 32*X^15 + 4*X^16) : ℚ⟦X⟧) ≠ 0 from mul_ne_zero (pow_ne_zero _ X_ne_zero) (fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h)) (by linear_combination (-4*X^3 + 16*X^4 - 8*X^5 - 44*X^7 - 8*X^9 + 16*X^10 - 4*X^11)*h2 - (-12*X^2 + 60*X^3 - 36*X^4 - 264*X^6 - 60*X^8 + 132*X^9 - 36*X^10)*hD + (4*X^6 - 16*X^7 + 8*X^8 + 44*X^10 + 8*X^12 - 16*X^13 + 4*X^14)*(S*h1 - 2*d⁄dX ℚ S*hS))
  have h := congrArg (coeff (m+4)) h
  rcases m with _|m <;>
  simp [pow_succ, mul_sub, mul_add, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_derivative, ← map_ofNat (C : ℚ →+* _)] at h ⊢ <;>
  linarith
