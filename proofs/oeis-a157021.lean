import OMAStatements.S_oeis_a157021
import Mathlib
open PowerSeries
theorem OMA.solution : type_of% @OMA.S_oeis_a157021.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have z (k : ℕ) [k.AtLeastTwo] : d⁄dX ℚ (OfNat.ofNat k) = 0 := Derivation.map_natCast _ k
  have hD : (4*X^8 - 8*X^9 + 4*X^10)*G = 2*X^4 - 10*X^5 + 22*X^6 - 26*X^7 + 16*X^8 - 4*X^9 + (-2*X^4 + 6*X^5 - 8*X^6 + 4*X^7)*S := by
    linear_combination ((2*X^4 - 2*X^5))*hG + (0)*hS
  have h1 := congrArg (d⁄dX ℚ) hS
  have h2 := congrArg (d⁄dX ℚ) hD
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at h1 h2
  have h : d⁄dX ℚ G * (X - 7*X^2 + 22*X^3 - 40*X^4 + 41*X^5 - 19*X^6 - 4*X^7 + 6*X^8) + G * (4 - 25*X + 68*X^2 - 104*X^3 + 88*X^4 - 33*X^5 + 6*X^7) = 4 - 20*X + 48*X^2 - 64*X^3 + 48*X^4 - 16*X^5 := by
    exact mul_left_cancel₀ (show (X^11*(-16 + 32*X - 16*X^2) : ℚ⟦X⟧) ≠ 0 from mul_ne_zero (pow_ne_zero _ X_ne_zero) (fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h)) (by linear_combination (-4*X^4 + 28*X^5 - 88*X^6 + 160*X^7 - 164*X^8 + 76*X^9 + 16*X^10 - 24*X^11)*h2 - (-16*X^3 + 132*X^4 - 480*X^5 + 992*X^6 - 1152*X^7 + 612*X^8 + 112*X^9 - 216*X^10)*hD + (4*X^8 - 24*X^9 + 68*X^10 - 112*X^11 + 112*X^12 - 64*X^13 + 16*X^14)*(S*h1 - 2*d⁄dX ℚ S*hS))
  have h := congrArg (coeff (m+7)) h
  rcases m with _|m <;>
  simp [pow_succ, mul_sub, mul_add, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_derivative, ← map_ofNat (C : ℚ →+* _)] at h ⊢ <;>
  linarith
