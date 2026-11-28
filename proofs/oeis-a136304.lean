import OMAStatements.S_oeis_a136304
import Mathlib
open PowerSeries
theorem OMA.solution : type_of% @OMA.S_oeis_a136304.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have z (k : ℕ) [k.AtLeastTwo] : d⁄dX ℚ (OfNat.ofNat k) = 0 := Derivation.map_natCast _ k
  have hD : (4*X^2 - 24*X^3 + 52*X^4 - 56*X^5 + 40*X^6 - 16*X^7 + 4*X^8)*G = 2*X - 10*X^2 + 18*X^3 - 16*X^4 + 8*X^5 - 2*X^6 + (-2*X + 10*X^2 - 18*X^3 + 16*X^4 - 8*X^5 + 2*X^6)*S := by
    linear_combination ((2*X - 6*X^2 + 4*X^3 - 2*X^4))*hG + (0)*hS
  have h1 := congrArg (d⁄dX ℚ) hS
  have h2 := congrArg (d⁄dX ℚ) hD
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at h1 h2
  have h : d⁄dX ℚ G * (-X + 8*X^2 - 21*X^3 + 23*X^4 - 13*X^5 + 4*X^6) + G * (-1 + 7*X - 18*X^2 + 20*X^3 - 20*X^4 + 6*X^5) = -1 + 3*X - 3*X^2 + X^3 := by
    exact mul_left_cancel₀ (show (X^2*(16 - 112*X + 304*X^2 - 432*X^3 + 384*X^4 - 224*X^5 + 80*X^6 - 16*X^7) : ℚ⟦X⟧) ≠ 0 from mul_ne_zero (pow_ne_zero _ X_ne_zero) (fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h)) (by linear_combination (-4*X + 36*X^2 - 116*X^3 + 176*X^4 - 144*X^5 + 68*X^6 - 16*X^7)*h2 - (-4 + 64*X - 308*X^2 + 632*X^3 - 656*X^4 + 376*X^5 - 104*X^6)*hD + (4*X^2 - 40*X^3 + 172*X^4 - 424*X^5 + 676*X^6 - 744*X^7 + 584*X^8 - 328*X^9 + 128*X^10 - 32*X^11 + 4*X^12)*(S*h1 - 2*d⁄dX ℚ S*hS))
  have h := congrArg (coeff (m+5)) h
  rcases m with _|m <;>
  simp [pow_succ, mul_sub, mul_add, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_derivative, ← map_ofNat (C : ℚ →+* _)] at h ⊢ <;>
  linarith
