import OMAStatements.S_oeis_a116388
import Mathlib
open PowerSeries
theorem OMA.solution : type_of% @OMA.S_oeis_a116388.main := by
  intro S M G h1 _ h2 h3 n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have z (k : ℕ) [k.AtLeastTwo] : d⁄dX ℚ (OfNat.ofNat k) = 0 := Derivation.map_natCast _ k
  have hD : (4*X^3 - 16*X^4 - 8*X^5 + 44*X^6 + 44*X^7 + 12*X^8)*G = 2*X^3 - 4*X^4 - 6*X^5 + (2*X^3 - 6*X^4 - 4*X^5)*S := by
    linear_combination (2*X^3 - 4*X^4 - 6*X^5 + (2*X^3 - 6*X^4 - 4*X^5)*S)*h3 + ((X^2 - 2*X^3 - 3*X^4)*S*G + (X^2 - 3*X^3 - 2*X^4)*S^2*G)*h2 + ((-4*X^3 + 8*X^4 + 12*X^5 + 4*X^6)*G + (-X^2 + 3*X^3 + 2*X^4)*S*G)*h1
  have e1 := congrArg (d⁄dX ℚ) h1
  have e2 := congrArg (d⁄dX ℚ) hD
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at e1 e2
  have h : d⁄dX ℚ G * (-1 + 7*X - 8*X^2 - 25*X^3 + 18*X^4 + 52*X^5 + 31*X^6 + 6*X^7) + G * (2*X - 17*X^2 + 7*X^3 + 61*X^4 + 51*X^5 + 12*X^6) = -1 + X + 3*X^2 + 3*X^3 :=
    mul_left_cancel₀ (show (X^6*(-16 + 32*X + 48*X^2) : ℚ⟦X⟧) ≠ 0 from mul_ne_zero (pow_ne_zero _ X_ne_zero) (fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h)) (by linear_combination (4*X^3 - 20*X^4 + 4*X^5 + 52*X^6 + 24*X^7)*e2 - (12*X^2 - 76*X^3 + 20*X^4 + 268*X^5 + 144*X^6)*hD + (4*X^6 - 24*X^7 + 20*X^8 + 48*X^9 + 16*X^10)*(S*e1 - 2*d⁄dX ℚ S*h1))
  have h : d⁄dX ℚ G * (X - 7*X^2 + 8*X^3 + 25*X^4 - 18*X^5 - 52*X^6 - 31*X^7 - 6*X^8) + G * (-2*X^2 + 17*X^3 - 7*X^4 - 61*X^5 - 51*X^6 - 12*X^7) = X - X^2 - 3*X^3 - 3*X^4 :=
    by linear_combination (-X)*h
  have h := congrArg (coeff (m+7)) h
  rcases m with _|m <;>
  simp [pow_succ, mul_sub, mul_add, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_derivative, ← map_ofNat (C : ℚ →+* _)] at h ⊢ <;>
  linarith
