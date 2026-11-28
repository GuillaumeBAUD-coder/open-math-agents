import OMAStatements.S_oeis_a026672
import Mathlib
open PowerSeries
theorem OMA.solution : type_of% @OMA.S_oeis_a026672.main := by
  intro S c G h1 _ h2 h3 n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have z (k : ℕ) [k.AtLeastTwo] : d⁄dX ℚ (OfNat.ofNat k) = 0 := Derivation.map_natCast _ k
  have hD : (-256*X^6 + 1024*X^7 + 256*X^8)*G = 128*X^5 - 640*X^6 + 256*X^7 + (-128*X^5 + 384*X^6)*S := by
    linear_combination (-128*X^6 + 384*X^7 + 256*X^8 + (-128*X^6 + 128*X^7)*S)*h3 + (-8*X^3 + 24*X^4 + 16*X^5 + (-16*X^4 + 48*X^5 + 32*X^6)*c + (-32*X^5 + 96*X^6 + 64*X^7)*c^2 + (-64*X^6 + 192*X^7 + 128*X^8)*c^3 + (-16*X^4 + 48*X^5 + 32*X^6)*G + (-32*X^5 + 96*X^6 + 64*X^7)*G*c + (-64*X^6 + 192*X^7 + 128*X^8)*G*c^2 + (16*X^3 - 64*X^4 - 48*X^5)*S + (16*X^4 - 80*X^5 - 64*X^6)*S*c + (-64*X^6 - 64*X^7)*S*c^2 + (-64*X^6 + 64*X^7)*S*c^3 + (16*X^4 - 80*X^5 - 64*X^6)*S*G + (-64*X^6 - 64*X^7)*S*G*c + (-64*X^6 + 64*X^7)*S*G*c^2 + (48*X^4 + 48*X^5)*S^2 + (16*X^4 + 16*X^5 + 32*X^6)*S^2*c + (32*X^5 - 32*X^6)*S^2*c^2 + (16*X^4 + 16*X^5 + 32*X^6)*S^2*G + (32*X^5 - 32*X^6)*S^2*G*c + (-16*X^3 - 16*X^5)*S^3 + (-16*X^4 + 16*X^5)*S^3*c + (-16*X^4 + 16*X^5)*S^3*G + (8*X^3 - 8*X^4)*S^4)*h2 + (8*X^3 + 8*X^4 + 144*X^5 - 64*X^6 + (16*X^4 + 16*X^5 + 160*X^6)*G + (-24*X^3 - 8*X^4 - 96*X^5)*S + (-32*X^4 - 32*X^6)*S*G + (24*X^3 - 8*X^4 + 16*X^5)*S^2 + (16*X^4 - 16*X^5)*S^2*G + (-8*X^3 + 8*X^4)*S^3)*h1
  have e1 := congrArg (d⁄dX ℚ) h1
  have e2 := congrArg (d⁄dX ℚ) hD
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at e1 e2
  have h : d⁄dX ℚ G * (-X + 11*X^2 - 39*X^3 + 41*X^4 + 12*X^5) + G * (-1 + 10*X - 27*X^2 + 8*X^3 + 18*X^4) = -2*X + 6*X^2 + 6*X^3 :=
    mul_left_cancel₀ (show (X^10*(-65536) : ℚ⟦X⟧) ≠ 0 from mul_ne_zero (pow_ne_zero _ X_ne_zero) (fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h)) (by linear_combination (-256*X^5 + 1792*X^6 - 3072*X^7)*e2 - (-1280*X^4 + 10240*X^5 - 19968*X^6)*hD + (16384*X^10 - 98304*X^11 + 147456*X^12)*(S*e1 - 2*d⁄dX ℚ S*h1))
  have d1 := congrArg (d⁄dX ℚ) h
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at d1
  have h : (d⁄dX ℚ) (d⁄dX ℚ G) * (-X^2 + 8*X^3 - 15*X^4 - 4*X^5) + d⁄dX ℚ G * (4*X - 22*X^2 + 24*X^3 - 2*X^4) + G * (6 - 32*X + 12*X^2 + 12*X^3) = 10*X + 6*X^2 :=
    mul_left_cancel₀ (show (-1 + 3*X : ℚ⟦X⟧) ≠ 0 from fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h) (by linear_combination (6)*h + (-X)*d1)
  have h := congrArg (coeff (m+3)) h
  rcases m with _|_|m <;>
  simp [pow_succ, mul_sub, mul_add, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_derivative, ← map_ofNat (C : ℚ →+* _)] at h ⊢ <;>
  linarith
