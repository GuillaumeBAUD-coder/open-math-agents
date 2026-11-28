import OMAStatements.S_oeis_a172025
import Mathlib
open PowerSeries
theorem OMA.solution : type_of% @OMA.S_oeis_a172025.main := by
  intro S c G h1 _ h2 h3 n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have z (k : ℕ) [k.AtLeastTwo] : d⁄dX ℚ (OfNat.ofNat k) = 0 := Derivation.map_natCast _ k
  have hD : (-512*X^6 + 1792*X^7 + 1024*X^8)*G = 128*X^3 - 512*X^4 + (-128*X^3 + 256*X^4 + 256*X^5)*S := by
    linear_combination (-64*X^6 + 256*X^7 - 192*X^6*S)*h3 + (-16*X^3 + 64*X^4 + (-32*X^4 + 128*X^5)*c + (-64*X^5 + 256*X^6)*c^2 + (-16*X^3 - 128*X^4)*S + (-64*X^4 - 128*X^5)*S*c - 192*X^5*S*c^2 + (80*X^3 + 64*X^4)*S^2 + 96*X^4*S^2*c - 48*X^3*S^3)*h2 + (144*X^3 + 576*X^6*G + (-128*X^3 - 64*X^4)*S + 48*X^3*S^2)*h1
  have e1 := congrArg (d⁄dX ℚ) h1
  have e2 := congrArg (d⁄dX ℚ) hD
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at e1 e2
  have h : d⁄dX ℚ G * (2*X - 11*X^2 + 6*X^3 + 22*X^4 + 8*X^5) + G * (6 - 32*X + 12*X^2 + 48*X^3 + 20*X^4) = 6 :=
    mul_left_cancel₀ (show (X^8*(65536 - 262144*X) : ℚ⟦X⟧) ≠ 0 from mul_ne_zero (pow_ne_zero _ X_ne_zero) (fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h)) (by linear_combination (-256*X^3 + 1536*X^4 - 1536*X^5 - 2048*X^6)*e2 - (-768*X^2 + 5632*X^3 - 6656*X^4 - 11264*X^5)*hD + (16384*X^6 - 65536*X^7 + 131072*X^9 + 65536*X^10)*(S*e1 - 2*d⁄dX ℚ S*h1))
  have d1 := congrArg (d⁄dX ℚ) h
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at d1
  have h : (d⁄dX ℚ) (d⁄dX ℚ G) * (2*X^2 - 7*X^3 - 4*X^4) + d⁄dX ℚ G * (8*X - 38*X^2 - 30*X^3) + G * (-32*X - 40*X^2) = 0 :=
    mul_left_cancel₀ (show (-1 + 2*X + 2*X^2 : ℚ⟦X⟧) ≠ 0 from fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h) (by linear_combination (-X)*d1)
  have h := congrArg (coeff (m+2)) h
  rcases m with _|_|m <;>
  simp [pow_succ, mul_sub, mul_add, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_derivative, ← map_ofNat (C : ℚ →+* _)] at h ⊢ <;>
  linarith
