import OMAStatements.S_oeis_a165201
import Mathlib
open PowerSeries
theorem OMA.solution : type_of% @OMA.S_oeis_a165201.main := by
  intro S c G h1 _ h2 h3 n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have z (k : ℕ) [k.AtLeastTwo] : d⁄dX ℚ (OfNat.ofNat k) = 0 := Derivation.map_natCast _ k
  have hD : (-64*X^4 + 256*X^5 + 64*X^6)*G = -32*X^4 + 96*X^5 + 64*X^6 + (-32*X^4 + 32*X^5)*S := by
    linear_combination (-32*X^4 + 96*X^5 + 64*X^6 + (-32*X^4 + 32*X^5)*S)*h3 + ((-4*X^2 + 12*X^3 + 8*X^4)*G + (-8*X^3 + 24*X^4 + 16*X^5)*G*c + (-16*X^4 + 48*X^5 + 32*X^6)*G*c^2 + (4*X^2 - 20*X^3 - 16*X^4)*S*G + (-16*X^4 - 16*X^5)*S*G*c + (-16*X^4 + 16*X^5)*S*G*c^2 + (4*X^2 + 4*X^3 + 8*X^4)*S^2*G + (8*X^3 - 8*X^4)*S^2*G*c + (-4*X^2 + 4*X^3)*S^3*G)*h2 + ((4*X^2 + 4*X^3 + 40*X^4)*G + (-8*X^2 - 8*X^4)*S*G + (4*X^2 - 4*X^3)*S^2*G)*h1
  have e1 := congrArg (d⁄dX ℚ) h1
  have e2 := congrArg (d⁄dX ℚ) hD
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at e1 e2
  have h : d⁄dX ℚ G * (-1 + 9*X - 23*X^2 + 11*X^3 + 4*X^4) + G * (1 - 15*X^2 + 2*X^3) = 2*X - 10*X^2 + 2*X^3 :=
    mul_left_cancel₀ (show (X^8*(-4096) : ℚ⟦X⟧) ≠ 0 from mul_ne_zero (pow_ne_zero _ X_ne_zero) (fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h)) (by linear_combination (-64*X^4 + 320*X^5 - 256*X^6)*e2 - (-256*X^3 + 1472*X^4 - 1408*X^5)*hD + (1024*X^8 - 2048*X^9 + 1024*X^10)*(S*e1 - 2*d⁄dX ℚ S*h1))
  have d1 := congrArg (d⁄dX ℚ) h
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at d1
  have h : (d⁄dX ℚ) (d⁄dX ℚ G) * (X^2 - 8*X^3 + 15*X^4 + 4*X^5) + d⁄dX ℚ G * (-2*X + 6*X^2 + 6*X^3 + 10*X^4) + G * (2*X + 2*X^2 + 2*X^3) = 2*X^2 + 2*X^3 :=
    mul_left_cancel₀ (show (-1 + X : ℚ⟦X⟧) ≠ 0 from fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h) (by linear_combination (-2*X)*h + (X^2)*d1)
  have h := congrArg (coeff (m+4)) h
  rcases m with _|m <;>
  simp [pow_succ, mul_sub, mul_add, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_derivative, ← map_ofNat (C : ℚ →+* _)] at h ⊢ <;>
  linarith
