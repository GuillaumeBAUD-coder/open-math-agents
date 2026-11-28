import OMAStatements.S_oeis_a116387
import Mathlib
open PowerSeries
theorem OMA.solution : type_of% @OMA.S_oeis_a116387.main := by
  intro S M G h1 _ h2 h3 n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have z (k : ℕ) [k.AtLeastTwo] : d⁄dX ℚ (OfNat.ofNat k) = 0 := Derivation.map_natCast _ k
  have hD : (4*X^2 - 16*X^3 - 12*X^4 + 56*X^5 + 48*X^6)*G = 2*X^2 - 4*X^3 - 6*X^4 + (2*X^2 - 2*X^3 - 8*X^4)*S := by
    linear_combination (2*X^2 - 4*X^3 - 6*X^4 + (2*X^2 - 2*X^3 - 8*X^4)*S)*h3 + ((1 - 2*X - 3*X^2)*S*G + (1 - X - 4*X^2)*S^2*G)*h2 + ((-4*X^2 + 8*X^3 + 16*X^4)*G + (-1 + X + 4*X^2)*S*G)*h1
  have e1 := congrArg (d⁄dX ℚ) h1
  have e2 := congrArg (d⁄dX ℚ) hD
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at e1 e2
  have h : d⁄dX ℚ G * (1 - 5*X - 3*X^2 + 33*X^3 + 10*X^4 - 68*X^5 - 48*X^6) + G * (-2 + 2*X + 14*X^2 + 14*X^3 - 40*X^4 - 48*X^5) = 2*X - 6*X^2 - 6*X^3 :=
    mul_left_cancel₀ (show (X^4*(16 - 32*X - 48*X^2) : ℚ⟦X⟧) ≠ 0 from mul_ne_zero (pow_ne_zero _ X_ne_zero) (fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h)) (by linear_combination (4*X^2 - 12*X^3 - 20*X^4 + 44*X^5 + 48*X^6)*e2 - (8*X - 32*X^2 - 72*X^3 + 192*X^4 + 240*X^5)*hD + (4*X^4 - 8*X^5 - 28*X^6 + 32*X^7 + 64*X^8)*(S*e1 - 2*d⁄dX ℚ S*h1))
  have d1 := congrArg (d⁄dX ℚ) h
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at d1
  have h : (d⁄dX ℚ) (d⁄dX ℚ G) * (17*X^2 + 17*X^3 - 391*X^4 - 17*X^5 + 1394*X^6 + 1020*X^7) + d⁄dX ℚ G * (-125*X + 146*X^2 + 533*X^3 - 722*X^4 + 2928*X^5 + 4320*X^6) + G * (250*X + 504*X^2 - 70*X^3 + 2280*X^5) = -216*X^2 + 30*X^3 :=
    mul_left_cancel₀ (show (-1 + X + 4*X^2 : ℚ⟦X⟧) ≠ 0 from fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h) (by linear_combination (125*X + 235*X^2)*h + (-17*X^2 - 85*X^3)*d1)
  have h := congrArg (coeff (m+5)) h
  rcases m with _|_|m <;>
  simp [pow_succ, mul_sub, mul_add, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_derivative, ← map_ofNat (C : ℚ →+* _)] at h ⊢ <;>
  linarith
