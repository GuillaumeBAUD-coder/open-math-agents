import OMAStatements.S_oeis_a135582
import Mathlib
open PowerSeries
theorem OMA.solution : type_of% @OMA.S_oeis_a135582.main := by
  intro S c G h1 _ h2 h3 n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have z (k : ℕ) [k.AtLeastTwo] : d⁄dX ℚ (OfNat.ofNat k) = 0 := Derivation.map_natCast _ k
  have hD : (4*X^2 - 12*X^3 - 4*X^4 + 32*X^5 - 8*X^6 - 28*X^7 + 16*X^8 + 16*X^9)*G = 4*X^2 - 6*X^3 - 6*X^4 + 4*X^5 + (-2*X^3 + 2*X^4 + 4*X^5)*S := by
    linear_combination (4*X^2 - 6*X^3 - 6*X^4 + 4*X^5 + (-2*X^3 + 2*X^4 + 4*X^5)*S)*h3 + ((2*X^3 - 5*X^4 - 4*X^5 + 11*X^6 + 4*X^7 - 4*X^8)*G + (-X^4 + 2*X^5 + 3*X^6 - 4*X^7 - 4*X^8)*S*G)*h2 + ((X^4 - 2*X^5 - 3*X^6 + 4*X^7 + 4*X^8)*G)*h1
  have e1 := congrArg (d⁄dX ℚ) h1
  have e2 := congrArg (d⁄dX ℚ) hD
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at e1 e2
  have h : d⁄dX ℚ G * (X - 6*X^2 + 7*X^3 + 7*X^4 - 13*X^5 + 2*X^6 + 8*X^7) + G * (-1 + 6*X - 5*X^2 + 8*X^3 - 21*X^4 + 2*X^5 + 28*X^6) = -1 + 6*X - X^2 :=
    mul_left_cancel₀ (show (X^4*(-16 + 32*X + 48*X^2 - 64*X^3 - 64*X^4) : ℚ⟦X⟧) ≠ 0 from mul_ne_zero (pow_ne_zero _ X_ne_zero) (fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h)) (by linear_combination (-4*X^3 + 20*X^4 - 8*X^5 - 32*X^6)*e2 - (-12*X^2 + 72*X^3 - 32*X^4 - 176*X^5)*hD + (4*X^6 - 8*X^7 - 12*X^8 + 16*X^9 + 16*X^10)*(S*e1 - 2*d⁄dX ℚ S*h1))
  have h := congrArg (coeff (m+6)) h
  rcases m with _|m <;>
  simp [pow_succ, mul_sub, mul_add, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_derivative, ← map_ofNat (C : ℚ →+* _)] at h ⊢ <;>
  linarith
