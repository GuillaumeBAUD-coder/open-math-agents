import OMAStatements.S_oeis_a071717
import Mathlib
open PowerSeries
theorem OMA.solution : type_of% @OMA.S_oeis_a071717.main := by
  intro S c G h1 _ h2 h3 n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have z (k : ℕ) [k.AtLeastTwo] : d⁄dX ℚ (OfNat.ofNat k) = 0 := Derivation.map_natCast _ k
  have hD : (64*X^6)*G = 32*X^4 - 32*X^5 - 96*X^6 + (-32*X^4 - 32*X^5 + 32*X^6)*S := by
    linear_combination (64*X^6)*h3 + (16*X^4 + 8*X^5 + (32*X^5 + 16*X^6)*c + 32*X^7*c^2 + (-16*X^4 - 16*X^5)*S - 16*X^6*S*c + 8*X^5*S^2)*h2 + (16*X^4 + 24*X^5 - 8*X^5*S)*h1
  have e1 := congrArg (d⁄dX ℚ) h1
  have e2 := congrArg (d⁄dX ℚ) hD
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at e1 e2
  have h : d⁄dX ℚ G * (-X + 3*X^2 + 5*X^3 - 4*X^4) + G * (-2 + 5*X + 2*X^2 + 2*X^3) = -2 - X - 6*X^2 - 3*X^3 :=
    mul_left_cancel₀ (show (X^9*(4096) : ℚ⟦X⟧) ≠ 0 from mul_ne_zero (pow_ne_zero _ X_ne_zero) (fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h)) (by linear_combination (-64*X^4 + 192*X^5 + 320*X^6 - 256*X^7)*e2 - (-256*X^3 + 832*X^4 + 1792*X^5 - 1664*X^6)*hD + (1024*X^8 + 2048*X^9 - 1024*X^10 - 2048*X^11 + 1024*X^12)*(S*e1 - 2*d⁄dX ℚ S*h1))
  have h := congrArg (coeff (m+4)) h
  simp [pow_succ, mul_sub, mul_add, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_derivative, ← map_ofNat (C : ℚ →+* _)] at h ⊢
  linarith
