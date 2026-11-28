import OMAStatements.S_oeis_a217214
import Mathlib
open PowerSeries
theorem OMA.solution : type_of% @OMA.S_oeis_a217214.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have z (k : ℕ) [k.AtLeastTwo] : d⁄dX ℚ (OfNat.ofNat k) = 0 := Derivation.map_natCast _ k
  have hD : (X^2 - 24*X^3 + 240*X^4 - 1280*X^5 + 3840*X^6 - 6144*X^7 + 4096*X^8)*G = X - 25*X^2 + 263*X^3 - 1496*X^4 + 4880*X^5 - 8704*X^6 + 6400*X^7 + 2048*X^8 - 4096*X^9 + (-X + 23*X^2 - 219*X^3 + 1100*X^4 - 3034*X^5 + 4152*X^6 - 1504*X^7 - 1408*X^8)*S := by
    linear_combination ((X - 12*X^2 + 48*X^3 - 64*X^4))*hG + (0)*hS
  have h1 := congrArg (d⁄dX ℚ) hS
  have h2 := congrArg (d⁄dX ℚ) hD
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at h1 h2
  have h : d⁄dX ℚ G * (X - 15*X^2 + 83*X^3 - 196*X^4 + 138*X^5 + 88*X^6) + G * (1 - 14*X + 71*X^2 - 154*X^3 + 146*X^4 - 44*X^5) = 8*X^3 + 72*X^4 - 240*X^5 - 44*X^6 := by
    exact mul_left_cancel₀ (show (X^2*(-2 + 72*X - 1152*X^2 + 10752*X^3 - 64512*X^4 + 258048*X^5 - 688128*X^6 + 1179648*X^7 - 1179648*X^8 + 524288*X^9) : ℚ⟦X⟧) ≠ 0 from mul_ne_zero (pow_ne_zero _ X_ne_zero) (fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h)) (by linear_combination (-2*X + 54*X^2 - 622*X^3 + 3952*X^4 - 14868*X^5 + 32576*X^6 - 36224*X^7 + 9216*X^8 + 11264*X^9)*h2 - (-2 + 104*X - 1774*X^2 + 14932*X^3 - 69940*X^4 + 183320*X^5 - 236960*X^6 + 67712*X^7 + 95744*X^8)*hD + (X^2 - 46*X^3 + 967*X^4 - 12274*X^5 + 104629*X^6 - 629668*X^7 + 2732892*X^8 - 8559744*X^9 + 18933540*X^10 - 27886432*X^11 + 23267776*X^12 - 3945472*X^13 - 9430016*X^14 + 4235264*X^15 + 1982464*X^16)*(S*h1 - 2*d⁄dX ℚ S*hS))
  have d1 := congrArg (d⁄dX ℚ) h
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at d1
  have h : (d⁄dX ℚ) (d⁄dX ℚ G) * (-423*X^2 - 423*X^3 + 17801*X^4 - 37364*X^5) + d⁄dX ℚ G * (872*X + 3510*X^2 + 4478*X^3 - 47462*X^4) + G * (1718 + 6074*X - 22460*X^2 + 14390*X^3) = 3592*X^3 + 33072*X^4 :=
    mul_left_cancel₀ (show (-1 + 11*X - 39*X^2 + 40*X^3 + 22*X^4 : ℚ⟦X⟧) ≠ 0 from fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h) (by linear_combination (-1718 - 5306*X + 39510*X^2)*h + (423*X + 2115*X^2 - 9341*X^3)*d1)
  have h := congrArg (coeff (m+5)) h
  simp [pow_succ, mul_sub, mul_add, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_derivative, ← map_ofNat (C : ℚ →+* _)] at h ⊢
  linarith
