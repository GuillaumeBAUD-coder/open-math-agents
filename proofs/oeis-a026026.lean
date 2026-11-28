import OMAStatements.S_oeis_a026026
import Mathlib
open PowerSeries
theorem OMA.solution : type_of% @OMA.S_oeis_a026026.main := by
  intro S c G h1 _ h2 h3 n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have z (k : ℕ) [k.AtLeastTwo] : d⁄dX ℚ (OfNat.ofNat k) = 0 := Derivation.map_natCast _ k
  have hD : (16384*X^14)*G = 8192*X^11 - 57344*X^12 + 122880*X^13 - 81920*X^14 + (-8192*X^11 + 40960*X^12 - 57344*X^13 + 16384*X^14)*S := by
    linear_combination (16384*X^14)*h3 + (128*X^11 + 2048*X^13 + (256*X^12 + 4096*X^14)*c + (512*X^13 + 8192*X^15)*c^2 + 1024*X^14*c^3 + 2048*X^15*c^4 + 4096*X^16*c^5 + 8192*X^17*c^6 + (-768*X^11 - 4096*X^13)*S + (-1280*X^12 - 4096*X^14)*S*c - 2048*X^13*S*c^2 - 3072*X^14*S*c^3 - 4096*X^15*S*c^4 - 4096*X^16*S*c^5 + (1920*X^11 + 2048*X^13)*S^2 + 2560*X^12*S^2*c + 3072*X^13*S^2*c^2 + 3072*X^14*S^2*c^3 + 2048*X^15*S^2*c^4 - 2560*X^11*S^3 - 2560*X^12*S^3*c - 2048*X^13*S^3*c^2 - 1024*X^14*S^3*c^3 + 1920*X^11*S^4 + 1280*X^12*S^4*c + 512*X^13*S^4*c^2 - 768*X^11*S^5 - 256*X^12*S^5*c + 128*X^11*S^6)*h2 + (8064*X^11 - 25088*X^12 + 20480*X^13 + (-7296*X^11 + 11776*X^12 - 4096*X^13)*S + (5376*X^11 - 3584*X^12)*S^2 + (-2816*X^11 + 512*X^12)*S^3 + 896*X^11*S^4 - 128*X^11*S^5)*h1
  have e1 := congrArg (d⁄dX ℚ) h1
  have e2 := congrArg (d⁄dX ℚ) hD
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at e1 e2
  have h : d⁄dX ℚ G * (X - 9*X^2 + 27*X^3 - 30*X^4 + 8*X^5) + G * (3 - 20*X + 37*X^2 - 14*X^3 - 4*X^4) = 5*X^2 - 20*X^3 + 20*X^4 :=
    mul_left_cancel₀ (show (X^24*(-268435456) : ℚ⟦X⟧) ≠ 0 from mul_ne_zero (pow_ne_zero _ X_ne_zero) (fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h)) (by linear_combination (-16384*X^11 + 147456*X^12 - 442368*X^13 + 491520*X^14 - 131072*X^15)*e2 - (-180224*X^10 + 1736704*X^11 - 5586944*X^12 + 6651904*X^13 - 1900544*X^14)*hD + (67108864*X^22 - 671088640*X^23 + 2617245696*X^24 - 4966055936*X^25 + 4630511616*X^26 - 1879048192*X^27 + 268435456*X^28)*(S*e1 - 2*d⁄dX ℚ S*h1))
  have d1 := congrArg (d⁄dX ℚ) h
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at d1
  have h : (d⁄dX ℚ) (d⁄dX ℚ G) * (-11*X^2 + 70*X^3 - 104*X^4) + d⁄dX ℚ G * (-6*X + 38*X^2 - 20*X^3) + G * (114 - 306*X - 16*X^2) = 80*X^2 :=
    mul_left_cancel₀ (show (-1 + 5*X - 7*X^2 + 2*X^3 : ℚ⟦X⟧) ≠ 0 from fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h) (by linear_combination (-38 + 112*X)*h + (11*X - 26*X^2)*d1)
  have h := congrArg (coeff (m+3)) h
  rcases m with _|m <;>
  simp [pow_succ, mul_sub, mul_add, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_derivative, ← map_ofNat (C : ℚ →+* _)] at h ⊢ <;>
  linarith
