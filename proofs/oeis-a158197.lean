import OMAStatements.S_oeis_a158197
import Mathlib
open PowerSeries
theorem OMA.solution : type_of% @OMA.S_oeis_a158197.main := by
  intro S c G h1 _ h2 h3 n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have z (k : ℕ) [k.AtLeastTwo] : d⁄dX ℚ (OfNat.ofNat k) = 0 := Derivation.map_natCast _ k
  have hD : (-1024*X^7 + 6400*X^8)*G = -128*X^6 + 512*X^7 + (128*X^6 - 1280*X^7)*S := by
    linear_combination (-512*X^7 + 1280*X^8 - 512*X^7*S)*h3 + (32*X^5 - 80*X^6 + (64*X^6 - 160*X^7)*c + (128*X^7 - 320*X^8)*c^2 + (256*X^8 - 640*X^9)*c^3 + (-512*X^6 + 1280*X^7)*G + (-1024*X^7 + 2560*X^8)*G*c + (-64*X^5 + 240*X^6)*S + (-64*X^6 + 320*X^7)*S*c + 320*X^8*S*c^2 + 256*X^8*S*c^3 - 1280*X^7*S*G - 1024*X^7*S*G*c - 240*X^6*S^2 + (-64*X^6 - 160*X^7)*S^2*c - 128*X^7*S^2*c^2 + 512*X^6*S^2*G + (64*X^5 + 80*X^6)*S^3 + 64*X^6*S^3*c - 32*X^5*S^4)*h2 + (-32*X^5 - 176*X^6 + 320*X^7 + (512*X^6 + 1280*X^7)*G + (96*X^5 + 192*X^6)*S - 512*X^6*S*G + (-96*X^5 - 80*X^6)*S^2 + 32*X^5*S^3)*h1
  have e1 := congrArg (d⁄dX ℚ) h1
  have e2 := congrArg (d⁄dX ℚ) hD
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at e1 e2
  have h : d⁄dX ℚ G * (-4*X + 81*X^2 - 510*X^3 + 1000*X^4) + G * (-4 + 58*X - 320*X^2 + 500*X^3) = -4 + 26*X - 40*X^2 :=
    mul_left_cancel₀ (show (X^12*(65536) : ℚ⟦X⟧) ≠ 0 from mul_ne_zero (pow_ne_zero _ X_ne_zero) (fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h)) (by linear_combination (256*X^6 - 3584*X^7 + 10240*X^8)*e2 - (1536*X^5 - 24576*X^6 + 76800*X^7)*hD + (16384*X^12 - 327680*X^13 + 1638400*X^14)*(S*e1 - 2*d⁄dX ℚ S*h1))
  have h := congrArg (coeff (m+3)) h
  rcases m with _|m <;>
  simp [pow_succ, mul_sub, mul_add, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_derivative, ← map_ofNat (C : ℚ →+* _)] at h ⊢ <;>
  linarith
