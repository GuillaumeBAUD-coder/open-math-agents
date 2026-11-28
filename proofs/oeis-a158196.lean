import OMAStatements.S_oeis_a158196
import Mathlib
open PowerSeries
theorem OMA.solution : type_of% @OMA.S_oeis_a158196.main := by
  intro S c G h1 _ h2 h3 n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have z (k : ℕ) [k.AtLeastTwo] : d⁄dX ℚ (OfNat.ofNat k) = 0 := Derivation.map_natCast _ k
  have hD : (-768*X^7 + 4096*X^8)*G = -128*X^6 + 512*X^7 + (128*X^6 - 1024*X^7)*S := by
    linear_combination (-384*X^7 + 1024*X^8 - 384*X^7*S)*h3 + (24*X^5 - 64*X^6 + (48*X^6 - 128*X^7)*c + (96*X^7 - 256*X^8)*c^2 + (192*X^8 - 512*X^9)*c^3 + (-288*X^6 + 768*X^7)*G + (-576*X^7 + 1536*X^8)*G*c + (-48*X^5 + 192*X^6)*S + (-48*X^6 + 256*X^7)*S*c + 256*X^8*S*c^2 + 192*X^8*S*c^3 - 768*X^7*S*G - 576*X^7*S*G*c - 192*X^6*S^2 + (-48*X^6 - 128*X^7)*S^2*c - 96*X^7*S^2*c^2 + 288*X^6*S^2*G + (48*X^5 + 64*X^6)*S^3 + 48*X^6*S^3*c - 24*X^5*S^4)*h2 + (-24*X^5 - 160*X^6 + 256*X^7 + (288*X^6 + 768*X^7)*G + (72*X^5 + 160*X^6)*S - 288*X^6*S*G + (-72*X^5 - 64*X^6)*S^2 + 24*X^5*S^3)*h1
  have e1 := congrArg (d⁄dX ℚ) h1
  have e2 := congrArg (d⁄dX ℚ) hD
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at e1 e2
  have h : d⁄dX ℚ G * (-3*X + 52*X^2 - 288*X^3 + 512*X^4) + G * (-3 + 38*X - 176*X^2 + 256*X^3) = -3 + 20*X - 32*X^2 :=
    mul_left_cancel₀ (show (X^12*(65536) : ℚ⟦X⟧) ≠ 0 from mul_ne_zero (pow_ne_zero _ X_ne_zero) (fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h)) (by linear_combination (256*X^6 - 3072*X^7 + 8192*X^8)*e2 - (1536*X^5 - 20992*X^6 + 61440*X^7)*hD + (16384*X^12 - 262144*X^13 + 1048576*X^14)*(S*e1 - 2*d⁄dX ℚ S*h1))
  have h := congrArg (coeff (m+3)) h
  rcases m with _|m <;>
  simp [pow_succ, mul_sub, mul_add, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_derivative, ← map_ofNat (C : ℚ →+* _)] at h ⊢ <;>
  linarith
