import OMAStatements.S_oeis_a172064
import Mathlib
open PowerSeries
theorem OMA.solution : type_of% @OMA.S_oeis_a172064.main := by
  intro S c G h1 _ h2 h3 n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have z (k : ℕ) [k.AtLeastTwo] : d⁄dX ℚ (OfNat.ofNat k) = 0 := Derivation.map_natCast _ k
  have hD : (-131072*X^14 + 458752*X^15 + 262144*X^16)*G = 32768*X^7 - 262144*X^8 + 589824*X^9 - 196608*X^10 - 262144*X^11 + (-32768*X^7 + 196608*X^8 - 262144*X^9 - 65536*X^10 + 65536*X^11)*S := by
    linear_combination (-16384*X^14 + 65536*X^15 - 49152*X^14*S)*h3 + (-256*X^7 + 1024*X^8 + (-512*X^8 + 2048*X^9)*c + (-1024*X^9 + 4096*X^10)*c^2 + (-2048*X^10 + 8192*X^11)*c^3 + (-4096*X^11 + 16384*X^12)*c^4 + (-8192*X^12 + 32768*X^13)*c^5 + (-16384*X^13 + 65536*X^14)*c^6 + (768*X^7 - 6144*X^8)*S + (1024*X^8 - 10240*X^9)*S*c + (1024*X^9 - 16384*X^10)*S*c^2 - 24576*X^11*S*c^3 + (-4096*X^11 - 32768*X^12)*S*c^4 + (-16384*X^12 - 32768*X^13)*S*c^5 - 49152*X^13*S*c^6 + (768*X^7 + 15360*X^8)*S^2 + (2560*X^8 + 20480*X^9)*S^2*c + (6144*X^9 + 24576*X^10)*S^2*c^2 + (12288*X^10 + 24576*X^11)*S^2*c^3 + (20480*X^11 + 16384*X^12)*S^2*c^4 + 24576*X^12*S^2*c^5 + (-6400*X^7 - 20480*X^8)*S^3 + (-10240*X^8 - 20480*X^9)*S^3*c + (-14336*X^9 - 16384*X^10)*S^3*c^2 + (-16384*X^10 - 8192*X^11)*S^3*c^3 - 12288*X^11*S^3*c^4 + (11520*X^7 + 15360*X^8)*S^4 + (12800*X^8 + 10240*X^9)*S^4*c + (11264*X^9 + 4096*X^10)*S^4*c^2 + 6144*X^10*S^4*c^3 + (-9984*X^7 - 6144*X^8)*S^5 + (-7168*X^8 - 2048*X^9)*S^5*c - 3072*X^9*S^5*c^2 + (4352*X^7 + 1024*X^8)*S^6 + 1536*X^8*S^6*c - 768*X^7*S^7)*h2 + (33024*X^7 - 131072*X^8 + 65536*X^9 + 65536*X^10 + 147456*X^14*G + (-33792*X^7 + 68608*X^8 + 12288*X^9 - 16384*X^10)*S + (33024*X^7 - 20480*X^8 - 16384*X^9)*S^2 + (-26624*X^7 - 2048*X^8 + 4096*X^9)*S^3 + (15104*X^7 + 4096*X^8)*S^4 + (-5120*X^7 - 1024*X^8)*S^5 + 768*X^7*S^6)*h1
  have e1 := congrArg (d⁄dX ℚ) h1
  have e2 := congrArg (d⁄dX ℚ) hD
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at e1 e2
  have h : d⁄dX ℚ G * (-2*X + 19*X^2 - 54*X^3 + 28*X^4 + 50*X^5 - 6*X^6 - 8*X^7) + G * (-14 + 124*X - 316*X^2 + 108*X^3 + 282*X^4 - 4*X^5 - 36*X^6) = -14 - 4*X :=
    mul_left_cancel₀ (show (X^20*(-4294967296 + 17179869184*X) : ℚ⟦X⟧) ≠ 0 from mul_ne_zero (pow_ne_zero _ X_ne_zero) (fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h)) (by linear_combination (-65536*X^7 + 655360*X^8 - 2097152*X^9 + 1966080*X^10 + 655360*X^11 - 524288*X^12)*e2 - (-458752*X^6 + 5111808*X^7 - 18087936*X^8 + 18612224*X^9 + 6946816*X^10 - 6029312*X^11)*hD + (1073741824*X^14 - 12884901888*X^15 + 55834574848*X^16 - 98784247808*X^17 + 38654705664*X^18 + 60129542144*X^19 - 30064771072*X^20 - 8589934592*X^21 + 4294967296*X^22)*(S*e1 - 2*d⁄dX ℚ S*h1))
  have d1 := congrArg (d⁄dX ℚ) h
  have d2 := congrArg (d⁄dX ℚ) d1
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at d1 d2
  have h : (d⁄dX ℚ) ((d⁄dX ℚ) (d⁄dX ℚ G)) * (6*X^3 - 21*X^4 - 12*X^5) + (d⁄dX ℚ) (d⁄dX ℚ G) * (82*X^2 - 338*X^3 - 230*X^4) + d⁄dX ℚ G * (224*X - 1502*X^2 - 1236*X^3) + G * (-1792*X - 1800*X^2) = 0 :=
    mul_left_cancel₀ (show (1 - 12*X + 52*X^2 - 92*X^3 + 36*X^4 + 56*X^5 - 28*X^6 - 8*X^7 + 4*X^8 : ℚ⟦X⟧) ≠ 0 from fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h) (by linear_combination (4*X - 20*X^2 + 24*X^3 - 4*X^4)*h + (-14*X + 66*X^2 - 64*X^3 - 10*X^4 + 4*X^5)*d1 + (-3*X^2 + 18*X^3 - 24*X^4 - 6*X^5 + 6*X^6)*d2)
  have h := congrArg (coeff (m+2)) h
  rcases m with _|_|_|m <;>
  simp [pow_succ, mul_sub, mul_add, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_derivative, ← map_ofNat (C : ℚ →+* _)] at h ⊢ <;>
  linarith
