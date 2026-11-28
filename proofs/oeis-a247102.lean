import OMAStatements.S_oeis_a247102
import Mathlib
open PowerSeries
theorem OMA.solution : type_of% @OMA.S_oeis_a247102.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have z (k : ℕ) [k.AtLeastTwo] : d⁄dX ℚ (OfNat.ofNat k) = 0 := Derivation.map_natCast _ k
  have hD : (-16*X^2 + 64*X^3 + 224*X^4 + 192*X^5 + 48*X^6)*G = 8*X - 24*X^2 - 152*X^3 - 168*X^4 - 48*X^5 + (-8*X - 32*X^2 - 24*X^3)*S := by
    linear_combination ((-4*X - 4*X^2)*S)*hG + ((8*X + 24*X^2 + 16*X^3) + (16*X^2 + 32*X^3 + 16*X^4)*G)*hS
  have h1 := congrArg (d⁄dX ℚ) hS
  have h2 := congrArg (d⁄dX ℚ) hD
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at h1 h2
  have h : d⁄dX ℚ G * (X - 2*X^2 - 24*X^3 - 30*X^4 - 9*X^5) + G * (1 - 7*X - 27*X^2 - 45*X^3 - 18*X^4) = 2 + 6*X + 15*X^2 + 9*X^3 := by
    exact mul_left_cancel₀ (show (X^2*(256 - 1024*X - 3584*X^2 - 3072*X^3 - 768*X^4) : ℚ⟦X⟧) ≠ 0 from mul_ne_zero (pow_ne_zero _ X_ne_zero) (fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h)) (by linear_combination (-16*X + 32*X^2 + 384*X^3 + 480*X^4 + 144*X^5)*h2 - (-16 + 16*X + 912*X^2 + 1584*X^3 + 576*X^4)*hD + (64*X^2 + 512*X^3 + 1408*X^4 + 1536*X^5 + 576*X^6)*(S*h1 - 2*d⁄dX ℚ S*hS))
  have h := congrArg (coeff (m+4)) h
  rcases m with _|m <;>
  simp [pow_succ, mul_sub, mul_add, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_derivative, ← map_ofNat (C : ℚ →+* _)] at h ⊢ <;>
  linarith
