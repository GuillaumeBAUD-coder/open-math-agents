import OMAStatements.S_oeis_a337499
import Mathlib
open PowerSeries
theorem OMA.solution : type_of% @OMA.S_oeis_a337499.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have z (k : ℕ) [k.AtLeastTwo] : d⁄dX ℚ (OfNat.ofNat k) = 0 := Derivation.map_natCast _ k
  have hD : (-16*X^4 + 64*X^6)*G = 16*X^2 + 16*X^3 - 64*X^4 - 64*X^5 + (-16*X^2 - 16*X^3 + 16*X^4)*S := by
    linear_combination ((2 - 8*X^2) + (-2 + 4*X^2)*S)*hG + ((-4 - 8*X + 8*X^2 + 16*X^3) + (16*X^4)*G + (2)*S*G + (2 - 4*X^2)*S^2*G)*hS
  have h1 := congrArg (d⁄dX ℚ) hS
  have h2 := congrArg (d⁄dX ℚ) hD
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at h1 h2
  have h : d⁄dX ℚ G * (X + X^2 - 5*X^3 - 4*X^4 + 4*X^5) + G * (2 + X - 12*X^2 - 8*X^3 + 4*X^4) = 2 + 7*X + 8*X^2 := by
    exact mul_left_cancel₀ (show (X^5*(512 - 2048*X^2) : ℚ⟦X⟧) ≠ 0 from mul_ne_zero (pow_ne_zero _ X_ne_zero) (fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h)) (by linear_combination (-32*X^2 - 32*X^3 + 160*X^4 + 128*X^5 - 128*X^6)*h2 - (-64*X - 96*X^2 + 512*X^3 + 512*X^4 - 640*X^5)*hD + (256*X^4 + 512*X^5 - 256*X^6 - 512*X^7 + 256*X^8)*(S*h1 - 2*d⁄dX ℚ S*hS))
  have h := congrArg (coeff (m+4)) h
  rcases m with _|m <;>
  simp [pow_succ, mul_sub, mul_add, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_derivative, ← map_ofNat (C : ℚ →+* _)] at h ⊢ <;>
  linarith
