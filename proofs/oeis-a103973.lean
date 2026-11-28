import OMAStatements.S_oeis_a103973
import Mathlib
open PowerSeries
theorem OMA.solution : type_of% @OMA.S_oeis_a103973.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have z (k : ℕ) [k.AtLeastTwo] : d⁄dX ℚ (OfNat.ofNat k) = 0 := Derivation.map_natCast _ k
  have hD : (-4*X^2 + 32*X^4)*G = -2*X + 16*X^3 + (2*X - 4*X^2 - 16*X^3)*S := by
    linear_combination ((-2*X)*S)*hG + ((-2*X) + (4*X^2)*G)*hS
  have h1 := congrArg (d⁄dX ℚ) hS
  have h2 := congrArg (d⁄dX ℚ) hD
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at h1 h2
  have h : d⁄dX ℚ G * (-X + 2*X^2 + 16*X^3 - 16*X^4 - 64*X^5) + G * (-1 + 8*X^2 - 16*X^3) = -1 - 4*X + 32*X^3 := by
    exact mul_left_cancel₀ (show (X^2*(16 - 128*X^2) : ℚ⟦X⟧) ≠ 0 from mul_ne_zero (pow_ne_zero _ X_ne_zero) (fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h)) (by linear_combination (4*X - 8*X^2 - 64*X^3 + 64*X^4 + 256*X^5)*h2 - (4 - 16*X - 160*X^2 + 192*X^3 + 1024*X^4)*hD + (4*X^2 - 16*X^3 - 48*X^4 + 128*X^5 + 256*X^6)*(S*h1 - 2*d⁄dX ℚ S*hS))
  have d1 := congrArg (d⁄dX ℚ) h
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at d1
  have h : (d⁄dX ℚ) (d⁄dX ℚ G) * (11*X^2 + 16*X^3 - 88*X^4 - 128*X^5) + d⁄dX ℚ G * (22*X + 52*X^2 - 440*X^3 - 800*X^4) + G * (20*X - 136*X^2) = 64*X + 272*X^2 :=
    mul_left_cancel₀ (show (-1 + 2*X + 8*X^2 : ℚ⟦X⟧) ≠ 0 from fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h) (by linear_combination (20*X)*h + (11*X + 16*X^2)*d1)
  have h := congrArg (coeff (m+3)) h
  rcases m with _|_|m <;>
  simp [pow_succ, mul_sub, mul_add, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_derivative, ← map_ofNat (C : ℚ →+* _)] at h ⊢ <;>
  linarith
