import OMAStatements.S_oeis_a128057
import Mathlib
open PowerSeries
theorem OMA.solution : type_of% @OMA.S_oeis_a128057.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have z (k : ℕ) [k.AtLeastTwo] : d⁄dX ℚ (OfNat.ofNat k) = 0 := Derivation.map_natCast _ k
  have hD : (-1 - 4*X^2)*G = 0 + (-1 - X)*S := by
    linear_combination ((-1)*S)*hG + ((1)*G)*hS
  have h1 := congrArg (d⁄dX ℚ) hS
  have h2 := congrArg (d⁄dX ℚ) hD
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at h1 h2
  have h : d⁄dX ℚ G * (1 + X + 4*X^2 + 4*X^3) + G * (-1 + 4*X) = 0 := by
    exact mul_left_cancel₀ (show (2 + 8*X^2 : ℚ⟦X⟧) ≠ 0 from fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h) (by linear_combination (-2 - 2*X - 8*X^2 - 8*X^3)*h2 - (-2 - 8*X - 16*X^2)*hD + (1 + 2*X + X^2)*(S*h1 - 2*d⁄dX ℚ S*hS))
  have d1 := congrArg (d⁄dX ℚ) h
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at d1
  have h : (d⁄dX ℚ) (d⁄dX ℚ G) * (5*X^2 + 20*X^4) + d⁄dX ℚ G * (-4*X + 44*X^3) + G * (4*X) = 0 :=
    mul_left_cancel₀ (show (1 + X : ℚ⟦X⟧) ≠ 0 from fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h) (by linear_combination (-4*X)*h + (5*X^2)*d1)
  have h := congrArg (coeff (m+2)) h
  rcases m with _|_|m <;>
  simp [pow_succ, mul_sub, mul_add, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_derivative, ← map_ofNat (C : ℚ →+* _)] at h ⊢ <;>
  linarith
