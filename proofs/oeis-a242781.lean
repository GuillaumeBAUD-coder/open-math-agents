import OMAStatements.S_oeis_a242781
import Mathlib
open PowerSeries
theorem OMA.solution : type_of% @OMA.S_oeis_a242781.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have z (k : ℕ) [k.AtLeastTwo] : d⁄dX ℚ (OfNat.ofNat k) = 0 := Derivation.map_natCast _ k
  have hD : (-12*X + 48*X^2 - 4*X^3 + 16*X^4)*G = 2 - 8*X + 2*X^2 - 8*X^3 + (-2 + 4*X + 2*X^2)*S := by
    linear_combination ((1 - 5*X + 4*X^2) + (-1 - 3*X)*S)*hG + ((1 + 3*X) + (1 + 6*X + 9*X^2)*G)*hS
  have h1 := congrArg (d⁄dX ℚ) hS
  have h2 := congrArg (d⁄dX ℚ) hD
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at h1 h2
  have h : d⁄dX ℚ G * (3*X - 18*X^2 + 22*X^3 + 6*X^4 + 7*X^5 + 4*X^6) + G * (3 - 18*X + 18*X^2 - 24*X^3 + 19*X^4 + 6*X^5) = 9*X^2 - 6*X^3 - X^4 := by
    exact mul_left_cancel₀ (show (16 - 64*X : ℚ⟦X⟧) ≠ 0 from fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h) (by linear_combination (-4 + 24*X - 28*X^2 - 16*X^3)*h2 - (16 - 40*X - 40*X^2)*hD + (4 - 16*X + 8*X^2 + 16*X^3 + 4*X^4)*(S*h1 - 2*d⁄dX ℚ S*hS))
  have h := congrArg (coeff (m+5)) h
  rcases m with _|m <;>
  simp [pow_succ, mul_sub, mul_add, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_derivative, ← map_ofNat (C : ℚ →+* _)] at h ⊢ <;>
  linarith
