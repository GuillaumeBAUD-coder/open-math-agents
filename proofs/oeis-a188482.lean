import OMAStatements.S_oeis_a188482
import Mathlib
open PowerSeries
theorem OMA.solution : type_of% @OMA.S_oeis_a188482.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have z (k : ℕ) [k.AtLeastTwo] : d⁄dX ℚ (OfNat.ofNat k) = 0 := Derivation.map_natCast _ k
  have hD : (4 - 56*X + 260*X^2 - 328*X^3 - 552*X^4 + 736*X^5 + 1156*X^6 + 480*X^7 + 64*X^8)*G = 4 - 42*X + 122*X^2 + 4*X^3 - 258*X^4 - 176*X^5 - 32*X^6 + (2*X - 14*X^2 + 16*X^3 + 30*X^4 + 8*X^5)*S := by
    linear_combination ((2 - 14*X + 16*X^2 + 30*X^3 + 8*X^4))*hG + (0)*hS
  have h1 := congrArg (d⁄dX ℚ) hS
  have h2 := congrArg (d⁄dX ℚ) hD
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at h1 h2
  have h : d⁄dX ℚ G * (-X + 7*X^2 - 8*X^3 - 15*X^4 - 4*X^5) + G * (1 - 2*X - 2*X^2 - 22*X^3 - 10*X^4) = 1 - 2*X + X^2 := by
    exact mul_left_cancel₀ (show (-16 + 288*X - 1936*X^2 + 5472*X^3 - 3040*X^4 - 11776*X^5 + 7152*X^6 + 16576*X^7 + 7424*X^8 + 1024*X^9 : ℚ⟦X⟧) ≠ 0 from fun h => by simpa [← map_ofNat (C : ℚ →+* _)] using congrArg constantCoeff h) (by linear_combination (4*X - 44*X^2 + 144*X^3 - 68*X^4 - 224*X^5 - 64*X^6)*h2 - (4 - 80*X + 376*X^2 - 208*X^3 - 1000*X^4 - 352*X^5)*hD + (4*X^2 - 56*X^3 + 260*X^4 - 328*X^5 - 552*X^6 + 736*X^7 + 1156*X^8 + 480*X^9 + 64*X^10)*(S*h1 - 2*d⁄dX ℚ S*hS))
  have h := congrArg (coeff (m+4)) h
  rcases m with _|m <;>
  simp [pow_succ, mul_sub, mul_add, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_derivative, ← map_ofNat (C : ℚ →+* _)] at h ⊢ <;>
  linarith
