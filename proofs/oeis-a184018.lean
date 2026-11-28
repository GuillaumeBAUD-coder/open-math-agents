import OMAStatements.S_oeis_a184018
import Mathlib
open PowerSeries
theorem OMA.solution : type_of% @OMA.S_oeis_a184018.main := by
  intro T G hT _ hG n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have z (k : ℕ) [k.AtLeastTwo] : d⁄dX ℚ (OfNat.ofNat k) = 0 := Derivation.map_natCast _ k
  have h1 := congrArg (d⁄dX ℚ) hT
  have h2 := congrArg (d⁄dX ℚ) hG
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at h1 h2
  have h : d⁄dX ℚ G * (4*X - 24*X^2 + 12*X^3 + 24*X^4 + 4*X^5) + G * (4 - 16*X + 12*X^2 + 32*X^3 + 4*X^4) = 4 + 4*X^2 := by
    linear_combination 2*(1 - 6*X + 3*X^2 + 6*X^3 + X^4)*h2 - (-4 - 4*X^2)*hG - (1 - X - X^2)*T*h1 + (2*d⁄dX ℚ T*(1 - X - X^2) + T*(-1 - 2*X))*hT
  have h := congrArg (coeff (m+4)) h
  rcases m with _|m <;>
  simp [pow_succ, mul_sub, mul_add, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_derivative, ← map_ofNat (C : ℚ →+* _)] at h ⊢ <;>
  linarith
