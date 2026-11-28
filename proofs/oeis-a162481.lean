import OMAStatements.S_oeis_a162481
import Mathlib
open PowerSeries
theorem OMA.solution : type_of% @OMA.S_oeis_a162481.main := by
  intro T G hT _ hG n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have z (k : ℕ) [k.AtLeastTwo] : d⁄dX ℚ (OfNat.ofNat k) = 0 := Derivation.map_natCast _ k
  have h1 := congrArg (d⁄dX ℚ) hT
  have h2 := congrArg (d⁄dX ℚ) hG
  simp [Derivation.leibniz, Derivation.leibniz_pow, z] at h1 h2
  have h : d⁄dX ℚ G * (4*X - 32*X^2 + 40*X^3 - 16*X^4 + 4*X^5) + G * (4 - 24*X + 56*X^2 - 16*X^3 + 4*X^4) = 4 + 8*X := by
    linear_combination 2*(1 - 8*X + 10*X^2 - 4*X^3 + X^4)*h2 - (-4 - 8*X)*hG - (1 - X)*T*h1 + (2*d⁄dX ℚ T*(1 - X) + T*(-3))*hT
  have h := congrArg (coeff (m+4)) h
  rcases m with _|m <;>
  simp [pow_succ, mul_sub, mul_add, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_derivative, ← map_ofNat (C : ℚ →+* _)] at h ⊢ <;>
  linarith
