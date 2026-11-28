import OMAStatements.S_oeis_a365847
import Mathlib

namespace OMA.S_oeis_a365847
open PowerSeries

lemma uniq (A A' : PowerSeries ℚ)
    (h : A * (1 - X * A) ^ 4 = (1 + X * A) ^ 4)
    (h' : A' * (1 - X * A') ^ 4 = (1 + X * A') ^ 4) : A = A' := by
  have key : (1 - X * ((4 + 6*X*(A+A') + 4*X^2*(A^2+A*A'+A'^2) + X^3*(A^3+A^2*A'+A*A'^2+A'^3)
      + 4*(A+A') - 6*X*(A^2+A*A'+A'^2) + 4*X^2*(A^3+A^2*A'+A*A'^2+A'^3)
      - X^3*(A^4+A^3*A'+A^2*A'^2+A*A'^3+A'^4)) : PowerSeries ℚ)) * (A - A') = 0 := by
    linear_combination h - h'
  rcases mul_eq_zero.mp key with h0 | h0
  · exfalso
    have := congrArg (constantCoeff) h0
    simp at this
  · exact sub_eq_zero.mp h0

end OMA.S_oeis_a365847

theorem OMA.solution : type_of% @OMA.S_oeis_a365847.main := by
  intro A B hA hB
  open PowerSeries in
  have hA' : A * (1 - X * A) ^ 4 = (1 + X * A) ^ 4 := by
    have : (X : PowerSeries ℚ) * (A * (1 - X * A) ^ 4) = X * (1 + X * A) ^ 4 := by
      linear_combination hA
    exact mul_left_cancel₀ (PowerSeries.X_ne_zero) this
  have hC : B ^ 4 * (1 - X * B ^ 4) ^ 4 = (1 + X * B ^ 4) ^ 4 := by
    have : B * (1 - X * B ^ 4) = 1 + X * B ^ 4 := by linear_combination hB
    calc B ^ 4 * (1 - X * B ^ 4) ^ 4 = (B * (1 - X * B ^ 4)) ^ 4 := by ring
      _ = _ := by rw [this]
  exact OMA.S_oeis_a365847.uniq A (B ^ 4) hA' hC
