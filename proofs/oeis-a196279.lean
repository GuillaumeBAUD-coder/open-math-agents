import OMAStatements.S_oeis_a196279
import Mathlib

open OMA.S_oeis_a196279 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a196279.main := by
  have p (m : ℕ) : a (m+10) = a m + 1 := by
    simp only [a]
    omega
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    simp [p] <;> ring
  rw [show mk a * ((1 + X) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) * (X ^ 4 - X ^ 3 + X ^ 2 - X + 1) * (X - 1) ^ 2) = X^11*mk a - X^10*mk a - X^1*mk a + mk a by ring, show (X * (-2 + X - 2 * X ^ 3 + X ^ 4 - 2 * X ^ 6 + X ^ 7 + X ^ 9 + X ^ 2 + X ^ 5 + X ^ 8) : ℤ⟦X⟧) = -X^1-X^1+X^2+X^3-X^4-X^4+X^5+X^6-X^7-X^7+X^8+X^9+X^10 by ring]
  ext n
  rcases lt_or_ge n 11 with h | h
  · interval_cases n <;> simp [coeff_X_pow_mul', coeff_X_pow, coeff_X, a] <;> omega
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' h
    simp [coeff_X_pow_mul', coeff_X_pow, coeff_X, p] <;> ring
