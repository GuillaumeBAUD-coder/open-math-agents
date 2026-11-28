import OMAStatements.S_oeis_a134119
import Mathlib

open OMA.S_oeis_a134119 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a134119.main := by
  have A (n : ℕ) : a n = (n:ℤ)^2/(10:ℕ) - ((n:ℤ)-1)^2/(10:ℕ) := by
    rw [a, ← Rat.floor_intCast_div_natCast, ← Rat.floor_intCast_div_natCast]
    push_cast
    rfl
  rw [show mk a * (X^11 - X^10 - X + 1 : ℤ⟦X⟧) = X^11*mk a - X^10*mk a - X^1*mk a + mk a by ring, show (X^4*(X^4+1) : ℤ⟦X⟧) = X^8+X^4 by ring]
  ext n
  rcases lt_or_ge n 11 with h | h
  · interval_cases n <;> simp [coeff_X_pow_mul', coeff_X_pow, A]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' h
    simp [coeff_X_pow_mul', coeff_X_pow, A]
    ring_nf
    omega
