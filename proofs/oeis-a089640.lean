import OMAStatements.S_oeis_a089640
import Mathlib

open OMA.S_oeis_a089640 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a089640.main := by
  have key (F : ℤ⟦X⟧) : F * (X^5+2*X^4+X^3-1) = X^5*F + X^4*F + X^4*F + X^3*F - F := by ring
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    simp [a, ways]
    ring
  rw [key]
  ext n
  rcases lt_or_ge n 6 with h | h
  · interval_cases n <;> simp [coeff_X_pow_mul', coeff_X_pow, coeff_X, a, ways]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' h
    simp [coeff_X_pow_mul', coeff_X_pow, coeff_X, a, ways]
    ring
