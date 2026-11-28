import OMAStatements.S_oeis_a144135
import Mathlib

open PowerSeries OMA.S_oeis_a144135 in
theorem OMA.solution : type_of% @OMA.S_oeis_a144135.main := by
  have R (k : ℕ) : a (k+4) = 32 * a (k+3) - 258 * a (k+2) + 32 * a (k+1) - a k := by
    simp [a, gegenbauer, add_assoc]
    ring_nf
    field_simp
    ring
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
    exact R k
  · suffices h : mk a * (X^2 - 16*X + 1)^2 = 1 by rw [mul_assoc, h, mul_one]
    rw [show ((X:ℚ⟦X⟧)^2 - 16*X + 1)^2 = C 1 * X^0 + C (-32) * X^1 + C 258 * X^2 + C (-32) * X^3 + C 1 * X^4 by
      simp only [map_neg, map_ofNat, map_one]; ring]
    ext n
    simp only [mul_add, map_add, ← mul_assoc, coeff_mul_X_pow', coeff_mul_C, coeff_mk]
    rcases n with _|_|_|_|n
    iterate 4 norm_num [a, gegenbauer]
    simp [R]
    ring
