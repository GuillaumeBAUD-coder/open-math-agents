import OMAStatements.S_oeis_a114698
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a114698.main := by
  open PowerSeries OMA.S_oeis_a114698 in
  refine ⟨?_, ?_⟩
  · have e : (1 - X : PowerSeries ℚ) ^ 2 = 1 - X ^ 1 * C (2:ℚ) + X ^ 2 := by
      simp only [map_ofNat]; ring
    have e2 : (1 + 16 * X + 3 * X ^ 2 : PowerSeries ℚ) = C (1:ℚ) + C (16:ℚ) * X ^ 1 + C (3:ℚ) * X ^ 2 := by
      simp only [map_ofNat, map_one]; ring
    rw [e, e2]
    ext n
    simp only [mul_add, mul_sub, mul_one, map_add, map_sub, ← mul_assoc, coeff_mul_X_pow', coeff_mul_C,
      coeff_C_mul_X_pow, coeff_C, coeff_C_mul, coeff_mk]
    rcases n with _ | _ | _ | n <;> simp [a] <;> push_cast <;> ring_nf <;> omega
  · intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    simp [a]
    omega
