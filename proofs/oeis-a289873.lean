import OMAStatements.S_oeis_a289873
import Mathlib

open OMA.S_oeis_a289873 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a289873.main := by
  rw [show ((1-X)^3*(1+X)*(1-X+X^2)*(1+X+X^2) : ℚ⟦X⟧) = 1-(X+X)+X^2-X^6+(X^7+X^7)-X^8 by ring]
  ext n
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n
  iterate 10
    simp [mul_add, mul_sub, add_mul, sub_mul, ← mul_assoc, pow_succ, two_mul, a, coeff_X, coeff_one]
    try norm_num
  obtain ⟨i, j, hj, rfl⟩ : ∃ i j, j < 6 ∧ n = 6*i+j := ⟨n/6, n%6, by omega⟩
  interval_cases j <;>
  simp [mul_add, mul_sub, add_mul, sub_mul, ← mul_assoc, pow_succ, two_mul, a, coeff_X, coeff_one,
    add_assoc, show ∀ c, (6*i+c)%6 = c%6 by omega] <;> ring
