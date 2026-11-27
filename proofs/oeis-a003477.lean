import OMAStatements.S_oeis_a003477
import Mathlib

namespace OMA.A003477Disproof

open PowerSeries Finset

noncomputable def P1 : ℤ⟦X⟧ := (1 - C 2 * X) * (1 + X ^ 2) * (1 - X - C 2 * X ^ 3)
noncomputable def P2 : ℤ⟦X⟧ := (1 - C 2 * X) * (1 + X ^ 2) * (1 - X)

theorem a_eq (n : ℕ) : OMA.S_oeis_a003477.a n = coeff n (invOfUnit P1 1) := rfl
theorem b_eq (n : ℕ) : OMA.S_oeis_a003477.b n = coeff n (invOfUnit P2 1) := rfl

theorem P1_eq : P1 = 1 - C 3 * X + C 3 * X ^ 2 - C 5 * X ^ 3 + C 6 * X ^ 4 - C 2 * X ^ 5
    + C 4 * X ^ 6 := by
  simp only [P1, map_ofNat]
  ring

theorem P2_eq : P2 = 1 - C 3 * X + C 3 * X ^ 2 - C 3 * X ^ 3 + C 2 * X ^ 4 := by
  simp only [P2, map_ofNat]
  ring

theorem c1 (n : ℕ) : coeff n P1 = if n = 0 then 1 else if n = 1 then -3 else if n = 2 then 3
    else if n = 3 then -5 else if n = 4 then 6 else if n = 5 then -2 else if n = 6 then 4 else 0 := by
  rw [P1_eq]
  rcases n with _ | _ | _ | _ | _ | _ | _ | n <;>
    simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_one] <;> simp

theorem c2 (n : ℕ) : coeff n P2 = if n = 0 then 1 else if n = 1 then -3 else if n = 2 then 3
    else if n = 3 then -3 else if n = 4 then 2 else 0 := by
  rw [P2_eq]
  rcases n with _ | _ | _ | _ | _ | n <;>
    simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_one] <;> simp

theorem k1 : constantCoeff P1 = ((1 : ℤˣ) : ℤ) := by
  rw [← coeff_zero_eq_constantCoeff_apply, c1]; rfl

theorem k2 : constantCoeff P2 = ((1 : ℤˣ) : ℤ) := by
  rw [← coeff_zero_eq_constantCoeff_apply, c2]; rfl

end OMA.A003477Disproof

open OMA.A003477Disproof PowerSeries Finset in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a003477.main) := by
  intro h
  have h4 := h 4 le_rfl
  simp only [a_eq, b_eq, show 4 - 3 = 1 from rfl, sum_range_one] at h4
  have e1 := invOfUnit_mul P1 1 k1
  have e2 := invOfUnit_mul P2 1 k2
  have q : ∀ n : ℕ, coeff n (invOfUnit P1 1 * P1) = coeff n (1 : ℤ⟦X⟧) := fun n => by rw [e1]
  have r : ∀ n : ℕ, coeff n (invOfUnit P2 1 * P2) = coeff n (1 : ℤ⟦X⟧) := fun n => by rw [e2]
  have q0 := q 0
  have q1 := q 1
  have q2 := q 2
  have q3 := q 3
  have q4 := q 4
  have r0 := r 0
  have r1 := r 1
  have r2 := r 2
  have r3 := r 3
  have r4 := r 4
  simp only [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ,
    sum_range_zero, c1, c2, coeff_one] at q0 q1 q2 q3 q4 r0 r1 r2 r3 r4
  norm_num at q0 q1 q2 q3 q4 r0 r1 r2 r3 r4
  linarith
