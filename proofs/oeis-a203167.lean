import OMAStatements.S_oeis_a203167
import Mathlib

open OMA.S_oeis_a203167 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a203167.main := by
  have h (n : ℕ) : a (n+6) = 8 * a (n+3) - 16 * a n := by
    obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 3 ∧ n = 3*q+r := ⟨n/3, n%3, by omega⟩
    rcases hp : products (3*q) with ⟨p, e⟩
    interval_cases r <;>
    simp [a, products, digit, hp, add_assoc, show ∀ c, (3*q+c)%3 = c%3 by omega] <;> ring
  constructor
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
    exact h (k+1)
  · rw [mul_comm]
    ext (_ | _ | _ | _ | _ | _ | n) <;>
    simp [pow_succ, mul_sub, sub_mul, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_C, coeff_mul_C,
      -eq_intCast] <;>
    first | linarith [h n] | simp [a, products, digit]
